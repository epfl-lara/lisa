package lisa.hol

import lisa.SetTheoryLibrary
import lisa.hol.HOLHelperTheorems._
import lisa.hol.VarsAndFunctions._
import lisa.hol.extractor._
import lisa.hol.{core => h}
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.unification.UnificationUtils.RewriteContext
import lisa.utils.unification.UnificationUtils.matchExpr

import scala.collection.mutable

object Import extends lisa.HOL:
  val lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary
  type Justification = lib.JUSTIFICATION

  val itr: Iterator[(String, JustifiedTheorem)] = ???

  sealed trait ImportException extends Exception
  case class InvalidAbstractionException(term: h.Term) extends Exception(s"Invalid abstraction term: $term. Expected a variable.") with ImportException
  case class InvalidDefinitionException(name: String, term: h.Term) extends Exception(s"Invalid definition for constant $name: $term. Expected a term of the form 'name = body'.") with ImportException
  case class MalformedConstantInstance(name: String, tpe: h.Type) extends Exception(s"Malformed instance of constant $name with type $tpe. No matching definition found.") with ImportException
  case class UnknownAxiom(expr: Expr[Ind]) extends Exception(s"Unknown axiom: $expr. No matching HOL Light axiom found.") with ImportException

  object Axioms:
    val infinityAx = HOLBasics.infinityAx
    val etaAx = HOLBasics.etaAx
    val selectAx = HOLBasics.selectAx

    private val axioms = Seq(
      infinityAx,
      etaAx,
      selectAx
    )

    def fromHOL(expr: Expr[Ind]): Justification =
      axioms.find: ax =>
        ax.statement match
          case HOLSequent(_, axiom) if isSame(expr, axiom) => true
          case _ => false
      .getOrElse(throw UnknownAxiom(expr))

  /**
    * A destructed sequent corresponding to a constant definition.
    */
  case class Definition(
    name: String,
    /**
      * The full type of the constant, with free variables
      */
    abstractType: Expr[Ind],
    /**
      * The free type variables of the constant
      *
      * Order unimportant for HOL Light during generation, but our definitions
      * order them.
      */
    typeArgs: Seq[Variable[Ind]],
    /**
      * The actual defining term
      */
    body: Expr[Ind]
  )

  private object Definition:
    def unapply(term: h.Term): Option[Definition] =
      term match
        case h.Combination(h.Combination(h.Constant("=", _), h.Constant(name, tt)), body) =>
          val abstractType = tt.toLisaType
          Some(
            Definition(
              name = name,
              abstractType = abstractType,
              typeArgs = abstractType.freeVars.collect { case v: Variable[?] => v.asInstanceOf }.toSeq,
              body = body.toLisaTerm
            )
          )
        case _ => None
      

  private object Constants:

    private case class DefinedConstant(cst: HOLConstant, typeVars: Seq[Variable[Ind]], definition: Justification)
    
    private val typeDefinitions: mutable.Map[String, Nothing] = mutable.Map.empty
    private val constantDefinitions: mutable.Map[String, DefinedConstant] = mutable.Map.empty

    def lookupTypeConstant(name: String): HOLConstantType = 
      ???
      
    def lookupTypedConstant(name: String, tpe: h.Type): Expr[Ind] = 
      // translate type to lisa expr, then match against the known
      // abstract type of the constant, instantiating the definition 
      // appropriately
      constantDefinitions.get(name) match
        case None => throw new NoSuchElementException(s"Constant $name is not defined.")
        case Some(DefinedConstant(cst, typeVars, definition)) =>
          // find the instantiation of type variables
          val lisaType = tpe.toLisaType
          matchExpr(using RewriteContext.empty)(lisaType, cst.typ) match
            case None => throw MalformedConstantInstance(name, tpe)
            case Some(subst) =>
              val typeArgs = typeVars.map(v => subst(v).getOrElse(v))
              val appliedCst = (cst #@@ typeArgs).asInstanceOf[Expr[Ind]]

              appliedCst

    def lookupTypedConstantDefinition(using proof: lib.Proof)(name: String, tpe: h.Type): (Expr[Ind], proof.Fact) = 
      // translate type to lisa expr, then match against the known
      // abstract type of the constant, instantiating the definition 
      // appropriately
      constantDefinitions.get(name) match
        case None => throw new NoSuchElementException(s"Constant $name is not defined.")
        case Some(DefinedConstant(cst, typeVars, definition)) =>
          // find the instantiation of type variables
          val lisaType = tpe.toLisaType
          matchExpr(using RewriteContext.empty)(lisaType, cst.typ) match
            case None => throw MalformedConstantInstance(name, tpe)
            case Some(subst) =>
              val typeArgs = typeVars.map(v => subst(v).getOrElse(v))
              val appliedCst = (cst #@@ typeArgs).asInstanceOf[Expr[Ind]]
              val instantiatedDef = definition.of(subst.asSubstPair*)

              (appliedCst, instantiatedDef)

    def register(name: String, cst: HOLConstant, typeVars: Seq[Variable[Ind]], definition: Justification): Unit =
      if constantDefinitions.contains(name) then
        throw new IllegalArgumentException(s"Constant $name is already defined.")
      else 
        constantDefinitions(name) = DefinedConstant(cst, typeVars, definition)

  end Constants

  extension (typ: h.Type) 
    def toLisaType : Expr[Ind] =
      typ match
        case h.BoolType => 𝔹
        case h.FunType(in, out) => in.toLisaType ->: out.toLisaType
        case h.TypeVariable(name) => TypeVariable(K.Identifier(name))
        case h.TypeApplication(name, args) =>
          val typeConstant = Constants.lookupTypeConstant(name)
          val typeArgs = args.map(_.toLisaType)

          // expr should be fully applied
          // this is runtime checked wherever used
          (typeConstant #@@ typeArgs).asInstanceOf

  extension (v: h.Variable)
    def toLisaVar : TypedVariable =
      val name = K.Identifier(v.name)
      val tpe = v.tpe.toLisaType
      TypedVariable(name, tpe)

  extension (v: h.TypeVariable)
    def toLisaVar : TypeVariable =
      val name = K.Identifier(v.name)
      TypeVariable(name)

  extension (term: h.Term)
    def toLisaTerm : Expr[Ind] =
      term match
        case v @ h.Variable(_, _) => v.toLisaVar 
        case h.Constant(name, tpe) => Constants.lookupTypedConstant(name, tpe)
        case h.Combination(left, right) => left.toLisaTerm @@ right.toLisaTerm
        case h.Abstraction(absVar, inner) =>
          fun(absVar.toLisaVar, inner.toLisaTerm)

  /**
    * Reconstruct a single proof step from a [[JustifiedTheorem]] within the
    * given proof context.
    * 
    * @param ctx current proof context
    * @param step the step to reconstruct, as a [[JustifiedTheorem]]
    */
  private def reconstructStep(using library: SetTheoryLibrary.type, ctx: library.Proof)(step: JustifiedTheorem): ctx.Fact =
    def resolveFact(index: Long): ctx.Fact =
      // is this a named theorem?
      // if not, start reconstructing its tree of dependencies recursively
      ???
    
    val JustifiedTheorem(stmt, proofStep) = step

    proofStep match
      case h.REFL(term) => 
        REFL(term.toLisaTerm)
      case h.TRANS(left, right) => 
        val leftFact = resolveFact(left)
        val rightFact = resolveFact(right)
        TRANS(leftFact, rightFact)
      case h.MK_COMB(left, right) => 
        val leftFact = resolveFact(left)
        val rightFact = resolveFact(right)
        MK_COMB(leftFact, rightFact)
      case h.ABS(absVar, from) => 
        val lisaVar = absVar.toLisaVar
        val fromFact = resolveFact(from)
        ABS(lisaVar)(fromFact)
      case h.BETA(term) => 
        BETA(term.toLisaTerm)
      case h.ASSUME(term) => 
        ASSUME(term.toLisaTerm)
      case h.EQ_MP(left, right) =>
        val leftFact = resolveFact(left)
        val rightFact = resolveFact(right)
        EQ_MP(leftFact, rightFact)
      case h.DEDUCT_ANTISYM_RULE(left, right) =>
        val leftFact = resolveFact(left)
        val rightFact = resolveFact(right)
        DEDUCT_ANTISYM_RULE(leftFact, rightFact)
      case h.INST(from, inst) => 
        val fromFact = resolveFact(from)
        val lisaInst = inst.map { case (v, t) => (v.toLisaVar, t.toLisaTerm) }
        INST(lisaInst.toSeq, fromFact)
      case h.INST_TYPE(from, inst) => 
        val fromFact = resolveFact(from)
        val lisaInst = inst.map { case (v, t) => (v.toLisaVar, t.toLisaType) }
        INST_TYPE(lisaInst.toSeq, fromFact)
      case h.AXIOM(term) => Axioms.fromHOL(term.toLisaTerm)
      case h.DEFINITION(name, term) => 
        // the definition is of the form ???
        // possibly with free type variables, e.g. v[A]
        term match
          case Definition(name, abstractType, typeArgs, body) =>
            val definitionTerm = 
              typeArgs.foldRight(body: Expr[?])((v, acc) => λ(v, acc))
            
            val cst = DEF(definitionTerm)(using unsafeSortEvidence(definitionTerm.sort))

            val nonEmptyAssumptions = typeArgs.map(nonEmpty)
            val conj = nonEmptyAssumptions.reduceOption(_ /\ _).getOrElse(⊤)

            val appliedCst: Expr[Ind] = (cst #@@ typeArgs).asInstanceOf
            val baseTyping = appliedCst :: abstractType

            val fullTyping = typeArgs.foldRight(conj ==> baseTyping): (v, inner) =>
              ∀(v, inner)

            val typeJust = Lemma(fullTyping): proof ?=>

              lib.have(nonEmptyAssumptions |- body :: abstractType) by Typecheck.prove
              thenHave(nonEmptyAssumptions |- appliedCst :: abstractType) by Substitute(cst.definition)

              thenHave(conj ==> baseTyping) by Restate
              
              typeArgs.foldRight(lastStep: proof.Fact): (v, premise) => 
                val prev = premise.statement.right.head // inv: always singleton
                lib.have(∀(v, prev)) by RightForall(premise)


            // lift this to an HOL Constant
            val holCst = HOLConstant(cst.id, abstractType, typeJust)

            // register this constant and definition
            Constants.register(name, holCst, typeArgs, cst.definition)
            
            cst.definition
          case _ => 
            throw InvalidDefinitionException(name, term)
        
      case h.TYPE_DEFINITION(name, term, just) => ???

  end reconstructStep

    

end Import