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
import lisa.utils.collection.VecSet
import lisa.hol.extractor.TheoremRef
import lisa.utils.prooflib.OutputManager
import lisa.hol.extractor.ExtractorException

object Import extends lisa.HOL:
  val lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

  type Justification = lib.JUSTIFICATION

  sealed trait ImportException extends Exception
  case class InvalidAbstractionException(term: h.Term) extends Exception(s"Invalid abstraction term: $term. Expected a variable.") with ImportException
  case class InvalidDefinitionException(name: String, term: h.Term) extends Exception(s"Invalid definition for constant $name: $term. Expected a term of the form 'name = body'.") with ImportException
  case class MalformedConstantInstance(name: String, tpe: Expr[Ind]) extends Exception(s"Malformed instance of constant $name with type $tpe. No matching definition found.") with ImportException
  case class UnknownAxiom(expr: Expr[Ind]) extends Exception(s"Unknown axiom: $expr. No matching HOL Light axiom found.") with ImportException

  // logging

  object Logging:
    enum LoggingMode:
      case Silent, Debug

    def debug(using mode: LoggingMode)(msg: String): Unit =
      mode match
        case LoggingMode.Silent => ()
        case LoggingMode.Debug => 
          msg.linesIterator.foreach(line => println(s"[DEBUG] $line"))
      
    def info(using mode: LoggingMode)(msg: String): Unit =
      msg.linesIterator.foreach(line => println(s"[INFO] $line"))

    def debugAssert(using mode: LoggingMode)(cond: => Boolean, msg: => String): Unit =
      if !cond then throw new AssertionError(s"Debug assertion failed: $msg")

  import Logging.*
  private var currentLoggingMode: LoggingMode = LoggingMode.Silent
  given LoggingMode = currentLoggingMode

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
          case HOLSequent(_, _, axiom) if isSame(expr, axiom) => true
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
          // the constant is not defined at this point, so we have to be careful
          // to not attempt to look it up in the current context
          val abstractType = tt.toLisaType
          Some(
            Definition(
              name = name,
              abstractType = abstractType,
              typeArgs = abstractType.freeVars.collect { case v: Variable[?] => v.asInstanceOf[Variable[Ind]] }.toSeq,
              body = body.toLisaTerm
            )
          )
        case _ => None
      
  private object NameHandling:
    private val illegalChars = "}]`)[{(,;?_."
    private val replacementMap: collection.MapView[Char, Char] =
      illegalChars.zipWithIndex.toMap.view.mapValues(c => (9312 + c).toChar)

    def sanitize(name: String): String =
      name.map(c => replacementMap.getOrElse(c, c))

  import NameHandling.sanitize

  private object Constants:

    case class DefinedConstant(cst: Constant[?], typeVars: Seq[Variable[Ind]], typ: Expr[Ind], definition: Justification)

    case class DefinedType(cst: HOLConstantType, typeVars: Seq[Variable[Ind]], definition: Justification)
    
    private val typeDefinitions: mutable.Map[String, DefinedType] = mutable.Map.empty
    private val constantDefinitions: mutable.Map[String, DefinedConstant] = mutable.Map.empty

    def lookupTypeConstant(name: String): HOLConstantType = 
      typeDefinitions.get(name) match
        case None => throw new NoSuchElementException(s"Type constant $name is not defined.")
        case Some(cst) => cst.cst

    def isDefinedType(name: String): Boolean = typeDefinitions.contains(name)
    def isDefinedConstant(name: String): Boolean = constantDefinitions.contains(name)
      
    def lookupTypedConstant(name: String, tpe: Expr[Ind]): Expr[Ind] = 
      // translate type to lisa expr, then match against the known
      // abstract type of the constant, instantiating the definition 
      // appropriately
      constantDefinitions.get(name) match
        case None => throw new NoSuchElementException(s"Constant $name is not defined.")
        case Some(DefinedConstant(cst, typeVars, cstType, definition)) =>
          // find the instantiation of type variables
          
          debug(s"[Constant Lookup] Looking up constant $name with type $tpe. Known abstract type is $cstType with type variables {${typeVars.mkString(", ")}}.")

          matchExpr(using RewriteContext.empty)(cstType, tpe) match
            case None => throw MalformedConstantInstance(name, tpe)
            case Some(subst) =>
              debug(s"[Constant Lookup] Match successful with substitution: ${subst.map { case (k, v) => s"$k -> $v" }.mkString(", ")}")
              val typeArgs = typeVars.map(v => subst(v).getOrElse(v))
              val appliedCst = (cst #@@ typeArgs).asInstanceOf[Expr[Ind]]

              appliedCst

    /**
      * Lookup the definition of a constant, given its name. The returned
      * definition will possibly have free type variables, which are returned as
      * the first element.
      */
    def lookupConstantDefinition(name: String): (Seq[Variable[Ind]], Justification) = 
      // translate type to lisa expr, then match against the known
      // abstract type of the constant, instantiating the definition 
      // appropriately
      constantDefinitions.get(name) match
        case None => throw new NoSuchElementException(s"Constant $name is not defined.")
        case Some(DefinedConstant(cst, typeVars, cstType, definition)) =>
          (typeVars, definition)

    def register(name: String, cst: Constant[?], typeVars: Seq[Variable[Ind]], cstType: Expr[Ind], definition: Justification): Unit =
      if constantDefinitions.contains(name) then
        throw new IllegalArgumentException(s"Constant $name is already defined.")
      else 
        constantDefinitions(name) = DefinedConstant(cst, typeVars, cstType, definition)

    def registerType(name: String, cst: HOLConstantType, typeVars: Seq[Variable[Ind]], definition: Justification): Unit =
      if typeDefinitions.contains(name) then
        throw new IllegalArgumentException(s"Type constant $name is already defined.")
      else
        typeDefinitions(name) = DefinedType(cst, typeVars, definition)

  end Constants

  /**
  * Contain and register constants and types defined and justified in the
  * preamble before the import. This includes, for example, `ind`, `bool`,
  * equality, and some basic FOL operators.
  */
  private object Initialization:
    import Constants.{DefinedConstant, DefinedType, register, registerType}
    import HOLBasics.*

    val definedConstants = Map(
      // equality
      "=" -> DefinedConstant(holeq, Seq(A), holeq.typ.outTyp, holeq.definition),
      // binders
      "!" -> DefinedConstant(hforall, Seq(A), hforall.typ.outTyp, hforall.definition),
      "?" -> DefinedConstant(hexists, Seq(A), hexists.typ.outTyp, hexists.definition),
      "@" -> DefinedConstant(hselect, Seq(A), hselect.typ.outTyp, hselect.definition),
      // boolean ops
      "/\\" -> DefinedConstant(hand, Seq.empty, hand.typ.outTyp, hand.definition),
      "~" -> DefinedConstant(hnot, Seq.empty, hnot.typ.outTyp, hnot.definition),
      "==>" -> DefinedConstant(himp, Seq.empty, himp.typ.outTyp, himp.definition),
      // complex defs
      "ONE_ONE" -> DefinedConstant(hOneOne, Seq(A, B), hOneOne.typ.outTyp, hOneOne.definition),
      "ONTO" -> DefinedConstant(hOnto, Seq(A, B), hOnto.typ.outTyp, hOnto.definition)
    )

    val definedTypes = Map(
      "ind" -> DefinedType(ind, Seq.empty, ind.nonEmptyThm),
      "bool" -> DefinedType(𝔹, Seq.empty, 𝔹.nonEmptyThm)
    )

    def initializeConstants(): Unit =
      definedConstants.foreach:
        case (name, DefinedConstant(cst, typeVars, cstType, definition)) =>
          register(name, cst, typeVars, cstType, definition)

    def initializeTypes(): Unit =
      definedTypes.foreach:
        case (name, DefinedType(cst, typeVars, definition)) =>
          registerType(name, cst, typeVars, definition)

    def initializeDefinitions(): Unit =
      initializeConstants()
      initializeTypes()

  extension (typ: h.Type) 
    def toLisaType : Expr[Ind] =
      typ match
        case h.BoolType => 𝔹
        case h.FunType(in, out) => in.toLisaType ->: out.toLisaType
        case h.TypeVariable(name) => TypeVariable(K.Identifier(name))
        case h.TypeApplication(name, args) =>
          if name == "fun" && args.length == 2 then
            // since function types are defined as a shorthand for Pi types, we
            // handle them separately instead of defining fun as a
            // HOLConstantType layer over Pi
            args(0).toLisaType ->: args(1).toLisaType
          else
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
        case h.Constant(name, tpe) => Constants.lookupTypedConstant(name, tpe.toLisaType)
        case h.Combination(left, right) => left.toLisaTerm @@ right.toLisaTerm
        case h.Abstraction(absVar, inner) =>
          fun(absVar.toLisaVar, inner.toLisaTerm)

  extension (seq: h.HOLSequent)
    def toLisaSequent : Sequent =
      val assumptions = seq.hyps.map(_.toLisaTerm)
      val conclusion = seq.concl.toLisaTerm
      HOLSequent(assumptions.to(VecSet), conclusion)

  private val theoremMap: mutable.Map[Long, Justification] = mutable.Map.empty

  private def reconstructTheorem(using extractor: ExtractorContext)(ref: TheoremRef): Justification =
     val TheoremRef(index, name) = ref
     theoremMap.get(index) match
      case Some(just) => 
        debug(s"Theorem with id $index found cached.")
        just
      case None =>
        debug(s"Theorem with id $index not found cached. Starting reconstruction.")
        // reconstruct the step from the HOL Light proof
        val step = extractor.getTheorem(index)

        def processGeneric(step: JustifiedTheorem): Justification =
            val goal = step.statement.toLisaSequent

            // give the theorem a custom qualified name
            val sanitizedName = sanitize(name)
            val baseName = summon[sourcecode.Name].value.stripSuffix(".")
            val theoremName = sourcecode.FullName(s"$baseName.$sanitizedName")

            debug(s"Reconstructing theorem #$index.")

            HOLTheorem(using 
              summon[OutputManager],
              theoremName, // just need to set the right name for better tracking
              summon[sourcecode.Line],
              summon[sourcecode.File]
            )(goal) { reconstructStep(step) }

        
        val reconstructed = 
          step.proof match
            case s: h.AXIOM => 
              // recover a matching axiom
              reconstructAxiom(s)
            case s: h.DEFINITION => 
              // deal with it as a definition
              // where not all symbols are defined yet
              reconstructConstantDefinition(s)
            case s: h.TYPE_DEFINITION => 
              reconstructTypeDefinition(s)
            case _ =>
              // any other step should become a theorem
              processGeneric(step)
          
        theoremMap(index) = reconstructed

        reconstructed

  private def reconstructAxiom(using extractor: ExtractorContext)(step: h.AXIOM): Justification =
    val h.AXIOM(term) = step
    val lisaTerm = term.toLisaTerm
    Axioms.fromHOL(lisaTerm)

  private def reconstructTypeDefinition(using extractor: ExtractorContext)(step: h.TYPE_DEFINITION): Justification = 
    ???

  private def reconstructConstantDefinition(using extractor: ExtractorContext)(step: h.DEFINITION): Justification =
    val h.DEFINITION(name, term) = step
    // the definition is of the form `name = body`, 
    // where `name` is not yet defined at this point;
    // possibly with free type variables, e.g. v[A]

    // we extract just the body and use it to define the constant
    term match
      case Definition(name, abstractType, typeArgs, body) =>
        if Constants.isDefinedConstant(name) then
          // just retrieve the existing definition
          debug(s"Constant $name already defined. Retrieving existing definition.")
          Constants
            .lookupConstantDefinition(name)
            ._2 // discard the free variable data
        else
          // actually define the constant, and register it for future lookup
          debug(s"Defining new constant $name with abstract type $abstractType and body $body. Type variables are {${typeArgs.mkString(", ")}}.")

          val definitionTerm = 
            typeArgs.foldRight(body: Expr[?])((v, acc) => λ(v, acc))
          
          val cleanedName =
            val baseName = summon[sourcecode.Name].value.stripSuffix(".")
            val sanitized = sanitize(name)
            sourcecode.FullName(s"$baseName.$sanitized")

          val cst = DEF(using
            summon[OutputManager],
            cleanedName,
            summon[sourcecode.Line],
            summon[sourcecode.File]
          )(definitionTerm)(using unsafeSortEvidence(definitionTerm.sort))

          val nonEmptyAssumptions = typeArgs.map(nonEmpty)
          val conj = nonEmptyAssumptions.reduceOption(_ /\ _).getOrElse(⊤)

          val appliedCst: Expr[Ind] = (cst #@@ typeArgs).asInstanceOf
          val baseTyping = appliedCst :: abstractType

          val fullTyping = typeArgs.foldRight(conj ==> baseTyping): (v, inner) =>
            ∀(v, inner)

          val typeJust = Lemma(fullTyping){ proof ?=>

            lib.have(nonEmptyAssumptions |- body :: abstractType) by Typecheck.prove
            thenHave(nonEmptyAssumptions |- appliedCst :: abstractType) by Substitute(cst.definition)

            thenHave(conj ==> baseTyping) by Restate
            
            typeArgs.foldRight(lastStep: proof.Fact): (v, premise) => 
              val prev = premise.statement.right.head // inv: always singleton
              lib.have(∀(v, prev)) by RightForall(premise)
          }

          val funClass = FunctionalClass(
            inTyp = typeArgs.map(_ => None),
            args = typeArgs,
            outTyp = abstractType
          )

          // lift this to an HOL Constant
          val holCst = 
            TypedConstantFunctional(cst.id, funClass, typeJust)(using unsafeSortEvidence(cst.sort))

          // register this constant and definition
          Constants.register(name, holCst, typeArgs, abstractType, cst.definition)
          
          cst.definition
      case _ => 
        throw InvalidDefinitionException(name, term)
    
  private def reconstructStepIndex(using extractor: ExtractorContext, ctx: lib.Proof)(index: Long): ctx.Fact =
    theoremMap.get(index) match
      case Some(just) => just
      case None =>
        // reconstruct the step from the HOL Light proof
        val step = extractor.getTheorem(index)
        reconstructStep(step)

  /**
    * Reconstruct a single proof step from a [[JustifiedTheorem]] within the
    * given proof context.
    * 
    * @param ctx current proof context
    * @param step the step to reconstruct, as a [[JustifiedTheorem]]
    */
  private def reconstructStep(using extractor: ExtractorContext, ctx: lib.Proof)(step: JustifiedTheorem): ctx.Fact =
    debug(s"Reconstructing step with statement ${step.statement} and proof type ${step.proof.getClass.getSimpleName}")

    def resolveFact(index: Long): ctx.Fact =
      debug(s"Resolving fact with index $index")

      // is this a named theorem?
      // if not, start reconstructing its tree of dependencies recursively
      theoremMap.get(index) match
        case Some(just) => just
        case None =>
          // reconstruct steps recursively
          reconstructStepIndex(index)

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
      case s @ h.DEFINITION(name, term) => reconstructConstantDefinition(s)
      case s @ h.TYPE_DEFINITION(name, term, just) => reconstructTypeDefinition(s) 

  end reconstructStep

  def importFromPrefix(prefix: String): Unit =
    val (extractor, names) = JSONParser.initializeFromPrefix(prefix)

    Initialization.initializeDefinitions()
    
    var count = 0
    val startTime = System.currentTimeMillis()
    def time() = (System.currentTimeMillis() - startTime) / 1000d

    names.foreach: ref =>
      try
        debug(s"Importing theorem ${ref.name} with id ${ref.id}")

        reconstructTheorem(using extractor)(ref)
        count += 1
        if true then // count % 10 == 0 then
          println(f"[INFO] Extracted $count theorems so far in ${time()}%.2f seconds.")
      catch 
        case e: ExtractorException =>
          println(f"""
          | [INFO] Extracted $count theorems so far in ${time()}%.2f.
          | [ERROR] Encountered an error while reconstructing further.
          | [ERROR] Error message: ${e.getMessage}
          | """.stripMargin)
    
    println(s"[INFO] Successfully imported ${names.length} theorems in ${time()}.")

  @main
  def importMain(prefix: String, logMode: String = "--silent") = 
    currentLoggingMode = logMode.toLowerCase match
      case "--silent" => LoggingMode.Silent
      case "--debug" => LoggingMode.Debug
      case _ => throw new IllegalArgumentException(s"Invalid logging mode: $logMode. Expected '--silent' or '--debug'.")

    importFromPrefix(prefix)

end Import