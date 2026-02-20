package lisa.hol

import lisa.SetTheoryLibrary
import lisa.hol.{core => h}
import lisa.hol.extractor.*
import lisa.hol.HOLHelperTheorems.*
import lisa.hol.VarsAndFunctions.*

object Import extends lisa.HOL:
  val itr: Iterator[(String, JustifiedTheorem)] = ???

  sealed trait ImportException extends Exception
  case class InvalidAbstractionException(term: h.Term) extends Exception(s"Invalid abstraction term: $term. Expected a variable.") with ImportException

  def lookupTypeConstant(name: String): HOLConstantType = ???
  def lookupTypedConstant(name: String, tpe: h.Type): HOLConstant = ???

  extension (typ: h.Type) 
    def toLisaType : Expr[Ind] =
      typ match
        case h.BoolType => 𝔹
        case h.FunType(in, out) => in.toLisaType ->: out.toLisaType
        case h.TypeVariable(name) => TypeVariable(K.Identifier(name))
        case h.TypeApplication(name, args) =>
          val typeConstant = lookupTypeConstant(name)
          val typeArgs = args.map(_.toLisaType)
          typeArgs
            .foldLeft(typeConstant)(App.unsafe)
            // expr should be fully applied
            // this is runtime checked wherever used
            .asInstanceOf 

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
        case h.Constant(name, tpe) => lookupTypedConstant(name, tpe)
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
      case h.AXIOM(term) => ???
      case h.DEFINITION(name, term) => 
        // the definition is of the form ???
        // possibly with free type variables, e.g. v[A]
        ???
      case h.TYPE_DEFINITION(name, term, just) => ???

  end reconstructStep

    

end Import