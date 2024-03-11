package lisa.hol

import holimp.{Core => HOLL}
import lisa.utils.memoization.memoized

object HOLImport extends lisa.HOL{

  val x = typedvar(𝔹)
  val y = typedvar(𝔹)
  val f = typedvar(𝔹 |=> 𝔹)
  val g = typedvar(𝔹 |=> (𝔹 |=> 𝔹))
  val h = typedvar((𝔹 |=> 𝔹) |=> 𝔹)
  
  val parser = holimp.JSONParser
  val steps = parser.getProofs
  val thms = parser.getTheorems
  val stmts = parser.getStatements

  private def toLisaType__(typ: HOLL.Type): Type =
    typ match
      // special cases
      case HOLL.BoolType => 𝔹
      case HOLL.FunType(from, to) => toLisaType(from) |=> toLisaType(to)
      // others
      case HOLL.TypeVariable(name) => variable(using name)
      case HOLL.TypeApplication(name, args) => ???

  case object ExpectedVariableException extends Exception

  private def asVar(v: Term): TypedVar =
    v match
      case v : TypedVar => v
      case _ => throw ExpectedVariableException
    

  private def toLisaTerm__(term: HOLL.Term): Term = 
    term match
      case HOLL.Variable(name, typ) => typedvar(using name)(toLisaType(typ))
      case HOLL.Constant(name, typ) => ??? // theory.getConstant; definitions must be handled externally
      case HOLL.Combination(left, right) => toLisaTerm(left)*(toLisaTerm(right))
      case HOLL.Abstraction(vbl, tm) => λ(asVar(toLisaTerm(vbl)), toLisaTerm(tm))
    
  val toLisaType: HOLL.Type => Type = memoized(toLisaType__)
  val toLisaTerm: HOLL.Term => Term = memoized(toLisaTerm__)

  private def reconstruct(proof: HOLL.ProofStep)(using library: HOLSteps.library.type, ctx: library.Proof): ctx.Fact =
    import HOLSteps._
    def transformed = 
      proof match
        case HOLL.REFL(term) => REFL(toLisaTerm(term))
        case HOLL.TRANS(left, right) => ???
        case HOLL.MK_COMB(left, right) => MK_COMB(reconstruct(left), reconstruct(right))
        case HOLL.ABS(absVar, from) => ABS(asVar(toLisaTerm(absVar)))(reconstruct(from))
        case HOLL.BETA(term) => BETA(toLisaTerm(term))
        case HOLL.ASSUME(term) => ASSUME(toLisaTerm(term))
        case HOLL.EQ_MP(left, right) => ???
        case HOLL.DEDUCT_ANTISYM_RULE(left, right) => DEDUCT_ANTISYM_RULE(reconstruct(left), reconstruct(right))
        case HOLL.INST(from, insts) => ???
        case HOLL.INST_TYPE(from, insts) => ???
        case HOLL.AXIOM(term) => ???
        case HOLL.DEFINITION(name, term) => ???
        case HOLL.TYPE_DEFINITION(name, term, just) => ???

    library.have(transformed)
    

  /**
    * Checks if this HOL Light sequent is a "new_basic_definition".
    * 
    * Must be of the form `|- ((=) (symbol)) (defn)`
    * if we have not seen `symbol` before. 
    * 
    */
  private def isDefinition(hyps: Seq[HOLL.Term], conclusion: HOLL.Term): Boolean =
    import HOLL.{Combination, Constant}
    conclusion match
      case Combination(Combination(Constant("=", _), Constant(name, _)), _) =>
        hyps.isEmpty && ??? // have not seen this constant yet
      case _ => false
    
  val lisaThms = 
    for 
      thm <- thms 
    yield
      val (hypotheses, conclusion) = stmts(thm.id)
      if isDefinition(hypotheses, conclusion) then
        // register the constant
        ???
      else
        val lisaHyps = hypotheses.toSet.map(toLisaTerm)
        val lisaConc = toLisaTerm(conclusion)
        val sequent = HOLSequent(lisaHyps, lisaConc)

        HOLSteps.library.THM(sequent, thm.nm, thm.id, "HOL.Import", Theorem):
          val proof = steps(thm.id)
          reconstruct(proof)
}
