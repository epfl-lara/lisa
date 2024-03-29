package lisa.hol

import holimp.{Core => HOLL}
import lisa.utils.memoization.memoized

import lisa.maths.settheory.types.TypeLib.definition
import HOLSteps.{_, given}
import lisa.prooflib.BasicStepTactic._
import lisa.prooflib.SimpleDeducedSteps._
import lisa.automation.Substitution
import lisa.fol.FOL as F
import lisa.fol.FOL.{Identifier, Term}
import lisa.fol.FOL.{*, given}
import lisa.automation._
import sourcecode.Name
import lisa.utils.Serialization.termLabelToString
import lisa.utils.unification.UnificationUtils.matchTerm
import lisa.maths.settheory.types.TypeSystem
import lisa.hol.VarsAndFunctions.TypingTheorem

object HOLImport extends lisa.HOL {
  private val A = variable
  private val B = variable
  private val x = typedvar(A)
  private val y = typedvar(A)

  import library._
  
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
      case HOLL.TypeVariable(name) => HOLSteps.variable(using name)
      case HOLL.TypeApplication(name, args) => ???

  case object ExpectedVariableException extends Exception

  private def asVar(v: Term): TypedVar =
    v match
      case v : TypedVar => v
      case _ => throw ExpectedVariableException
    

  private def toLisaTerm__(term: HOLL.Term): Term = 
    term match
      case HOLL.Variable(name, typ) => typedvar(using name)(toLisaType(typ))
      // special case equality
      case HOLL.Combination(
        HOLL.Combination(HOLL.Constant("=", _), l),
        r
      ) => toLisaTerm(l) =:= toLisaTerm(r)
      case HOLL.Constant(name, typ) => Constants.get(name, toLisaType(typ))
      case HOLL.Combination(left, right) => toLisaTerm(left)*(toLisaTerm(right))
      case HOLL.Abstraction(vbl, tm) => λ(asVar(toLisaTerm(vbl)), toLisaTerm(tm))
    
  val toLisaType: HOLL.Type => Type = memoized(toLisaType__)
  val toLisaTerm: HOLL.Term => Term = memoized(toLisaTerm__)

  object Constants:
    sealed trait LabelStore
    case class JustConstant[A <: TypeSystem.Class](c: TypedConstant[A]) extends LabelStore
    case class Functional[N <: Arity](f: TypedConstantFunctional[N], freeType: F.Term, params: Seq[F.Variable], innerDef: JUSTIFICATION) extends LabelStore

    case object MalformedTypeInstantiationException extends Exception
    
    private val illegalChars = "}]`)[{(,;?_."
    private val subst = illegalChars.zipWithIndex.toMap.view.mapValues(c => (9312 + c).toChar)

    def sanitizeName(name: String): String = 
      name.map(c => if subst.contains(c) then subst(c) else c)

    private val constants = scala.collection.mutable.HashMap.empty[String, LabelStore]
    def register[A <: TypeSystem.Class](c: TypedConstant[A]): Unit =
      // two things should not have the same name, as they cannot be distinguished by no. from HOL
      constants.update(c.id.name, JustConstant(c))
    def register[N <: Arity](c: TypedConstantFunctional[N], tpe: F.Term, params: Seq[F.Variable], innerDef: JUSTIFICATION): Unit =
      // two things should not have the same name, as they cannot be distinguished by no. from HOL
      constants.update(c.id.name, Functional(c, tpe, params, innerDef))
    def get(name: String, tpe: Term) =
      // guaranteed to be safe if we read theorems in the order HOL produces them
      val store = constants("HOL@" + sanitizeName(name))
      store match
        case JustConstant(c) => c
        case Functional(f, freeType, params, _) =>
          val subst = matchTerm(tpe, freeType)
          if subst.isEmpty then
            throw MalformedTypeInstantiationException
          else
            val substs = subst.get
            val inputs = params.map(p => substs.getOrElse(p, p))
            f.applySeq(inputs)

    def getDefinition(name: String): JUSTIFICATION =
      constants("HOL@" + sanitizeName(name)) match
        case JustConstant(c) => c.definition
        case Functional(_, _, _, innerDef) => 
          // the definition, instantiated into a usable form at time of construction
          innerDef
          

    // handling equality separately
    val equality = Functional(=:=, (A |=> (A |=> B)), Seq(A), eqCorrect)
    constants.update("HOL@=", equality)
    
    
  import Constants.{register, get, getDefinition, sanitizeName}

  private val theoremCache = collection.mutable.HashMap.empty[HOLL.ProofStep, library.THM]

  private def reconstruct(using library: HOLSteps.library.type, ctx: library.Proof)(proof: HOLL.ProofStep): ctx.Fact =
    import HOLSteps._
    object Rec:
      val rec = (p: HOLL.ProofStep) => theoremCache.getOrElse(p, recm(p))
      val recm: HOLL.ProofStep => ctx.ProofStep = memoized(rec_(_))
      def rec_(proof: HOLL.ProofStep): ctx.ProofStep = {
    def transformed: ctx.ProofTacticJudgement =
      proof match
        case HOLL.REFL(term) => REFL(toLisaTerm(term))
        case HOLL.TRANS(left, right) => 
          val l = rec(left)
          val r = rec(right)
          TRANS(l, r)
        case HOLL.MK_COMB(left, right) => 
          val l = rec(left)
          val r = rec(right)
          MK_COMB(l, r)
        case HOLL.ABS(absVar, from) => 
          val pf = rec(from)
          ABS(asVar(toLisaTerm(absVar)))(pf)
        case HOLL.BETA(term) => 
          val inp = toLisaTerm(term)
          val fin = BETA(inp)
          fin
        case HOLL.ASSUME(term) => ASSUME(toLisaTerm(term))
        case HOLL.EQ_MP(left, right) =>
          val pf = rec(left)
          EQ_MP(rec(left), rec(right))
        case HOLL.DEDUCT_ANTISYM_RULE(left, right) => DEDUCT_ANTISYM_RULE(rec(left), rec(right))
        case HOLL.INST(from, insts) => 
          val inner = rec(from)
          val instss = insts.toSeq.map((k, v) => asVar(toLisaTerm(k)) -> toLisaTerm(v))
          val fin = INST(instss, inner)
          fin
        case HOLL.INST_TYPE(from, insts) =>
          def singleTypeInst = (step: ctx.Fact, inst: (HOLL.TypeVariable, HOLL.Type)) =>
            val x = 
              toLisaType(inst._1) match
                case v : F.Variable => v
                case _ => throw ExpectedVariableException              
            val typ = toLisaType(inst._2)
            library.have(INST_TYPE(x, typ, step))
          val fin = insts.foldLeft(rec(from))(singleTypeInst)
          Restate.from(fin)(fin.statement)
        case HOLL.AXIOM(term) => 
          // prove the axioms and simply retrieve them
          ???
        case HOLL.DEFINITION(name, term) => 
          // must have been handled previously
          // retrieve it
          val defn = Constants.getDefinition(name)
          Restate.from(defn)(defn.statement)
        case HOLL.TYPE_DEFINITION(name, term, just) => 
          // is this ever used?
          // what does it look like?
          ???

    val tr = library.have(transformed)
    tr
      }
    
    val res = Rec.rec(proof)
    res

  /**
    * Checks if this HOL Light sequent is a "new_basic_definition".
    *
    * Must be of the form DEFINITION(`|- ((=) (symbol)) (defn)`) if we have not
    * seen `symbol` before. 
    *
    * The form and visibility invariants are assumed to be maintained by the HOL
    * system for now.
    *
    */
  private def isDefinition(proof: HOLL.ProofStep): Boolean = proof.isInstanceOf[HOLL.DEFINITION]

  case class MalformedDefinitionException(id: Int, term: HOLL.Term) extends Exception(s"Malformed definition at id $id: ${term.pretty}")
  case class MalformedDefinitionFormat(id: Identifier) extends Exception(s"Definition of $id is not of the form forall(v, (v = $id) <=> (context => v = term))")
    
  val lisaThms = 
    for 
      thm <- thms.sortBy(_.id).take(15)
    yield
      println(s"Processing ${thm.id}")
      val (hypotheses, conclusion) = stmts(thm.id)
      val proof = steps(thm.id)
      if isDefinition(proof) then
        // register the constant
        assert(hypotheses.isEmpty)
        import HOLL.{Combination, Constant}
        conclusion match 
          case Combination(Combination(Constant("=", _), Constant(name, typ)), defTerm) =>
            val term = toLisaTerm(defTerm)
            val tpe = toLisaType(typ)
            val freeTypes = tpe.freeVariables.toSeq
            // TODO: special case freeTypes.isEmpty
            val context = computeContext(Set(term))
            // we need to check the set of declared abstractions in this term, and totally order and quantify over them
            val orderedAbstractions: List[Variable] =
              val abstractions = context._2
              // for each abstraction, first find which variable it's defining
              // then, find everything it depends on
              val dependencies = abstractions.map(
                abs =>
                  val l = abs.args(0).asInstanceOf[TypeAssignment[Type]].t
                  assert(l.isInstanceOf[Variable])
                  l.asInstanceOf[Variable & Term] -> (abs.bodyProp.allSchematicLabels.filter(a => a.id.name.startsWith("$λ") && a != l.label && a.isInstanceOf[Variable]).toList)
              ).toMap
              val ls = dependencies.keys.toList
              ls.sortWith((l, r) => dependencies.getOrElse(l, Nil).contains(r))
              ls
            val z = variable
            val ctx = (context._1 ++ context._2).toSeq
            inline def base(z: Term) = F.and(ctx) ==> (z === term)
            inline def zDef(z: Term) = 
              orderedAbstractions.foldRight(base(z))((label, inner) => forall(label, inner))
            val just = Lemma(existsOne(z, zDef(z))) {
              sorry
            }
            val newLabel = 
              FunctionDefinition(sanitizeName(s"HOL@$name"), thm.id, "HOLLight")(freeTypes, z, zDef(z), just).label
            val baseTypingFormula: F.Formula = (newLabel.applySeq(freeTypes) :: tpe)
            val quantifiedTypingFormula = freeTypes.foldRight(baseTypingFormula)((v, step) => forall(v, step))
            val typingProof = Lemma(quantifiedTypingFormula) {
              // have(zDef(constant)) by InstantiateForall(constant)(constant.definition)
              // val instDef = thenHave(base(constant)) by InstantiateForall(orderedAbstractions: _*)
              // val typed = have(TypingTheorem(term :: tpe))
              // have(constant === term) by Tautology.from(instDef, typed)
              // have(constant :: tpe) by Substitution.ApplyRules(lastStep)(typed)
              sorry
            }
            val typedLabel = TypedConstantFunctional(newLabel.id, newLabel.arity, FunctionalClass(freeTypes.map(x => any), freeTypes, tpe, newLabel.arity), typingProof)
            val f = typedLabel.applySeq(freeTypes)
            val innerDef = Lemma((f =:= term)) {
              val typingProof = have(ProofType(term))
              val fTyping = have(ProofType(f))

              if !ctx.isEmpty then assume(ctx: _*)
              have(zDef(f)) by Weakening(newLabel.definition of f)
              have(base(f)) by Weakening(lastStep.of(orderedAbstractions: _*))
              thenHave(f === term) by Weakening
              have(thesis) by Tautology.from(lastStep, fTyping, typingProof, eqCorrect of (A -> tpe, x -> f, y -> term))
            }
            println(s"DEFINING ${innerDef.statement}")
            Constants.register(typedLabel, tpe, freeTypes, innerDef)
            newLabel.definition
          case _ => throw MalformedDefinitionException(thm.id, conclusion)
      else
        val lisaHyps = hypotheses.toSet.map(toLisaTerm)
        val lisaConc = toLisaTerm(conclusion)
        val sequent = HOLSequent(lisaHyps, lisaConc)
          val proof = steps(thm.id)

        val res = THM(sequent, thm.nm, thm.id, "HOL.Import", lisa.SetTheoryLibrary.Theorem):
          val step = reconstruct(proof)
          have(Clean.all(step))
          println(s"PROVED :: \n\t${lastStep.statement}\nNEEDED ::\n\t$sequent")

        theoremCache.update(proof, res)
        res

  @main 
  def importHOLLight =
    lisaThms.foreach(t => println(t.repr))
}
