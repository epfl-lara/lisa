package lisa.hol

import lisa.hol.{core => h}
import lisa.hol.extractor.*
import lisa.utils.K
import org.scalatest.funsuite.AnyFunSuite

class TypeDefinitionWitnessSuite extends AnyFunSuite:
  private def encodeType(typ: h.Type): String = typ match
    case h.TypeVariable(name) => s"v[$name]"
    case h.TypeApplication(name, arguments) => s"c[$name][${arguments.map(t => s"[${encodeType(t)}]").mkString}]"

  private def encode(term: h.Term): String = term match
    case h.Variable(name, typ) => s"v($name)(${encodeType(typ)})"
    case h.Constant(name, typ) => s"c($name)(${encodeType(typ)})"
    case h.Combination(f, x) => s"C(${encode(f)})(${encode(x)})"
    case h.Abstraction(x, body) => s"A(${encode(x)})(${encode(body)})"

  test("eliminate a free witness's typing after proving subset non-emptiness"):
    val bool = h.BoolType
    val x = h.Variable("subset-bound", bool)
    val witness = h.Variable("subset-witness", bool)
    val predicate = h.Abstraction(x, h.Eq(x, x))
    val applied = h.Combination(predicate, witness)
    val equality = h.Constant("=", h.FunType(bool, h.FunType(bool, bool)))
    val carrier = h.TypeApplication("witnessSubset", Nil)
    val abs = h.Constant("witnessAbs", h.FunType(bool, carrier))
    val rep = h.Constant("witnessRep", h.FunType(carrier, bool))
    val a = h.Variable("a", carrier)
    val r = h.Variable("r", bool)
    val absGoal = h.Eq(h.Combination(abs, h.Combination(rep, a)), a)
    val repGoal = h.Eq(h.Combination(predicate, r), h.Eq(h.Combination(rep, h.Combination(abs, r)), r))

    // Reverse beta equality by congruence, then transport witness reflexivity.
    val steps = Seq(
      REFL(encode(witness)), BETA(encode(applied)), REFL(encode(equality)),
      MK_COMB(2, 1), REFL(encode(applied)), MK_COMB(3, 4),
      EQ_MP(5, 4), EQ_MP(6, 0),
      TYPE_DEFINITION(7, encode(absGoal), "witnessSubset"),
      TYPE_DEFINITION(7, encode(repGoal), "witnessSubset")
    )
    val reflexiveWitness = h.Eq(witness, witness)
    val goals = Seq(
      reflexiveWitness, h.Eq(applied, reflexiveWitness), h.Eq(equality, equality),
      h.Eq(h.Combination(equality, applied), h.Combination(equality, reflexiveWitness)),
      h.Eq(applied, applied), h.Eq(h.Eq(applied, applied), h.Eq(reflexiveWitness, applied)),
      h.Eq(reflexiveWitness, applied), applied, absGoal, repGoal
    )
    given ExtractorContext = new ExtractorContext(
      steps.iterator.zipWithIndex.map((step, id) => ProofLine(id, step)),
      goals.iterator.zipWithIndex.map((goal, id) => TheoremStatement(id, RawSequent(Nil, encode(goal))))
    )

    val store = new Import.StepStore
    for (id, name) <- Seq(8L -> "witnessSubsetAbs", 9L -> "witnessSubsetRep") do
      val theorem = store.theorem(TheoremRef(id, name)).asInstanceOf[lisa.SetTheoryLibrary.THM]
      assert(theorem.proofStatistics.kernelSize > 0)
      assert(!theorem.withSorry)
