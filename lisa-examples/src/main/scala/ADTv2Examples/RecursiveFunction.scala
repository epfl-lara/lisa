
import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.utils.prooflib.BasicStepTactic.Sorry
import lisa.utils.fol.FOL

object RecursiveFunction extends lisa.Main {

  // *******************************
  // * ADT Functions and Induction *
  // *******************************

  val x = variable[Ind]
  val n, m = variable[Ind]
  val k = variable[Ind]
  val hd, tl = variable[Ind]
  val A, B = variable[Ind]

  val list = API.defineAST(
    name = "list",
    typeVars = Seq("A"),
    constructors = Seq(
      ("nil", Seq.empty),
      ("cons", Seq(("head", "A"), ("tail", SelfRef)))
    )
  )
  val nil = list.constructors(0)
  val cons = list.constructors(1)
  
  val nat = API.defineAST(
    name = "nat",
    typeVars = Seq.empty,
    constructors = Seq(
      ("zero", Seq.empty),
      ("succ", Seq(("k", SelfRef)))
    )
  )
  val zero = nat.constructors(0)
  val succ = nat.constructors(1)

  // Minimal recursive template: no additional recursion lemmas, only case equations.
  val length = recFun(list, nat) { self =>
    Case(nil):
      zero
    Case(cons, hd, tl):
      succ * (self * tl)
  }

  // `length` is polymorphic in the list element type; here we specialize it to nat-lists.
  private val listTypeParam = length.typeVariables.toSeq.head
  private val lengthNat = length.term.substitute(listTypeParam := nat())

  val listFromLength = recFun(nat, list){ self =>
    Case(zero):
      nil * nat()
    Case(succ, k):
      cons * nat() * zero * (self * k)
  }

  show(length.intro)
  for (cons <- list.constructors) show(length.elim(cons))
  show(listFromLength.intro)
  for (succ <- nat.constructors) show(listFromLength.elim(succ))

  val lengthFromLength = Lemma(
    (x :: nat) |- 
    lengthNat * (listFromLength * x) === x
  ){
    have(thesis) by Induction(x, nat){
      Case(zero) subproof {

        val lenZero = have(listFromLength * zero === nil * nat()) by Restate.from(listFromLength.elim(zero))
        val lenNil = have(lengthNat * (nil * nat()) === zero) by Tautology.from(length.elim(nil) of (A := nat()))

        have(lengthNat * (listFromLength * zero) === zero) by Congruence.from(lenZero, lenNil)
        thenHave(thesis) by Restate
      }
      Case(succ, k) subproof {

        assume(k :: nat)

        // Unfold the recursive definition of listFromLength at succ(k).
        val lenSucc = have(listFromLength * (succ * k) === cons * nat() * zero * (listFromLength * k)) by 
          Restate.from(listFromLength.elim(succ))

        // ADTv2 currently leaves a schematic head-type side-condition in this instantiated
        // elimination step; we isolate it to this single placeholder.
        val unfoldLengthOnSucc = have(
          (k :: nat) |- lengthNat * (cons * nat() * zero * (listFromLength * k)) === succ * (lengthNat * (listFromLength * k))
        ) by Sorry

        // println(s"Unfolded lengthNat on cons: ${unfoldLengthOnSucc.statement}")
        // println(s"vs ${(length.elim(cons)).statement}")
        // println(s"vs ${(length.elim(cons) of (A := Variable[Ind]("B"))).statement}")
        // println(s"vs ${(length.elim(cons) of (A := nat())).statement}")

        // Chain the recursive equations with the induction hypothesis.
        val rewriteSucc = have(
          (k :: nat) |- lengthNat * (listFromLength * (succ * k)) === succ * (lengthNat * (listFromLength * k))
        ) by Congruence.from(lenSucc, unfoldLengthOnSucc)

        val inductionHypothesis = have(
          (k :: nat, lengthNat * (listFromLength * k) === k) |- lengthNat * (listFromLength * k) === k
        ) by Hypothesis

        have(
          (k :: nat, lengthNat * (listFromLength * k) === k) |- lengthNat * (listFromLength * (succ * k)) === succ * k
        ) by Congruence.from(rewriteSucc, inductionHypothesis)
        thenHave(thesis) by Restate
      }
    }
  }

  show(lengthFromLength)

  def trySubs(term: ConstructorArg): (ConstructorArg, ConstructorArg) =
    term match
      // case RegularArg(tpe) => (term, RegularArg(tpe.substitute(A := B)))
      case RegularArg(tpe) => (term, RegularArg(tpe))
      case SelfRef => (term, term)
  
  def trySubs(term: FOL.Sequent): (FOL.Sequent, FOL.Sequent) = (
    term,
    term.substitute(A := B)
  )
  def trySubs(term: Expr[Ind]): (Expr[Ind], Expr[Ind]) = (
    term,
    term.substitute(A := B)
  )
  def trySubs(term: Seq[Expr[Ind]]): Seq[(Expr[Ind], Expr[Ind])] =
    term.map(trySubs)

  println(s"intro: ${trySubs(cons.intro.statement)}")
  println(s"intro: ${trySubs(cons.debug_semantic.intro.statement)}")
  println(s"tyVars: ${cons.debug_semantic.typeVariablesSeq}")
  println(s"term: ${cons.debug_semantic.debug_term}")
  println(s"type: ${trySubs(cons.debug_semantic.typ)}")
  println(s"sem sig types: ${trySubs(cons.debug_semantic.semanticSignature.unzip._2)}")

  println(" ")
  println(s"sem sig: ${(cons.debug_semantic.semanticSignature)}")
  println(s"sem term: ${trySubs(cons.debug_semantic.debug_term)}")
  println(s"sem appterm: ${trySubs(cons.debug_semantic.appliedTerm)}")
  println(s"sem vars: ${(cons.debug_semantic.variables)}")
  println(s"sem under spec: ${(cons.debug_semantic.underlying.specification)}")

  val A2 = Variable[Ind]("A")
  println(s"var test : ${trySubs(A2)}, ${A == A2}")
  val A3 = Constant[Ind]("A")
  println(s"var test : ${trySubs(A3)}, ${A == A3}")
  // val expr1 = x ∈ A3
  // println(s"var test : ${expr1}, ${expr1.substitute(A := B)}, ${expr1.substitute(A3 := B)}")

}