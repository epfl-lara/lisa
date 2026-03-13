package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Types.ADTv2
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.encoding.Utils.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Pair

/** Syntactic set theoretical interpretation of a constructor for an algebraic data type.
 * In set theory, a constructor is a tuple containing the arguments it has been applied to, in addition to a tag
 * uniquely identifying it.
 *
 * E.g. `cons(1, nil())` is represented as `(tagcons, (1, ((tagnil, ∅), ∅)))`
 *
 * Constructors injectivity is proved within this class.
 *
 * @constructor creates a new constructor out of a user specification
 * @param specification types that the constructor takes as arguments
 * @param variables1 variables used to represent the arguments of the constructor
 */
class SyntacticConstructor(
    val specification: Seq[ConstructorArg],
    val variables1: Seq[Variable[Ind]],
    val variables2: Seq[Variable[Ind]]
) {

  /** Unique identifier of this constructor
 */
  val tag: Int = Constructors.tagCounter
  Constructors.tagCounter = Constructors.tagCounter + 1

  /** Term representation of the tag of this constructor
 */
  val tagTerm: Expr[Ind] = toTerm(tag)

  /** Sequence of variables used to represent the arguments of the constructor
 */
  val variables: Seq[Variable[Ind]] = variables1

  /** Number of arguments that this constructor takes
 */
  val arity: Int = specification.length

  /** Sequence of variables of the constructor with their respective domains.
 */
  val signature1: Seq[(Variable[Ind], ConstructorArg)] = variables1.zip(specification)

  /** Alternative sequence of variables of the constructor with their respective domains.
 */
  val signature2: Seq[(Variable[Ind], ConstructorArg)] = variables2.zip(specification)

  /** Sequence of variables of the constructor with their respective domains.
 */
  val signature: Seq[(Variable[Ind], ConstructorArg)] = signature1

  /** Internally, an instance of this constructor is represented as a list.
 * The first element of this list is the tag of this constructor.
 * The following elements are its arguments. We represent lists as chained
 * pairs followed by the empty set.
 *
 * e.g. cons(1, nil()) --> (tagcons, (1, ((tagnil, ∅), ∅)))
 *
 * @param args the arguments of this instance of the constructor
 */
  def term(args: Seq[Expr[Ind]]): Expr[Ind] = pair(tagTerm, subterm(args))

  /** Internal representation of an instance of this constructor in which arguments are schematic variables.
 */
  val term1: Expr[Ind] = term(variables1)

  /** Internal representation of an instance of this constructor in which arguments are an alternative set of schematic variables.
 */
  val term2: Expr[Ind] = term(variables2)

  /** Internal representation of an instance of this constructor in which arguments are schematic variables.
 */
  val term: Expr[Ind] = term1

  /** Internal representation of an instance of this constructor without the tag
 *
 * @param args the arguments of this instance of the constructor
 *
 * @see [[this.term]]
 */
  def subterm(args: Seq[Expr[Ind]]): Expr[Ind] = args.foldRight[Expr[Ind]](∅)(pair(_, _))

  /** Internal representation of an instance of this constructor without the tag, in which arguments are schematic variables.
 */
  val subterm1: Expr[Ind] = subterm(variables1)

  /** Internal representation of an instance of this constructor without the tag, in which arguments are an alternative set
 * of schematic variables.
 */
  val subterm2: Expr[Ind] = subterm(variables2)

  /** Internal representation of an instance of this constructor without the tag, in which arguments are schematic variables.
 */
  val subterm: Expr[Ind] = subterm1

  /** Theorem --- Injectivity of constructors.
 *
 *    Two instances of this constructor are equal if and only if all of their arguments are pairwise equal
 *
 * e.g. cons(head1, tail1) === cons(head2, tail2) <=> head1 === head2 /\ tail1 === tail2
 */
  lazy val injectivity =
    if arity == 0 then
      Lemma(term1 === term2) {
        have(thesis) by RightRefl
      }
    else
      Lemma((term1 === term2) <=> seqEq(variables1, variables2)) {

        // STEP 1: Get rid of the tag using pair extensionality
        have((term1 === term2) <=> (subterm1 === subterm2)) by Restate.from(Pair.extensionality of (a := tagTerm, b := subterm1, c := tagTerm, d := subterm2))

        // STEP 2: Repeat pair extensionality until all variables have been pulled out of the term
        variables1
          .zip(variables2)
          .foldLeft(Seq.empty[Variable[Ind]], variables1, Seq.empty[Variable[Ind]], variables2, lastStep)((acc, v) =>

            // pulledVars1 are the variables that have been pulled out of the left term
            // remainingVars1 are the variables that are still in the left term
            // pulledVars2 are the variables that have been pulled out of the right term
            // remainingVars2 are the variables that are still in the right term
            val (pulledVars1, remainingVars1, pulledVars2, remainingVars2, previousFact) = acc

            // v1 and v2 are the variables that are being pulled out
            val (v1, v2) = v

            val updatedPulledVars1 = pulledVars1 :+ v1
            val updatedPulledVars2 = pulledVars2 :+ v2
            val updatedRemainingVars1 = remainingVars1.tail
            val updatedRemainingVars2 = remainingVars2.tail

            val subsubterm1 = subterm(updatedRemainingVars1)
            val subsubterm2 = subterm(updatedRemainingVars2)

            have(
              (pair(v1, subsubterm1) === pair(v2, subsubterm2)) <=>
                ((v1 === v2) /\ (subsubterm1 === subsubterm2))
            ) by Restate.from(Pair.extensionality of (a := v1, b := subsubterm1, c := v2, d := subsubterm2))
            have(
              (seqEq(pulledVars1, pulledVars2) /\ (pair(v1, subsubterm1) === pair(v2, subsubterm2))) <=>
                (seqEq(pulledVars1, pulledVars2) /\ (v1 === v2) /\ (subsubterm1 === subsubterm2))
            ) by Tautology.from(lastStep)
            val newFact = have(
              (term1 === term2) <=>
                (seqEq(updatedPulledVars1, updatedPulledVars2) /\ (subsubterm1 === subsubterm2))
            ) by Tautology.from(previousFact, lastStep)

            (updatedPulledVars1, updatedRemainingVars1, updatedPulledVars2, updatedRemainingVars2, newFact)
          )
      }

}

