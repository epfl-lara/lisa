package lisa.utils.tactics

import lisa.utils.tactics.BasicStepTactic.*
import lisa.kernel.fol.FOL.*
import lisa.utils.tactics.SimpleDeducedSteps.Restate
import lisa.utils.Helpers.{*, given}
import lisa.utils.{Library, LisaException, OutputManager}

object Exports {

  def Hypothesis(using _proof: Library#Proof): Hypothesis{val proof: _proof.type} = (new Hypothesis).asInstanceOf
  def Cut(using _proof: Library#Proof): CutWithoutFormula{val proof: _proof.type} = (new CutWithoutFormula).asInstanceOf
  def Restate(using _proof: Library#Proof): Restate{val proof: _proof.type} = (new Restate).asInstanceOf

  def LeftAnd(using _proof: Library#Proof): LeftAndWithoutFormula{val proof: _proof.type} = (new LeftAndWithoutFormula).asInstanceOf
  def LeftOr(using _proof: Library#Proof): LeftOrWithoutFormula{val proof: _proof.type} = (new LeftOrWithoutFormula).asInstanceOf
  def LeftImplies(using _proof: Library#Proof): LeftImpliesWithoutFormula{val proof: _proof.type} = (new LeftImpliesWithoutFormula).asInstanceOf
  def LeftIff(using _proof: Library#Proof): LeftIffWithoutFormula{val proof: _proof.type} = (new LeftIffWithoutFormula()).asInstanceOf
  def LeftNot(using _proof: Library#Proof): LeftNotWithoutFormula{val proof: _proof.type} = (new LeftNotWithoutFormula).asInstanceOf
  def LeftForall(t:Term)(using _proof: Library#Proof): LeftForallWithoutFormula{val proof: _proof.type} = (new LeftForallWithoutFormula(t)).asInstanceOf
  def LeftExists(using _proof: Library#Proof): LeftExistsWithoutFormula{val proof: _proof.type} = (new LeftExistsWithoutFormula()).asInstanceOf
  def LeftExistsOne(using _proof: Library#Proof): LeftExistsOneWithoutFormula{val proof: _proof.type} = (new LeftExistsOneWithoutFormula()).asInstanceOf

  def RightAnd(using _proof: Library#Proof): RightAnd{val proof: _proof.type} = (new RightAndWithoutFormula).asInstanceOf
  def RightOr(using _proof: Library#Proof): RightOr{val proof: _proof.type} = (new RightOrWithoutFormula()).asInstanceOf
  def RightImplies(using _proof: Library#Proof): RightImpliesWithoutFormula{val proof: _proof.type} = (new RightImpliesWithoutFormula()).asInstanceOf
  def RightIff(using _proof: Library#Proof): RightIffWithoutFormula{val proof: _proof.type} = (new RightIffWithoutFormula()).asInstanceOf
  def RightNot(using _proof: Library#Proof): RightNotWithoutFormula{val proof: _proof.type} = (new RightNotWithoutFormula()).asInstanceOf
  def RightForall(using _proof: Library#Proof): RightForallWithoutFormula{val proof: _proof.type} = (new RightForallWithoutFormula()).asInstanceOf
  def RightExists(using _proof: Library#Proof)(t: Term): RightExistsWithoutFormula{val proof: _proof.type} = (new RightExistsWithoutFormula(t)).asInstanceOf
  def RightExistsOne(using _proof: Library#Proof): RightExistsOneWithoutFormula{val proof: _proof.type} = (new RightExistsOneWithoutFormula).asInstanceOf
  def Weakening(using _proof:Library#Proof): Weakening{val proof: _proof.type} = (new Weakening).asInstanceOf

  def LeftRefl(using _proof: Library#Proof): LeftReflWithoutFormula{val proof: _proof.type} = (new LeftReflWithoutFormula).asInstanceOf
  def RightRefl(using _proof: Library#Proof): RightReflWithoutFormula{val proof: _proof.type} = (new RightReflWithoutFormula).asInstanceOf

  def LeftSubstEq(equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula)(using _proof: Library#Proof): LeftSubstEq{val proof: _proof.type} = (new LeftSubstEq(equals, lambdaPhi)).asInstanceOf
  def RightSubstEq(equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula)(using _proof: Library#Proof): RightSubstEq{val proof: _proof.type} = (new RightSubstEq(equals, lambdaPhi)).asInstanceOf
  def LeftSubstIff(equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula)(using _proof: Library#Proof): LeftSubstIff{val proof: _proof.type} = (new LeftSubstIff(equals, lambdaPhi)).asInstanceOf
  def RightSubstIff(equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula)(using _proof: Library#Proof): RightSubstIff{val proof: _proof.type} = (new RightSubstIff(equals, lambdaPhi)).asInstanceOf

  def InstFunSchema(insts: Map[SchematicTermLabel, LambdaTermTerm])(using _proof: Library#Proof): InstFunSchema{val proof: _proof.type} = (new InstFunSchema(insts)).asInstanceOf
  def InstPredSchema(insts: Map[SchematicTermLabel, LambdaTermTerm])(using _proof: Library#Proof): InstFunSchema{val proof: _proof.type} = (new InstFunSchema(insts)).asInstanceOf

}
