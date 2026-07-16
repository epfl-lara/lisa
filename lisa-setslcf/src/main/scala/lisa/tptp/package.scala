package lisa.tptp

import leo.datastructures.TPTP
import lisa.utils.K

sealed trait AnnotatedStatement {
  def role: String
  def name: String
  def annotations: TPTP.Annotations

  def toFormula: AnnotatedFormula = this match {
    case f: AnnotatedFormula => f
    case s: AnnotatedSequent => AnnotatedFormula(role, name, K.sequentToFormula(s.sequent), annotations)
  }

  def toSequent: AnnotatedSequent = this match {
    case f: AnnotatedFormula => AnnotatedSequent(role, name, K.Sequent(Set(), Set(f.formula)), annotations)
    case s: AnnotatedSequent => s
  }
}

case class AnnotatedFormula(role: String, name: String, formula: K.Expression, annotations: TPTP.Annotations) extends AnnotatedStatement

case class AnnotatedSequent(role: String, name: String, sequent: K.Sequent, annotations: TPTP.Annotations) extends AnnotatedStatement

case class Problem(file: String, domain: String, name: String, status: String, spc: Seq[String], formulas: Seq[AnnotatedStatement]):
  def conjecture = formulas.find(_.role == "conjecture").getOrElse(throw new Exception("No conjecture found in the problem."))
  def axioms = formulas.filter(_.role == "axiom")

case class FileNotAcceptedException(msg: String, file: String) extends Exception(msg + " File: " + file)
