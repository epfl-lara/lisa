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

/** A parsed TPTP problem.
  *
  * `distinctObjects` are the kernel constants the problem's distinct objects (`"foo"`) were encoded as, in
  * first-occurrence order. TPTP gives them their meaning — any two of them denote different things — and that
  * is a fact about the *problem*, not about any constant's name, so it is recorded here as the parser meets
  * them rather than recovered downstream from the `$d` prefix the encoding happens to use. A consumer that
  * wants the distinctness turns these into pairwise disequalities; nothing else can know to. */
case class TptpProblem(file: String, domain: String, name: String, status: String, spc: Seq[String],
                       formulas: Seq[AnnotatedStatement], distinctObjects: IndexedSeq[K.Expression] = IndexedSeq.empty):
  def conjecture = formulas.find(_.role == "conjecture").getOrElse(throw new Exception("No conjecture found in the problem."))
  def axioms = formulas.filter(_.role == "axiom")

case class FileNotAcceptedException(msg: String, file: String) extends Exception(msg + " File: " + file)
