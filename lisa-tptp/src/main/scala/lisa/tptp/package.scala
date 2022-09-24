package lisa.tptp

import lisa.kernel.fol.FOL

case class AnnotatedFormula(role: String, name: String, formula: lisa.kernel.fol.FOL.Formula)

case class Problem(file: String, domain: String, name: String, status: String, spc: Seq[String], formulas: Seq[AnnotatedFormula])

case class FileNotAcceptedException(msg: String, file: String) extends Exception(msg + " File: " + file)
