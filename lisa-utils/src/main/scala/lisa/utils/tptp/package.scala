package lisa.utils.tptp

import lisa.kernel.fol.FOL as K

case class AnnotatedFormula(role: String, name: String, formula: K.Formula)

case class Problem(file: String, domain: String, name: String, status: String, spc: Seq[String], formulas: Seq[AnnotatedFormula])

case class FileNotAcceptedException(msg: String, file: String) extends Exception(msg + " File: " + file)
