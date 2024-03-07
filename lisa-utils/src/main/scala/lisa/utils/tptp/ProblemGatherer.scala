package lisa.utils.tptp

import lisa.utils.tptp.KernelParser.*

object ProblemGatherer {
  // Path to the TPTP problems directory
  val TPTPProblemPath: String = getClass.getResource("/TPTP/Problems/").getPath

  /**
   * @return sequence of tptp problems in the library lib with the tags in spc.
   */
  def getLibProblems(spc: Seq[String], lib: String): Seq[Problem] = gatherFormulas(spc, TPTPProblemPath + lib + "/")

  /**
   * This takes up to several minutes to run.
   * @return sequence of all tptp problems with the tags in spc.
   */
  def getAllProblems(spc: Seq[String]): Seq[Problem] = gatherAllTPTPFormulas(spc, TPTPProblemPath).flatten

  /**
   * @return sequence of tptp problems with the PRP (propositional) tag.
   */
  def getPRPproblems: Seq[Problem] = getLibProblems(Seq("PRP"), "SYN")
}
