package lisa.utils.tptp

import lisa.utils.tptp.KernelParser.*

object ProblemGatherer {

  /**
   * The tptp library needs to be included in main/resources. It can be found at http://www.tptp.org/
   * @return sequence of tptp problems with the PRP (propositional) tag.
   */
  def getPRPproblems: Seq[Problem] = {
    val path = getClass.getResource("/TPTP/Problems/SYN/").getPath
    gatherFormulas(Seq("PRP"), path)
  }

}
