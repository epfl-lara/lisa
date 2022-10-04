package lisa.front.parser

import lisa.kernel.proof.SCProof

object KernelReader {

  def readProof(str: String): SCProof =
    KernelResolver.resolveProof(FrontParser.parseProof(FrontLexer.lexingExtendedUnicode(str)), FrontSymbols.FrontUnicodeSymbols)

}
