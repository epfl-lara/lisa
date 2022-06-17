package utilities

/**
 * A helper file that provides natural language methods for LISA.
 * Usage:
 * <pre>
 * import utilities.Attempto.*
 * </pre>
 */
object Attempto {

    /**
     * Helper for the aceToTptp function.
     *
     * @param URL String
     * @return the corresponding content (String)
     */
    def get(url: String) = scala.io.Source.fromURL(url).mkString

    /**
     * Send a request to the Attempto Webservice and get the TPTP formula.
     *
     * @param ACE (Attempto Controlled English) String
     * @return the TPTP formula (String) corresponding to the ACE input
     */
    def aceToTptp(text: String) : String = {
     var query = text.replaceAll("\\s", "+")
     return get(s"http://attempto.ifi.uzh.ch/ws/ape/apews.perl?text=$query&ctptp=on&solo=tptp")
    }
}
