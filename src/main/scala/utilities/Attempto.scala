package utilities
import util.control.Breaks._

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

    /**
     * Helper for the tptpToAce function.
     * Decides if the appended string should be capitalized.
     *
     * @param String to be appended and the original String
     * @return String to be appended with proper first letter case
     */
    def appendFormatStr(appendStr : String, originalStr : String) : String = {
      var penultimateChar = 'c'
      var resultStr = ""
      if (originalStr.length > 2) {
        penultimateChar = originalStr(originalStr.length-2)
      }
      if (penultimateChar == ':') {
        resultStr = originalStr + appendStr.capitalize + ' '
      } else {
        resultStr = originalStr + appendStr + ' '
      }
      return resultStr
    }

    /**
     * Helper for the tptpToAce function.
     * Extracts the String from the matched Option[String].
     *
     * @param Regular expression for pattern matching, the matched String
     * @return Tuple with the extracted String (if any) and a bool for the error code
     */
     def extractString(regex : scala.util.matching.Regex, matchedStr : String) : (String, Boolean) = {
       var resultStr = ""
       var errorCode = false
       try {
         resultStr = regex.findFirstIn(matchedStr).get
       } catch {
         case error:NoSuchElementException => errorCode = true
       }
       return (resultStr, errorCode)
     }

   /**
    * Convert TPTP input to its (paraphrased) natural language representation.
    *
    * @param String in TPTP format (fof or cnf)
    * @return corresponding natural language representation (String)
    */
    def tptpToAce(formalInput : String) : String = {
      val regex = " \\(| \\)|\\( |\\(\\(|\\)\\)|fof\\(|cnf\\(|\n".r // matches the elements to be deleted
      val bracketVars = "(?<=[\\[|\\(]).+?(?=[\\]|\\)])".r // matches the content in brackets
      val squareBracket = "(\\[.*)".r
      val parenthesis = "(.*\\(.*)".r
      val lineName = "[^\\(].*[^,axiom|conjecture]".r
      val propertyName = "^[^\\(,]*".r
      val axiom = "(.*axiom.*)".r
      val conjecture = "(.*conjecture.*)".r
      val space = "( *)".r
      var str = regex.replaceAllIn(formalInput, "")
      var tokens = str.split(" ").toSeq
      var translation = "" // translation result
      var errorCode = false

      breakable {

      for(i <- 0 to tokens.length-1) {

        if (errorCode) {
          translation = "Cannot translate the TPTP formula "
          break
        }

        tokens(i) match {
          case "!" => translation = appendFormatStr("for all", translation)
          case "?" => translation = appendFormatStr("there exist(s)", translation)
          case "~" => translation = appendFormatStr("it is not the case that", translation)
          case squareBracket(x) => bracketVars.findAllIn(x).foreach(a => translation += a + ' ')
          case parenthesis(x) =>
            {
              bracketVars.findAllIn(x).foreach(a => translation += a + " is ")
              translation += extractString(propertyName, x)._1 + ' '
              errorCode = extractString(propertyName, x)._2
            }
          case axiom(x) =>
            {
              translation += "Given " + extractString(lineName, x)._1 + ": "
              errorCode = extractString(propertyName, x)._2
            }
          case conjecture(x) =>
            {
              translation += "Prove " + extractString(lineName, x)._1 + ": "
              errorCode = extractString(propertyName, x)._2
            }
          case "&" => translation += "and "
          case "|" => translation += "or "
          case "=>" =>
            {
              translation = translation.dropRight(1) + ", and it follows that "
            }
          case space(x) => translation += ""
          case ":" => translation += "such that "
          case x => translation += x // unknown symbol
          }
        }
        }
      translation = translation.dropRight(1) + '.'
      return translation
    }
}
