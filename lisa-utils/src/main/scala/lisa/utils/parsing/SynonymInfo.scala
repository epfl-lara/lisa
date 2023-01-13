package lisa.utils.parsing

import scala.collection.mutable

case class CanonicalId(internal: String, print: String)

case class SynonymInfo(private val synonymToCanonical: Map[String, CanonicalId]) {

  /**
   * @return the preferred way to output this id, if available, otherwise the id itself.
   */
  def getPrintName(id: String): String = synonymToCanonical.get(id).map(_.print).getOrElse(id)

  /**
   * @return the synonym of `id` that is used to construct the corresponding `ConstantPredicateLabel` or
   *         `ConstantFunctionLabel`. If not available, `id` has no known synonyms, so return `id` itself.
   */
  def getInternalName(id: String): String = synonymToCanonical.get(id).map(_.internal).getOrElse(id)
}

object SynonymInfo {
  val empty: SynonymInfo = SynonymInfo(Map.empty[String, CanonicalId])
}

class SynonymInfoBuilder {
  private val mapping: mutable.Map[String, CanonicalId] = mutable.Map()

  def addSynonyms(internal: String, print: String, equivalentLabels: List[String] = Nil): SynonymInfoBuilder = {
    (print :: internal :: equivalentLabels).foreach(mapping(_) = CanonicalId(internal, print))
    this
  }

  def build: SynonymInfo = SynonymInfo(mapping.toMap)
}
