package lisa.utilcfs.prooflib

import lisa.kernelcf.proof.{Sequent, Theory}
import lisa.utilcfs.K

import scala.collection.mutable
import scala.collection.View

abstract class Library:
  val theory: Theory = Theory.empty
  given Theory = theory

  private val theoremByFullName = mutable.LinkedHashMap.empty[String, Theorem]
  private val theoremByShortName = mutable.HashMap.empty[String, Vector[Theorem]]

  /**
   * Provides access to theorems in the library.
   */
  object theorems:
    /**
     * Mutably update the named theorem registry
     */
    private[prooflib] def register(theorem: Theorem): Unit =
      val fullName = theorem.fullName.toString
      require(!theoremByFullName.contains(fullName), s"Theorem $fullName is already registered.")
      theoremByFullName.update(fullName, theorem)
      theoremByShortName.updateWith(theorem.shortName):
        case Some(existing) => Some(existing :+ theorem)
        case None => Some(Vector(theorem))

    /**
      * A view over all named registered theorems.
      */
    def all: View[Theorem] =
      theoremByFullName.values.view

    /**
     * Lookup a theorem by full or short name (in that order of preference).
     */
    def get(name: String): Option[Theorem] =
      getFull(name).orElse(getShort(name))

    /**
      * Lookup a theorem by full name.
      */
    def getFull(fullName: String): Option[Theorem] =
      theoremByFullName.get(fullName)

    /**
     * Lookup a theorem by short name, if the short name is unambiguous.
     */
    def getShort(shortName: String): Option[Theorem] =
      theoremByShortName.get(shortName) match
        case Some(Vector(single)) => Some(single)
        case _ => None
