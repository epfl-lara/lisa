package lisa.automation.superposition
package bench

import lisa.automation.ProofSyntax.Application
import lisa.automation.ProofSyntax.Expression
import lisa.automation.ProofSyntax.Lambda
import lisa.automation.ProofSyntax.ProofCertificate
import lisa.automation.ProofSyntax.CertificateStep
import lisa.automation.ProofSyntax.Subproof
import lisa.automation.ProofSyntax.Sequent
import lisa.automation.ProofSyntax.bot

import scala.collection.mutable

/**
 * Size of a reconstructed certificate, before flattening.
 *
 * @param steps      certificate nodes, including subproof wrappers, as [[ProofCertificate.totalLength]] counts them
 * @param rawSize    node count over every step conclusion, without sharing
 * @param sharedSize the same count with each distinct subexpression counted once
 * @param maxSequent node count of the largest step conclusion
 * @param imports    number of imports, excluded from the sizes
 */
final case class ProofMetrics(steps: Int, rawSize: Long, sharedSize: Long, maxSequent: Long, imports: Int)

/**
 * Sharing is detected by [[Expression.uniqueNumber]], so `sharedSize` equals `rawSize` when hash-consing is off
 * (`lisa.hashcons` or `LISA_HASHCONS` set to `false`).
 */
object ProofMetrics:

  def of(proof: ProofCertificate): ProofMetrics =
    val seen = mutable.HashSet.empty[Long]
    var raw = 0L
    var shared = 0L
    var maxSeq = 0L

    def sharedSizeOf(e: Expression): Long =
      // A repeated subtree was already counted whole.
      if !seen.add(e.uniqueNumber) then 0L
      else
        e match
          case Application(f, a) => 1L + sharedSizeOf(f) + sharedSizeOf(a)
          case Lambda(_, body) => 1L + sharedSizeOf(body)
          case _ => 1L

    def visit(bot: Sequent): Unit =
      var here = 0L
      bot.left.foreach { e =>
        here += rawSizeOf(e); shared += sharedSizeOf(e)
      }
      bot.right.foreach { e =>
        here += rawSizeOf(e); shared += sharedSizeOf(e)
      }
      raw += here
      if here > maxSeq then maxSeq = here

    def walk(steps: IndexedSeq[CertificateStep]): Unit =
      steps.foreach {
        case s: Subproof => visit(s.bot); walk(s.proof.steps) // body + 1, as in `totalLength`
        case s => visit(s.bot)
      }

    walk(proof.steps)
    ProofMetrics(proof.totalLength, raw, shared, maxSeq, proof.imports.length)

  /**
   * Node count of an expression: variables, constants, applications and lambdas each count one.
   */
  def rawSizeOf(e: Expression): Long = e match
    case Application(f, a) => 1L + rawSizeOf(f) + rawSizeOf(a)
    case Lambda(_, body) => 1L + rawSizeOf(body)
    case _ => 1L
