package lisa.tptp

import lisa.utils.K
import lisa.utils.KernelHelpers.given
import org.scalatest.funsuite.AnyFunSuite

/**
 * The contract [[KernelParser.sanitize]] owes: every TPTP symbol name, however written, becomes a valid kernel
 * identifier, and [[KernelParser.unsanitize]] gives the source name back exactly.
 *
 * TPTP single-quoted atoms may contain anything at all, and some library axiom files use whole English
 * sentences as symbol names, so "however written" is not hypothetical: before this encoding was completed,
 * `Axioms/BIO001+0.ax` and `Axioms/NLP001+0.ax` — and so the four CASC-J13 problems including them — failed to
 * parse on the comma in a gloss.
 */
class SanitizeTest extends AnyFunSuite:

  import KernelParser.{sanitize, unsanitize}

  /** Every character an identifier may not contain, plus the escape character itself. */
  private val hostile: String = K.Identifier.forbiddenChars.mkString + " \t\n\r $"

  private val cases: Seq[String] = Seq(
    "",
    "plain",
    "a_b",
    "a$ub", //                                   the source name that used to collide with `a_b`
    "$", "$$", "$u", "$s", "$x0041",
    "c_bcase_3235139646", //                     a SUMO id: the counter suffix must stay in the name
    "trailing_", "_leading", "__",
    hostile,
    "(geology) a depression in Asia; extends from Jordan to Mozambique",
    """Suborganismal \'living\' components of organisms,   including systems, organs, and cells.""",
    "éèê", //                     non-ASCII, none of it forbidden, so it must pass through
    "mixed ,;?[]{}`() and\ttabs"
  )

  test("sanitize yields a valid kernel identifier for every name") {
    for s <- cases do
      val encoded = sanitize(s)
      assert(K.Identifier.isValidIdentifier(encoded), s"sanitize(${s.replace("\n", "\\n")}) = $encoded is not a valid identifier")
      // The String -> Identifier conversion is what actually threw on the CASC problems, so exercise it rather
      // than `isValidIdentifier` alone: it also rejects a `_`-counter shape, and it is the caller in question.
      val id: K.Identifier = encoded
      assert(id.name == encoded && id.no == 0, s"$encoded did not survive the conversion whole: $id")
  }

  test("unsanitize inverts sanitize exactly") {
    for s <- cases do assert(unsanitize(sanitize(s), 0) == s, s"round trip failed on ${s.replace("\n", "\\n")}")
  }

  test("sanitize is injective, which the `$u`-only encoding was not") {
    // `a_b` and `a$ub` are different symbols and must stay different: under the old encoding both became
    // `a$ub`, silently identifying two constants.
    assert(sanitize("a_b") != sanitize("a$ub"))
    val encoded = cases.map(sanitize)
    assert(encoded.distinct.size == cases.distinct.size, s"two distinct names encoded alike: $encoded")
  }

  test("random names round-trip") {
    val alphabet = ("abz09" + hostile).toIndexedSeq
    val rng = new scala.util.Random(42)
    for _ <- 1 to 5000 do
      val s = List.fill(rng.nextInt(12))(alphabet(rng.nextInt(alphabet.size))).mkString
      val encoded = sanitize(s)
      assert(K.Identifier.isValidIdentifier(encoded), s"invalid identifier for $s: $encoded")
      assert(unsanitize(encoded, 0) == s, s"round trip failed on $s (encoded $encoded)")
  }

  test("unsanitize passes through an unsanitized kernel name unchanged") {
    // Every identifier printed to TSTP goes through `unsanitize`, including generated ones that were never
    // encoded, so a stray or unknown escape must not throw or eat characters.
    for s <- Seq("sk", "sk_1", "nm", "epsi", "a$", "$", "$q", "$xZZZZ", "$x00") do
      assert(unsanitize(s, 0) == s, s"unexpected decode of $s: ${unsanitize(s, 0)}")
  }
