package lisa.tptp

import lisa.utils.K
import lisa.utils.KernelHelpers.given
import org.scalatest.funsuite.AnyFunSuite

/**
 * [[KernelParser.sanitize]] turns every TPTP symbol name, including quoted sentences, into a valid kernel
 * identifier, and [[KernelParser.unsanitize]] gives the name back exactly.
 */
class SanitizeTest extends AnyFunSuite:

  import KernelParser.{sanitize, unsanitize}

  /** Every character an identifier may not contain, plus the escape character itself. */
  private val hostile: String = K.Identifier.forbiddenChars.mkString + " \t\n\r $"

  private val cases: Seq[String] = Seq(
    "",
    "plain",
    "a_b",
    "a$ub", // must not collide with `a_b`
    "$", "$$", "$u", "$s", "$x0041",
    "c_bcase_3235139646", // the counter suffix must stay in the name
    "trailing_", "_leading", "__",
    hostile,
    "(geology) a depression in Asia; extends from Jordan to Mozambique",
    """Suborganismal \'living\' components of organisms,   including systems, organs, and cells.""",
    "éèê", // non-ASCII, not forbidden
    "mixed ,;?[]{}`() and\ttabs"
  )

  test("sanitize yields a valid kernel identifier for every name") {
    for s <- cases do
      val encoded = sanitize(s)
      assert(K.Identifier.isValidIdentifier(encoded), s"sanitize(${s.replace("\n", "\\n")}) = $encoded is not a valid identifier")
      // The String -> Identifier conversion is the real caller and also splits off a `_`-counter.
      val id: K.Identifier = encoded
      assert(id.name == encoded && id.no == 0, s"$encoded did not survive the conversion whole: $id")
  }

  test("unsanitize inverts sanitize exactly") {
    for s <- cases do assert(unsanitize(sanitize(s), 0) == s, s"round trip failed on ${s.replace("\n", "\\n")}")
  }

  test("sanitize is injective, which the `$u`-only encoding was not") {
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
    // Generated names reach `unsanitize` unencoded: unknown escapes must not throw or drop characters.
    for s <- Seq("sk", "sk_1", "nm", "epsi", "a$", "$", "$q", "$xZZZZ", "$x00") do
      assert(unsanitize(s, 0) == s, s"unexpected decode of $s: ${unsanitize(s, 0)}")
  }
