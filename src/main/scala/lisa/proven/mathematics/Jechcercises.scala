package lisa.proven.mathematics

import lisa.automation.kernel.Destructors.*
import lisa.automation.kernel.ProofTactics.*

/**
 * Practicing exercises from Jech, some of them may be moved to become theorems
 */
object Jechcercises extends SetTheory2 {


    val powerSetNonInclusion = makeTHM(
            Exists(x, strictSubset(powerSet(x), x)) |- ()
        ) {

        }
}
