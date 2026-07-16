package lisa.maths.SetTheory.Cardinal

/**
 * Exports for the `cardinal` package
 *
 * This package object only exports a minimal set of definitions that are
 * relevant to other developments. To avoid cluttering the global namespace,
 * only fundamental theorems should be exported.
 */
object Predef {
  export lisa.maths.SetTheory.Cardinal.Universe.{*}
  export lisa.maths.SetTheory.Cardinal.UniverseRank.{level, levelIsOrdinal, universesAreNested}
}
