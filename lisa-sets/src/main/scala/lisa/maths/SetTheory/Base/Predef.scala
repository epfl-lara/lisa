package lisa.maths.SetTheory.Base

/**
  * Exports for the `base` package.
  *
  * This package object only exports a minimal set of definitions that are
  * relevant to other developments. To avoid cluttering the global namespace,
  * only fundamental theorems should be exported.
  */
object Predef {
  export lisa.maths.SetTheory.Base.Extensionality
  export lisa.maths.SetTheory.Base.EmptySet
  export lisa.maths.SetTheory.Base.UnorderedPair
  export lisa.maths.SetTheory.Base.Comprehension
  export lisa.maths.SetTheory.Base.Comprehension.{|}
  export lisa.maths.SetTheory.Base.Replacement
  export lisa.maths.SetTheory.Base.Replacement.{|}
  export lisa.maths.SetTheory.Base.Singleton
  export lisa.maths.SetTheory.Base.Singleton.{singleton}
  export lisa.maths.SetTheory.Base.Class
  export lisa.maths.SetTheory.Base.Class.{Class, ClassFunction, 𝕍, proper}
  export lisa.maths.SetTheory.Base.Subset
  export lisa.maths.SetTheory.Base.Subset.{⊂, doubleInclusion}
  export lisa.maths.SetTheory.Base.PowerSet
  export lisa.maths.SetTheory.Base.Difference
  export lisa.maths.SetTheory.Base.Difference.{∖}
  export lisa.maths.SetTheory.Base.Union
  export lisa.maths.SetTheory.Base.Union.{∪}
  export lisa.maths.SetTheory.Base.Intersection
  export lisa.maths.SetTheory.Base.Intersection.{∩, ⋂}
  export lisa.maths.SetTheory.Base.Pair
  export lisa.maths.SetTheory.Base.Pair.{pair, fst, snd, given}
  export lisa.maths.SetTheory.Base.CartesianProduct
  export lisa.maths.SetTheory.Base.CartesianProduct.{×}
  export lisa.maths.SetTheory.Base.WellFounded
}
