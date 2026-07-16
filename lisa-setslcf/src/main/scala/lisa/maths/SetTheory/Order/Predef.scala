package lisa.maths.SetTheory.Order

import lisa.utilcfs.fol.FOL._

/**
 * Base exports for the `Order` package.
 */
object Predef {

  /**
   * Order symbols. Since < and <= also refer to infix methods, we cannot simply export them.
   * Instead, we use the type declaration to force only variables to be exported.
   */
  val < : Variable[Ind] = lisa.maths.SetTheory.Order.PartialOrder.<
  val <= : Variable[Ind] = lisa.maths.SetTheory.Order.PartialOrder.<=

  export lisa.maths.SetTheory.Order.PartialOrder.{partialOrder, strictPartialOrder}
  export lisa.maths.SetTheory.Order.TotalOrder.{totalOrder, strictTotalOrder}
  export lisa.maths.SetTheory.Order.Extrema.{maximal, minimal, upperBound, lowerBound, greatest, least}
  export lisa.maths.SetTheory.Order.OrderIsomorphism.{isomorphism as orderIsomorphism, isomorphic as orderIsomorphic, ≈}
}
