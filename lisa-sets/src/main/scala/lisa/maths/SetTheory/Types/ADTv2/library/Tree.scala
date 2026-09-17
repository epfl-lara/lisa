package lisa.maths.SetTheory.Types.ADTv2.library

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2._
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef

private val treeLeafValue = variable[Ind]
private val treeNodeLeft = variable[Ind]
private val treeNodeRight = variable[Ind]

lazy val tree = adt(
  name = "tree",
  typeVars = "A",
  constructors = Seq(
    ("leaf", Seq.empty),
    ("node", Seq(("value", "A"), ("left", SelfRef), ("right", SelfRef)))
  )
)
lazy val leaf = tree.constructors(0)
lazy val node = tree.constructors(1)

lazy val size = recFun(tree, nat) { self =>
  Case(leaf):
    zero
  Case(node, treeLeafValue, treeNodeLeft, treeNodeRight):
    succ * (add * (self * treeNodeLeft) * (self * treeNodeRight))
}

lazy val leafCount = recFun(tree, nat) { self =>
  Case(leaf):
    succ * zero
  Case(node, treeLeafValue, treeNodeLeft, treeNodeRight):
    add * (self * treeNodeLeft) * (self * treeNodeRight)
}

lazy val mirror = recFun(tree, tree.term) { self =>
  Case(leaf):
    leaf.term
  Case(node, treeLeafValue, treeNodeLeft, treeNodeRight):
    node.term * treeLeafValue * (self * treeNodeRight) * (self * treeNodeLeft)
}

lazy val isEmpty = fun(tree, bool) {
  Case(leaf):
    tru
  Case(node, treeLeafValue, treeNodeLeft, treeNodeRight):
    fals
}

object Tree:
  export lisa.maths.SetTheory.Types.ADTv2.library.{tree, leaf, node, size, leafCount, mirror, isEmpty}
