package lisa

import lisa.TopologyLibrary
import lisa.Topology
import lisa.prooflib.BasicMain

trait Main extends BasicMain {

  export TopologyLibrary.{given, _}
  export Topology.{given, _}

}
