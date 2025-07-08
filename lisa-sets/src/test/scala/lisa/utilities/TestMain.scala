package lisa

import lisa.utils.prooflib.*

trait TestMain extends lisa.Main {

  override val om: OutputManager = new OutputManager {
    def finishOutput(exception: Exception): Nothing = {
      log(exception)
      main(Array[String]())
      throw exception
    }
    val stringWriter: java.io.StringWriter = new java.io.StringWriter()
  }

}
