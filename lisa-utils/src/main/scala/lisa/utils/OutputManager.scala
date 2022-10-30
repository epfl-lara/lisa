package lisa.utils

abstract class OutputManager {

  val output: (String => Unit) 

  val finishOutput: (Throwable => Nothing) 

}
