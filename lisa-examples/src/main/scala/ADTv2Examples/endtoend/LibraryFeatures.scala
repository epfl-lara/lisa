package ADTv2Examples.endtoend

/**
 * Combined library coverage runner.
 */
object LibraryFeatures extends lisa.Main {
  section("Library ADTs")
  LibraryADTs.main(Array.empty)

  section("Library functions")
  LibraryFunctions.main(Array.empty)
}
