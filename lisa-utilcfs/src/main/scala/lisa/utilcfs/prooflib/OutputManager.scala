package lisa.utilcfs.prooflib

import java.io.StringWriter

trait OutputManager:
  given OutputManager = this

  def output(message: String): Unit

  def section(index: Int, name: String, file: String): Unit =
    output(OutputManager.BLUE(s"Section $index: $name"))

final class StringOutputManager extends OutputManager:
  val writer: StringWriter = StringWriter()

  def output(message: String): Unit =
    writer.write(message)
    writer.write("\n")

  override def toString: String =
    writer.toString

object OutputManager:
  def stdout: OutputManager = message => println(message)

  def RED(s: String): String = Console.RED + s + Console.RESET
  def GREEN(s: String): String = Console.GREEN + s + Console.RESET
  def BLUE(s: String): String = Console.BLUE + s + Console.RESET
  def YELLOW(s: String): String = Console.YELLOW + s + Console.RESET
  def CYAN(s: String): String = Console.CYAN + s + Console.RESET
  def MAGENTA(s: String): String = Console.MAGENTA + s + Console.RESET

  def WARNING(s: String): String = YELLOW("Warning: " + s)
