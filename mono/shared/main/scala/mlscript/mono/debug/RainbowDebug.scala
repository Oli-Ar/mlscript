package mlscript.mono.debug

import scala.collection.mutable.ArrayBuffer
import scala.collection.immutable.StringOps

class RainbowDebug extends Debug:
  import RainbowDebug._

  private inline def currentColor = colors(indent % colors.size)
  private inline def beginMark = currentColor("┌")
  private inline def endMark = currentColor("└")
  private var indent = 0

  def trace[T](name: String, pre: Any*)
              (thunk: => T)
              (post: T => Any): T = {
    printPrologue(name, pre.map(toLines))
    indent += 1
    val res =
      try thunk
      finally indent -= 1
    if (post eq Debug.noPostTrace) {
      log(s"$endMark $name")
    } else {
      val result = post(res)
      printEpilogue(name, toLines(result))
    }
    res
  }

  private def printPrologue(name: String, things: Iterable[List[String]]): Unit =
    val leadingLength = name.length + 1
    val leadingSpaces = " " * leadingLength
    things.headOption.foreach {
      case Nil => ()
      case head :: Nil =>
        log(s"$beginMark ${name} ${black(head)}")
      case list =>
        log(s"$beginMark ${name}")
        indent += 1
        list.foreach { line => log(line) }
        indent -= 1
    }
    indent += 1
    things.tail.foreach { _.foreach { log(_) } }
    indent -= 1

  private def printEpilogue(name: String, lines: List[String]): Unit =
    val leadingLength = name.length + 3
    val leadingSpaces = " " * leadingLength
    lines match {
      case Nil => ()
      case head :: Nil =>
        log(s"$endMark $name ${black(head)}")
      case items =>
        log(s"$endMark $name")
        items.foreach { line => log(s"  $line") }
    }

  inline def log(msg: => String): Unit =
    import scala.collection.mutable.StringBuilder
    val indentBuilder = StringBuilder()
    for i <- 0 until indent do
      indentBuilder ++= colors(i % colors.size)("│ ")
    println("[mono] " + indentBuilder.toString + msg)

object RainbowDebug:
  def toLines(thingy: Any): List[String] =
    thingy match
      case printable: Printable => printable.getDebugOutput.toLines
      case _ => thingy.toString.linesIterator.toList

  val colors = ArrayBuffer(red, yellow, green, cyan, blue, magenta)

  def red(content: String): String =
    Console.RED + content + Console.RESET
  def yellow(content: String): String =
    Console.YELLOW + content + Console.RESET
  def green(content: String): String =
    Console.GREEN + content + Console.RESET
  def cyan(content: String): String =
    Console.CYAN + content + Console.RESET
  def blue(content: String): String =
    Console.BLUE + content + Console.RESET
  def magenta(content: String): String =
    Console.MAGENTA + content + Console.RESET

  def black(content: String): String =
    Console.BLACK + content + Console.RESET

  def underline(content: String): String =
    Console.UNDERLINED + content + Console.RESET
  def bold(content: String): String =
    Console.BOLD + content + Console.RESET
