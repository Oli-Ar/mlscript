package mlscript.mono.debug

abstract class Debug:
  def trace[T](name: String, pre: Any*)
              (thunk: => T)
              (post: T => Any = Debug.noPostTrace): T
  inline def log(msg: => String): Unit

object Debug:
  val noPostTrace: Any => Any = _ => ""
