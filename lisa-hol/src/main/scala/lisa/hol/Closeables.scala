package lisa.hol

/** Close all resources in order, propagating the last close failure. */
private[hol] inline def closeAll(resources: List[AutoCloseable]): Unit =
  def close(remaining: List[AutoCloseable]): Unit = remaining match
    case Nil => ()
    case resource :: rest =>
      try resource.close()
      finally close(rest)
  close(resources)
