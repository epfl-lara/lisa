package lisa.utils.collection

object Extensions:

  extension [A](seq: Iterable[A]) {

    /**
     * Iterable.collectFirst, but for a function returning an Option. Evaluates
     * the function only once per argument. Returns when the first non-`None`
     * value is found.
     *
     * @param f the function to evaluate
     */
    def collectFirstDefined[T](f: A => Option[T]): Option[T] = {
      var res: Option[T] = None
      val iter = seq.iterator
      while (res.isEmpty && iter.hasNext) {
        res = f(iter.next())
      }
      res
    }

  }

