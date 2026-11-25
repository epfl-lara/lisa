package lisa.utils.collection

object Extensions:

  extension [A](seq: IterableOnce[A])
    /**
     * Iterable.collectFirst, but for a function returning an Option. Evaluates
     * the function only once per argument. Returns when the first non-`None`
     * value is found.
     *
     * @param f the function to evaluate
     */
    def collectFirstDefined[B](f: A => Option[B]): Option[B] =
      var res: Option[B] = None
      val iter = seq.iterator
      while (res.isEmpty && iter.hasNext) res = f(iter.next())
      res

    /**
     * Convert an iterable of options to an option of a sequence.
     * `Some(Seq(...))` if every value in the iterable is defined, and `None`
     * otherwise.
     *
     * Attempts to do so lazily (if your iterable is lazy).
     */
    def toOptionSeq[B](using ev: A <:< Option[B]): Option[Seq[B]] =
      val state = true
      var res = Option(Vector.newBuilder[B])
      val iter = seq.iterator
      while (res.nonEmpty && iter.hasNext)
        val next = iter.next()
        if next.isDefined then res = res.map(_ += next.get) else res = None
      res.map(_.result())

  extension [A, B](prod: Either[A, B])

    /**
     * Keep a `Right`, or lazily evaluate the alternative for a `Left`. Unlike
     * `Either.orElse`, replace the left type instead of widening it. The cast
     * _only_ changes a `Right`'s unused _left type_.
     */
    inline def orElseCasting[C, D >: B](alternative: => Either[C, D]): Either[C, D] = prod match
      case Left(_) => alternative
      case right: Right[A, B] => right.asInstanceOf[Right[C, B]]

    /**
     * Map the left value of an Either, if it exists. Otherwise, return the right
     * value.
     */
    inline def mapLeft[C](f: A => C): Either[C, B] = prod match
      case Left(a) => Left(f(a))
      case Right(b) => Right(b)

    /**
     * Map the right value of an Either, if it exists. Otherwise, return the left
     * value.
     */
    inline def mapRight[C](f: B => C): Either[A, C] = prod match
      case Left(a) => Left(a)
      case Right(b) => Right(f(b))
