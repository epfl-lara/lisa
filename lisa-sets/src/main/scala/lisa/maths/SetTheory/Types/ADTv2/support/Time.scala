package lisa.maths.SetTheory.Types.ADTv2.support

final case class Time private (nanos: Long) {
  def -(other: Time): Time = Time(nanos - other.nanos)

  override def toString: String = {
    val millis = nanos / 1000000L
    val seconds = millis / 1000L
    val remainingMillis = millis % 1000L
    s"${seconds}.${remainingMillis.toString.reverse.padTo(3, '0').reverse} s"
  }
}

object Time {
  def get(): Time = Time(System.nanoTime())
}
