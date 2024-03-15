// val circ = ConstantFunctionLabel.infix("o", 2)

//   def char(c: Char) =

//     val zero = Constant("0")
//     val one = Constant("1")
//     val e = Constant("Ɛ")

//     addSymbol(zero)
//     addSymbol(one)
//     addSymbol(circ)
//     addSymbol(e)

//     def toBinary(v: Int, b: Int = 8, buffer: Term = emptySet): Term =
//       if b == 0 then buffer
//       else toBinary(v >> 1, b - 1, circ(if v % 2 == 1 then one else zero, buffer))

//     toBinary(c)

//   def string(s: String) =
//     // val stringTitle = variable
//     // (DEF(stringTitle) --> s.foldRight(emptySet)((c, acc: Term) => circ(char(c), acc)))(Constant(s))
//     s.foldRight(emptySet)((c, acc: Term) => circ(char(c), acc))