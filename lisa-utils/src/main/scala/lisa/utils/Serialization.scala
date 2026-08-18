package lisa.utils

import lisa.kernel.proof.SequentCalculus._
import lisa.utils.K.{LeftSubstEq => _, LeftSubstIff => _, RightSubstEq => _, RightSubstIff => _, _}

import java.io._
import scala.collection.mutable.{Map => MutMap}

object Serialization {

  case class InvalidStepTag(tag: Byte) extends Exception("Invalid proof step tag: " + tag)
  case class InvalidExprTag(tag: Byte) extends Exception("Invalid expression tag: " + tag)
  case class IncompleteTreeException(idx: Int) extends Exception("Unexpected end of file while reading tree, after index " + idx)

  object Tag:
    // proof step tags
    inline val restate = 0
    inline val restateTrue = 1
    inline val hypothesis = 2
    inline val cut = 3
    inline val leftAnd = 4
    inline val leftOr = 5
    inline val leftImplies = 6
    inline val leftIff = 7
    inline val leftNot = 8
    inline val leftForall = 9
    inline val leftExists = 10
    inline val rightAnd = 12
    inline val rightOr = 13
    inline val rightImplies = 14
    inline val rightIff = 15
    inline val rightNot = 16
    inline val rightForall = 17
    inline val rightExists = 18
    inline val rightEpsilon = 19
    inline val weakening = 20
    inline val beta = 21
    inline val leftRefl = 22
    inline val rightRefl = 23
    inline val leftSubstEq = 24
    inline val rightSubstEq = 25
    inline val instSchema = 26
    inline val scSubproof = 27
    inline val sorry = 28

    // tree tags
    inline val variable = 0
    inline val constant = 1
    inline val lambda = 2
    inline val application = 3

  type Line = Int

  def typeToString(t: Sort): String =
    t match
      case Ind => "T"
      case Prop => "F"
      case Arrow(from, to) => s">${typeToString(from)}${typeToString(to)}"

  def constantToDOS(c: Constant, dos: DataOutputStream): Unit =
    dos.writeByte(Tag.constant)
    dos.writeUTF(c.id.name)
    dos.writeInt(c.id.no)
    dos.writeUTF(typeToString(c.sort))

  def variableToDOS(v: Variable, dos: DataOutputStream): Unit =
    dos.writeByte(Tag.variable)
    dos.writeUTF(v.id.name)
    dos.writeInt(v.id.no)
    dos.writeUTF(typeToString(v.sort))

  def lamdbaToDOS(l: Lambda, dos: DataOutputStream, exprMap: MutMap[Long, Line]): Unit =
    dos.writeByte(Tag.lambda)
    dos.writeInt(exprMap(l.v.uniqueNumber))
    dos.writeInt(exprMap(l.body.uniqueNumber))

  def applicationToDOS(a: Application, dos: DataOutputStream, exprMap: MutMap[Long, Line]): Unit =
    dos.writeByte(Tag.application)
    dos.writeInt(exprMap(a.f.uniqueNumber))
    dos.writeInt(exprMap(a.arg.uniqueNumber))

  /**
   * Read a variable from a [[DataInputStream]], given that the tag has already
   * been read and is [[Tag.variable]].
   */
  inline def variableFromDIS(tag: Tag.variable.type, dis: DataInputStream): Variable =
    val name = dis.readUTF()
    val no = dis.readInt()
    val sort = dis.readUTF()
    Variable(Identifier(name, no), typeFromString(sort)._1)

  /**
   * Read a constant from a [[DataInputStream]], given that the tag has already
   * been read and is [[Tag.constant]].
   */
  inline def constantFromDIS(tag: Tag.constant.type, dis: DataInputStream): Constant =
    val name = dis.readUTF()
    val no = dis.readInt()
    val sort = dis.readUTF()
    Constant(Identifier(name, no), typeFromString(sort)._1)

  /**
   * Read a lambda from a [[DataInputStream]], given that the tag has already
   * been read and is [[Tag.lambda]]. The subexpressions of the lambda should
   * already be in the expression map.
   */
  inline def lambdaFromDIS(tag: Tag.lambda.type, dis: DataInputStream, exprMap: MutMap[Line, Expression]): Lambda =
    val v = exprMap(dis.readInt())
    val body = exprMap(dis.readInt())
    Lambda(v.asInstanceOf[Variable], body)

  /**
   * Read an application from a [[DataInputStream]], given that the tag has
   * already been read and is [[Tag.application]]. The subexpressions of the
   * application should already be in the expression map.
   */
  inline def applicationFromDIS(tag: Tag.application.type, dis: DataInputStream, exprMap: MutMap[Line, Expression]): Application =
    val f = exprMap(dis.readInt())
    val arg = exprMap(dis.readInt())
    Application(f, arg)

  /**
   * Write all tree entries for expression e to dos, using and populating exprMap.
   * Returns the line number assigned to e. Subexpressions are written first.
   */
  def lineOfExpr(e: Expression, dos: DataOutputStream, exprMap: MutMap[Long, Line]): Line =
    exprMap.getOrElse(
      e.uniqueNumber, {
        e match
          case v: Variable => variableToDOS(v, dos)
          case c: Constant => constantToDOS(c, dos)
          case l: Lambda =>
            lineOfExpr(l.v, dos, exprMap)
            lineOfExpr(l.body, dos, exprMap)
            lamdbaToDOS(l, dos, exprMap)
          case a: Application =>
            lineOfExpr(a.f, dos, exprMap)
            lineOfExpr(a.arg, dos, exprMap)
            applicationToDOS(a, dos, exprMap)
        val newLine = exprMap.size
        exprMap(e.uniqueNumber) = newLine
        newLine
      }
    )

  /**
   * Read a single expression entry from a DataInputStream, dispatching on tag.
   */
  def exprFromDIS(tag: Byte, dis: DataInputStream, exprMap: MutMap[Line, Expression]): Expression =
    tag match
      case tag: 0 => variableFromDIS(tag, dis)
      case tag: 1 => constantFromDIS(tag, dis)
      case tag: 2 => lambdaFromDIS(tag, dis, exprMap)
      case tag: 3 => applicationFromDIS(tag, dis, exprMap)
      case _ => throw InvalidExprTag(tag)

  /**
   * Write a sequent to a single DataOutputStream (self-contained).
   * Format: [Int: nodeCount][tree entries][Short: leftSize][line refs][Short: rightSize][line refs]
   */
  def sequentToDOS(s: Sequent, dos: DataOutputStream): Unit =
    val exprMap = MutMap[Long, Line]()
    val buffer = new ByteArrayOutputStream()
    val bufDOS = new DataOutputStream(buffer)
    val leftLines = s.left.toSeq.map(lineOfExpr(_, bufDOS, exprMap))
    val rightLines = s.right.toSeq.map(lineOfExpr(_, bufDOS, exprMap))
    bufDOS.flush()
    dos.writeInt(exprMap.size)
    dos.write(buffer.toByteArray)
    dos.writeShort(leftLines.size)
    leftLines.foreach(dos.writeInt)
    dos.writeShort(rightLines.size)
    rightLines.foreach(dos.writeInt)

  /**
   * Read a sequent from a single DataInputStream.
   * Inverse of [[sequentToDOS]].
   */
  def sequentFromDIS(dis: DataInputStream): Sequent =
    val nodeCount = dis.readInt()
    val exprMap = MutMap[Line, Expression]()
    readTreeEntries(dis, nodeCount, exprMap)
    val leftSize = dis.readShort()
    val left = (1 to leftSize).map(_ => exprMap(dis.readInt())).to(Set)
    val rightSize = dis.readShort()
    val right = (1 to rightSize).map(_ => exprMap(dis.readInt())).to(Set)
    Sequent(left, right)

  def readTreeEntries(dis: DataInputStream, count: Int, exprMap: MutMap[Line, Expression]): Unit =
    for lineNo <- 0 until count do
      val tag = dis.readByte()
      val expr = exprFromDIS(tag, dis, exprMap)
      exprMap(lineNo) = expr

  /**
   * Main function that, when given a proof, will serialize it to a file. It will also serialize all the formulas appearing in it to another file.
   */
  def proofsToDataStream(treesDOS: DataOutputStream, proofDOS: DataOutputStream, theorems: Seq[(String, SCProof, List[String])]): Unit = {

    val exprMap = MutMap[Long, Line]()

    def lineOfExpr(e: Expression): Line = Serialization.lineOfExpr(e, treesDOS, exprMap)

    // Write a sequent to the proof file.
    def sequentToProofDOS(sequent: Sequent): Unit =
      proofDOS.writeShort(sequent.left.size)
      sequent.left.foreach(f => proofDOS.writeInt(lineOfExpr(f)))
      proofDOS.writeShort(sequent.right.size)
      sequent.right.foreach(f => proofDOS.writeInt(lineOfExpr(f)))

    /**
     * Write a proof step to the proof file.
     * First write the code describing the proof step, then the "bot" sequent, then the various parameters in order.
     * List are described by first writing (as a short) the number of elements in the list.
     *
     * @param ps
     */
    def proofStepToProofDOS(ps: SCProofStep): Unit = {
      ps match {
        case Restate(bot, t1) =>
          proofDOS.writeByte(Tag.restate)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
        case RestateTrue(bot) =>
          proofDOS.writeByte(Tag.restateTrue)
          sequentToProofDOS(bot)
        case Hypothesis(bot, phi) =>
          proofDOS.writeByte(Tag.hypothesis)
          sequentToProofDOS(bot)
          proofDOS.writeInt(lineOfExpr(phi))
        case Cut(bot, t1, t2, phi) =>
          proofDOS.writeByte(Tag.cut)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(t2)
          proofDOS.writeInt(lineOfExpr(phi))
        case LeftAnd(bot, t1, phi, psi) =>
          proofDOS.writeByte(Tag.leftAnd)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(psi))
        case LeftOr(bot, t, disjuncts) =>
          proofDOS.writeByte(Tag.leftOr)
          sequentToProofDOS(bot)
          proofDOS.writeShort(t.size)
          t.foreach(proofDOS.writeInt)
          proofDOS.writeShort(disjuncts.size)
          disjuncts.foreach(f => proofDOS.writeInt(lineOfExpr(f)))
        case LeftImplies(bot, t1, t2, phi, psi) =>
          proofDOS.writeByte(Tag.leftImplies)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(t2)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(psi))
        case LeftIff(bot, t1, phi, psi) =>
          proofDOS.writeByte(Tag.leftIff)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(psi))
        case LeftNot(bot, t1, phi) =>
          proofDOS.writeByte(Tag.leftNot)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
        case LeftForall(bot, t1, phi, x, t) =>
          proofDOS.writeByte(Tag.leftForall)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(x))
          proofDOS.writeInt(lineOfExpr(t))
        case LeftExists(bot, t1, phi, x) =>
          proofDOS.writeByte(Tag.leftExists)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(x))
        case RightAnd(bot, t, conjuncts) =>
          proofDOS.writeByte(Tag.rightAnd)
          sequentToProofDOS(bot)
          proofDOS.writeShort(t.size)
          t.foreach(proofDOS.writeInt)
          proofDOS.writeShort(conjuncts.size)
          conjuncts.foreach(f => proofDOS.writeInt(lineOfExpr(f)))
        case RightOr(bot, t1, phi, psi) =>
          proofDOS.writeByte(Tag.rightOr)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(psi))
        case RightImplies(bot, t1, phi, psi) =>
          proofDOS.writeByte(Tag.rightImplies)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(psi))
        case RightIff(bot, t1, t2, phi, psi) =>
          proofDOS.writeByte(Tag.rightIff)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(t2)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(psi))
        case RightNot(bot, t1, phi) =>
          proofDOS.writeByte(Tag.rightNot)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
        case RightForall(bot, t1, phi, x) =>
          proofDOS.writeByte(Tag.rightForall)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(x))
        case RightExists(bot, t1, phi, x, t) =>
          proofDOS.writeByte(Tag.rightExists)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(x))
          proofDOS.writeInt(lineOfExpr(t))
        case RightEpsilon(bot, t1, phi, x, t) =>
          proofDOS.writeByte(Tag.rightEpsilon)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(x))
          proofDOS.writeInt(lineOfExpr(t))
        case Weakening(bot, t1) =>
          proofDOS.writeByte(Tag.weakening)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
        case LeftRefl(bot, t1, fa) =>
          proofDOS.writeByte(Tag.leftRefl)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(fa))
        case RightRefl(bot, fa) =>
          proofDOS.writeByte(Tag.rightRefl)
          sequentToProofDOS(bot)
          proofDOS.writeInt(lineOfExpr(fa))
        case LeftSubstEq(bot, t1, equals, lambdaPhi) =>
          proofDOS.writeByte(Tag.leftSubstEq)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeShort(equals.size)
          equals.foreach(ltts =>
            proofDOS.writeInt(lineOfExpr(ltts._1))
            proofDOS.writeInt(lineOfExpr(ltts._2))
          )
          proofDOS.writeShort(lambdaPhi._1.size)
          lambdaPhi._1.foreach(stl => proofDOS.writeInt(lineOfExpr(stl)))
          proofDOS.writeInt(lineOfExpr(lambdaPhi._2))
        case RightSubstEq(bot, t1, equals, lambdaPhi) =>
          proofDOS.writeByte(Tag.rightSubstEq)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeShort(equals.size)
          equals.foreach(ltts =>
            proofDOS.writeInt(lineOfExpr(ltts._1))
            proofDOS.writeInt(lineOfExpr(ltts._2))
          )
          proofDOS.writeShort(lambdaPhi._1.size)
          lambdaPhi._1.foreach(stl => proofDOS.writeInt(lineOfExpr(stl)))
          proofDOS.writeInt(lineOfExpr(lambdaPhi._2))
        case InstSchema(bot, t1, m) =>
          proofDOS.writeByte(Tag.instSchema)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeShort(m.size)
          m.foreach(t =>
            proofDOS.writeInt(lineOfExpr(t._1))
            proofDOS.writeInt(lineOfExpr(t._2))
          )
        case SCSubproof(sp, premises) => throw new Exception("Cannot support subproofs, flatten the proof first.")
        case Sorry(bot) =>
          proofDOS.writeByte(Tag.sorry)
          sequentToProofDOS(bot)
      }
    }

    proofDOS.writeShort(theorems.size)
    theorems.foreach((thmName, proof, justifications) =>
      proofDOS.writeUTF(thmName)
      proofDOS.writeShort(justifications.size)
      justifications.foreach(j => proofDOS.writeUTF(j))
      proofDOS.writeInt(proof.imports.size)
      proof.imports.foreach(sequent => sequentToProofDOS(sequent))
      proofDOS.writeInt(proof.steps.size)
      proof.steps.foreach(ps => proofStepToProofDOS(ps))
    )

  }

  def typeFromString(s: String): (Sort, String) =
    if s(0) == 'T' then (Ind, s.drop(1))
    else if s(0) == 'F' then (Prop, s.drop(1))
    else if s(0) == '>' then
      val (from, reminder) = typeFromString(s.drop(1))
      val (to, r) = typeFromString(reminder)
      (Arrow(from, to), r)
    else throw new Exception("Unknown type: " + s)

  /**
   * This functions reverses the effect of proofToDataStream
   *
   * @param lines The lines of the "file" where the proof is stored
   */
  def proofsFromDataStream(treesDIS: DataInputStream, proofDIS: DataInputStream): Seq[(String, SCProof, List[String])] = {

    val exprMap = MutMap[Line, Expression]()

    // Read and reconstruct all the terms and formulas in the tree file. Fill the table with it.
    var lineNo = -1

    try {
      while treesDIS.available() > 0 do
        lineNo += 1
        val tag = treesDIS.readByte()
        val expr = exprFromDIS(tag, treesDIS, exprMap)
        exprMap(lineNo) = expr
    } catch
      case _: EOFException =>
        throw IncompleteTreeException(lineNo)

    // Terms and Formulas finished, deal with the proof now.

    def sequentFromProofDIS(): Sequent =
      val leftSize = proofDIS.readShort()
      val left = (1 to leftSize).map(_ => exprMap(proofDIS.readInt())).to(Set)
      val rightSize = proofDIS.readShort()
      val right = (1 to rightSize).map(_ => exprMap(proofDIS.readInt())).to(Set)
      Sequent(left, right)

    // Read a proof step from the proof file. Inverse of proofStepToProofDOS
    def proofStepFromProofDIS(): SCProofStep =
      proofDIS.readByte() match
        case Tag.restate => Restate(sequentFromProofDIS(), proofDIS.readInt())
        case Tag.restateTrue => RestateTrue(sequentFromProofDIS())
        case Tag.hypothesis => Hypothesis(sequentFromProofDIS(), exprMap(proofDIS.readInt()))
        case Tag.cut => Cut(sequentFromProofDIS(), proofDIS.readInt(), proofDIS.readInt(), exprMap(proofDIS.readInt()))
        case Tag.leftAnd => LeftAnd(sequentFromProofDIS(), proofDIS.readInt(), exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()))
        case Tag.leftOr =>
          LeftOr(
            sequentFromProofDIS(),
            (1 to proofDIS.readShort()).map(_ => proofDIS.readInt()).toSeq,
            (1 to proofDIS.readShort()).map(_ => exprMap(proofDIS.readInt())).toSeq
          )
        case Tag.leftImplies => LeftImplies(sequentFromProofDIS(), proofDIS.readInt(), proofDIS.readInt(), exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()))
        case Tag.leftIff => LeftIff(sequentFromProofDIS(), proofDIS.readInt(), exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()))
        case Tag.leftNot => LeftNot(sequentFromProofDIS(), proofDIS.readInt(), exprMap(proofDIS.readInt()))
        case Tag.leftForall =>
          LeftForall(
            sequentFromProofDIS(),
            proofDIS.readInt(),
            exprMap(proofDIS.readInt()),
            exprMap(proofDIS.readInt()).asInstanceOf[Variable],
            exprMap(proofDIS.readInt())
          )
        case Tag.leftExists => LeftExists(sequentFromProofDIS(), proofDIS.readInt(), exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()).asInstanceOf[Variable])
        case Tag.rightAnd =>
          RightAnd(
            sequentFromProofDIS(),
            (1 to proofDIS.readShort()).map(_ => proofDIS.readInt()).toSeq,
            (1 to proofDIS.readShort()).map(_ => exprMap(proofDIS.readInt())).toSeq
          )
        case Tag.rightOr => RightOr(sequentFromProofDIS(), proofDIS.readInt(), exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()))
        case Tag.rightImplies => RightImplies(sequentFromProofDIS(), proofDIS.readInt(), exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()))
        case Tag.rightIff => RightIff(sequentFromProofDIS(), proofDIS.readInt(), proofDIS.readInt(), exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()))
        case Tag.rightNot => RightNot(sequentFromProofDIS(), proofDIS.readInt(), exprMap(proofDIS.readInt()))
        case Tag.rightForall => RightForall(sequentFromProofDIS(), proofDIS.readInt(), exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()).asInstanceOf[Variable])
        case Tag.rightExists =>
          RightExists(
            sequentFromProofDIS(),
            proofDIS.readInt(),
            exprMap(proofDIS.readInt()),
            exprMap(proofDIS.readInt()).asInstanceOf[Variable],
            exprMap(proofDIS.readInt())
          )
        case Tag.rightEpsilon =>
          RightEpsilon(
            sequentFromProofDIS(),
            proofDIS.readInt(),
            exprMap(proofDIS.readInt()),
            exprMap(proofDIS.readInt()).asInstanceOf[Variable],
            exprMap(proofDIS.readInt())
          )
        case Tag.weakening => Weakening(sequentFromProofDIS(), proofDIS.readInt())
        case Tag.leftRefl => LeftRefl(sequentFromProofDIS(), proofDIS.readInt(), exprMap(proofDIS.readInt()))
        case Tag.rightRefl => RightRefl(sequentFromProofDIS(), exprMap(proofDIS.readInt()))
        case Tag.leftSubstEq =>
          LeftSubstEq(
            sequentFromProofDIS(),
            proofDIS.readInt(),
            (1 to proofDIS.readShort()).map(_ => (exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()))).toList,
            ((1 to proofDIS.readShort()).map(_ => exprMap(proofDIS.readInt()).asInstanceOf[Variable]).toList, exprMap(proofDIS.readInt()))
          )
        case Tag.rightSubstEq =>
          RightSubstEq(
            sequentFromProofDIS(),
            proofDIS.readInt(),
            (1 to proofDIS.readShort()).map(_ => (exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()))).toList,
            ((1 to proofDIS.readShort()).map(_ => exprMap(proofDIS.readInt()).asInstanceOf[Variable]).toList, exprMap(proofDIS.readInt()))
          )
        case Tag.instSchema =>
          InstSchema(
            sequentFromProofDIS(),
            proofDIS.readInt(),
            (1 to proofDIS.readShort()).map(_ => exprMap(proofDIS.readInt()).asInstanceOf[Variable] -> exprMap(proofDIS.readInt())).toMap
          )
        case Tag.sorry => Sorry(sequentFromProofDIS())
        case psType => throw new Exception("Unknown proof step tag: " + psType)

    // for each given theorem, write it to the file.
    val numberThm = proofDIS.readShort()
    (1 to numberThm)
      .map(_ =>
        val thmName = proofDIS.readUTF()
        val justificationsSize = proofDIS.readShort()
        val justifications = (1 to justificationsSize).map(_ => proofDIS.readUTF()).toList
        val importsSize = proofDIS.readInt()
        val imports = (1 to importsSize).map(_ => sequentFromProofDIS()).toSeq
        val noSteps = proofDIS.readInt()
        val steps = (1 to noSteps).map(_ => proofStepFromProofDIS()).toSeq

        (thmName, new SCProof(steps.toIndexedSeq, imports.toIndexedSeq), justifications)
      )
      .toSeq

  }

  /**
   * Write a list of theorems to a pair of OutputStrem, one for the formulas and term trees, one for the proof.
   * Each theorem has a name, a proof and a list of justifications, with a name for those justifications that can be fetched in the code base.
   */
  def thmsToDataStream(treesDOS: DataOutputStream, proofDOS: DataOutputStream, theory: RunningTheory, theorems: List[(String, SCProof, List[(String, theory.Justification)])]): Unit = {
    proofsToDataStream(
      treesDOS,
      proofDOS,
      theorems.map((name, proof, justs) =>
        val justNames = justs.map {
          case (obj, theory.Axiom(name, ax)) => "a" + obj + "$" + name
          case (obj, theory.Theorem(name, proposition, withSorry)) => "t" + obj + "$" + name
          case (obj, theory.Definition(label, expression, vars)) =>
            "d" + obj + "$" + label.id.name + "_" + label.id.no + "_" + typeToString(label.sort) // + "__" +
          // vars.size + vars.map(v => v.id.name + "_" + v.id.no + "_" + typeToString(v.sort)).mkString("__")
        }
        // (name, minimizeProofOnce(proof), justNames)
        (name, proof, justNames)
      )
    )
  }

  /**
   * Read theorems from two files, one for the formulas and term trees, one for the proof.
   * Theorems are validated in the kernel. Justifications are looked up by their fully-qualified
   * kernel name, which is stored verbatim in the proof file.
   */
  def thmsFromDataStream(treesDIS: DataInputStream, proofDIS: DataInputStream, theory: RunningTheory, debug: Boolean = false): Seq[(theory.Theorem, SCProof)] = {
    proofsFromDataStream(treesDIS, proofDIS).map { (name, proof, justifications) =>
      val justs = justifications.map { j =>
        val nl = j.tail
        val Array(_, jName) = nl.split("\\$")
        j(0) match
          case 'a' => theory.getAxiom(jName).get
          case 't' => theory.getTheorem(jName).get
          case 'd' =>
            val Array(id, no, sort) = jName.split("_")
            val cst = Constant(Identifier(id, no.toInt), typeFromString(sort)._1)
            theory.getDefinition(cst).get
      }
      val verdict =
        if debug then theory.makeTheorem(name + "_test", proof.conclusion, proof, justs)
        else theory.makeTheorem(name, proof.conclusion, proof, justs)
      (verdict.get, proof)
    }

  }

  /**
   * Write a list of theorems to a pair file, one for the formulas and term trees, one for the proof.
   * Each theorem has a name, a proof and a list of justifications, with a name for those justifications that can be fetched in the code base.
   */
  def thmsToFile(filename: String, theory: RunningTheory, theorems: List[(String, SCProof, List[(String, theory.Justification)])]): Unit = {
    val directory = File(filename).getParentFile()
    if (directory != null) && !directory.exists() then directory.mkdirs()
    val treeFile = File(filename + ".trees")
    if !treeFile.exists() then treeFile.createNewFile()
    val proofFile = File(filename + ".proof")
    if !proofFile.exists() then proofFile.createNewFile()
    val treesDOS = new DataOutputStream(new BufferedOutputStream(new FileOutputStream(treeFile)))
    val proofDOS = new DataOutputStream(new BufferedOutputStream(new FileOutputStream(proofFile)))
    thmsToDataStream(treesDOS, proofDOS, theory, theorems)
    treesDOS.close()
    proofDOS.close()
  }

  /**
   * Read theorems from two files, one for the formulas and term trees, one for the proof.
   * Theorems are validated in the kernel. Justifications are fetched from the code base using the name written in the file.
   */
  def thmsFromFile(filename: String, theory: RunningTheory): Seq[(theory.Theorem, SCProof)] = {
    val treesDIS = new DataInputStream(new BufferedInputStream(new FileInputStream(File(filename + ".trees"))))
    val proofDIS = new DataInputStream(new BufferedInputStream(new FileInputStream(File(filename + ".proof"))))
    val thm = thmsFromDataStream(treesDIS, proofDIS, theory, false)
    treesDIS.close()
    proofDIS.close()
    thm
  }

  /**
   * Same as [[thmsFromFile]] but only returns the first theorem (usually because we know there is only one theorem in the file).
   */
  def oneThmFromFile(filename: String, theory: RunningTheory): Option[theory.Theorem] = {
    val treeFile = File(filename + ".trees")
    val proofFile = File(filename + ".proof")
    if treeFile.isFile() && proofFile.isFile() then
      val treesDIS = new DataInputStream(new BufferedInputStream(new FileInputStream(treeFile)))
      val proofDIS = new DataInputStream(new BufferedInputStream(new FileInputStream(proofFile)))

      val thm =
        try { Some(thmsFromDataStream(treesDIS, proofDIS, theory, false)) }
        catch {
          case e: Exception =>
            println("Error while reading theorems from file: " + filename)
            None
        }
      treesDIS.close()
      proofDIS.close()
      thm.map(_.head._1)
    else None
  }

}
