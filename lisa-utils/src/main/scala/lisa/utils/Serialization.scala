package lisa.utils

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.Sequent
import lisa.utils.kernel.*

import java.io.*
import scala.collection.mutable.{Map => MutMap}

/**
 * Serialize expressions, sequents, and linear proofs in binary form.
 */
object Serialization:

  case class InvalidStepTag(tag: Byte) extends Exception("Invalid proof step tag: " + tag)
  case class InvalidExprTag(tag: Byte) extends Exception("Invalid expression tag: " + tag)
  case class IncompleteTreeException(idx: Int) extends Exception("Unexpected end of file while reading tree, after index " + idx)

  object Tag:
    // Proof-step tags.
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
    inline val beta = 21 // reserved proof-step tag
    inline val leftRefl = 22
    inline val rightRefl = 23
    inline val leftSubstEq = 24
    inline val rightSubstEq = 25
    inline val instSchema = 26
    inline val scSubproof = 27 // reserved proof-step tag
    inline val sorry = 28

    // LCF proof-step tags.
    inline val axiom = 29
    inline val assume = 30
    inline val discharge = 31
    inline val definition = 32

    // Expression-tree tags.
    inline val variable = 0
    inline val constant = 1
    inline val lambda = 2
    inline val application = 3

  type Line = Int

  /**
   * Encode a sort as a prefix string.
   */
  def typeToString(t: Sort): String = t match
    case Ind => "T"
    case Prop => "F"
    case Arrow(from, to) => s">${typeToString(from)}${typeToString(to)}"

  /**
   * Decode the leading sort and return the unconsumed suffix.
   */
  def typeFromString(s: String): (Sort, String) =
    if s(0) == 'T' then (Ind, s.drop(1))
    else if s(0) == 'F' then (Prop, s.drop(1))
    else if s(0) == '>' then
      val (from, remainder) = typeFromString(s.drop(1))
      val (to, rest) = typeFromString(remainder)
      (Arrow(from, to), rest)
    else throw new Exception("Unknown type: " + s)

  /**
   * Write a constant tree entry.
   */
  def constantToDOS(c: Constant, dos: DataOutputStream): Unit =
    dos.writeByte(Tag.constant)
    dos.writeUTF(c.id.name)
    dos.writeInt(c.id.no)
    dos.writeUTF(typeToString(c.sort))

  /**
   * Write a variable tree entry.
   */
  def variableToDOS(v: Variable, dos: DataOutputStream): Unit =
    dos.writeByte(Tag.variable)
    dos.writeUTF(v.id.name)
    dos.writeInt(v.id.no)
    dos.writeUTF(typeToString(v.sort))

  /**
   * Write a lambda tree entry using existing child lines.
   */
  def lamdbaToDOS(l: Lambda, dos: DataOutputStream, exprMap: MutMap[Long, Line]): Unit =
    dos.writeByte(Tag.lambda)
    dos.writeInt(exprMap(l.v.uniqueNumber))
    dos.writeInt(exprMap(l.body.uniqueNumber))

  /**
   * Write an application tree entry using existing child lines.
   */
  def applicationToDOS(a: Application, dos: DataOutputStream, exprMap: MutMap[Long, Line]): Unit =
    dos.writeByte(Tag.application)
    dos.writeInt(exprMap(a.f.uniqueNumber))
    dos.writeInt(exprMap(a.arg.uniqueNumber))

  /**
   * Read a variable after its tag.
   */
  inline def variableFromDIS(tag: Tag.variable.type, dis: DataInputStream): Variable =
    Variable(Identifier(dis.readUTF(), dis.readInt()), typeFromString(dis.readUTF())._1)

  /**
   * Read a constant after its tag.
   */
  inline def constantFromDIS(tag: Tag.constant.type, dis: DataInputStream): Constant =
    Constant(Identifier(dis.readUTF(), dis.readInt()), typeFromString(dis.readUTF())._1)

  /**
   * Read a lambda after its tag.
   */
  inline def lambdaFromDIS(tag: Tag.lambda.type, dis: DataInputStream, exprMap: MutMap[Line, Expression]): Lambda =
    Lambda(exprMap(dis.readInt()).asInstanceOf[Variable], exprMap(dis.readInt()))

  /**
   * Read an application after its tag.
   */
  inline def applicationFromDIS(tag: Tag.application.type, dis: DataInputStream, exprMap: MutMap[Line, Expression]): Application =
    Application(exprMap(dis.readInt()), exprMap(dis.readInt()))

  /**
   * Write unseen subexpressions first and return the expression line.
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
        val line = exprMap.size
        exprMap(e.uniqueNumber) = line
        line
      }
    )

  /**
   * Read one expression tree entry.
   */
  def exprFromDIS(tag: Byte, dis: DataInputStream, exprMap: MutMap[Line, Expression]): Expression = tag match
    case tag: 0 => variableFromDIS(tag, dis)
    case tag: 1 => constantFromDIS(tag, dis)
    case tag: 2 => lambdaFromDIS(tag, dis, exprMap)
    case tag: 3 => applicationFromDIS(tag, dis, exprMap)
    case _ => throw InvalidExprTag(tag)

  /**
   * Read expression tree entries into a line map.
   */
  def readTreeEntries(dis: DataInputStream, count: Int, exprMap: MutMap[Line, Expression]): Unit =
    for line <- 0 until count do exprMap(line) = exprFromDIS(dis.readByte(), dis, exprMap)

  /**
   * Write a self-contained sequent.
   */
  def sequentToDOS(s: Sequent, dos: DataOutputStream): Unit =
    val exprMap = MutMap[Long, Line]()
    val buffer = new ByteArrayOutputStream()
    val treeDOS = new DataOutputStream(buffer)
    val left = s.left.toSeq.map(lineOfExpr(_, treeDOS, exprMap))
    val right = s.right.toSeq.map(lineOfExpr(_, treeDOS, exprMap))
    treeDOS.flush()
    dos.writeInt(exprMap.size)
    dos.write(buffer.toByteArray)
    dos.writeShort(left.size)
    left.foreach(dos.writeInt)
    dos.writeShort(right.size)
    right.foreach(dos.writeInt)

  /**
   * Read a self-contained sequent.
   */
  def sequentFromDIS(dis: DataInputStream): Sequent =
    val exprMap = MutMap[Line, Expression]()
    readTreeEntries(dis, dis.readInt(), exprMap)
    val left = (1 to dis.readShort()).map(_ => exprMap(dis.readInt())).toSet
    val right = (1 to dis.readShort()).map(_ => exprMap(dis.readInt())).toSet
    Sequent(left, right)

  private final class ProofWriter(treesDOS: DataOutputStream, proofDOS: DataOutputStream):
    private val exprMap = MutMap[Long, Line]()

    private def line(e: Expression): Line = lineOfExpr(e, treesDOS, exprMap)

    private def writeSequent(s: Sequent): Unit =
      proofDOS.writeShort(s.left.size)
      s.left.foreach(e => proofDOS.writeInt(line(e)))
      proofDOS.writeShort(s.right.size)
      s.right.foreach(e => proofDOS.writeInt(line(e)))

    private def writeExprs(es: Seq[Expression]): Unit =
      proofDOS.writeShort(es.size)
      es.foreach(e => proofDOS.writeInt(line(e)))

    private def writePremises(ps: Array[Int]): Unit =
      proofDOS.writeShort(ps.length)
      ps.foreach(proofDOS.writeInt)

    private def writeEquals(equals: Seq[(Expression, Expression)]): Unit =
      proofDOS.writeShort(equals.size)
      equals.foreach { (left, right) =>
        proofDOS.writeInt(line(left))
        proofDOS.writeInt(line(right))
      }

    private def writeLambda(lambdaPhi: (Seq[Variable], Expression)): Unit =
      proofDOS.writeShort(lambdaPhi._1.size)
      lambdaPhi._1.foreach(v => proofDOS.writeInt(line(v)))
      proofDOS.writeInt(line(lambdaPhi._2))

    /**
     * Write one proof step.
     */
    def writeStep(step: ProofStep): Unit = step match
      case Restate(statement, premise) =>
        proofDOS.writeByte(Tag.restate); writeSequent(statement); proofDOS.writeInt(premise)
      case RestateTrue(statement) =>
        proofDOS.writeByte(Tag.restateTrue); writeSequent(statement)
      case Hypothesis(statement, phi) =>
        proofDOS.writeByte(Tag.hypothesis); writeSequent(statement); proofDOS.writeInt(line(phi))
      case Cut(statement, premise1, premise2, phi) =>
        proofDOS.writeByte(Tag.cut); writeSequent(statement); proofDOS.writeInt(premise1); proofDOS.writeInt(premise2); proofDOS.writeInt(line(phi))
      case LeftAnd(statement, premise, phi, psi) =>
        proofDOS.writeByte(Tag.leftAnd); writeSequent(statement); proofDOS.writeInt(premise); proofDOS.writeInt(line(phi)); proofDOS.writeInt(line(psi))
      case LeftOr(statement, premises, disjuncts) =>
        proofDOS.writeByte(Tag.leftOr); writeSequent(statement); writePremises(premises); writeExprs(disjuncts)
      case LeftImplies(statement, premise1, premise2, phi, psi) =>
        proofDOS.writeByte(Tag.leftImplies); writeSequent(statement); proofDOS.writeInt(premise1); proofDOS.writeInt(premise2); proofDOS.writeInt(line(phi)); proofDOS.writeInt(line(psi))
      case LeftIff(statement, premise, phi, psi) =>
        proofDOS.writeByte(Tag.leftIff); writeSequent(statement); proofDOS.writeInt(premise); proofDOS.writeInt(line(phi)); proofDOS.writeInt(line(psi))
      case LeftNot(statement, premise, phi) =>
        proofDOS.writeByte(Tag.leftNot); writeSequent(statement); proofDOS.writeInt(premise); proofDOS.writeInt(line(phi))
      case LeftForall(statement, premise, phi, x, t) =>
        proofDOS.writeByte(Tag.leftForall); writeSequent(statement); proofDOS.writeInt(premise); proofDOS.writeInt(line(phi)); proofDOS.writeInt(line(x)); proofDOS.writeInt(line(t))
      case LeftExists(statement, premise, phi, x) =>
        proofDOS.writeByte(Tag.leftExists); writeSequent(statement); proofDOS.writeInt(premise); proofDOS.writeInt(line(phi)); proofDOS.writeInt(line(x))
      case RightAnd(statement, premises, conjuncts) =>
        proofDOS.writeByte(Tag.rightAnd); writeSequent(statement); writePremises(premises); writeExprs(conjuncts)
      case RightOr(statement, premise, phi, psi) =>
        proofDOS.writeByte(Tag.rightOr); writeSequent(statement); proofDOS.writeInt(premise); proofDOS.writeInt(line(phi)); proofDOS.writeInt(line(psi))
      case RightImplies(statement, premise, phi, psi) =>
        proofDOS.writeByte(Tag.rightImplies); writeSequent(statement); proofDOS.writeInt(premise); proofDOS.writeInt(line(phi)); proofDOS.writeInt(line(psi))
      case RightIff(statement, premise1, premise2, phi, psi) =>
        proofDOS.writeByte(Tag.rightIff); writeSequent(statement); proofDOS.writeInt(premise1); proofDOS.writeInt(premise2); proofDOS.writeInt(line(phi)); proofDOS.writeInt(line(psi))
      case RightNot(statement, premise, phi) =>
        proofDOS.writeByte(Tag.rightNot); writeSequent(statement); proofDOS.writeInt(premise); proofDOS.writeInt(line(phi))
      case RightForall(statement, premise, phi, x) =>
        proofDOS.writeByte(Tag.rightForall); writeSequent(statement); proofDOS.writeInt(premise); proofDOS.writeInt(line(phi)); proofDOS.writeInt(line(x))
      case RightExists(statement, premise, phi, x, t) =>
        proofDOS.writeByte(Tag.rightExists); writeSequent(statement); proofDOS.writeInt(premise); proofDOS.writeInt(line(phi)); proofDOS.writeInt(line(x)); proofDOS.writeInt(line(t))
      case RightEpsilon(statement, premise, phi, x, t) =>
        proofDOS.writeByte(Tag.rightEpsilon); writeSequent(statement); proofDOS.writeInt(premise); proofDOS.writeInt(line(phi)); proofDOS.writeInt(line(x)); proofDOS.writeInt(line(t))
      case Weakening(statement, premise) =>
        proofDOS.writeByte(Tag.weakening); writeSequent(statement); proofDOS.writeInt(premise)
      case LeftRefl(statement, premise, phi) =>
        proofDOS.writeByte(Tag.leftRefl); writeSequent(statement); proofDOS.writeInt(premise); proofDOS.writeInt(line(phi))
      case RightRefl(statement, phi) =>
        proofDOS.writeByte(Tag.rightRefl); writeSequent(statement); proofDOS.writeInt(line(phi))
      case LeftSubstEq(statement, premise, equals, lambdaPhi) =>
        proofDOS.writeByte(Tag.leftSubstEq); writeSequent(statement); proofDOS.writeInt(premise); writeEquals(equals); writeLambda(lambdaPhi)
      case RightSubstEq(statement, premise, equals, lambdaPhi) =>
        proofDOS.writeByte(Tag.rightSubstEq); writeSequent(statement); proofDOS.writeInt(premise); writeEquals(equals); writeLambda(lambdaPhi)
      case InstSchema(statement, premise, subst) =>
        proofDOS.writeByte(Tag.instSchema); writeSequent(statement); proofDOS.writeInt(premise); proofDOS.writeShort(subst.size)
        subst.foreach { (variable, expression) =>
          proofDOS.writeInt(line(variable)); proofDOS.writeInt(line(expression))
        }
      case Sorry(statement) =>
        proofDOS.writeByte(Tag.sorry); writeSequent(statement)
      case Axiom(statement) =>
        proofDOS.writeByte(Tag.axiom); writeSequent(statement)
      case Assume(statement) =>
        proofDOS.writeByte(Tag.assume); writeSequent(statement)
      case Discharge(statement, premise, justification) =>
        proofDOS.writeByte(Tag.discharge); writeSequent(statement); proofDOS.writeInt(premise); proofDOS.writeInt(justification)
      case Definition(statement, cst, vars, exp) =>
        proofDOS.writeByte(Tag.definition); writeSequent(statement); proofDOS.writeInt(line(cst)); writeExprs(vars); proofDOS.writeInt(line(exp))

    /**
     * Write one linear proof.
     */
    def writeProof(proof: LinearProof): Unit =
      proofDOS.writeInt(proof.imports.length)
      proof.imports.foreach(writeSequent)
      proofDOS.writeInt(proof.steps.length)
      proof.steps.foreach(writeStep)

  private final class ProofReader(treesDIS: DataInputStream, proofDIS: DataInputStream):
    private val exprMap = MutMap[Line, Expression]()
    private var nextLine = 0

    try
      while treesDIS.available() > 0 do
        exprMap(nextLine) = exprFromDIS(treesDIS.readByte(), treesDIS, exprMap)
        nextLine += 1
    catch case _: EOFException => throw IncompleteTreeException(nextLine - 1)

    private def expr(): Expression = exprMap(proofDIS.readInt())
    private def variable(): Variable = expr().asInstanceOf[Variable]
    private def constant(): Constant = expr().asInstanceOf[Constant]

    private def readSequent(): Sequent =
      val left = (1 to proofDIS.readShort()).map(_ => expr()).toSet
      val right = (1 to proofDIS.readShort()).map(_ => expr()).toSet
      Sequent(left, right)

    private def readPremises(): Array[Int] = Array.fill(proofDIS.readShort())(proofDIS.readInt())
    private def readExprs(): Seq[Expression] = Seq.fill(proofDIS.readShort())(expr())
    private def readVariables(): Seq[Variable] = Seq.fill(proofDIS.readShort())(variable())
    private def readEquals(): Seq[(Expression, Expression)] = Seq.fill(proofDIS.readShort())((expr(), expr()))
    private def readLambda(): (Seq[Variable], Expression) = (readVariables(), expr())

    /**
     * Read one proof step.
     */
    def readStep(): ProofStep = proofDIS.readByte() match
      case Tag.restate => Restate(readSequent(), proofDIS.readInt())
      case Tag.restateTrue => RestateTrue(readSequent())
      case Tag.hypothesis => Hypothesis(readSequent(), expr())
      case Tag.cut => Cut(readSequent(), proofDIS.readInt(), proofDIS.readInt(), expr())
      case Tag.leftAnd => LeftAnd(readSequent(), proofDIS.readInt(), expr(), expr())
      case Tag.leftOr => LeftOr(readSequent(), readPremises(), readExprs())
      case Tag.leftImplies => LeftImplies(readSequent(), proofDIS.readInt(), proofDIS.readInt(), expr(), expr())
      case Tag.leftIff => LeftIff(readSequent(), proofDIS.readInt(), expr(), expr())
      case Tag.leftNot => LeftNot(readSequent(), proofDIS.readInt(), expr())
      case Tag.leftForall => LeftForall(readSequent(), proofDIS.readInt(), expr(), variable(), expr())
      case Tag.leftExists => LeftExists(readSequent(), proofDIS.readInt(), expr(), variable())
      case Tag.rightAnd => RightAnd(readSequent(), readPremises(), readExprs())
      case Tag.rightOr => RightOr(readSequent(), proofDIS.readInt(), expr(), expr())
      case Tag.rightImplies => RightImplies(readSequent(), proofDIS.readInt(), expr(), expr())
      case Tag.rightIff => RightIff(readSequent(), proofDIS.readInt(), proofDIS.readInt(), expr(), expr())
      case Tag.rightNot => RightNot(readSequent(), proofDIS.readInt(), expr())
      case Tag.rightForall => RightForall(readSequent(), proofDIS.readInt(), expr(), variable())
      case Tag.rightExists => RightExists(readSequent(), proofDIS.readInt(), expr(), variable(), expr())
      case Tag.rightEpsilon => RightEpsilon(readSequent(), proofDIS.readInt(), expr(), variable(), expr())
      case Tag.weakening => Weakening(readSequent(), proofDIS.readInt())
      case Tag.leftRefl => LeftRefl(readSequent(), proofDIS.readInt(), expr())
      case Tag.rightRefl => RightRefl(readSequent(), expr())
      case Tag.leftSubstEq => LeftSubstEq(readSequent(), proofDIS.readInt(), readEquals(), readLambda())
      case Tag.rightSubstEq => RightSubstEq(readSequent(), proofDIS.readInt(), readEquals(), readLambda())
      case Tag.instSchema =>
        val statement = readSequent()
        val premise = proofDIS.readInt()
        val subst = (1 to proofDIS.readShort()).map(_ => variable() -> expr()).toMap
        InstSchema(statement, premise, subst)
      case Tag.sorry => Sorry(readSequent())
      case Tag.axiom => Axiom(readSequent())
      case Tag.assume => Assume(readSequent())
      case Tag.discharge => Discharge(readSequent(), proofDIS.readInt(), proofDIS.readInt())
      case Tag.definition => Definition(readSequent(), constant(), readVariables(), expr())
      case tag => throw InvalidStepTag(tag)

    /**
     * Read one linear proof.
     */
    def readProof(): LinearProof =
      val imports = Array.fill(proofDIS.readInt())(readSequent())
      val steps = Array.fill(proofDIS.readInt())(readStep())
      LinearProof(steps, imports)

  /**
   * Write one linear proof to separate tree and proof streams.
   */
  def proofToDataStream(treesDOS: DataOutputStream, proofDOS: DataOutputStream, proof: LinearProof): Unit =
    ProofWriter(treesDOS, proofDOS).writeProof(proof)

  /**
   * Read one linear proof from separate tree and proof streams.
   */
  def proofFromDataStream(treesDIS: DataInputStream, proofDIS: DataInputStream): LinearProof =
    ProofReader(treesDIS, proofDIS).readProof()

  /**
   * Write named linear proofs and their justification names.
   */
  def proofsToDataStream(
      treesDOS: DataOutputStream,
      proofDOS: DataOutputStream,
      proofs: Seq[(String, LinearProof, List[String])]
  ): Unit =
    val writer = ProofWriter(treesDOS, proofDOS)
    proofDOS.writeShort(proofs.size)
    proofs.foreach { (name, proof, justifications) =>
      proofDOS.writeUTF(name)
      proofDOS.writeShort(justifications.size)
      justifications.foreach(proofDOS.writeUTF)
      writer.writeProof(proof)
    }

  /**
   * Read named linear proofs and their justification names.
   */
  def proofsFromDataStream(
      treesDIS: DataInputStream,
      proofDIS: DataInputStream
  ): Seq[(String, LinearProof, List[String])] =
    val reader = ProofReader(treesDIS, proofDIS)
    (1 to proofDIS.readShort()).map { _ =>
      val name = proofDIS.readUTF()
      val justifications = (1 to proofDIS.readShort()).map(_ => proofDIS.readUTF()).toList
      (name, reader.readProof(), justifications)
    }
