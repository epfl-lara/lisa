package lisa.utils

import lisa.kernel.proof.SequentCalculus._
import lisa.utils.K.{LeftSubstEq => _, LeftSubstIff => _, RightSubstEq => _, RightSubstIff => _, _}
import lisa.utils.ProofsShrink._

import java.io._
import scala.collection.mutable.{Map => MutMap}

object Serialization {

  // Define codes for the various proof steps
  inline def restate: Byte = 0
  inline def restateTrue: Byte = 1
  inline def hypothesis: Byte = 2
  inline def cut: Byte = 3
  inline def leftAnd: Byte = 4
  inline def leftOr: Byte = 5
  inline def leftImplies: Byte = 6
  inline def leftIff: Byte = 7
  inline def leftNot: Byte = 8
  inline def leftForall: Byte = 9
  inline def leftExists: Byte = 10
  inline def rightAnd: Byte = 12
  inline def rightOr: Byte = 13
  inline def rightImplies: Byte = 14
  inline def rightIff: Byte = 15
  inline def rightNot: Byte = 16
  inline def rightForall: Byte = 17
  inline def rightExists: Byte = 18
  inline def rightEpsilon: Byte = 19
  inline def weakening: Byte = 20
  inline def beta: Byte = 21
  inline def leftRefl: Byte = 22
  inline def rightRefl: Byte = 23
  inline def leftSubstEq: Byte = 24
  inline def rightSubstEq: Byte = 25
  inline def instSchema: Byte = 26
  inline def scSubproof: Byte = 27
  inline def sorry: Byte = 28

  type Line = Int

  def typeToString(t: Sort): String =
    t match
      case Ind => "T"
      case Prop => "F"
      case Arrow(from, to) => s">${typeToString(from)}${typeToString(to)}"

  def constantToString(c: Constant): String = "cst_" + c.id.name + "_" + c.id.no + "_" + typeToString(c.sort)
  def variableToString(v: Variable): String = "var_" + v.id.name + "_" + v.id.no + "_" + typeToString(v.sort)

  def constantToDos(c: Constant, dos: DataOutputStream): Unit =
    dos.writeByte(0)
    dos.writeUTF(c.id.name)
    dos.writeInt(c.id.no)
    dos.writeUTF(typeToString(c.sort))

  def variableToDOS(v: Variable, dos: DataOutputStream): Unit =
    dos.writeByte(1)
    dos.writeUTF(v.id.name)
    dos.writeInt(v.id.no)
    dos.writeUTF(typeToString(v.sort))

  /*
  def formulaLabelToDOS(label: FormulaLabel, dos: DataOutputStream): Unit =
    label match
      case l: ConstantAtomicLabel =>
        dos.writeByte(3)
        dos.writeUTF(l.id.name)
        dos.writeInt(l.id.no)
        dos.writeInt(l.arity)
      case l: SchematicPredicateLabel =>
        dos.writeByte(4)
        dos.writeUTF(l.id.name)
        dos.writeInt(l.id.no)
        dos.writeInt(l.arity)
      case l: ConstantConnectorLabel =>
        dos.writeByte(5)
        dos.writeUTF(l.id.name)
      case l: SchematicConnectorLabel =>
        dos.writeByte(6)
        dos.writeUTF(l.id.name)
        dos.writeInt(l.id.no)
        dos.writeInt(l.arity)
      case l: VariableFormulaLabel =>
        dos.writeByte(7)
        dos.writeUTF(l.id.name)
        dos.writeInt(l.id.no)
      case l: BinderLabel =>
        dos.writeByte(8)
        dos.writeUTF(l.id.name)
   */

  /**
   * Main function that, when given a proof, will serialize it to a file. It will also serialize all the formulas appearing in it to another file.
   */
  def proofsToDataStream(treesDOS: DataOutputStream, proofDOS: DataOutputStream, theorems: Seq[(String, SCProof, List[String])]): Unit = {

    val exprMap = MutMap[Long, Line]()

    var line = -1

    // Compute the line of a formula. If it is not in the map, add it to the map and write it to the tree file
    def lineOfExpr(e: Expression): Line =
      exprMap.get(e.uniqueNumber) match
        case Some(line) => line
        case None =>
          val nextLine = e match
            case v: Variable =>
              treesDOS.writeByte(0)
              treesDOS.writeUTF(v.id.name)
              treesDOS.writeInt(v.id.no)
              treesDOS.writeUTF(typeToString(v.sort))
            case c: Constant =>
              treesDOS.writeByte(1)
              treesDOS.writeUTF(c.id.name)
              treesDOS.writeInt(c.id.no)
              treesDOS.writeUTF(typeToString(c.sort))
            case Lambda(v, inner) =>
              treesDOS.writeByte(2)
              val vi = lineOfExpr(v)
              val ni = lineOfExpr(inner)
              treesDOS.writeInt(vi)
              treesDOS.writeInt(ni)
            case Application(f, arg) =>
              treesDOS.writeByte(3)
              val a1 = lineOfExpr(f)
              val a2 = lineOfExpr(arg)
              treesDOS.writeInt(a1)
              treesDOS.writeInt(a2)
          line = line + 1
          exprMap(e.uniqueNumber) = line
          line

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
          proofDOS.writeByte(restate)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
        case RestateTrue(bot) =>
          proofDOS.writeByte(restateTrue)
          sequentToProofDOS(bot)
        case Hypothesis(bot, phi) =>
          proofDOS.writeByte(hypothesis)
          sequentToProofDOS(bot)
          proofDOS.writeInt(lineOfExpr(phi))
        case Cut(bot, t1, t2, phi) =>
          proofDOS.writeByte(cut)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(t2)
          proofDOS.writeInt(lineOfExpr(phi))
        case LeftAnd(bot, t1, phi, psi) =>
          proofDOS.writeByte(leftAnd)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(psi))
        case LeftOr(bot, t, disjuncts) =>
          proofDOS.writeByte(leftOr)
          sequentToProofDOS(bot)
          proofDOS.writeShort(t.size)
          t.foreach(proofDOS.writeInt)
          proofDOS.writeShort(disjuncts.size)
          disjuncts.foreach(f => proofDOS.writeInt(lineOfExpr(f)))
        case LeftImplies(bot, t1, t2, phi, psi) =>
          proofDOS.writeByte(leftImplies)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(t2)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(psi))
        case LeftIff(bot, t1, phi, psi) =>
          proofDOS.writeByte(leftIff)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(psi))
        case LeftNot(bot, t1, phi) =>
          proofDOS.writeByte(leftNot)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
        case LeftForall(bot, t1, phi, x, t) =>
          proofDOS.writeByte(leftForall)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(x))
          proofDOS.writeInt(lineOfExpr(t))
        case LeftExists(bot, t1, phi, x) =>
          proofDOS.writeByte(leftExists)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(x))
        case RightAnd(bot, t, conjuncts) =>
          proofDOS.writeByte(rightAnd)
          sequentToProofDOS(bot)
          proofDOS.writeShort(t.size)
          t.foreach(proofDOS.writeInt)
          proofDOS.writeShort(conjuncts.size)
          conjuncts.foreach(f => proofDOS.writeInt(lineOfExpr(f)))
        case RightOr(bot, t1, phi, psi) =>
          proofDOS.writeByte(rightOr)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(psi))
        case RightImplies(bot, t1, phi, psi) =>
          proofDOS.writeByte(rightImplies)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(psi))
        case RightIff(bot, t1, t2, phi, psi) =>
          proofDOS.writeByte(rightIff)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(t2)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(psi))
        case RightNot(bot, t1, phi) =>
          proofDOS.writeByte(rightNot)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
        case RightForall(bot, t1, phi, x) =>
          proofDOS.writeByte(rightForall)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(x))
        case RightExists(bot, t1, phi, x, t) =>
          proofDOS.writeByte(rightExists)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(x))
          proofDOS.writeInt(lineOfExpr(t))
        case RightEpsilon(bot, t1, phi, x, t) =>
          proofDOS.writeByte(rightEpsilon)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(phi))
          proofDOS.writeInt(lineOfExpr(x))
          proofDOS.writeInt(lineOfExpr(t))
        case Weakening(bot, t1) =>
          proofDOS.writeByte(weakening)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
        case Beta(bot, t1) =>
          proofDOS.writeByte(beta)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
        case LeftRefl(bot, t1, fa) =>
          proofDOS.writeByte(leftRefl)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfExpr(fa))
        case RightRefl(bot, fa) =>
          proofDOS.writeByte(rightRefl)
          sequentToProofDOS(bot)
          proofDOS.writeInt(lineOfExpr(fa))
        case LeftSubstEq(bot, t1, equals, lambdaPhi) =>
          proofDOS.writeByte(leftSubstEq)
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
          proofDOS.writeByte(leftSubstEq)
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
          proofDOS.writeByte(instSchema)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeShort(m.size)
          m.foreach(t =>
            proofDOS.writeInt(lineOfExpr(t._1))
            proofDOS.writeInt(lineOfExpr(t._2))
          )
        case SCSubproof(sp, premises) => throw new Exception("Cannot support subproofs, flatten the proof first.")
        case Sorry(bot) =>
          proofDOS.writeByte(sorry)
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
      while true do
        lineNo = lineNo + 1
        treesDIS.readByte() match
          case 0 =>
            val name = treesDIS.readUTF()
            val no = treesDIS.readInt()
            val sort = treesDIS.readUTF()
            Variable(Identifier(name, no), typeFromString(sort)._1)
          case 1 =>
            val name = treesDIS.readUTF()
            val no = treesDIS.readInt()
            val sort = treesDIS.readUTF()
            Constant(Identifier(name, no), typeFromString(sort)._1)
          case 2 =>
            val v = exprMap(treesDIS.readInt())
            val body = exprMap(treesDIS.readInt())
            Lambda(v.asInstanceOf[Variable], body)
          case 3 =>
            val f = exprMap(treesDIS.readInt())
            val arg = exprMap(treesDIS.readInt())
            Application(f, arg)
    } catch
      case _: EOFException =>
        ()

    // Terms and Formulas finished, deal with the proof now.

    def sequentFromProofDIS(): Sequent =
      val leftSize = proofDIS.readShort()
      val left = (1 to leftSize).map(_ => exprMap(proofDIS.readInt())).toSet
      val rightSize = proofDIS.readShort()
      val right = (1 to rightSize).map(_ => exprMap(proofDIS.readInt())).toSet
      Sequent(left, right)

    // Read a proof step from the proof file. Inverse of proofStepToProofDOS
    def proofStepFromProofDIS(): SCProofStep = {
      val psType = proofDIS.readByte()
      if (psType == restate) Restate(sequentFromProofDIS(), proofDIS.readInt())
      else if (psType == restateTrue) RestateTrue(sequentFromProofDIS())
      else if (psType == hypothesis) Hypothesis(sequentFromProofDIS(), exprMap(proofDIS.readInt()))
      else if (psType == cut) Cut(sequentFromProofDIS(), proofDIS.readInt(), proofDIS.readInt(), exprMap(proofDIS.readInt()))
      else if (psType == leftAnd) LeftAnd(sequentFromProofDIS(), proofDIS.readInt(), exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()))
      else if (psType == leftOr)
        LeftOr(
          sequentFromProofDIS(),
          (1 to proofDIS.readShort()).map(_ => proofDIS.readInt()).toSeq,
          (1 to proofDIS.readShort()).map(_ => exprMap(proofDIS.readInt())).toSeq
        )
      else if (psType == leftImplies) LeftImplies(sequentFromProofDIS(), proofDIS.readInt(), proofDIS.readInt(), exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()))
      else if (psType == leftIff) LeftIff(sequentFromProofDIS(), proofDIS.readInt(), exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()))
      else if (psType == leftNot) LeftNot(sequentFromProofDIS(), proofDIS.readInt(), exprMap(proofDIS.readInt()))
      else if (psType == leftForall)
        LeftForall(
          sequentFromProofDIS(),
          proofDIS.readInt(),
          exprMap(proofDIS.readInt()),
          exprMap(proofDIS.readInt()).asInstanceOf[Variable],
          exprMap(proofDIS.readInt())
        )
      else if (psType == leftExists) LeftExists(sequentFromProofDIS(), proofDIS.readInt(), exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()).asInstanceOf[Variable])
      else if (psType == rightAnd)
        RightAnd(
          sequentFromProofDIS(),
          (1 to proofDIS.readShort()).map(_ => proofDIS.readInt()).toSeq,
          (1 to proofDIS.readShort()).map(_ => exprMap(proofDIS.readInt())).toSeq
        )
      else if (psType == rightOr) RightOr(sequentFromProofDIS(), proofDIS.readInt(), exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()))
      else if (psType == rightImplies) RightImplies(sequentFromProofDIS(), proofDIS.readInt(), exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()))
      else if (psType == rightIff) RightIff(sequentFromProofDIS(), proofDIS.readInt(), proofDIS.readInt(), exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()))
      else if (psType == rightNot) RightNot(sequentFromProofDIS(), proofDIS.readInt(), exprMap(proofDIS.readInt()))
      else if (psType == rightForall) RightForall(sequentFromProofDIS(), proofDIS.readInt(), exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()).asInstanceOf[Variable])
      else if (psType == rightExists)
        RightExists(
          sequentFromProofDIS(),
          proofDIS.readInt(),
          exprMap(proofDIS.readInt()),
          exprMap(proofDIS.readInt()).asInstanceOf[Variable],
          exprMap(proofDIS.readInt())
        )
      else if (psType == rightEpsilon)
        RightEpsilon(
          sequentFromProofDIS(),
          proofDIS.readInt(),
          exprMap(proofDIS.readInt()),
          exprMap(proofDIS.readInt()).asInstanceOf[Variable],
          exprMap(proofDIS.readInt())
        )
      else if (psType == weakening) Weakening(sequentFromProofDIS(), proofDIS.readInt())
      else if (psType == beta)
        Beta(sequentFromProofDIS(), proofDIS.readInt())
      else if (psType == leftRefl) LeftRefl(sequentFromProofDIS(), proofDIS.readInt(), exprMap(proofDIS.readInt()))
      else if (psType == rightRefl) RightRefl(sequentFromProofDIS(), exprMap(proofDIS.readInt()))
      else if (psType == leftSubstEq)
        LeftSubstEq(
          sequentFromProofDIS(),
          proofDIS.readInt(),
          (1 to proofDIS.readShort()).map(_ => (exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()))).toList,
          ((1 to proofDIS.readShort()).map(_ => exprMap(proofDIS.readInt()).asInstanceOf[Variable]).toList, exprMap(proofDIS.readInt()))
        )
      else if (psType == rightSubstEq)
        RightSubstEq(
          sequentFromProofDIS(),
          proofDIS.readInt(),
          (1 to proofDIS.readShort()).map(_ => (exprMap(proofDIS.readInt()), exprMap(proofDIS.readInt()))).toList,
          ((1 to proofDIS.readShort()).map(_ => exprMap(proofDIS.readInt()).asInstanceOf[Variable]).toList, exprMap(proofDIS.readInt()))
        )
      else if (psType == instSchema)
        InstSchema(
          sequentFromProofDIS(),
          proofDIS.readInt(),
          (1 to proofDIS.readShort()).map(_ => exprMap(proofDIS.readInt()).asInstanceOf[Variable] -> exprMap(proofDIS.readInt())).toMap
        )
      else if (psType == sorry) Sorry(sequentFromProofDIS())
      else throw new Exception("Unknown proof step type: " + psType)
    }

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
   * Theorems are validated in the kernel. Justifications are fetched from the code base using the name written in the file.
   * This uses java reflection, for example to obtain the theorem [[scala.mathematics.settheory.SetTheoryLibrary.russelsParadox]] from the
   * string "scala.mathematics.settheory.SetTheoryLibrary.russelsParadox".
   * A bit ugly, but don't really have better for now.
   */
  def thmsFromDataStream(treesDIS: DataInputStream, proofDIS: DataInputStream, theory: RunningTheory, debug: Boolean = false): Seq[(theory.Theorem, SCProof)] = {
    proofsFromDataStream(treesDIS, proofDIS).map { (name, proof, justifications) =>
      val justs = justifications.map { j =>
        val nl = j.tail
        val Array(obj, name) = nl.split("\\$")
        try {
          Class.forName(obj + "$").getField("MODULE$").get(null)
        } catch { case _ => "Not found: " + obj }
        j(0) match
          case 'a' => theory.getAxiom(name).get
          case 't' =>
            theory.getTheorem(name).get
          case 'd' =>
            val Array(id, no, sort) = name.split("_")
            val cst = Constant(Identifier(id, no.toInt), typeFromString(sort)._1)
            theory.getDefinition(cst).get
      }
      if debug then
        // To avoid conflicts where a theorem already exists, for example in test suits.
        (theory.makeTheorem(name + "_test", proof.conclusion, proof, justs).get, proof)
      else (theory.makeTheorem(name, proof.conclusion, proof, justs).get, proof)
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
      val thm = thmsFromDataStream(treesDIS, proofDIS, theory, false)
      treesDIS.close()
      proofDIS.close()
      Some(thm.head._1)
    else None
  }

}
