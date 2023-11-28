package lisa.utils

import lisa.utils.K.*
import lisa.utils.ProofsShrink.*

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
  inline def leftExistsOne: Byte = 11
  inline def rightAnd: Byte = 12
  inline def rightOr: Byte = 13
  inline def rightImplies: Byte = 14
  inline def rightIff: Byte = 15
  inline def rightNot: Byte = 16
  inline def rightForall: Byte = 17
  inline def rightExists: Byte = 18
  inline def rightExistsOne: Byte = 19
  inline def weakening: Byte = 20
  inline def leftRefl: Byte = 21
  inline def rightRefl: Byte = 22
  inline def leftSubstEq: Byte = 23
  inline def rightSubstEq: Byte = 24
  inline def leftSubstIff: Byte = 25
  inline def rightSubstIff: Byte = 26
  inline def instSchema: Byte = 27
  inline def scSubproof: Byte = 28
  inline def sorry: Byte = 29

  type Line = Int

  // Injectively represent a TermLabel as a string
  def termLabelToString(label: TermLabel): String =
    label match
      case l: ConstantFunctionLabel => "cfl_" + l.id.name + "_" + l.id.no + "_" + l.arity
      case l: SchematicFunctionLabel => "sfl_" + l.id.name + "_" + l.id.no + "_" + l.arity
      case l: VariableLabel => "vl_" + l.id.name + "_" + l.id.no

  // Injectively represent a FormulaLabel as a string.
  def formulaLabelToString(label: FormulaLabel): String =
    label match
      case l: ConstantAtomicLabel => "cpl_" + l.id.name + "_" + l.id.no + "_" + l.arity
      case l: SchematicPredicateLabel => "spl_" + l.id.name + "_" + l.id.no + "_" + l.arity
      case l: ConstantConnectorLabel => "ccl_" + l.id.name + "_" + l.id.no + "_" + l.arity
      case l: SchematicConnectorLabel => "scl_" + l.id.name + "_" + l.id.no + "_" + l.arity
      case l: VariableFormulaLabel => "vfl_" + l.id.name + "_" + l.id.no
      case l: BinderLabel => "bl_" + l.id.name + "_" + l.id.no

  // write a term label to an OutputStream
  def termLabelToDOS(label: TermLabel, dos: DataOutputStream): Unit =
    label match
      case l: ConstantFunctionLabel =>
        dos.writeByte(0)
        dos.writeUTF(l.id.name)
        dos.writeInt(l.id.no)
        dos.writeInt(l.arity)
      case l: SchematicFunctionLabel =>
        dos.writeByte(1)
        dos.writeUTF(l.id.name)
        dos.writeInt(l.id.no)
        dos.writeInt(l.arity)
      case l: VariableLabel =>
        dos.writeByte(2)
        dos.writeUTF(l.id.name)
        dos.writeInt(l.id.no)
  // write a formula label to an OutputStream
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

  /**
   * Main function that, when given a proof, will serialize it to a file. It will also serialize all the formulas appearing in it to another file.
   */
  def proofsToDataStream(treesDOS: DataOutputStream, proofDOS: DataOutputStream, theorems: Seq[(String, SCProof, List[String])]): Unit = {

    val termMap = MutMap[Long, Line]()
    val formulaMap = MutMap[Long, Line]()

    var line = -1

    // Compute the line of a term. If it is not in the map, add it to the map and write it to the tree file
    def lineOfTerm(term: Term): Line =
      termMap.get(term.uniqueNumber) match
        case Some(line) => line
        case None =>
          val na = term.args.map(t => lineOfTerm(t))
          termLabelToDOS(term.label, treesDOS)
          na.foreach(t => treesDOS.writeInt(t))
          line = line + 1
          termMap(term.uniqueNumber) = line
          line

    // Compute the line of a formula. If it is not in the map, add it to the map and write it to the tree file
    def lineOfFormula(formula: Formula): Line =
      formulaMap.get(formula.uniqueNumber) match
        case Some(line) => line
        case None =>
          val nextLine = formula match
            case PredicateFormula(label, args) =>
              val na = args.map(t => lineOfTerm(t))
              formulaLabelToDOS(label, treesDOS)
              na.foreach(t => treesDOS.writeInt(t))
            case ConnectorFormula(label, args) =>
              val na = args.map(t => lineOfFormula(t))
              formulaLabelToDOS(label, treesDOS)
              treesDOS.writeShort(na.size)
              na.foreach(t => treesDOS.writeInt(t))
            case BinderFormula(label, bound, inner) =>
              val ni = lineOfFormula(inner)
              formulaLabelToDOS(label, treesDOS)
              termLabelToDOS(bound, treesDOS)
              treesDOS.writeInt(ni)
          line = line + 1
          formulaMap(formula.uniqueNumber) = line
          line

    // Write a sequent to the proof file.
    def sequentToProofDOS(sequent: Sequent): Unit =
      proofDOS.writeShort(sequent.left.size)
      sequent.left.foreach(f => proofDOS.writeInt(lineOfFormula(f)))
      proofDOS.writeShort(sequent.right.size)
      sequent.right.foreach(f => proofDOS.writeInt(lineOfFormula(f)))

    def lttToProofDOS(ltt: LambdaTermTerm): Unit =
      val body = lineOfTerm(ltt.body)
      proofDOS.writeShort(ltt.vars.size)
      ltt.vars.foreach(v => termLabelToDOS(v, proofDOS))
      proofDOS.writeInt(body)

    def ltfToProofDOS(ltf: LambdaTermFormula): Unit =
      val body = lineOfFormula(ltf.body)
      proofDOS.writeShort(ltf.vars.size)
      ltf.vars.foreach(v => termLabelToDOS(v, proofDOS))
      proofDOS.writeInt(body)

    def lffToProofDOS(lff: LambdaFormulaFormula): Unit =
      val body = lineOfFormula(lff.body)
      proofDOS.writeShort(lff.vars.size)
      lff.vars.foreach(v => formulaLabelToDOS(v, proofDOS))
      proofDOS.writeInt(body)

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
          proofDOS.writeInt(lineOfFormula(phi))
        case Cut(bot, t1, t2, phi) =>
          proofDOS.writeByte(cut)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(t2)
          proofDOS.writeInt(lineOfFormula(phi))
        case LeftAnd(bot, t1, phi, psi) =>
          proofDOS.writeByte(leftAnd)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfFormula(phi))
          proofDOS.writeInt(lineOfFormula(psi))
        case LeftOr(bot, t, disjuncts) =>
          proofDOS.writeByte(leftOr)
          sequentToProofDOS(bot)
          proofDOS.writeShort(t.size)
          t.foreach(proofDOS.writeInt)
          proofDOS.writeShort(disjuncts.size)
          disjuncts.foreach(f => proofDOS.writeInt(lineOfFormula(f)))
        case LeftImplies(bot, t1, t2, phi, psi) =>
          proofDOS.writeByte(leftImplies)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(t2)
          proofDOS.writeInt(lineOfFormula(phi))
          proofDOS.writeInt(lineOfFormula(psi))
        case LeftIff(bot, t1, phi, psi) =>
          proofDOS.writeByte(leftIff)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfFormula(phi))
          proofDOS.writeInt(lineOfFormula(psi))
        case LeftNot(bot, t1, phi) =>
          proofDOS.writeByte(leftNot)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfFormula(phi))
        case LeftForall(bot, t1, phi, x, t) =>
          proofDOS.writeByte(leftForall)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfFormula(phi))
          termLabelToDOS(x, proofDOS)
          proofDOS.writeInt(lineOfTerm(t))
        case LeftExists(bot, t1, phi, x) =>
          proofDOS.writeByte(leftExists)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfFormula(phi))
          termLabelToDOS(x, proofDOS)
        case LeftExistsOne(bot, t1, phi, x) =>
          proofDOS.writeByte(leftExistsOne)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfFormula(phi))
          termLabelToDOS(x, proofDOS)
        case RightAnd(bot, t, conjuncts) =>
          proofDOS.writeByte(rightAnd)
          sequentToProofDOS(bot)
          proofDOS.writeShort(t.size)
          t.foreach(proofDOS.writeInt)
          proofDOS.writeShort(conjuncts.size)
          conjuncts.foreach(f => proofDOS.writeInt(lineOfFormula(f)))
        case RightOr(bot, t1, phi, psi) =>
          proofDOS.writeByte(rightOr)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfFormula(phi))
          proofDOS.writeInt(lineOfFormula(psi))
        case RightImplies(bot, t1, phi, psi) =>
          proofDOS.writeByte(rightImplies)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfFormula(phi))
          proofDOS.writeInt(lineOfFormula(psi))
        case RightIff(bot, t1, t2, phi, psi) =>
          proofDOS.writeByte(rightIff)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(t2)
          proofDOS.writeInt(lineOfFormula(phi))
          proofDOS.writeInt(lineOfFormula(psi))
        case RightNot(bot, t1, phi) =>
          proofDOS.writeByte(rightNot)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfFormula(phi))
        case RightForall(bot, t1, phi, x) =>
          proofDOS.writeByte(rightForall)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfFormula(phi))
          termLabelToDOS(x, proofDOS)
        case RightExists(bot, t1, phi, x, t) =>
          proofDOS.writeByte(rightExists)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfFormula(phi))
          termLabelToDOS(x, proofDOS)
          proofDOS.writeInt(lineOfTerm(t))
        case RightExistsOne(bot, t1, phi, x) =>
          proofDOS.writeByte(rightExistsOne)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfFormula(phi))
          termLabelToDOS(x, proofDOS)
        case Weakening(bot, t1) =>
          proofDOS.writeByte(weakening)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
        case LeftRefl(bot, t1, fa) =>
          proofDOS.writeByte(leftRefl)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeInt(lineOfFormula(fa))
        case RightRefl(bot, fa) =>
          proofDOS.writeByte(rightRefl)
          sequentToProofDOS(bot)
          proofDOS.writeInt(lineOfFormula(fa))
        case LeftSubstEq(bot, t1, equals, lambdaPhi) =>
          proofDOS.writeByte(leftSubstEq)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeShort(equals.size)
          equals.foreach(t =>
            proofDOS.writeInt(lineOfTerm(t._1))
            proofDOS.writeInt(lineOfTerm(t._2))
          )
          ltfToProofDOS(lambdaPhi)
        case RightSubstEq(bot, t1, equals, lambdaPhi) =>
          proofDOS.writeByte(rightSubstEq)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeShort(equals.size)
          equals.foreach(t =>
            proofDOS.writeInt(lineOfTerm(t._1))
            proofDOS.writeInt(lineOfTerm(t._2))
          )
          ltfToProofDOS(lambdaPhi)
        case LeftSubstIff(bot, t1, equals, lambdaPhi) =>
          proofDOS.writeByte(leftSubstIff)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeShort(equals.size)
          equals.foreach(t =>
            proofDOS.writeInt(lineOfFormula(t._1))
            proofDOS.writeInt(lineOfFormula(t._2))
          )
          lffToProofDOS(lambdaPhi)
        case RightSubstIff(bot, t1, equals, lambdaPhi) =>
          proofDOS.writeByte(rightSubstIff)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeShort(equals.size)
          equals.foreach(t =>
            proofDOS.writeInt(lineOfFormula(t._1))
            proofDOS.writeInt(lineOfFormula(t._2))
          )
          lffToProofDOS(lambdaPhi)
        case InstSchema(bot, t1, mCon, mPred, mTerm) =>
          proofDOS.writeByte(instSchema)
          sequentToProofDOS(bot)
          proofDOS.writeInt(t1)
          proofDOS.writeShort(mCon.size)
          mCon.foreach(t =>
            formulaLabelToDOS(t._1, proofDOS)
            lffToProofDOS(t._2)
          )
          proofDOS.writeShort(mPred.size)
          mPred.foreach(t =>
            formulaLabelToDOS(t._1, proofDOS)
            ltfToProofDOS(t._2)
          )
          proofDOS.writeShort(mTerm.size)
          mTerm.foreach(t =>
            termLabelToDOS(t._1, proofDOS)
            lttToProofDOS(t._2)
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

  /**
   * This functions reverses the effect of proofToDataStream
   *
   * @param lines The lines of the "file" where the proof is stored
   */
  def proofsFromDataStream(treesDIS: DataInputStream, proofDIS: DataInputStream): Seq[(String, SCProof, List[String])] = {

    val termMap = MutMap[Line, Term]()
    val formulaMap = MutMap[Line, Formula]()

    // Read a label from the tree file, reversing the effect of termLabelToDOS and formulaLabelToDOS.
    def labelFromInputStream(dis: DataInputStream): Label = {
      val labelType = dis.readByte()
      labelType match
        case 0 =>
          val name = dis.readUTF()
          val no = dis.readInt()
          val arity = dis.readInt()
          ConstantFunctionLabel(Identifier(name, no), arity)
        case 1 =>
          val name = dis.readUTF()
          val no = dis.readInt()
          val arity = dis.readInt()
          SchematicFunctionLabel(Identifier(name, no), arity)
        case 2 =>
          val name = dis.readUTF()
          val no = dis.readInt()
          VariableLabel(Identifier(name, no))
        case 3 =>
          val name = dis.readUTF()
          val no = dis.readInt()
          val arity = dis.readInt()
          ConstantAtomicLabel(Identifier(name, no), arity)
        case 4 =>
          val name = dis.readUTF()
          val no = dis.readInt()
          val arity = dis.readInt()
          SchematicPredicateLabel(Identifier(name, no), arity)
        case 5 =>
          val name = dis.readUTF()
          name match
            case And.id.name => And
            case Or.id.name => Or
            case Implies.id.name => Implies
            case Iff.id.name => Iff
            case Neg.id.name => Neg
        case 6 =>
          val name = dis.readUTF()
          val no = dis.readInt()
          val arity = dis.readInt()
          SchematicConnectorLabel(Identifier(name, no), arity)
        case 7 =>
          val name = dis.readUTF()
          val no = dis.readInt()
          VariableFormulaLabel(Identifier(name, no))
        case 8 =>
          dis.readUTF() match
            case Forall.id.name => Forall
            case Exists.id.name => Exists
            case ExistsOne.id.name => ExistsOne

    }

    // Read and reconstruct all the terms and formulas in the tree file. Fill the table with it.
    var lineNo = -1
    try {
      while true do
        lineNo = lineNo + 1
        val label = labelFromInputStream(treesDIS)
        label match
          case l: TermLabel =>
            val args = (1 to l.arity).map(_ => termMap(treesDIS.readInt())).toSeq
            termMap(lineNo) = Term(l, args)
          case l: FormulaLabel =>
            val formula = label match
              case l: AtomicLabel =>
                val args = (1 to l.arity).map(_ => termMap(treesDIS.readInt())).toSeq
                PredicateFormula(l, args)
              case l: ConnectorLabel =>
                val ar = treesDIS.readShort()
                val args = (1 to ar).map(_ => formulaMap(treesDIS.readInt())).toSeq
                ConnectorFormula(l, args)
              case l: BinderLabel =>
                BinderFormula(l, labelFromInputStream(treesDIS).asInstanceOf[VariableLabel], formulaMap(treesDIS.readInt()))
            formulaMap(lineNo) = formula
    } catch
      case _: EOFException =>
        ()

    // Terms and Formulas finished, deal with the proof now.

    def lttFromProofDIS(): LambdaTermTerm =
      val vars = (1 to proofDIS.readShort()).map(_ => labelFromInputStream(proofDIS).asInstanceOf[VariableLabel]).toSeq
      val body = termMap(proofDIS.readInt())
      LambdaTermTerm(vars, body)

    def ltfFromProofDIS(): LambdaTermFormula =
      val vars = (1 to proofDIS.readShort()).map(_ => labelFromInputStream(proofDIS).asInstanceOf[VariableLabel]).toSeq
      val body = formulaMap(proofDIS.readInt())
      LambdaTermFormula(vars, body)

    def lffFromProofDIS(): LambdaFormulaFormula =
      val vars = (1 to proofDIS.readShort()).map(_ => labelFromInputStream(proofDIS).asInstanceOf[VariableFormulaLabel]).toSeq
      val body = formulaMap(proofDIS.readInt())
      LambdaFormulaFormula(vars, body)

    def sequentFromProofDIS(): Sequent =
      val leftSize = proofDIS.readShort()
      val left = (1 to leftSize).map(_ => formulaMap(proofDIS.readInt())).toSet
      val rightSize = proofDIS.readShort()
      val right = (1 to rightSize).map(_ => formulaMap(proofDIS.readInt())).toSet
      Sequent(left, right)

    // Read a proof step from the proof file. Inverse of proofStepToProofDOS
    def proofStepFromProofDIS(): SCProofStep = {
      val psType = proofDIS.readByte()
      if (psType == restate) Restate(sequentFromProofDIS(), proofDIS.readInt())
      else if (psType == restateTrue) RestateTrue(sequentFromProofDIS())
      else if (psType == hypothesis) Hypothesis(sequentFromProofDIS(), formulaMap(proofDIS.readInt()))
      else if (psType == cut) Cut(sequentFromProofDIS(), proofDIS.readInt(), proofDIS.readInt(), formulaMap(proofDIS.readInt()))
      else if (psType == leftAnd) LeftAnd(sequentFromProofDIS(), proofDIS.readInt(), formulaMap(proofDIS.readInt()), formulaMap(proofDIS.readInt()))
      else if (psType == leftOr)
        LeftOr(
          sequentFromProofDIS(),
          (1 to proofDIS.readShort()).map(_ => proofDIS.readInt()).toSeq,
          (1 to proofDIS.readShort()).map(_ => formulaMap(proofDIS.readInt())).toSeq
        )
      else if (psType == leftImplies) LeftImplies(sequentFromProofDIS(), proofDIS.readInt(), proofDIS.readInt(), formulaMap(proofDIS.readInt()), formulaMap(proofDIS.readInt()))
      else if (psType == leftIff) LeftIff(sequentFromProofDIS(), proofDIS.readInt(), formulaMap(proofDIS.readInt()), formulaMap(proofDIS.readInt()))
      else if (psType == leftNot) LeftNot(sequentFromProofDIS(), proofDIS.readInt(), formulaMap(proofDIS.readInt()))
      else if (psType == leftForall)
        LeftForall(
          sequentFromProofDIS(),
          proofDIS.readInt(),
          formulaMap(proofDIS.readInt()),
          labelFromInputStream(proofDIS).asInstanceOf[VariableLabel],
          termMap(proofDIS.readInt())
        )
      else if (psType == leftExists) LeftExists(sequentFromProofDIS(), proofDIS.readInt(), formulaMap(proofDIS.readInt()), labelFromInputStream(proofDIS).asInstanceOf[VariableLabel])
      else if (psType == leftExistsOne) LeftExistsOne(sequentFromProofDIS(), proofDIS.readInt(), formulaMap(proofDIS.readInt()), labelFromInputStream(proofDIS).asInstanceOf[VariableLabel])
      else if (psType == rightAnd)
        RightAnd(
          sequentFromProofDIS(),
          (1 to proofDIS.readShort()).map(_ => proofDIS.readInt()).toSeq,
          (1 to proofDIS.readShort()).map(_ => formulaMap(proofDIS.readInt())).toSeq
        )
      else if (psType == rightOr) RightOr(sequentFromProofDIS(), proofDIS.readInt(), formulaMap(proofDIS.readInt()), formulaMap(proofDIS.readInt()))
      else if (psType == rightImplies) RightImplies(sequentFromProofDIS(), proofDIS.readInt(), formulaMap(proofDIS.readInt()), formulaMap(proofDIS.readInt()))
      else if (psType == rightIff) RightIff(sequentFromProofDIS(), proofDIS.readInt(), proofDIS.readInt(), formulaMap(proofDIS.readInt()), formulaMap(proofDIS.readInt()))
      else if (psType == rightNot) RightNot(sequentFromProofDIS(), proofDIS.readInt(), formulaMap(proofDIS.readInt()))
      else if (psType == rightForall) RightForall(sequentFromProofDIS(), proofDIS.readInt(), formulaMap(proofDIS.readInt()), labelFromInputStream(proofDIS).asInstanceOf[VariableLabel])
      else if (psType == rightExists)
        RightExists(
          sequentFromProofDIS(),
          proofDIS.readInt(),
          formulaMap(proofDIS.readInt()),
          labelFromInputStream(proofDIS).asInstanceOf[VariableLabel],
          termMap(proofDIS.readInt())
        )
      else if (psType == rightExistsOne) RightExistsOne(sequentFromProofDIS(), proofDIS.readInt(), formulaMap(proofDIS.readInt()), labelFromInputStream(proofDIS).asInstanceOf[VariableLabel])
      else if (psType == weakening) Weakening(sequentFromProofDIS(), proofDIS.readInt())
      else if (psType == leftRefl) LeftRefl(sequentFromProofDIS(), proofDIS.readInt(), formulaMap(proofDIS.readInt()))
      else if (psType == rightRefl) RightRefl(sequentFromProofDIS(), formulaMap(proofDIS.readInt()))
      else if (psType == leftSubstEq)
        LeftSubstEq(
          sequentFromProofDIS(),
          proofDIS.readInt(),
          (1 to proofDIS.readShort()).map(_ => (termMap(proofDIS.readInt()), termMap(proofDIS.readInt()))).toList,
          ltfFromProofDIS()
        )
      else if (psType == rightSubstEq)
        RightSubstEq(
          sequentFromProofDIS(),
          proofDIS.readInt(),
          (1 to proofDIS.readShort()).map(_ => (termMap(proofDIS.readInt()), termMap(proofDIS.readInt()))).toList,
          ltfFromProofDIS()
        )
      else if (psType == leftSubstIff)
        LeftSubstIff(
          sequentFromProofDIS(),
          proofDIS.readInt(),
          (1 to proofDIS.readShort()).map(_ => (formulaMap(proofDIS.readInt()), formulaMap(proofDIS.readInt()))).toList,
          lffFromProofDIS()
        )
      else if (psType == rightSubstIff)
        RightSubstIff(
          sequentFromProofDIS(),
          proofDIS.readInt(),
          (1 to proofDIS.readShort()).map(_ => (formulaMap(proofDIS.readInt()), formulaMap(proofDIS.readInt()))).toList,
          lffFromProofDIS()
        )
      else if (psType == instSchema)
        InstSchema(
          sequentFromProofDIS(),
          proofDIS.readInt(),
          (1 to proofDIS.readShort()).map(_ => (labelFromInputStream(proofDIS).asInstanceOf[SchematicConnectorLabel], lffFromProofDIS())).toMap,
          (1 to proofDIS.readShort()).map(_ => (labelFromInputStream(proofDIS).asInstanceOf[SchematicAtomicLabel], ltfFromProofDIS())).toMap,
          (1 to proofDIS.readShort()).map(_ => (labelFromInputStream(proofDIS).asInstanceOf[SchematicTermLabel], lttFromProofDIS())).toMap
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
          case (obj, theory.FunctionDefinition(label, out, expression, withSorry)) => "f" + obj + "$" + label.id.name + "_" + label.id.no + "_" + label.arity
          case (obj, theory.PredicateDefinition(label, expression)) => "p" + obj + "$" + label.id.name + "_" + label.id.no + "_" + label.arity
        }
        (name, minimizeProofOnce(proof), justNames)
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
          case 'f' =>
            name.split("_") match
              case Array(name, no, arity) => theory.getDefinition(ConstantFunctionLabel(Identifier(name, no.toInt), arity.toInt)).get
          case 'p' =>
            name.split("_") match
              case Array(name, no, arity) => theory.getDefinition(ConstantAtomicLabel(Identifier(name, no.toInt), arity.toInt)).get
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
