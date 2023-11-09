package lisa.utils

import lisa.utils.K.*
import scala.collection.mutable.{Map => MutMap}
import lisa.utils.ProofsShrink.*
object Serialization {

    type Line = Int


    def proofToStringSeq(proof: SCProof, thmName:String, justifications: List[String]): Seq[String] = {

        var part1: List[String] = List()
        var part2: List[String] = List()
        var part3: List[String] = List()

        val termMap = MutMap[Long, Line]()
        val formulaMap = MutMap[Long, Line]()

        
        def termLabelToString(label: TermLabel): String = 
            label match 
                case l: ConstantFunctionLabel =>  "cfl_" + l.id.name + "_" + l.id.no + "_" + l.arity
                case l: SchematicFunctionLabel => "sfl_" + l.id.name + "_" + l.id.no + "_" + l.arity
                case l: VariableLabel =>          "vl_" + l.id.name + "_" + l.id.no

        def formulaLabelToString(label:FormulaLabel): String = 
            label match 
                case l: ConstantPredicateLabel =>  "cpl_" + l.id.name + "_" + l.id.no + "_" + l.arity
                case l: SchematicPredicateLabel => "spl_" + l.id.name + "_" + l.id.no + "_" + l.arity
                case l: ConstantConnectorLabel =>  "ccl_" + l.id.name + "_" + l.id.no + "_" + l.arity
                case l: SchematicConnectorLabel => "scl_" + l.id.name + "_" + l.id.no + "_" + l.arity
                case l: VariableFormulaLabel =>  "vfl_" + l.id.name + "_" + l.id.no
                case l: BinderLabel => "bl_" + l.id.name + "_"+ l.id.no

        def lineOfTerm(term: Term): Line = 
            termMap.get(term.uniqueNumber) match 
                case Some(line) => line
                case None =>
                    val nextLine = termLabelToString(term.label) + " ," + term.args.map(t => lineOfTerm(t)).mkString(",")
                    val line = part1.length
                    part1 = nextLine :: part1
                    termMap(term.uniqueNumber) = line
                    line

        def lineOfFormula(formula: Formula): Line = 
            formulaMap.get(formula.uniqueNumber) match 
                case Some(line) => line
                case None =>
                    val nextLine = formula match
                        case PredicateFormula(label, args) =>
                            formulaLabelToString(label) + " ," + args.map(t => lineOfTerm(t)).mkString(",")
                        case ConnectorFormula(label, args) =>
                            formulaLabelToString(label) + " ," + args.map(t => lineOfFormula(t)).mkString(",")
                        case BinderFormula(label, bound, inner) =>
                            formulaLabelToString(label) + " " + termLabelToString(bound) + " " + lineOfFormula(inner)
                    val line = part1.length
                    part1 = nextLine :: part1
                    formulaMap(formula.uniqueNumber) = line
                    line

        def sequentToString(sequent: Sequent): String = 
            sequent.left.map(f => lineOfFormula(f)).mkString(",") + "|-" + ","+sequent.right.map(f => lineOfFormula(f)).mkString(",")

        def lttToString(ltt: LambdaTermTerm): String = 
            ltt.vars.map(termLabelToString).mkString(",")+"?" + lineOfTerm(ltt.body)

        def ltfToString(ltf: LambdaTermFormula): String = 
            ltf.vars.map(termLabelToString).mkString(",")+"?" + lineOfFormula(ltf.body)

        def lffToString(lff: LambdaFormulaFormula): String = 
            lff.vars.map(formulaLabelToString).mkString(",")+"?" + lineOfFormula(lff.body)

        
        def proofStepToString(ps: SCProofStep): String = {
            ps match {
                case Restate(bot, t1) => s"Restate ${sequentToString(bot)} $t1"
                case RestateTrue(bot) => s"RestateTrue ${sequentToString(bot)}"
                case Hypothesis(bot, phi) => s"Hypothesis ${sequentToString(bot)} ${lineOfFormula(phi)}"
                case Cut(bot, t1, t2, phi) => s"Cut ${sequentToString(bot)} $t1 $t2 ${lineOfFormula(phi)}"
                case LeftAnd(bot, t1, phi, psi) => s"LeftAnd ${sequentToString(bot)} $t1 ${lineOfFormula(phi)} ${lineOfFormula(psi)}"
                case LeftOr(bot, t, disjuncts) => s"LeftOr ${sequentToString(bot)} ,${t.mkString(",")} ${disjuncts.map(f => lineOfFormula(f)).mkString(",")}"
                case LeftImplies(bot, t1, t2, phi, psi) => s"LeftImplies ${sequentToString(bot)} $t1 $t2 ${lineOfFormula(phi)} ${lineOfFormula(psi)}"
                case LeftIff(bot, t1, phi, psi) => s"LeftIff ${sequentToString(bot)} $t1 ${lineOfFormula(phi)} ${lineOfFormula(psi)}"
                case LeftNot(bot, t1, phi) => s"LeftNot ${sequentToString(bot)} $t1 ${lineOfFormula(phi)}"
                case LeftForall(bot, t1, phi, x, t) => s"LeftForall ${sequentToString(bot)} $t1 ${lineOfFormula(phi)} ${termLabelToString(x)} ${lineOfTerm(t)}"
                case LeftExists(bot, t1, phi, x) => s"LeftExists ${sequentToString(bot)} $t1 ${lineOfFormula(phi)} ${termLabelToString(x)}"
                case LeftExistsOne(bot, t1, phi, x) => s"LeftExistsOne ${sequentToString(bot)} $t1 ${lineOfFormula(phi)} ${termLabelToString(x)}"
                case RightAnd(bot, t, conjuncts) => s"RightAnd ${sequentToString(bot)} ,${t.mkString(",")} ,${conjuncts.map(f => lineOfFormula(f)).mkString(",")}"
                case RightOr(bot, t1, phi, psi) => s"RightOr ${sequentToString(bot)} $t1 ${lineOfFormula(phi)} ${lineOfFormula(psi)}"
                case RightImplies(bot, t1, phi, psi) => s"RightImplies ${sequentToString(bot)} $t1 ${lineOfFormula(phi)} ${lineOfFormula(psi)}"
                case RightIff(bot, t1, t2, phi, psi) => s"RightIff ${sequentToString(bot)} $t1 $t2 ${lineOfFormula(phi)} ${lineOfFormula(psi)}"
                case RightNot(bot, t1, phi) => s"RightNot ${sequentToString(bot)} $t1 ${lineOfFormula(phi)}"
                case RightForall(bot, t1, phi, x) => s"RightForall ${sequentToString(bot)} $t1 ${lineOfFormula(phi)} ${termLabelToString(x)}"
                case RightExists(bot, t1, phi, x, t) => s"RightExists ${sequentToString(bot)} $t1 ${lineOfFormula(phi)} ${termLabelToString(x)} ${lineOfTerm(t)}"
                case RightExistsOne(bot, t1, phi, x) => s"RightExistsOne ${sequentToString(bot)} $t1 ${lineOfFormula(phi)} ${termLabelToString(x)}"
                case Weakening(bot, t1) => s"Weakening ${sequentToString(bot)} $t1"
                case LeftRefl(bot, t1, fa) => s"LeftRefl ${sequentToString(bot)} $t1 ${lineOfFormula(fa)}"
                case RightRefl(bot, fa) => s"RightRefl ${sequentToString(bot)} ${lineOfFormula(fa)}"
                case LeftSubstEq(bot, t1, equals, lambdaPhi) => 
                    s"LeftSubstEq ${sequentToString(bot)} $t1 ,${equals.map(t => s"${lineOfTerm(t._1)};${lineOfTerm(t._2)}").mkString(",")} ${ltfToString(lambdaPhi)}"
                case RightSubstEq(bot, t1, equals, lambdaPhi) =>
                        s"RightSubstEq ${sequentToString(bot)} $t1 ,${equals.map(t => s"${lineOfTerm(t._1)};${lineOfTerm(t._2)}").mkString(",")} ${ltfToString(lambdaPhi)}"
                case LeftSubstIff(bot, t1, equals, lambdaPhi) => 
                    s"LeftSubstIff ${sequentToString(bot)} $t1 ,${equals.map(t => s"${lineOfFormula(t._1)};${lineOfFormula(t._2)}").mkString(",")} ${lffToString(lambdaPhi)}"
                case RightSubstIff(bot, t1, equals, lambdaPhi) => 
                    s"RightSubstIff ${sequentToString(bot)} $t1 ,${equals.map(t => s"${lineOfFormula(t._1)};${lineOfFormula(t._2)}").mkString(",")} ${lffToString(lambdaPhi)}"
                case InstSchema(bot, t1, mCon, mPred, mTerm) => 
                    val sConn = mCon.map(t => s"${formulaLabelToString(t._1)};${lffToString(t._2)}").mkString(",")
                    val sPred = mPred.map(t => s"${formulaLabelToString(t._1)};${ltfToString(t._2)}").mkString(",")
                    val sTerm = mTerm.map(t => s"${termLabelToString(t._1)};${lttToString(t._2)}").mkString(",")
                    s"InstSchema ${sequentToString(bot)} $t1 ,$sConn ,$sPred ,$sTerm"
                case SCSubproof(sp, premises) => throw new Exception("Cannot support subproofs, flatten the proof first.")
                case Sorry(bot) => s"Sorry ${sequentToString(bot)}"
            }
        }

        proof.imports.foreach(sequent => part2 = sequentToString(sequent) :: part2)

        proof.steps.foreach(ps => part3 = proofStepToString(ps) :: part3)

        // {} separates theorems
        // () separates imports from steps
        (part1.reverse ++ ("{}" :: thmName :: justifications) ++ ("{}" :: part2) ++ ("{}" :: part3)).toSeq
    }

    


    /**
      * This functions reverses the effect of proofToStringSeq
      *
      * @param lines The lines of the "file" where the proof is stored
      */
    def SeqStringToProof(lines: Seq[String]): (SCProof, String, List[String]) = {


        var part1: List[String] = List()
        var part2: List[String] = List()
        var part3: List[String] = List()


        val termMap = MutMap[Line, Term]()
        val formulaMap = MutMap[Line, Formula]()

        def labelFromString(label: String): Label = {
            val parts = label.split("_")
            val id = Identifier(parts(1), parts(2).toInt)
            val arity = if parts.length > 3 then parts(3).toInt else 0
            parts(0) match {
                case "cfl" => ConstantFunctionLabel(id, arity)
                case "sfl" => SchematicFunctionLabel(id, arity)
                case "vl" => VariableLabel(id)
                case "cpl" => ConstantPredicateLabel(id, arity)
                case "spl" => SchematicPredicateLabel(id, arity)
                case "ccl" => parts(1) match
                    case And.id.name => And
                    case Or.id.name => Or
                    case Implies.id.name => Implies
                    case Iff.id.name => Iff
                    case Neg.id.name => Neg
                    
                case "scl" => SchematicConnectorLabel(id, arity)
                case "vfl" => VariableFormulaLabel(id)
                case "bl" => parts(1) match
                    case Forall.id.name => Forall
                    case Exists.id.name => Exists
                    case ExistsOne.id.name => ExistsOne
                

                
            }
        }


        val iterator = lines.iterator
        var lineNo = 0
        var line = iterator.next()
        while line != "{}" do
            //Formula or Term from line
            val parts = line.split(" ")
            val label = labelFromString(parts(0))
            label match
                case l: TermLabel =>
                    val args = parts(1).split(",").filterNot(_.size==0).map(s => termMap(s.toInt)).toSeq
                    val term = Term(l, args)
                    termMap(lineNo) = term
                case l: FormulaLabel =>
                    
                    val formula = label match
                        case l: PredicateLabel => 
                            val args = parts(1).split(",").filterNot(_.size==0).map(s => termMap(s.toInt)).toSeq
                            PredicateFormula(l, args)
                        case l: ConnectorLabel => 
                            val args = parts(1).split(",").filterNot(_.size==0).map(s => formulaMap(s.toInt)).toSeq
                            ConnectorFormula(l, args)
                        case l: BinderLabel => 
                            BinderFormula(l, labelFromString(parts(1)).asInstanceOf[VariableLabel], formulaMap(parts(2).toInt))
                    formulaMap(lineNo) = formula
            lineNo = lineNo +1
            line = iterator.next()

        //Terms and Formulas finished, deal with the proof now.

        // case "Restate" => Restate(sequentFromString(parts(1)), parts(2).toInt)

        def lttFromString(s:String): LambdaTermTerm = 
            val parts = s.split("\\?")
            val vars = parts(0).split(",").filterNot(_.size==0).map(s => labelFromString(s).asInstanceOf[VariableLabel]).toSeq
            val body = termMap(parts(1).toInt)
            LambdaTermTerm(vars, body)

        def ltfFromString(s:String): LambdaTermFormula = 
            val parts = s.split("\\?")
            val vars = parts(0).split(",").filterNot(_.size==0).map(s => labelFromString(s).asInstanceOf[VariableLabel]).toSeq
            val body = formulaMap(parts(1).toInt)
            LambdaTermFormula(vars, body)

        def lffFromString(s:String): LambdaFormulaFormula =
            val parts = s.split("\\?")
            val vars = parts(0).split(",").filterNot(_.size==0).map(s => labelFromString(s).asInstanceOf[VariableFormulaLabel]).toSeq
            val body = formulaMap(parts(1).toInt)
            LambdaFormulaFormula(vars, body)

            
        def sequentFromString(s:String): Sequent =
            val parts = s.split("\\|-")
            val left =  parts(0).split(",").filterNot(_.size==0).map(s => formulaMap(s.toInt)).toSet
            val right = parts(1).split(",").filterNot(_.size==0).map(s => formulaMap(s.toInt)).toSet
            Sequent(left, right)

        def proofStepFromString(s:String): SCProofStep = {
            val parts = s.split(" ")
            val ps = parts(0) match 
                case "Restate" => Restate(sequentFromString(parts(1)), parts(2).toInt)
                case "RestateTrue" => RestateTrue(sequentFromString(parts(1)))
                case "Hypothesis" => Hypothesis(sequentFromString(parts(1)), formulaMap(parts(2).toInt))
                case "Cut" => Cut(sequentFromString(parts(1)), parts(2).toInt, parts(3).toInt, formulaMap(parts(4).toInt))
                case "LeftAnd" => LeftAnd(sequentFromString(parts(1)), parts(2).toInt, formulaMap(parts(3).toInt), formulaMap(parts(4).toInt))
                case "LeftOr" => LeftOr(sequentFromString(parts(1)), parts(2).split(",").filterNot(_.size==0).map(s => s.toInt).toSeq, parts(3).split(",").filterNot(_.size==0).map(s => formulaMap(s.toInt)).toSeq)
                case "LeftImplies" => LeftImplies(sequentFromString(parts(1)), parts(2).toInt, parts(3).toInt, formulaMap(parts(4).toInt), formulaMap(parts(5).toInt))
                case "LeftIff" => LeftIff(sequentFromString(parts(1)), parts(2).toInt, formulaMap(parts(3).toInt), formulaMap(parts(4).toInt))
                case "LeftNot" => LeftNot(sequentFromString(parts(1)), parts(2).toInt, formulaMap(parts(3).toInt))
                case "LeftForall" => LeftForall(sequentFromString(parts(1)), parts(2).toInt, formulaMap(parts(3).toInt), labelFromString(parts(4)).asInstanceOf[VariableLabel], termMap(parts(5).toInt))
                case "LeftExists" => LeftExists(sequentFromString(parts(1)), parts(2).toInt, formulaMap(parts(3).toInt), labelFromString(parts(4)).asInstanceOf[VariableLabel])
                case "LeftExistsOne" => LeftExistsOne(sequentFromString(parts(1)), parts(2).toInt, formulaMap(parts(3).toInt), labelFromString(parts(4)).asInstanceOf[VariableLabel])
                case "RightAnd" => RightAnd(sequentFromString(parts(1)), parts(2).split(",").filterNot(_.size==0).map(s => s.toInt).toSeq, parts(3).split(",").filterNot(_.size==0).map(s => formulaMap(s.toInt)).toSeq)
                case "RightOr" => RightOr(sequentFromString(parts(1)), parts(2).toInt, formulaMap(parts(3).toInt), formulaMap(parts(4).toInt))
                case "RightImplies" => RightImplies(sequentFromString(parts(1)), parts(2).toInt, formulaMap(parts(3).toInt), formulaMap(parts(4).toInt))
                case "RightIff" => RightIff(sequentFromString(parts(1)), parts(2).toInt, parts(3).toInt, formulaMap(parts(4).toInt), formulaMap(parts(5).toInt))
                case "RightNot" => RightNot(sequentFromString(parts(1)), parts(2).toInt, formulaMap(parts(3).toInt))
                case "RightForall" => RightForall(sequentFromString(parts(1)), parts(2).toInt, formulaMap(parts(3).toInt), labelFromString(parts(4)).asInstanceOf[VariableLabel])
                case "RightExists" => RightExists(sequentFromString(parts(1)), parts(2).toInt, formulaMap(parts(3).toInt), labelFromString(parts(4)).asInstanceOf[VariableLabel], termMap(parts(5).toInt))
                case "RightExistsOne" => RightExistsOne(sequentFromString(parts(1)), parts(2).toInt, formulaMap(parts(3).toInt), labelFromString(parts(4)).asInstanceOf[VariableLabel])
                case "Weakening" => Weakening(sequentFromString(parts(1)), parts(2).toInt)
                case "LeftRefl" => LeftRefl(sequentFromString(parts(1)), parts(2).toInt, formulaMap(parts(3).toInt))
                case "RightRefl" => RightRefl(sequentFromString(parts(1)), formulaMap(parts(2).toInt))
                case "LeftSubstEq" => 
                    LeftSubstEq(sequentFromString(parts(1)), parts(2).toInt, parts(3).split(",").filterNot(_.size==0).map(s => {val ts = s.split(";"); (termMap(ts(0).toInt), termMap(ts(1).toInt))}).toList, ltfFromString(parts(4)))
                case "RightSubstEq" => 
                    RightSubstEq(sequentFromString(
                        parts(1)),
                        parts(2).toInt,
                        parts(3).split(",").filterNot(_.size==0).map(s => {val ts = s.split(";"); (termMap(ts(0).toInt), termMap(ts(1).toInt))}).toList,
                        ltfFromString(parts(4)))
                case "LeftSubstIff" => 
                    LeftSubstIff(sequentFromString(parts(1)), parts(2).toInt, parts(3).split(",").filterNot(_.size==0).map(s => {val ts = s.split(";"); (formulaMap(ts(0).toInt), formulaMap(ts(1).toInt))}).toList, lffFromString(parts(4)))
                case "RightSubstIff" => 
                    RightSubstIff(sequentFromString(parts(1)), parts(2).toInt, parts(3).split(",").filterNot(_.size==0).map(s => {val ts = s.split(";"); (formulaMap(ts(0).toInt), formulaMap(ts(1).toInt))}).toList, lffFromString(parts(4)))
                case "InstSchema" =>
                    InstSchema(sequentFromString(parts(1)), parts(2).toInt, 
                        parts(3).split(",").filterNot(_.size==0).map(s => {val ts = s.split(";"); (labelFromString(ts(0)).asInstanceOf[SchematicConnectorLabel], lffFromString(ts(1)))}).toMap,
                        parts(4).split(",").filterNot(_.size==0).map(s => {val ts = s.split(";"); (labelFromString(ts(0)).asInstanceOf[SchematicVarOrPredLabel], ltfFromString(ts(1)))}).toMap,
                        parts(5).split(",").filterNot(_.size==0).map(s => {val ts = s.split(";"); (labelFromString(ts(0)).asInstanceOf[SchematicTermLabel], lttFromString(ts(1)))}).toMap)
                case "SCSubproof" => throw new Exception("Cannot support subproofs, flatten the proof first.")
                case "Sorry" => Sorry(sequentFromString(parts(1)))
            ps
        }
        
        var imports: List[Sequent] = List()
        var justifications: List[String] = List()
        var steps:List[SCProofStep] = List()

        
        val name = iterator.next()
        line = iterator.next()
        while line != "{}" do
            justifications = line :: justifications
            line = iterator.next()

        line = iterator.next()
        while line != "{}" do
            imports = sequentFromString(line) :: imports
            line = iterator.next()
        
        
        while iterator.hasNext do
            line = iterator.next()
            steps = proofStepFromString(line) :: steps



        (new SCProof(steps.toIndexedSeq, imports.toIndexedSeq), name, justifications)

    }

    /**
      * Flatten and simplify the proof with `minimizeProof`, then convert it to a list of string
      *
      * @param proof
      * @param thmName
      * @return
      */
    def flatProofToString(proof: SCProof, thmName:String, justifications: List[String]) = proofToStringSeq(minimizeProofOnce(proof), thmName, justifications)


    def main(args: Array[String]): Unit = {
        import lisa.utils.KernelHelpers.{_, given}

        val x = VariableLabel("x")
        val y = VariableLabel("y")
        val z = VariableLabel("z")
        val a = PredicateFormula(ConstantPredicateLabel("A", 0), Seq())
        val b = PredicateFormula(ConstantPredicateLabel("B", 0), Seq())
        val fp = ConstantPredicateLabel("F", 1)
        val sT = VariableLabel("t")
        val phi = formulaVariable()
        val psi = formulaVariable()
        val PierceLaw = SCProof(
            Hypothesis(phi |- phi, phi),
            Weakening(phi |- (phi, psi), 0),
            RightImplies(() |- (phi, phi ==> psi), 1, phi, psi),
            LeftImplies((phi ==> psi) ==> phi |- phi, 2, 0, (phi ==> psi), phi),
            RightImplies(() |- ((phi ==> psi) ==> phi) ==> phi, 3, (phi ==> psi) ==> phi, phi)
            )

        val t0 = Hypothesis(fp(x) |- fp(x), fp(x))
        val t1 = RightSubstEq(Set(fp(x), x === y) |- fp(y), 0, List((x, y)), LambdaTermFormula(Seq(sT), fp(sT)))
        val SubstTest = new SCProof(IndexedSeq(t0, t1))


        test(PierceLaw, "PierceLaw")
        test(SubstTest, "SubstTest")
    }

    def test(proof:SCProof, name:String): Unit = {
        println("\n\nTesting " + name)
        checkProof(minimizeProofOnce(proof), (s => ()))
        val lines = proofToStringSeq(proof, "PierceLaw", Nil)
        lines.foreach(println)
        println("Now: Decode")
        val proof2 = SeqStringToProof(lines)
        println(proof2._2)
        checkProof(proof2._1, println)
    }


}
