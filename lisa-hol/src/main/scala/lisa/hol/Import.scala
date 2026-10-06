package lisa.hol

import lisa.SetTheoryLibrary
import lisa.hol.ExtendedHOLSteps._INST_TYPE_RENAME
import lisa.hol.HOLHelperTheorems._
import lisa.hol.HOLSteps.HOLProofType
import lisa.hol.VarsAndFunctions._
import lisa.hol.basics.Exists.{hexists, hexistsCorrect}
import lisa.hol.basics.TypeDefs
import lisa.automation.Substitution.{Apply => Substitute}
import lisa.hol.extractor.ExtractorException
import lisa.hol.extractor.TheoremRef
import lisa.hol.extractor._
import lisa.hol.{core => h}
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.utils.collection.VecSet
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.OutputManager
import lisa.utils.prooflib.SimpleDeducedSteps.Discharge
import lisa.utils.unification.UnificationUtils.RewriteContext
import lisa.utils.unification.UnificationUtils.matchExpr

import scala.collection.mutable

object Import extends lisa.HOL:
  val lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

  // lib.withCache()

  type Justification = lib.JUSTIFICATION

  sealed trait ImportException extends Exception
  case class InvalidAbstractionException(term: h.Term) extends Exception(s"Invalid abstraction term: $term. Expected a variable.") with ImportException
  case class InvalidDefinitionException(name: String, term: h.Term) extends Exception(s"Invalid definition for constant $name: $term. Expected a term of the form 'name = body'.") with ImportException
  case class MalformedConstantInstance(name: String, tpe: Expr[Ind]) extends Exception(s"Malformed instance of constant $name with type $tpe. No matching definition found.") with ImportException
  case class MalformedTypeDefinition(index: Long, term: h.Term) extends Exception(s"Malformed type definition at $index: $term") with ImportException
  case class MalformedNonEmptinessThm(index: Long, thm: Justification) extends Exception(s"Malformed non-emptiness theorem at $index: $thm") with ImportException
  case class UnknownAxiom(expr: Expr[Ind]) extends Exception(s"Unknown axiom: $expr. No matching HOL Light axiom found.") with ImportException

  // logging

  object Logging:
    enum LoggingMode:
      case Silent, Debug

    def debug(using mode: LoggingMode)(msg: => String): Unit =
      mode match
        case LoggingMode.Silent => ()
        case LoggingMode.Debug =>
          msg.linesIterator.foreach(line => println(s"[DEBUG] $line"))

    def info(using mode: LoggingMode)(msg: String): Unit =
      msg.linesIterator.foreach(line => println(s"[INFO] $line"))

    def debugAssert(using mode: LoggingMode)(cond: => Boolean, msg: => String): Unit =
      ifDebug:
        if !cond then throw new AssertionError(s"Debug assertion failed: $msg")

    def ifDebug(using mode: LoggingMode)(body: => Unit): Unit =
      if mode == LoggingMode.Debug then body

  import Logging.*
  private var currentLoggingMode: LoggingMode = LoggingMode.Silent
  given LoggingMode = currentLoggingMode

  /** Bound successful conversion results; recheck capacity after recursive work. */
  private[hol] final class ConversionCache[A, B](capacity: Int):
    require(capacity >= 0)
    private val entries = mutable.HashMap.empty[A, B]
    def clear(): Unit = entries.clear()
    def apply(key: A)(compute: => B): B =
      if capacity == 0 then compute
      else entries.get(key) match
        case Some(value) => value
        case None =>
          val value = compute
          if entries.size >= capacity then entries.clear()
          entries.put(key, value)
          value

  object Transformers:
    private val types = new ConversionCache[h.Type, Expr[Ind]](sys.props.get("lisa.hol.typeCache").fold(0)(_.toInt))
    private val constants = new ConversionCache[h.Constant, Expr[Ind]](sys.props.get("lisa.hol.constantCache").fold(0)(_.toInt))

    /** Release converted objects at named-theorem boundaries and import exit. */
    private[hol] def resetConversionCache(): Unit =
      types.clear()
      constants.clear()

    private val typeNumbers = mutable.Map.empty[K.Expression, Int]
    private var nextTypeNumber = 1

    private def typeNumber(tpe: Expr[Ind]): Int =
      typeNumbers.getOrElseUpdate(tpe.underlying, {
        val result = nextTypeNumber
        nextTypeNumber += 1
        result
      })

    def mkTypedVar(name: String, tpe: Expr[Ind]): TypedVariable =
      // Encode erased HOL types without relying on collision-free hashes.
      TypedVariable(K.Identifier(name, typeNumber(tpe)), tpe)

    extension (typ: h.Type)
      def toLisaType: Expr[Ind] = types(typ) {
        typ match
          case h.BoolType => 𝔹
          case h.FunType(in, out) => in.toLisaType ->: out.toLisaType
          case h.TypeVariable(name) => TypeVariable(K.Identifier(name))
          case h.TypeApplication(name, args) =>
            if name == "fun" && args.length == 2 then
              // since function types are defined as a shorthand for Pi types, we
              // handle them separately instead of defining fun as a
              // HOLConstantType layer over Pi
              args(0).toLisaType ->: args(1).toLisaType
            else
              val typeConstant = Constants.lookupTypeConstant(name)
              val typeArgs = args.map(_.toLisaType)

              // expr should be fully applied
              // this is runtime checked wherever used
              (typeConstant #@@ typeArgs).asInstanceOf[Expr[Ind]]
      }

    extension (v: h.Variable)
      def toLisaVar: TypedVariable =
        val tpe = v.tpe.toLisaType
        mkTypedVar(v.name, tpe)

    extension (v: h.TypeVariable)
      def toLisaVar: TypeVariable =
        val name = K.Identifier(v.name)
        TypeVariable(name)

    extension (term: h.Term)
      def toLisaTerm: Expr[Ind] =
        term match
          case v @ h.Variable(_, _) => v.toLisaVar
          case c @ h.Constant(name, tpe) => constants(c)(Constants.lookupTypedConstant(name, tpe.toLisaType))
          case h.Combination(left, right) => left.toLisaTerm @@ right.toLisaTerm
          case h.Abstraction(absVar, inner) =>
            fun(absVar.toLisaVar, inner.toLisaTerm)

    extension (seq: h.HOLSequent)
      def toLisaSequent: Sequent =
        val assumptions = seq.hyps.map(_.toLisaTerm)
        val conclusion = seq.concl.toLisaTerm
        HOLSequent(assumptions.to(VecSet), conclusion)

  import Transformers.{*, given}

  object Axioms:
    val infinityAx = HOLBasics.infinityAx
    val etaAx = HOLBasics.etaAx
    val selectAx = HOLBasics.selectAx

    private val axioms = Seq(
      infinityAx,
      etaAx,
      selectAx
    )

    def fromHOL(expr: Expr[Ind]): Justification =
      axioms
        .find: ax =>
          ax.statement match
            case HOLSequent(_, _, axiom) if isSame(expr, axiom) => true
            case _ => false
        .getOrElse(throw UnknownAxiom(expr))

  /**
   * A destructed sequent corresponding to a constant definition.
   */
  case class Definition(
      name: String,
      /**
       * The full type of the constant, with free variables
       */
      abstractType: Expr[Ind],
      /**
       * The free type variables of the constant
       *
       * Order unimportant for HOL Light during generation, but our definitions
       * order them.
       */
      typeArgs: Seq[Variable[Ind]],
      /**
       * The actual defining term
       */
      body: Expr[Ind]
  )

  private object Definition:
    def unapply(term: h.Term): Option[Definition] =
      term match
        case h.Combination(h.Combination(h.Constant("=", _), h.Constant(name, tt)), body) =>
          // the constant is not defined at this point, so we have to be careful
          // to not attempt to look it up in the current context
          val abstractType = tt.toLisaType
          Some(
            Definition(
              name = name,
              abstractType = abstractType,
              typeArgs = abstractType.freeVars.collect { case v: Variable[?] => v.asInstanceOf[Variable[Ind]] }.toSeq,
              body = body.toLisaTerm
            )
          )
        case _ => None

  private object NameHandling:
    private val illegalChars = "}]`)[{(,;?_."
    private val replacementMap: collection.MapView[Char, Char] =
      illegalChars.zipWithIndex.toMap.view.mapValues(c => (9312 + c).toChar)

    def sanitize(name: String): String =
      name.map(c => replacementMap.getOrElse(c, c))

  import NameHandling.sanitize

  private object Constants:

    case class DefinedConstant(cst: Constant[?], typeVars: Seq[Variable[Ind]], typ: Expr[Ind], definition: Justification)

    enum TypeDefKind:
      case NoRecord
      case Abs(absThm: Justification)
      case Rep(repThm: Justification)
      case Both(absThm: Justification, repThm: Justification)

      def addAbs(absThm: Justification): TypeDefKind =
        this match
          case NoRecord => TypeDefKind.Abs(absThm)
          case TypeDefKind.Abs(_) => this
          case Rep(repThm) => Both(absThm, repThm)
          case Both(existingAbsThm, repThm) => this

      def addRep(repThm: Justification): TypeDefKind =
        this match
          case NoRecord => Rep(repThm)
          case TypeDefKind.Abs(absThm) => Both(absThm, repThm)
          case Rep(_) => this
          case Both(absThm, existingRepThm) => this

      def abs: Option[Justification] =
        this match
          case TypeDefKind.Abs(absThm) => Some(absThm)
          case Both(absThm, _) => Some(absThm)
          case _ => Option.empty

      def rep: Option[Justification] =
        this match
          case Rep(repThm) => Some(repThm)
          case Both(_, repThm) => Some(repThm)
          case _ => Option.empty

    case class DefinedType(cst: HOLConstantType, typeVars: Seq[Variable[Ind]], nonEmptiness: Justification, defns: TypeDefKind = TypeDefKind.NoRecord):
      def addAbs(absThm: Justification): DefinedType =
        copy(defns = defns.addAbs(absThm))

      def addRep(repThm: Justification): DefinedType =
        copy(defns = defns.addRep(repThm))

    private val typeDefinitions: mutable.Map[String, DefinedType] = mutable.Map.empty
    private val constantDefinitions: mutable.Map[String, DefinedConstant] = mutable.Map.empty

    def lookupTypeConstant(name: String): HOLConstantType =
      typeDefinitions.get(name) match
        case None => throw new NoSuchElementException(s"Type constant $name is not defined.")
        case Some(cst) => cst.cst

    def lookupTypeDefinition(name: String): DefinedType =
      typeDefinitions.get(name) match
        case None => throw new NoSuchElementException(s"Type constant $name is not defined.")
        case Some(cst) => cst

    def isDefinedType(name: String): Boolean = typeDefinitions.contains(name)
    def isDefinedConstant(name: String): Boolean = constantDefinitions.contains(name)

    def lookupTypedConstant(name: String, tpe: Expr[Ind]): Expr[Ind] =
      // translate type to lisa expr, then match against the known
      // abstract type of the constant, instantiating the definition
      // appropriately
      constantDefinitions.get(name) match
        case None => throw new NoSuchElementException(s"Constant $name is not defined.")
        case Some(DefinedConstant(cst, typeVars, cstType, definition)) =>
          // find the instantiation of type variables

          debug(s"[Constant Lookup] Looking up constant $name with type $tpe. Known abstract type is $cstType with type variables {${typeVars.mkString(", ")}}.")

          matchExpr(using RewriteContext.empty)(cstType, tpe) match
            case None => throw MalformedConstantInstance(name, tpe)
            case Some(subst) =>
              debug(s"[Constant Lookup] Match successful with substitution: ${subst.asSubstPair.mkString(", ")}")
              val typeArgs = typeVars.map(v => subst(v).getOrElse(v))
              val appliedCst = (cst #@@ typeArgs).asInstanceOf[Expr[Ind]]

              appliedCst

    /**
     * Lookup the definition of a constant, given its name. The returned
     * definition will possibly have free type variables, which are returned as
     * the first element.
     */
    def lookupConstantDefinition(name: String): (Seq[Variable[Ind]], Justification) =
      // translate type to lisa expr, then match against the known
      // abstract type of the constant, instantiating the definition
      // appropriately
      constantDefinitions.get(name) match
        case None => throw new NoSuchElementException(s"Constant $name is not defined.")
        case Some(DefinedConstant(cst, typeVars, cstType, definition)) =>
          (typeVars, definition)

    def register(name: String, cst: Constant[?], typeVars: Seq[Variable[Ind]], cstType: Expr[Ind], definition: Justification): Unit =
      if constantDefinitions.contains(name) then throw new IllegalArgumentException(s"Constant $name is already defined.")
      else constantDefinitions(name) = DefinedConstant(cst, typeVars, cstType, definition)

    def registerType(name: String, cst: HOLConstantType, typeVars: Seq[Variable[Ind]], definition: Justification, defns: TypeDefKind = TypeDefKind.NoRecord): Unit =
      if typeDefinitions.contains(name) then throw new IllegalArgumentException(s"Type constant $name is already defined.")
      else typeDefinitions(name) = DefinedType(cst, typeVars, definition, defns)

  end Constants

  /**
   * Contain and register constants and types defined and justified in the
   * preamble before the import. This includes, for example, `ind`, `bool`,
   * equality, and some basic FOL operators.
   */
  private object Initialization:
    import Constants.{DefinedConstant, DefinedType, register, registerType}
    import HOLBasics.*

    val definedConstants = Map(
      // equality
      // the definition of equality should, strictly, never be used directly
      "=" -> DefinedConstant(holeq, Seq(A), holeq.typ.outTyp, holeqBetaReduced),
      // binders
      "!" -> DefinedConstant(hforall, Seq(A), hforall.typ.outTyp, hforall.holDefinition),
      "?" -> DefinedConstant(hexists, Seq(A), hexists.typ.outTyp, hexists.holDefinition),
      "@" -> DefinedConstant(hselect, Seq(A), hselect.typ.outTyp, hselect.holDefinition),
      // boolean ops
      "/\\" -> DefinedConstant(hand, Seq.empty, hand.typ.outTyp, hand.holDefinition),
      "~" -> DefinedConstant(hnot, Seq.empty, hnot.typ.outTyp, hnot.holDefinition),
      "==>" -> DefinedConstant(himp, Seq.empty, himp.typ.outTyp, himp.holDefinition),
      "T" -> DefinedConstant(holT, Seq.empty, holT.typ, holT.holDefinition),
      "F" -> DefinedConstant(holF, Seq.empty, holF.typ, holF.holDefinition),
      // complex defs
      "ONE_ONE" -> DefinedConstant(hOneOne, Seq(A, B), hOneOne.typ.outTyp, hOneOne.holDefinition),
      "ONTO" -> DefinedConstant(hOnto, Seq(A, B), hOnto.typ.outTyp, hOnto.holDefinition)
    )

    val definedTypes = Map(
      "ind" -> DefinedType(ind, Seq.empty, ind.nonEmptyThm),
      "bool" -> DefinedType(𝔹, Seq.empty, 𝔹.nonEmptyThm)
    )

    def initializeConstants(): Unit =
      definedConstants.foreach:
        case (name, DefinedConstant(cst, typeVars, cstType, definition)) =>
          register(name, cst, typeVars, cstType, definition)

    def initializeTypes(): Unit =
      definedTypes.foreach:
        case (name, DefinedType(cst, typeVars, definition, _)) =>
          registerType(name, cst, typeVars, definition)

    def initializeDefinitions(): Unit =
      initializeConstants()
      initializeTypes()

  private lazy val initializedDefinitions: Unit = Initialization.initializeDefinitions()

  // Intermediate proofs are checked normally; retain output only for named theorems.
  private val stepOutput = new OutputManager:
    val stringWriter: java.io.Writer = java.io.Writer.nullWriter()
    def finishOutput(exception: Exception): Nothing = throw exception

  // The old builder requires an owning theorem. This checked tautology supplies
  // that owner only; no step imports it or relies on its declared goal.
  private lazy val stepOwner = Theorem(using stepOutput, sourcecode.FullName("Import.stepOwner"))(⊤):
    have(⊤) by Restate

  /** Share checked SC theorems, never proof-local fact indices, across trace steps. */
  private[hol] final class StepStore(using extractor: ExtractorContext, mode: LoggingMode = LoggingMode.Silent):
    private val steps = mutable.HashMap.empty[Long, Justification]
    private var definitionsThrough = -1L

    initializedDefinitions

    /** Count the stored steps, including unnamed premises and definitions. */
    def size: Int = steps.size

    /** Retrieve a checked step and construct any missing dependencies. */
    def apply(index: Long): Justification =
      steps.get(index) match
        case Some(step) => step
        case None =>
          defineThrough(index)
          steps.getOrElseUpdate(index, reconstruct(index, extractor.getProof(index)))

    /** Require an earlier premise and retrieve its checked proof. */
    def premise(index: Long, target: Long): Justification =
      require(target < index, s"Step $index references non-earlier premise $target")
      apply(target)

    private def reconstruct(index: Long, step: h.ProofStep): Justification =
      given StepStore = this
      step match
        case axiom: h.AXIOM => reconstructAxiom(axiom)
        case definition: h.DEFINITION => reconstructConstantDefinition(definition)
        case definition: h.TYPE_DEFINITION => reconstructTypeDefinition(index, definition)
        case _ =>
          val proof = new lib.BaseProof(stepOwner.asInstanceOf[lib.THMFromProof])
          given proof.type = proof
          val result = reconstructStep(using extractor, proof, this)(index, step)
          val cleaned = have(HOLSteps.Clean.all(result))
          ifDebug:
            val goal = withCTX(extractor.getStatement(index).toLisaSequent)
            val checked = Weakening(cleaned)(goal)
            if !checked.isValid then
              throw new IllegalArgumentException(s"Step $index (${step.getClass.getSimpleName}) proves ${cleaned.statement}, expected $goal")
          val scProof = proof.toSCProof
          lib.THM.fromSCProof(using stepOutput)(
            cleaned.statement, s"Import.step$index", lib.InternalStatement,
            () => scProof, proof.justifications.map(_.innerJustification)
          )

    private def defineThrough(index: Long): Unit =
      if index > definitionsThrough then
        extractor.getDefinitionsBetween(definitionsThrough, index).foreach: (definitionIndex, definition) =>
          definitionsThrough = definitionIndex
          definition match
            case _: h.DEFINITION =>
              try steps.getOrElseUpdate(definitionIndex, reconstruct(definitionIndex, definition))
              catch case exception: Exception => debug(s"Skipping unusable definition at $definitionIndex: ${exception.getMessage}")
            case _: h.TYPE_DEFINITION =>
              steps.getOrElseUpdate(definitionIndex, reconstruct(definitionIndex, definition))
            case _ => ()
        definitionsThrough = index

    /** Check the exported statement and register its public theorem name. */
    def theorem(ref: TheoremRef): Justification =
      HOLProofType.resetCache()
      Transformers.resetConversionCache()
      val result = apply(ref.id)
      val goal = extractor.getStatement(ref.id).toLisaSequent
      HOLTheorem(using summon[OutputManager], sourcecode.FullName(s"Import.${sanitize(ref.name)}"), summon[sourcecode.Line], summon[sourcecode.File])(goal):
        val cleaned = have(HOLSteps.Clean.all(result))
        have(thesis) by Weakening(cleaned)

  private def reconstructAxiom(using extractor: ExtractorContext)(step: h.AXIOM): Justification =
    val h.AXIOM(term) = step
    val lisaTerm = term.toLisaTerm
    Axioms.fromHOL(lisaTerm)

  private object TDefExtractors:
    import h.{Constant => Cst, Variable => Var, Combination => Comb, FunType, Eq}

    /**
     * Pattern match a type definition abstraction theorem of the form:
     *   |- abs (rep a) = a
     *
     * where `abs: rty -> aty`, and `rep: aty -> rty`.
     *
     * `aty` is the type being defined from a subset of `rty`.
     *
     * returning `(aty, rty, abs, rep, a)`
     */
    object AbsTh:
      def unapply(conclusion: h.Term): Option[(h.Type, h.Type, h.Constant, h.Constant, h.Variable)] =
        conclusion match
          case Eq(
            Comb(abs @ Cst(_, FunType(rty, aty)), Comb(rep @ Cst(_, _), a @ Var(_, _))),
            a2
          ) if a == a2 =>
            Some((aty, rty, abs, rep, a))
          case _ => None

    /**
     * Pattern match a type definition representation theorem of the form:
     *   |- P r <=> rep (abs r) = r
     *
     * where `abs: rty -> aty`, and `rep: aty -> rty`.
     *
     * `aty` is the type being defined from a subset of `rty`.
     *
     * returning `(aty, rty, abs, rep, P, r)`
     */
    object RepTh:
      def unapply(conclusion: h.Term): Option[(h.Type, h.Type, h.Constant, h.Constant, h.Term, h.Variable)] =
        import h.{Constant => Cst, Variable => Var, FunType, Eq}
        conclusion match
          case Eq(
            Comb(p, r @ Var(_, _)),
            Eq(
              Comb(rep @ Cst(_, FunType(aty, rty)), Comb(abs @ Cst(_, _), r2)),
              r3
            )
          ) if r == r2 && r == r3 =>
            Some((aty, rty, abs, rep, p, r))
          case _ => None

    /**
     * Pattern match a theorem as a non-emptiness theorem for a predicate of the form:
     *   Γ |- P t = One
     *
     * where `P` is a predicate and `t` is a term.
     */
    object NonEmptyThm:
      def unapply(thm: Justification): Option[(Expr[Ind], Expr[Ind])] =
        val right = thm.statement.right
        if right.size != 1 then
          None
        else
          right.head match
            case equality(applied, `One`) =>
              applied match
                case p * t => Some((p, t))
                case _ => None
            case _ => None

  /** Choose an unused short name in the SC theory's shared symbol namespace. */
  private def definitionName(name: String, sort: K.Sort): String =
    val base = sanitize(name)
    Iterator.from(0)
      .map(index => if index == 0 then base else s"$base$$$index")
      .find(candidate => theory.isAvailable(K.Constant(K.Identifier(candidate), sort)))
      .get

  private def defineHOLConstant(
      name: String,
      abstractType: Expr[Ind],
      typeArgs: Seq[Variable[Ind]],
      body: Expr[Ind],
      bodyTyping: Option[Justification] = None
  ): HOLPolymorphicConstant[?] =
    // define the underlying constant
    val definitionTerm = typeArgs.foldRight(body: Expr[?])((variable, inner) => λ(variable, inner))
    val baseName = summon[sourcecode.Name].value.stripSuffix(".")
    val cst = DEF(using summon[OutputManager], sourcecode.FullName(s"$baseName.${definitionName(name, definitionTerm.sort)}"), summon[sourcecode.Line], summon[sourcecode.File])(definitionTerm)(using unsafeSortEvidence(definitionTerm.sort))
    val appliedCst = (cst #@@ typeArgs).asInstanceOf[Expr[Ind]]

    val nonEmptyAssumptions = typeArgs.map(nonEmpty)
    val conjunction = nonEmptyAssumptions.reduceOption(_ /\ _).getOrElse(⊤)

    // prove the constant's HOL typing
    val fullTyping = typeArgs.foldRight(conjunction ==> (appliedCst :: abstractType))((v, result) => ∀(v, result))
    val typeJustification = Theorem(using summon[OutputManager], sourcecode.FullName(s"Import.${sanitize(name)}.typing"))(fullTyping): proof ?=>
      val typedBody = bodyTyping match
        case Some(typing) => have(HOLSteps.Clean.all(typing))
        case None =>
          val openTypes = HOLSteps.Clean.collectInstantiatingConstants(definitionTerm)
          val (types, justifications) = openTypes.unzip
          val assumptions = nonEmptyAssumptions ++ types.map(tpe => ∃(x, x ∈ tpe))
          val inferred = have(assumptions |- body :: abstractType) by Typecheck.prove
          have(Discharge(justifications*)(inferred))

      // Discharging a type constructor can expose its argument non-emptiness.
      val cleanedTyping = have(HOLSteps.Clean.all(typedBody))
      val withDefinition = have(cleanedTyping.statement.left |- appliedCst :: abstractType) by Substitute(cst.definition)(cleanedTyping)
      val implication = have(conjunction ==> (appliedCst :: abstractType)) by Restate.from(withDefinition)
      typeArgs.foldRight(implication: proof.Fact): (variable, premise) =>
        have(∀(variable, premise.statement.right.head)) by RightForall(premise)

    // Lift the definition to an HOL constant
    val functionalType = FunctionalClass(typeArgs.map(_ => None).toList, typeArgs.toList, abstractType)
    val holCst = HOLPolymorphicConstant(cst.id, functionalType, typeJustification)(using unsafeSortEvidence(cst.sort))
    Constants.register(name, holCst, typeArgs, abstractType, holCst.holDefinition)
    holCst

  private def reconstructTypeDefinition(using extractor: ExtractorContext, store: StepStore)(index: Long, step: h.TYPE_DEFINITION): Justification =
    val h.TYPE_DEFINITION(_, term, just) = step
    require(just < index, s"Step $index references non-earlier premise $just")

    import TDefExtractors.*

    // Decode which of the paired abstraction and representation theorems this step requests.
    val (aty, rty, abs, rep, isAbs) =
      term match
        case AbsTh(aty, rty, abs, rep, _) =>
          (aty, rty, abs, rep, true)

        case RepTh(aty, rty, abs, rep, _, _) =>
          (aty, rty, abs, rep, false)

        case _ =>
          throw MalformedTypeDefinition(index, term)

    val (theType, absThm, repThm) =
      if Constants.isDefinedType(aty.name) then
        // The first occurrence constructs both theorems; its partner only performs this lookup.
        val definition = Constants.lookupTypeDefinition(aty.name)
        definition.defns match
          case Constants.TypeDefKind.Both(absThm, repThm) => (definition.cst, absThm, repThm)
          case _ => throw new IllegalStateException(s"Type constant ${aty.name} has incomplete defining theorems.")
      else
        // Recover the HOL witness and the predicate whose inhabited subset defines the type.
        val nonEmptinessThm = store.premise(index, just)
        val (p, t) = nonEmptinessThm match
          case NonEmptyThm(p, t) => (p, t)
          case _ => throw MalformedNonEmptinessThm(index, nonEmptinessThm)

        // Translate the type parameters and formulate their local non-emptiness context.
        val typeArgs = aty match
          case h.TypeApplication(_, arguments) => arguments.map:
              case variable: h.TypeVariable => variable.toLisaVar
              case _ => throw MalformedTypeDefinition(index, term)
          case h.TypeVariable(_) => throw MalformedTypeDefinition(index, term)
        val representationType = rty.toLisaType
        val substitutions = Seq(TypeDefs.A := representationType, TypeDefs.p := p)
        val existsP = hexists(representationType) * p
        val localNonEmpty = typeArgs.map(nonEmpty)

        // Give each generated lemma a stable, type-specific theory identity.
        def typeTheorem(suffix: String)(statement: Sequent)(body: Proof ?=> Unit): THM =
          HOLTheorem(using summon[OutputManager], sourcecode.FullName(s"Import.type.${sanitize(aty.name)}.$suffix"), summon[sourcecode.Line], summon[sourcecode.File])(statement)(body)

        // Type the predicate and convert its concrete witness into HOL existence.
        val predicateTyping = typeTheorem("predicateTyping")(localNonEmpty |- p :: (representationType ->: 𝔹)):
          val inferred = have(HOLSteps.Clean.all(HOLProofType(p)))
          have(localNonEmpty |- p :: (representationType ->: 𝔹)) by Weakening(inferred)

        val existsPThm = typeTheorem("existsP")(localNonEmpty |- existsP):
          val witnessVariable = mkTypedVar("w", representationType)
          val witnessBody = (witnessVariable ∈ representationType) /\ ((p * witnessVariable) === One)
          val witnessTyping = have(HOLProofType(t))
          have(((t ∈ representationType) /\ ((p * t) === One)) ++<< nonEmptinessThm.statement ++<< witnessTyping.statement) by
            RightAnd(witnessTyping, nonEmptinessThm)
          val witness = thenHave(lastStep.statement.left |- ∃(witnessVariable, witnessBody)) by RightExists.withParameters(witnessBody, witnessVariable, t)
          val correctness = have(HOLSteps.Clean.all(hexistsCorrect.of(
            lisa.hol.basics.Exists.A := representationType,
            lisa.hol.basics.Exists.P := p,
            lisa.hol.basics.Exists.x := witnessVariable
          )))
          val implication = have((correctness.statement.left + ∃(witnessVariable, witnessBody)) |- existsP) by Weakening(correctness)
          have((witness.statement.left ++ correctness.statement.left) |- existsP) by
            Cut.withParameters(∃(witnessVariable, witnessBody))(witness, implication)
          val discharged = have(Discharge(predicateTyping)(lastStep))
          have(localNonEmpty |- existsP) by Weakening(discharged)

        // Define the new carrier as the subset selected by the predicate.
        val typeBody = TypeDefs.B.substitute(substitutions*).asInstanceOf[Expr[Ind]]
        val definitionTerm = typeArgs.foldRight(typeBody: Expr[?])((variable, inner) => λ(variable, inner))
        val baseName = summon[sourcecode.Name].value.stripSuffix(".")
        val rawType = DEF(using summon[OutputManager], sourcecode.FullName(s"$baseName.${definitionName(aty.name, definitionTerm.sort)}"), summon[sourcecode.Line], summon[sourcecode.File])(definitionTerm)(using unsafeSortEvidence(definitionTerm.sort))
        val rawDefinedType = (rawType #@@ typeArgs).asInstanceOf[Expr[Ind]]

        // Establish non-emptiness before wrapping the raw constant as an HOL type.
        val typeNonEmpty = typeTheorem("nonEmpty")(localNonEmpty |- ∃(TypeDefs.z, TypeDefs.z ∈ rawDefinedType)):
          val subsetNonEmpty = have(HOLSteps.Clean.all(TypeDefs.typeNonEmpty.of(substitutions*)))
          val withWitness = have((subsetNonEmpty.statement -<< (existsP === One)) ++<< existsPThm.statement) by
            Cut.withParameters(existsP === One)(existsPThm, subsetNonEmpty)
          val rewritten = have(withWitness.statement.left |- ∃(TypeDefs.z, TypeDefs.z ∈ rawDefinedType)) by Substitute(rawType.definition)(withWitness)
          val discharged = have(Discharge(predicateTyping)(rewritten))
          have(localNonEmpty |- ∃(TypeDefs.z, TypeDefs.z ∈ rawDefinedType)) by Weakening(discharged)

        val theType = HOLPolymorphicType(rawType.id, typeArgs, typeNonEmpty)(using unsafeSortEvidence(rawType.sort)).asInstanceOf[HOLConstantType]
        val definedType = (theType #@@ typeArgs).asInstanceOf[Expr[Ind]]

        // Specialize the canonical subset abstraction and representation functions.
        val absBody = TypeDefs.absFun.substitute(substitutions*).asInstanceOf[Expr[Ind]]
        val repBody = TypeDefs.repFun.substitute(substitutions*).asInstanceOf[Expr[Ind]]

        val absTyping = typeTheorem("absTyping")(localNonEmpty |- absBody :: (representationType ->: definedType)):
          val generic = have(HOLSteps.Clean.all(TypeDefs.absTyping.of(substitutions*)))
          val local = have((generic.statement -<< (existsP === One)) ++<< existsPThm.statement) by
            Cut.withParameters(existsP === One)(existsPThm, generic)
          val rewritten = have(local.statement.left |- absBody :: (representationType ->: definedType)) by Substitute(rawType.definition)(local)
          val discharged = have(Discharge(predicateTyping)(rewritten))
          have(localNonEmpty |- absBody :: (representationType ->: definedType)) by Weakening(discharged)

        val repTyping = typeTheorem("repTyping")(localNonEmpty |- repBody :: (definedType ->: representationType)):
          val generic = have(HOLSteps.Clean.all(TypeDefs.repTyping.of(substitutions*)))
          val rewritten = have(generic.statement.left |- repBody :: (definedType ->: representationType)) by Substitute(rawType.definition)(generic)
          val discharged = have(Discharge(predicateTyping)(rewritten))
          have(localNonEmpty |- repBody :: (definedType ->: representationType)) by Weakening(discharged)

        // Define and register both functions from their already-proved typings.
        val absConstant = defineHOLConstant(abs.name, representationType ->: definedType, typeArgs, absBody, Some(absTyping))
        val repConstant = defineHOLConstant(rep.name, definedType ->: representationType, typeArgs, repBody, Some(repTyping))
        val appliedAbs = (absConstant #@@ typeArgs).asInstanceOf[Expr[Ind]]
        val appliedRep = (repConstant #@@ typeArgs).asInstanceOf[Expr[Ind]]

        // State and prove both characteristic theorems while their shared data is available.
        val absVariable = mkTypedVar("a", definedType)
        val repVariable = mkTypedVar("r", representationType)
        val absStatement = appliedAbs * (appliedRep * absVariable) =:= absVariable
        val repStatement = p * repVariable =:= (appliedRep * (appliedAbs * repVariable) =:= repVariable)
        val definitions = Seq(absConstant.definition, repConstant.definition, rawType.definition)

        val absThm = typeTheorem("abs")(localNonEmpty |- absStatement):
          val generic = have(HOLSteps.Clean.all(TypeDefs.absThm.of((substitutions :+ (TypeDefs.y := absVariable))*)))
          have((thesis.left ++ predicateTyping.statement.right) |- absStatement) by Substitute(definitions*)(generic)
          val cleaned = have(HOLSteps.Clean.all(lastStep))
          val discharged = have(Discharge(predicateTyping)(cleaned))
          have(thesis) by Weakening(discharged)

        val repThm = typeTheorem("rep")(localNonEmpty |- repStatement):
          val generic = have(HOLSteps.Clean.all(TypeDefs.repThm.of((substitutions :+ (TypeDefs.x := repVariable))*)))
          val withWitness = have((generic.statement -<< (existsP === One)) ++<< existsPThm.statement) by
            Cut.withParameters(existsP === One)(existsPThm, generic)
          have((thesis.left ++ predicateTyping.statement.right) |- repStatement) by Substitute(definitions*)(withWitness)
          val cleaned = have(HOLSteps.Clean.all(lastStep))
          val discharged = have(Discharge(predicateTyping)(cleaned))
          have(thesis) by Weakening(discharged)

        // Publish the type only after its complete defining pair has been checked.
        Constants.registerType(aty.name, theType, typeArgs, typeNonEmpty, Constants.TypeDefKind.Both(absThm, repThm))
        (theType, absThm, repThm)

    // Return the member of the pair represented by this trace step.
    if isAbs then absThm else repThm

  private def reconstructConstantDefinition(using extractor: ExtractorContext)(step: h.DEFINITION): Justification =
    val h.DEFINITION(name, term) = step
    // the definition is of the form `name = body`,
    // where `name` is not yet defined at this point;
    // possibly with free type variables, e.g. v[A]

    // we extract just the body and use it to define the constant
    term match
      case Definition(name, abstractType, typeArgs, body) =>
        if Constants.isDefinedConstant(name) then
          debug(s"Constant $name already defined. Retrieving existing definition.")
          Constants.lookupConstantDefinition(name)._2
        else
          debug(s"Defining new constant $name with abstract type $abstractType and body $body. Type variables are {${typeArgs.mkString(", ")}}.")
          defineHOLConstant(name, abstractType, typeArgs, body).holDefinition
      case _ =>
        throw InvalidDefinitionException(name, term)

  /** Reconstruct a trace step using checked premises from the shared store. */
  private def reconstructStep(using extractor: ExtractorContext, ctx: lib.Proof, store: StepStore)(index: Long, proofStep: h.ProofStep): ctx.Fact =
    debug(s"Reconstructing step $index: ${proofStep.getClass.getSimpleName}")
    def resolveFact(target: Long): ctx.Fact = store.premise(index, target)

    val result = {
      proofStep match
        case h.REFL(term) =>
          have(ExtendedHOLSteps._REFL(term.toLisaTerm))
        case h.TRANS(left, right) =>
          val leftFact = resolveFact(left)
          val rightFact = resolveFact(right)
          have(ExtendedHOLSteps._TRANS(leftFact, rightFact))
        case h.MK_COMB(left, right) =>
          val leftFact = resolveFact(left)
          val rightFact = resolveFact(right)
          have(ExtendedHOLSteps._MK_COMB(leftFact, rightFact))
        case h.ABS(absVar, from) =>
          val lisaVar = absVar.toLisaVar
          val fromFact = resolveFact(from)
          have(ExtendedHOLSteps._ABS(lisaVar)(fromFact))
        case h.BETA(term) =>
          have(ExtendedHOLSteps._BETA(term.toLisaTerm))
        case h.ASSUME(term) =>
          have(ExtendedHOLSteps._ASSUME(term.toLisaTerm))
        case h.EQ_MP(left, right) =>
          val leftFact = resolveFact(left)
          val rightFact = resolveFact(right)
          have(ExtendedHOLSteps._EQ_MP(leftFact, rightFact))
        case h.DEDUCT_ANTISYM_RULE(left, right) =>
          val leftFact = resolveFact(left)
          val rightFact = resolveFact(right)
          have(ExtendedHOLSteps._DEDUCT_ANTISYM_RULE(leftFact, rightFact))
        case h.INST(from, inst) =>
          val fromFact = resolveFact(from)
          val lisaInst = inst.map { case (v, t) => (v.toLisaVar, t.toLisaTerm) }
          INST(lisaInst.toSeq, fromFact)
        case h.INST_TYPE(from, inst) =>
          val fromFact = resolveFact(from)
          val lisaInst = inst.map { case (v, t) => (v.toLisaVar, t.toLisaType) }
          have(ExtendedHOLSteps._INST_TYPE_RENAME(lisaInst.toSeq, fromFact))
        case h.AXIOM(term) => Axioms.fromHOL(term.toLisaTerm)
        case s @ h.DEFINITION(name, term) => reconstructConstantDefinition(s)
        case s @ h.TYPE_DEFINITION(name, term, just) => reconstructTypeDefinition(index, s)
    }

    result

  end reconstructStep

  object ExportConfig:
    val header = """
    |//> using scala "3.7.2"
    |//> using options -experimental
    |//> using dep "ch.epfl.lara::lisa::0.9.3,url=https://github.com/epfl-lara/lisa/releases/download/0.9.3/lisa_3-0.9.3.jar"
    |
    |object ImportedHOLTheorems extends lisa.HOL {
    |
    """.stripMargin

    val footer = """
    |}
    """.stripMargin

    import java.nio.file.{Files, Path, FileAlreadyExistsException}
    import java.io.{IOException, Writer}

    class OpenExport(inner: java.io.Writer, header: String, footer: String) extends java.io.Writer {

      def close(): Unit =
        inner.write(footer)
        inner.close()

      export inner.{flush, write}

      /////////////////////////////
      // on init
      this.write(header)
    }

    val dummyWriter = new Writer {
      def close() = ()
      def flush() = ()
      def write(cs: Array[Char], x: Int, y: Int) = ()
    }


    def initialize(fileName: String, overwrite: Boolean): OpenExport =
      val path = Path.of(fileName)
      if !overwrite && Files.exists(path) then
        throw new FileAlreadyExistsException(s"Output file already exists: $fileName")
      else
        if !Files.isWritable(path) then
          throw new IOException(s"Output file is not writable: $fileName")
        else
          val writer = Files.newBufferedWriter(path)
          OpenExport(writer, header, footer)


  /** Import a range of names and reconstruct their shared dependencies. */
  def importFromPrefix(prefix: String, limit: Int, outputPath: Option[String] = None, overwrite: Boolean = false, startAt: Int = 0): Unit =
    require(limit > 0, s"Cannot read $limit theorems. Expected positive theorem limit.")
    require(startAt >= 0, s"Cannot start at negative theorem index $startAt.")
    val (extractor, names) = JSONParser.initializeFromPrefix(prefix)

    val startTime = System.currentTimeMillis()
    def time() = (System.currentTimeMillis() - startTime) / 1000d
    def printProgress(count: Int, steps: Int) =
      val elapsed = time()
      val progressString = f"Extracted $count theorems so far in $elapsed%.2f seconds."
      val usedSteps = f"Used $steps proof steps from HOL Light."
      val memoryLeft = Runtime.getRuntime.freeMemory() / 1e6
      val memoryString = f"Memory left: $memoryLeft%.2f MB"
      println(f"\r[INFO] $progressString $usedSteps $memoryString")

    try
      val exporter = outputPath match
        case Some(path) => ExportConfig.initialize(path, overwrite)
        case None => ExportConfig.dummyWriter
      try
        val store = new StepStore(using extractor, currentLoggingMode)
        var count = 0
        names.drop(startAt).take(limit).foreach: ref =>
          debug(s"Importing theorem ${ref.name} with id ${ref.id}")
          store.theorem(ref)
          count += 1
          printProgress(count, store.size)
        println(s"[INFO] Successfully imported $count theorems with ${store.size} steps in ${time()}s.")
      finally exporter.close()
    finally
      extractor.close()
      HOLProofType.resetCache()
      Transformers.resetConversionCache()

  @main
  def importMain(prefix: String, logMode: String, theoremCount: Int, output: Boolean, outputFile: String, overwrite: Boolean) =
    val pid = ProcessHandle.current().pid()
    println(s"Running on PID: $pid")

    currentLoggingMode = logMode.toLowerCase match
      case "--silent" => LoggingMode.Silent
      case "--debug" => LoggingMode.Debug
      case _ => throw new IllegalArgumentException(s"Invalid logging mode: $logMode. Expected '--silent' or '--debug'.")

    importFromPrefix(prefix, theoremCount, if output then Some(outputFile) else None, overwrite)

end Import
