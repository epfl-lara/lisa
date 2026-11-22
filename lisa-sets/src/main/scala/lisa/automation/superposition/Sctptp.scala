package lisa.automation.superposition

import lisa.automation.{ProofSyntax as K}
import sctptp.{FOL as F, SequentCalculus as SC}
import sctptp.LVL2.{LVL2Proof, LVL2ProofStep as Step, RightSubstIffForall, StrictLVL2ProofStep}

import scala.collection.mutable
import scala.util.control.NonFatal

/** Export the strict first-order fragment of Lisa's sequent calculus. Certificate imports become SC-TPTP axioms. */
object Sctptp:
  /** Flatten nested certificates and translate each inference. An error names the import or linear step that failed.
    * The only accepted RestateTrue statements are the two nullary logical rules, ⊢ ⊤ and ⊥ ⊢.
    * A single pointwise predicate rewrite on the right uses the Level 2 rightSubstIffForall rule.
    * Weakening uses structural inclusion of the original Lisa sequents on both sides.
    */
  def fromKernel(certificate: K.ProofCertificate, name: String = "proof"): Either[String, SC.SCProof[?]] =
    try Right(new Translation().run(certificate.toLinearProof, name))
    catch case NonFatal(e) => Left(e.getMessage)

  private def fail(message: String): Nothing = throw new IllegalArgumentException(message)

  private def at[A](where: String)(f: => A): A =
    try f
    catch case NonFatal(e) => fail(s"$where: ${e.getMessage}")

  // The SC-TPTP dialect uses upper words for schematics and lower words for rigid symbols.
  // Encode exceptional names and counters separately so e.g. sk$1 and a literal name sk_1 cannot alias.
  private def identifier(id: K.Identifier, prefix: String): F.Identifier =
    val plain = id.name.matches("[a-zA-Z][a-zA-Z0-9]*") && !id.name.startsWith("lisa")
    val base =
      if plain then
        if prefix.isEmpty && id.name.head.isUpper then "lisaC" + id.name else prefix + id.name
      else
        val encoded = id.name.iterator.map(c => f"${c.toInt}%04x").mkString
        s"${prefix}lisaU$encoded"
    F.Identifier(if id.no == 0 then base else s"${base}_n${id.no}", 0)

  private def symbol(e: K.Expression): F.Identifier = e match
    case c: K.Constant => identifier(c.id, "")
    case v: K.Variable =>
      val prefix = if v.sort == K.Ind then "X" else if v.sort.isPredicate then s"P${v.sort.depth}x" else s"F${v.sort.depth}x"
      identifier(v.id, prefix)
    case _ => fail(s"Expected a first-order symbol, found $e")

  private def variable(v: K.Variable): F.VariableSymbol =
    require(v.sort == K.Ind, s"Expected an individual variable, found $v of sort ${v.sort}")
    F.VariableSymbol(symbol(v))

  private def application(e: K.Expression): (K.Expression, Seq[K.Expression]) = e match
    case K.Multiapp(head, args) => (head, args)
    case _ => (e, Nil)

  // InstSchema can leave an applied parameter lambda in its conclusion, e.g. (λx. A(x) ∧ B(x))(t).
  private def applyTemplate(lambda: K.Lambda, args: Seq[K.Expression]): K.Expression =
    require(args.nonEmpty && (lambda.sort.isPredicate || lambda.sort.isFunctional), s"Expected a first-order template application, found $lambda")
    val K.Lambda(x, body) = lambda
    term(args.head) // Validate even a discarded argument.
    args.tail.foldLeft(K.substituteVariables(body, Map(x -> args.head)))(_(_))

  private def binder(predicate: K.Expression): (F.VariableSymbol, F.Formula) = predicate match
    case K.Lambda(x, body) => variable(x) -> formula(body)
    case _ =>
      // The kernel can eta-contract λx.p(x) to p.
      val x = fresh(predicate.freeVariables, K.Ind)
      variable(x) -> formula(predicate(x))

  private def fresh(avoid: Iterable[K.Variable], sort: K.Sort): K.Variable =
    K.Variable(K.freshId(avoid.map(_.id), K.Identifier("scTmp")), sort)

  private def term(e: K.Expression): F.Term = e match
    case K.Application(K.epsilon, p) =>
      val (x, body) = binder(p)
      F.EpsilonTerm(x, body)
    case v: K.Variable if v.sort == K.Ind => F.Variable(variable(v))
    case _ =>
      val (head, args) = application(e)
      head match
        case lambda: K.Lambda => term(applyTemplate(lambda, args))
        case _ =>
          require(head.sort.isFunctional && head.sort.depth == args.size, s"Expected a first-order term, found $e")
          F.FunctionTerm(F.FunctionSymbol(symbol(head), args.size), args.map(term))

  private val connectives = Map(K.neg -> F.Neg, K.and -> F.And, K.or -> F.Or, K.implies -> F.Implies, K.iff -> F.Iff)

  private def formula(e: K.Expression): F.Formula =
    require(e.sort == K.Prop, s"Expected a first-order formula, found $e of sort ${e.sort}")
    val (head, args) = application(e)
    head match
      case lambda: K.Lambda => formula(applyTemplate(lambda, args))
      case K.top => F.AtomicFormula(F.top, Nil)
      case K.bot => F.AtomicFormula(F.bot, Nil)
      case K.equality => F.AtomicFormula(F.equality, args.map(term))
      case K.forall | K.exists =>
        require(args.size == 1, s"Expected a quantified formula, found $e")
        val (x, body) = binder(args.head)
        F.BinderFormula(if head == K.forall then F.Forall else F.Exists, x, body)
      case c: K.Constant if connectives.contains(c) => F.ConnectorFormula(connectives(c), args.map(formula))
      case _ =>
        require(head.sort.isPredicate && head.sort.depth == args.size, s"Expected a first-order formula, found $e")
        F.AtomicFormula(F.AtomicSymbol(symbol(head), args.size), args.map(term))

  private def sequent(s: K.Sequent): SC.Sequent =
    def side(fs: Set[K.Expression]) = fs.iterator.map(formula).toVector.sortBy(_.toString)
    SC.Sequent(side(s.left), side(s.right))

  private def index(side: Seq[F.Formula], f: F.Formula): Int =
    val i = side.indexWhere(F.isSame(_, f))
    if i < 0 then fail(s"Missing principal formula $f")
    i

  private final class Translation:
    private val steps = mutable.ArrayBuffer.empty[Step]
    private val sequents = mutable.Map.empty[String, SC.Sequent]
    private val refs = mutable.Map.empty[Int, Step]
    // Local rewrites and their identity proofs can be removed when a cut supplies the comparison directly.
    private val localComparisons = mutable.Map.empty[String, SC.Hyp]
    private val inlined = mutable.Set.empty[String]
    private def next = s"s${steps.size}"

    private def record[S <: Step](step: S): S =
      steps += step
      sequents(step.name) = step.bot
      step

    private def emit[S <: Step](step: S): S =
      step.checkCorrectness(sequents) match
        case SC.StepCheckOK => record(step)
        case SC.StepCheckError(msg) => fail(s"${step.getClass.getSimpleName}: $msg")
        case SC.StepCheckUnknown => fail(s"Unchecked rule ${step.getClass.getSimpleName}")

    def run(proof: K.LinearProof, name: String): SC.SCProof[?] =
      require(proof.steps.nonEmpty, "Empty proof certificate")
      for (s, i) <- proof.imports.iterator.zipWithIndex do
        refs(-i - 1) = at(s"import $i")(emit(SC.Axiom(s"input$i", sequent(s))))
      def source(p: Int) = if p < 0 then proof.imports(-p - 1) else proof.steps(p).statement
      for (step, i) <- proof.steps.iterator.zipWithIndex do
        refs(i) = at(s"step $i (${step.getClass.getSimpleName})")(translate(step, source))
      // If the final certificate step aliases an earlier line, the intervening suffix is unused.
      val last = refs(proof.steps.length - 1)
      val needed = mutable.Set(last.name)
      val kept = steps.take(steps.lastIndexOf(last) + 1).reverseIterator.filter { step =>
        val keep = !inlined(step.name) || needed(step.name)
        if keep then needed ++= step.premises
        keep
      }.toVector.reverse
      if kept.exists(_.isInstanceOf[StrictLVL2ProofStep]) then LVL2Proof(kept, name)
      else SC.LVL1Proof(kept.collect { case s: SC.LVL1ProofStep => s }, name)

    private def translate(step: K.ProofStep, source: Int => K.Sequent): Step =
      lazy val bot = sequent(step.statement)
      def left(f: K.Expression) = index(bot.left, formula(f))
      def right(f: K.Expression) = index(bot.right, formula(f))
      def ref(p: Int) = refs(p).name
      step match
        case K.RestateTrue(s) if s.left.isEmpty && s.right == Set(K.top) => emit(SC.RightTrue(next, bot, 0))
        case K.RestateTrue(s) if s.left == Set(K.bot) && s.right.isEmpty => emit(SC.LeftFalse(next, bot))
        case _: K.Restate | _: K.RestateTrue => fail("Restatement is outside the strict sequent calculus")
        case _: K.Axiom => emit(SC.Axiom(next, bot))
        case K.Hypothesis(_, a) => emit(SC.Hyp(next, bot, left(a)))
        case K.Cut(_, p, q, a) =>
          val pivot = formula(a)
          val cut = SC.Cut(next, bot, index(refs(p).bot.right, pivot), ref(p), ref(q))
          refs(q) match
            case local: RightSubstIffForall if localComparisons.get(local.name).exists(h => F.isSame(h.bot.right.head, pivot)) =>
              val fused = local.copy(name = next, bot = bot, i = cut.i, comparison = ref(p))
              if cut.checkCorrectness(sequents) == SC.StepCheckOK && fused.checkCorrectness(sequents) == SC.StepCheckOK then
                inlined ++= Seq(local.name, local.comparison)
                record(fused)
              else emit(cut)
            case _ => emit(cut)
        case K.Weakening(s, p) =>
          val from = source(p)
          require(from.left.subsetOf(s.left) && from.right.subsetOf(s.right), "Weakening must preserve each existing formula on its original side")
          weaken(refs(p), bot)
        case K.LeftAnd(_, p, a, b) =>
          val premise = withOperands(refs(p), a, b, onLeft = true)
          emit(SC.LeftAnd(next, bot, left(K.and(a)(b)), premise.name))
        case K.LeftOr(_, ps, as) => branches(ps, as, bot, onLeft = true)
        case K.LeftImplies(_, p, q, a, b) => emit(SC.LeftImplies(next, bot, left(K.implies(a)(b)), ref(p), ref(q)))
        case K.LeftIff(_, p, a, b) => emit(SC.LeftIff(next, bot, left(K.iff(a)(b)), ref(p)))
        case K.LeftNot(_, p, a) => emit(SC.LeftNot(next, bot, left(K.neg(a)), ref(p)))
        case K.LeftForall(_, p, a, x, t) => emit(SC.LeftForall(next, bot, left(K.forall(K.Lambda(x, a))), term(t), ref(p)))
        case K.LeftExists(_, p, a, x) => emit(SC.LeftExists(next, bot, left(K.exists(K.Lambda(x, a))), variable(x), ref(p)))
        case K.RightAnd(_, ps, as) => branches(ps, as, bot, onLeft = false)
        case K.RightOr(_, p, a, b) =>
          val premise = withOperands(refs(p), a, b, onLeft = false)
          emit(SC.RightOr(next, bot, right(K.or(a)(b)), premise.name))
        case K.RightImplies(_, p, a, b) => emit(SC.RightImplies(next, bot, right(K.implies(a)(b)), ref(p)))
        case K.RightIff(_, p, q, a, b) => emit(SC.RightIff(next, bot, right(K.iff(a)(b)), ref(p), ref(q)))
        case K.RightNot(_, p, a) => emit(SC.RightNot(next, bot, right(K.neg(a)), ref(p)))
        case K.RightExists(_, p, a, x, t) => emit(SC.RightExists(next, bot, right(K.exists(K.Lambda(x, a))), term(t), ref(p)))
        case K.RightForall(_, p, a, x) => emit(SC.RightForall(next, bot, right(K.forall(K.Lambda(x, a))), variable(x), ref(p)))
        case K.RightEpsilon(_, p, a, x, t) =>
          val choice = K.epsilon(K.Lambda(x, a))
          emit(SC.RightEpsilon(next, bot, right(K.substituteVariables(a, Map(x -> choice))), formula(a), variable(x), term(t), ref(p)))
        case K.RightRefl(_, a) => emit(SC.RightRefl(next, bot, right(a)))
        case K.LeftRefl(_, p, a) =>
          val refl = emit(SC.RightRefl(next, SC.Sequent(Nil, Seq(formula(a))), 0))
          emit(SC.Cut(next, bot, 0, refl.name, ref(p)))
        case K.InstSchema(_, p, subst) => instantiate(refs(p), source(p), subst, bot)
        case K.LeftSubstEq(_, p, pairs, ctx) => substitute(refs(p), pairs, ctx, Nil, bot, onLeft = true)
        case K.RightSubstEq(_, p, Seq(pair), (Seq(hole), body)) if pointwisePredicate(hole) =>
          val lifted = lisa.utils.kernel.Substitution.liftedEqualities(Seq(pair)).head
          val definition = bot.left(index(bot.left, formula(lifted.betaNormalForm)))
          val assumption = emit(SC.Hyp(next, SC.Sequent(Seq(definition), Seq(definition)), 0))
          val rewrite = quantifiedRewrite(refs(p), assumption, 0, pair, hole, body, bot)
          localComparisons(rewrite.name) = assumption
          rewrite
        case K.RightSubstEq(_, p, pairs, ctx) => substitute(refs(p), pairs, ctx, Nil, bot, onLeft = false)
        case K.LeftSubst(_, p, ps, rs, ctx) => comparisonSubst(refs(p), ps, rs, ctx, bot, onLeft = true)
        case K.RightSubst(_, p, Seq(q), Seq((lhs, rhs, xs)), (Seq(hole), body)) if pointwisePredicate(hole) =>
          require(xs.size == hole.sort.depth && xs.distinct == xs && xs.forall(_.sort == K.Ind), "Expected distinct individual parameters")
          require(xs.forall(x => !lhs.freeVariables(x) && !rhs.freeVariables(x)), "Comparison parameters must be fresh")
          def applied(f: K.Expression) = xs.foldLeft(f)(_(_)).betaNormalForm
          var principal = formula(K.iff(applied(lhs))(applied(rhs)))
          var comparison = refs(q)
          for x <- xs.reverseIterator do
            val j = index(comparison.bot.right, principal)
            principal = F.BinderFormula(F.Forall, variable(x), principal)
            val quantified = comparison.bot.copy(right = comparison.bot.right.updated(j, principal))
            comparison = emit(SC.RightForall(next, quantified, j, variable(x), comparison.name))
          quantifiedRewrite(refs(p), comparison, index(comparison.bot.right, principal), (lhs, rhs), hole, body, bot)
        case K.RightSubst(_, p, ps, rs, ctx) => comparisonSubst(refs(p), ps, rs, ctx, bot, onLeft = false)
        case _ => fail(s"Unsupported certificate rule ${step.getClass.getSimpleName}")

    // SC-TPTP requires both conjuncts on the left or both disjuncts on the right.
    private def withOperands(start: Step, a: K.Expression, b: K.Expression, onLeft: Boolean): Step =
      Seq(formula(a), formula(b)).foldLeft(start) { (line, operand) =>
        val side = if onLeft then line.bot.left else line.bot.right
        if side.exists(F.isSame(_, operand)) then line else addWeakening(line, operand, onLeft)
      }

    private def addWeakening(line: Step, f: F.Formula, onLeft: Boolean): Step =
      if onLeft then emit(SC.LeftWeaken(next, line.bot +<< f, line.bot.left.size, line.name))
      else emit(SC.RightWeaken(next, line.bot +>> f, line.bot.right.size, line.name))

    private def weaken(start: Step, goal: SC.Sequent): Step =
      var line = start
      require(F.isSubset(start.bot.left, goal.left) && F.isSubset(start.bot.right, goal.right), "Conclusion would remove or rewrite a formula")
      for f <- goal.left if !line.bot.left.contains(f) do line = addWeakening(line, f, onLeft = true)
      for f <- goal.right if !line.bot.right.contains(f) do line = addWeakening(line, f, onLeft = false)
      line

    private def branches(ps: Array[Int], as: Seq[K.Expression], goal: SC.Sequent, onLeft: Boolean): Step =
      require(ps.nonEmpty && ps.length == as.size, "Expected one premise per operand")
      var line = refs(ps.head)
      var operand = formula(as.head)
      for i <- 1 until ps.length do
        val other = refs(ps(i))
        val b = formula(as(i))
        val joined = F.ConnectorFormula(if onLeft then F.Or else F.And, Seq(operand, b))
        val bot =
          if i == ps.length - 1 then goal
          else if onLeft then
            SC.Sequent((line.bot.left.diff(Seq(operand)) ++ other.bot.left.diff(Seq(b)) :+ joined).distinct, (line.bot.right ++ other.bot.right).distinct)
          else SC.Sequent((line.bot.left ++ other.bot.left).distinct, (line.bot.right.diff(Seq(operand)) ++ other.bot.right.diff(Seq(b)) :+ joined).distinct)
        line =
          if onLeft then emit(SC.LeftOr(next, bot, index(bot.left, joined), line.name, other.name))
          else emit(SC.RightAnd(next, bot, index(bot.right, joined), line.name, other.name))
        operand = joined
      if ps.length == 1 then
        index(if onLeft then goal.left else goal.right, operand)
        weaken(line, goal)
      else line

    /** Expand a simultaneous schema instantiation without substituting inside another replacement. */
    private def instantiate(start: Step, source: K.Sequent, subst: Map[K.Variable, K.Expression], goal: SC.Sequent): Step =
      val used = mutable.Set.from((source.left ++ source.right ++ subst.values ++ subst.keys).flatMap(_.allVariables))
      def newVariable(sort: K.Sort): K.Variable =
        val v = fresh(used.toSet, sort)
        used += v
        v

      var line = start
      def applyOne(v: K.Variable, replacement: K.Expression): Unit =
        require(v.sort == replacement.sort && (v.sort.isPredicate || v.sort.isFunctional), s"Expected a first-order schema for $v")
        val params = Vector.fill(v.sort.depth)(newVariable(K.Ind))
        // Open only the parameter lambdas. Any higher-order expression left in the body fails FOL conversion.
        val body = params.foldLeft(replacement): (f, x) =>
          f match
            case K.Lambda(bound, inner) => K.substituteVariables(inner, Map(bound -> x))
            case _ => f(x)
        val xs = params.map(variable)
        def mapped(f: F.Formula => F.Formula) = SC.Sequent(line.bot.left.map(f).distinct, line.bot.right.map(f).distinct)
        if v.sort.isPredicate then
          val pred = F.AtomicSymbol(symbol(v), xs.size)
          val image = (formula(body), xs)
          val bot = mapped(F.substitutePredicatesInFormula(_, Map(pred -> image)))
          line = emit(SC.InstPred(next, bot, pred, image, line.name))
        else
          val fun = F.FunctionSymbol(symbol(v), xs.size)
          val image = (term(body), xs)
          val bot =
            if xs.isEmpty then mapped(F.substituteVariablesInFormula(_, Map(variable(v) -> image._1)))
            else mapped(F.substituteFunctionsInFormula(_, Map(fun -> image)))
          line = emit(SC.InstFun(next, bot, fun, image, line.name))

      val entries = subst.toVector.sortBy((v, _) => symbol(v).toString)
      val protectedEntries = entries.map: (v, replacement) =>
        if entries.exists((other, rhs) => other != v && rhs.freeVariables(v)) then
          val tmp = newVariable(v.sort)
          applyOne(v, tmp)
          (tmp, replacement)
        else (v, replacement)
      protectedEntries.foreach(applyOne)
      require(F.isSameSet(line.bot.left, goal.left) && F.isSameSet(line.bot.right, goal.right), "Conclusion is not the first-order instance of the premise")
      line

    private def pointwisePredicate(v: K.Variable): Boolean = v.sort.isPredicate && v.sort.depth > 0

    private def quantifiedRewrite(start: Step, comparison: Step, i: Int, pair: (K.Expression, K.Expression),
        hole: K.Variable, body: K.Expression, goal: SC.Sequent): RightSubstIffForall =
      require(pair._1.sort == hole.sort && pair._2.sort == hole.sort, "Expected predicate replacements of the context hole's sort")
      def filled(value: K.Expression) = formula(K.substituteVariables(body, Map(hole -> value)).betaNormalForm)
      index(start.bot.right, filled(pair._1))
      index(goal.right, filled(pair._2))
      // SC-TPTP marks the whole formula occurrence. Its arguments are inferred from the two sequents.
      val marker = fresh(body.allVariables, K.Prop)
      val x = fresh(body.allVariables, K.Ind)
      val constant = (0 until hole.sort.depth).foldLeft(marker: K.Expression)((f, _) => K.Lambda(x, f))
      emit(RightSubstIffForall(next, goal, i, filled(constant), F.AtomicSymbol(symbol(marker), 0), start.name, comparison.name))

    private type Context = (Seq[K.Variable], K.Expression)

    private def comparisonSubst(start: Step, ps: Seq[Int], replacements: Seq[(K.Expression, K.Expression, Seq[K.Variable])],
        ctx: Context, goal: SC.Sequent, onLeft: Boolean): Step =
      require(ps.size == replacements.size, "Expected one comparison proof per replacement")
      require(replacements.forall(_._3.isEmpty), "Pointwise substitution of function or predicate schemata is outside the strict fragment")
      substitute(start, replacements.map((s, t, _) => (s, t)), ctx, ps.map(refs), goal, onLeft)

    /** Replace one hole at a time, then cut away comparison assumptions supplied as separate proofs. */
    private def substitute(start: Step, pairs: Seq[(K.Expression, K.Expression)], ctx: Context,
        comparisons: Seq[Step], goal: SC.Sequent, onLeft: Boolean): Step =
      val (holes, body) = ctx
      require(holes.size == pairs.size && holes.distinct == holes, "Expected one distinct context parameter per replacement")
      val equations = holes.zip(pairs).map: (v, pair) =>
        val (s, t) = pair
        require(v.sort == s.sort && v.sort == t.sort && (v.sort == K.Ind || v.sort == K.Prop), "Expected an individual or propositional substitution")
        formula(if v.sort == K.Ind then K.equality(s)(t) else K.iff(s)(t))
      val avoid = (body +: pairs.flatMap((s, t) => Seq(s, t))).flatMap(_.allVariables) ++ holes
      var values = holes.zip(pairs.map(_._1)).toMap
      def filled(m: Map[K.Variable, K.Expression]) = formula(K.substituteVariables(body, m))
      val initial = filled(values)
      val side = if onLeft then start.bot.left else start.bot.right
      index(side, initial)
      val rest = side.filterNot(F.isSame(_, initial))
      var line = start
      for i <- holes.indices do
        val v = holes(i)
        val marker = fresh(avoid, v.sort)
        val shape = filled(values.updated(v, marker))
        values = values.updated(v, pairs(i)._2)
        val updated = (rest :+ filled(values)).distinct
        val assumptions = equations.take(i + 1)
        val bot =
          if onLeft then SC.Sequent((updated ++ assumptions).distinct, start.bot.right)
          else SC.Sequent((start.bot.left ++ assumptions).distinct, updated)
        val j = index(bot.left, equations(i))
        line = if v.sort == K.Ind then
          if onLeft then emit(SC.LeftSubst(next, bot, j, false, shape, variable(marker), line.name))
          else emit(SC.RightSubst(next, bot, j, false, shape, variable(marker), line.name))
        else
          val hole = F.AtomicSymbol(symbol(marker), 0)
          if onLeft then emit(SC.LeftSubstIff(next, bot, j, false, shape, hole, line.name))
          else emit(SC.RightSubstIff(next, bot, j, false, shape, hole, line.name))
      for (proof, i) <- comparisons.zipWithIndex do
        val eq = equations(i)
        val keep = equations.drop(i + 1).contains(eq) || goal.left.contains(eq)
        val left = if keep then line.bot.left else line.bot.left.filterNot(F.isSame(_, eq))
        val bot = SC.Sequent((proof.bot.left ++ left).distinct, (proof.bot.right.filterNot(F.isSame(_, eq)) ++ line.bot.right).distinct)
        line = emit(SC.Cut(next, bot, index(proof.bot.right, eq), proof.name, line.name))
      weaken(line, goal)
