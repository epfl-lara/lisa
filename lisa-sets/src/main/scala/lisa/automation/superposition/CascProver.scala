package lisa.automation.superposition

import java.io.File
import scala.util.{Try, Success, Failure}

import lisa.utils.K
import lisa.tptp.{AnnotatedFormula, AnnotatedStatement}
import lisa.tptp.KernelParser.{axiomLikeRoles, problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}

/** CASC-compatible command-line entry point (see the [[https://tptp.org/CASC/J13/Design.html CASC J13 design]]
  * and the [[https://tptp.org/UserDocs/SZSOntology/ SZS ontology]]).
  *
  * Parses one TPTP problem file, hands it to [[Prover.proveTstp]], and writes an SZS status line. On a
  * refutation it also prints the derivation, which [[Tstp]] renders. This object is the command line and
  * nothing else: argument parsing, the SZS verdict, and the order the two are printed in.
  *
  * Usage: `CascProver [-t <seconds>] <problem.p>`. The prover is given slightly less than the budget, so that
  * the status line is printed before an external wrapper's hard limit fires. */
object CascProver:

  private val DefaultLimitSeconds = 300L
  private val OutputMarginMillis  = 2000L // reserve time to print the answer before an external hard kill

  /** Parsed command line: the problem file, the wall-clock budget, and the search strategy (one portfolio slice). */
  private final case class Cli(problem: File, limitSeconds: Long, strategy: Strategy)

  private def parseCli(args: List[String], acc: Cli): Cli = args match
    case ("-t" | "--cpu-limit" | "--wc-limit") :: n :: rest => parseCli(rest, acc.copy(limitSeconds = n.toLong))
    case "--strategy" :: n :: rest                          =>
      Strategy.byName(n) match
        case Some(s) => parseCli(rest, acc.copy(strategy = s))
        case None =>
          Console.err.println(s"unknown strategy '$n'; available: ${Strategy.portfolio.map(_.name).mkString(", ")}")
          sys.exit(2)
    case flag :: rest if flag.startsWith("-")               => parseCli(rest, acc) // ignore unknown flags
    case file :: rest                                       => parseCli(rest, acc.copy(problem = new File(file)))
    case Nil                                                => acc

  /** The SZS status for an outcome. Deliberately conservative: a refutation (empty clause) is `Theorem` with a
   *  conjecture and `Unsatisfiable` without; a saturation is `GaveUp` (we never claim (Counter)Satisfiable, so an
   *  incomplete run, e.g. after SInE pruning, can never yield a wrong verdict); a timeout is `Timeout`.
   *  A parse/solve failure is reported as `Error` at the call sites. */
  private def szsStatus(hasConjecture: Boolean, outcome: Clausal.Outcome): String = outcome match
    case _: Clausal.Outcome.Success => if hasConjecture then "Theorem" else "Unsatisfiable"
    case Clausal.Outcome.Saturated  => "GaveUp"
    case Clausal.Outcome.Timeout    => "Timeout"

  def main(args: Array[String]): Unit =
    val cli = parseCli(args.toList, Cli(null, DefaultLimitSeconds, Strategy.balanced))
    if cli.problem == null then
      Console.err.println("usage: CascProver [-t <seconds>] [--strategy <name>] <problem.p>")
      sys.exit(2)
    val name = cli.problem.getName
    val budgetMillis = math.max(1000L, cli.limitSeconds * 1000L - OutputMarginMillis)

    Try(problemToKernel(cli.problem)(using (strictMapAtom, strictMapTerm, strictMapVariable))) match
      case Failure(e) =>
        // Includes are resolved by the TPTP parser; a parse/processing failure is reported as an SZS Error.
        println(s"% SZS status Error for $name")
        Console.err.println(s"parse error: $e")
      case Success(parsed) =>
        // Input formulas as AnnotatedFormula (a cnf clause becomes its disjunction), keeping names/roles.
        // `clausalProblemWithOrigins`' origins index into `axiomLike ++ [conjecture]`, in that order.
        val axiomLike0: IndexedSeq[AnnotatedFormula] = parsed.formulas.collect {
          case s: AnnotatedStatement if axiomLikeRoles.contains(s.role) => s.toFormula
        }.toIndexedSeq
        val conjecture: Option[AnnotatedFormula] = parsed.formulas.collectFirst {
          case s: AnnotatedStatement if s.role == "conjecture" => s.toFormula
        }
        val cprob = Prover.fromTptp(parsed)
        // `fromTptp` appends one hypothesis per pair of distinct objects, past the parsed formulas. The
        // derivation cites every clause's origin by name, so those get names here — they are the only
        // hypotheses with no input formula behind them.
        val generated: IndexedSeq[AnnotatedFormula] =
          cprob.hypotheses.toIndexedSeq.drop(axiomLike0.size).zipWithIndex.map { (s, k) =>
            AnnotatedFormula("axiom", s"distinct_$k", K.multior(s.left.toSeq.map(e => K.neg(e)) ++ s.right.toSeq), None)
          }
        val inputFormulas: IndexedSeq[AnnotatedFormula] = axiomLike0 ++ generated
        // SInE and orthologic normalisation are preprocessing phases inside [[Prover]] now. A refutation
        // reports which axioms SInE kept, so the derivation's leaves still name the survivors.
        Try(Prover.proveTstp(cprob, cli.strategy.opts.copy(maxMillis = budgetMillis))) match
          case Failure(e) =>
            println(s"% SZS status Error for $name")
            Console.err.println(s"solve error: $e")
          case Success(result) =>
            val outcome: Clausal.Outcome = result.fold(identity, _.success)
            println(s"% SZS status ${szsStatus(conjecture.isDefined, outcome)} for $name")
            result.foreach { r => // Saturated/Timeout produce no CNFRefutation
              val axiomLike: IndexedSeq[AnnotatedFormula] = r.axioms.map(inputFormulas)
              if axiomLike.size < inputFormulas.size then
                Console.err.println(s"% SInE: kept ${axiomLike.size} of ${inputFormulas.size} axioms")
              Tstp.printRefutation(name, axiomLike, conjecture, r.clauses, r.success, isCnf = parsed.spc.exists(_.contains("CNF")))
            }
    Console.out.flush()
