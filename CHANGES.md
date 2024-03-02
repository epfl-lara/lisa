# Change List

## 2024-03-02
Addition of a tactic that proves a sequent by applying a generic theorem on facts provided by the user. It can be used via `by Apply(thm).on(fact1, fact2,...)`. Replaces cases where using `Tautology` was overkill.
## 2024-02-05
The "draft()" option can now be used at the start of a file to skip checking proofs of theorem outside this file during development.


## 2024-01-02
The "of" keyword can now be used to instantiate quantified variables in facts whose right hand side is a single universaly quantified formula. This can be combined freely with instantiation of ffree schematic symbols. Manual and tests update.


## 2023-12-31
Expanded the Substitution rules to allow substitution under quantifiers when a statement of the form $\forall x. f(x) = g(x)$ is given.

## 2023-12-29
Update to the user manual, change format to B5 and more improvements.

## 2023-12-19
Introduction of local definitions, with methods `witness`, `t.replace`, `t.collect`, `t.map` and `t.filter`. Update of the manual, describing how those work, along with some corrections to the statement of axioms ot match LISA's presentation. Include test cases using each, and proved some required theorems. Fix an error in the reconstruction of OL-normalized formulas used in some tactics.

## 2023-12-06
Re-added discovery of formulas which could not be substituted for error reporting to `Substitution.ApplyRules`

Upgrade to Scala 3.3.1

- the `Proof` class has been temporarily unsealed, till [lampepfl/dotty#19031](https://github.com/lampepfl/dotty/issues/19031) / [epfl-lara/lisa#190](https://github.com/epfl-lara/lisa/issues/190) is fixed
- minor fixes to address compilation errors, mostly involving explicitly specifying types or implicits in some places.


## 2023-12-02
Creation of the present Change Liste, going back to October 2023

## 2023-12-02
Small improvement to Tableau tactics. It now uses sa weight-base heuristic for picking substitution and performs better.

## 2023-12-01
- Rename some FOL classes using the word "Atomics". For example, "SchematicVarOrPredLabel" --> "SchematicAtomicLabel". This does not change any functionality.
- Improved the logic in the front's FOL. Labels are no more contravariant in their type argument; Vars and constants are no longer extending `Label[Seq[Term] |-> Term]`. Apply paterns on Variables, Constants, Terms and Formulas should be cleaner and simpler. Some traits gained type parameters.
- Removed the match type for `T\*\*\*N`, which was used to obtain function application with arbitrary but fixed number of parameters given by N. Instead, `T\*\*N` is now an opaque type for `Seq[Term]`. Function application with `N` arguments is obtained through extension methods (one for each N, not one for each implementation of (T ** N) |-> S). That's a bit less general, but more flexible and possibly more efficient.
- Generally refactored the Common.scala file, ensuring uniformity across definitions. Uses less top-notch, scala-specific features and should be a bit more stable and easier to understand.

## 2023-11-27
Improvements and bug fix for the Tableau tactic.
- Occur check in unification in the tableau prover made it impossible to solve formulas such as $ \forall x. D(x) \land \neg D(f(x)) $.
Now variables in positive literals are renamed before unification, and mapped back after.
- The order of dependence of variables between each other is now tracked, so that when a substitution is decided, the outermost variable is instantiated first.
- New test cases that rely on these behaviours.

## 2023-11-24
Reafactor and reorganize files:
- Root project moved to lisa-sets
- Removed unused legacy files and tests
- Put all automation tools in the same place (lisa-sets/automation)
- Generally flatten folder structure, when possible

- Clean some files and imports
## 2023-11-15
- Added references to publications.
- Formatted the README file generally
- Fixed grammar or spelling errors
- Make instructions a bit more explicit

## 2023-11-15
- Added a tool to serialize kernel proofs. Theorems can be serialized to binary files and loaded back on later run.
- Test suite for serialization.
- On personal machine, running everything up to Recursion.scala takes 19s instead of 24s.
- Complete documentation of WithTheorems.scala
- Fixed an indexing bug in `ShrinkProof.flattenProof`

## 2023-11-8
- Fix typo in the Zermelo axioms in the manual.
- Pretty printing of front formulas, with infix. Printing should essentially always be valid code that can be copied back to a lisa file.
- Fix and improve extractor paterns of function and predicate symbols.
- It is now possible to return an `InvalidProofTactic` result inside a `TacticSubproof`. This was not possible because it is a non-local return, but some inlining makes it possible.
- Fix an unsoundness error in kernel proof checker related to steps with multiple premises.


## 2023-10-30
Implement a tableau based tactic for first order logic.
It can be used via `by Tableau`. It replaced lengthier proof scripts in most of the Quantifier.scala proofs.
It should be complete, and is not super optimized but does contains some important optimizations.
Also contains a set of dedicated tests.

## 2023-10-05
Big update to the manual. It now has a "Quick Guide" section explaining how to use LISA. Also contains general corrections and clean and uniform framing for code, with support for unicode in listings.


