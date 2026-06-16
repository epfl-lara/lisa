We are constructing a prover for problems in clausal form using ordered resolution and superposition for Lisa in Scala. We want to make it super efficient, low level, and with full proof reconstruction. We take heavy inspiration from Vampire, E and Prover9 to implement things optimally.

Phase 0: Core datastructure and utilities (terms, clauses, unification, KBO)
Phase 1: Ordered Resolution via the discount Loop, Factorization and proof reconstruction in Lisa.
Phase 2: Demodulation, forward/backward subsumption, redundancy elimination
Phase 3: Superposition, equality handling, paramodulation.
Phase 4: Heuristics, term indexing, and optimizations.