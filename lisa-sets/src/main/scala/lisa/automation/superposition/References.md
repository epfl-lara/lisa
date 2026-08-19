# References

The papers whose contributions are implemented in `lisa.automation.superposition` and its clausification front
end `lisa.automation.clausification`. Each entry corresponds to something a file here does. A survey, handbook
chapter or textbook is included where it is the best source for an implemented element, and the primary paper
otherwise; techniques this prover does not use are left out. Sections follow the pipeline and name the files
they cover.

Titles link to a copy, preferring an open-access publisher page, then a repository or author-hosted PDF, then
the publisher's page.

## Clausal normal form

`clausification/` — `NnfPhase`, `PrenexPhase`, `SkolemPhase`, `NamingPhase`, `DistributePhase`, `CertifiedClausifier`

- Plaisted, D. A., and Greenbaum, S. [A Structure-Preserving Clause Form Translation](https://doi.org/10.1016/S0747-7171(86)80028-1). *Journal of Symbolic Computation*, 1986.
- Nonnengart, A., and Weidenbach, C. [Computing Small Clause Normal Forms](https://www.sciencedirect.com/science/article/pii/B9780444508133500084). *Handbook of Automated Reasoning*, 2001.
- de Nivelle, H. [Extraction of Proofs from the Clausal Normal Form Transformation](https://doi.org/10.1007/3-540-45793-3_39). *CSL*, 2002.

## Resolution and superposition calculus

`Inference`, `Superposition`, `Generator`

- Robinson, J. A. [A Machine-Oriented Logic Based on the Resolution Principle](https://dl.acm.org/doi/10.1145/321250.321253). *Journal of the ACM*, 1965.
- Bachmair, L., and Ganzinger, H. [On Restrictions of Ordered Paramodulation with Simplification](https://link.springer.com/content/pdf/10.1007/3-540-52885-7_105.pdf). *CADE-10*, 1990.
- Bachmair, L., and Ganzinger, H. [Rewrite-Based Equational Theorem Proving with Selection and Simplification](https://doi.org/10.1093/logcom/4.3.217). *Journal of Logic and Computation*, 1994.

## Unification and matching

`Core` (`Trail`, `Applier`)

- Baader, F., and Snyder, W. [Unification Theory](https://www.sciencedirect.com/science/article/pii/B9780444508133500102). *Handbook of Automated Reasoning*, 2001.

## Term ordering

`ordering/KBO`, `ordering/Order`, `ordering/Precedence`

- Knuth, D. E., and Bendix, P. B. [Simple Word Problems in Universal Algebras](https://www.cs.tufts.edu/~nr/cs257/archive/don-knuth/knuth-bendix.pdf). *Computational Problems in Abstract Algebra*, 1970.
- Löchner, B. [Things to Know when Implementing KBO](https://doi.org/10.1007/s10817-006-9031-4). *Journal of Automated Reasoning*, 2006.

## Literal selection

`ordering/Selectors`

- Hoder, K., Reger, G., Suda, M., and Voronkov, A. [Selecting the Selection](https://arxiv.org/pdf/1604.08055). *IJCAR*, 2016.

## Saturation loop and clause selection

`Discount`, `PassiveSet`, `ActiveSet`

- Denzinger, J., Kronenburg, M., and Schulz, S. [DISCOUNT — A Distributed and Learning Equational Prover](https://doi.org/10.1023/A:1005879229581). *Journal of Automated Reasoning*, 1997.
- Schulz, S., and Möhrmann, M. [Performance of Clause Selection Heuristics for Saturation-Based Theorem Proving](http://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/sm_ijcar-2016.pdf). *IJCAR*, 2016.

## Simplification and redundancy

`Demodulation`, `Subsumption`, `Simplifier`

- Wos, L., Robinson, G. A., Carson, D. F., and Shalla, L. [The Concept of Demodulation in Theorem Proving](https://dl.acm.org/doi/10.1145/321420.321429). *Journal of the ACM*, 1967.
- Joyner, W. H. [Resolution Strategies as Decision Procedures](https://dl.acm.org/doi/10.1145/321958.321960). *Journal of the ACM*, 1976.
- Bachmair, L., Dershowitz, N., and Plaisted, D. A. [Completion Without Failure](https://www.cs.tau.ac.il/~nachum/papers/unfail-paper.pdf). *Resolution of Equations in Algebraic Structures, Volume 2*, 1989.
- Tammet, T. [Towards Efficient Subsumption](https://link.springer.com/content/pdf/10.1007/BFb0054276.pdf). *CADE-15*, 1998.
- Weidenbach, C. [Combining Superposition, Sorts and Splitting](https://pure.mpg.de/pubman/faces/ViewItemOverviewPage.jsp?itemId=item_1330615). *Handbook of Automated Reasoning*, 2001.

## Term and clause indexing

`index/DiscriminationTree`, `index/Fingerprint`, `index/FeatureVector`

- Sekar, R., Ramakrishnan, I. V., and Voronkov, A. [Term Indexing](https://www.sciencedirect.com/science/article/pii/B978044450813350028X). *Handbook of Automated Reasoning*, 2001.
- Schulz, S. [Fingerprint Indexing for Paramodulation and Rewriting](http://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/schulz_fp-index.pdf). *IJCAR*, 2012.
- Schulz, S. [Simple and Efficient Clause Subsumption with Feature Vector Indexing](http://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/Schulz2013-FVI.pdf). *Automated Reasoning and Mathematics: Essays in Memory of William W. McCune*, 2013.

## Axiom selection

`Sine`

- Hoder, K., and Voronkov, A. [Sine Qua Non for Large Theory Reasoning](https://doi.org/10.1007/978-3-642-22438-6_23). *CADE-23*, 2011.

## Proof output and reconstruction into a kernel

`Reconstruction`, `Bridge`, `Clausal`, `CascProver`, `clausification/CertifiedClausifier`

- Sutcliffe, G., Schulz, S., Claessen, K., and Van Gelder, A. [Using the TPTP Language for Writing Derivations and Finite Interpretations](https://doi.org/10.1007/11814771_7). *IJCAR*, 2006.
- Guilloud, S., Gambhir, S., and Kunčak, V. [LISA — A Modern Proof System](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2023.17). *ITP*, 2023.
- Guilloud, S., Cailler, J., Gambhir, S., Poiroux, A., Herklotz, Y., Bourgeat, T., and Kunčak, V. [Interoperability of Proof Systems with SC-TPTP](https://hal.science/hal-05329188v1/file/cade30.pdf). *CADE-30*, 2025.

## Reference implementations whose defaults are mirrored

`Strategy`, `ordering/Precedence`, `ordering/Selectors`, `PassiveSet`, `Sine`

- Riazanov, A., and Voronkov, A. [The Design and Implementation of VAMPIRE](https://doi.org/10.3233/EAI-2002-259). *AI Communications*, 2002.
- Schulz, S. [E — A Brainiac Theorem Prover](http://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/Schulz-AICOM-2002.pdf). *AI Communications*, 2002.

## Problem library

`bench/`, `CascProver`, the TPTP tests

- Sutcliffe, G. [The TPTP Problem Library and Associated Infrastructure. From CNF to TH0, TPTP v6.4.0](https://doi.org/10.1007/s10817-017-9407-7). *Journal of Automated Reasoning*, 2017.
