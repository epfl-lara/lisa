# Phase 1 — Ordered resolution via the DISCOUNT loop

> **Status: historical.** This is the original sketch, kept as a record of intent. Two things below no longer
> describe the code:
>
> - **Literal selection.** The default is now `CompleteBestLiteralSelector` (Vampire's selector 10), which
>   selects a negative literal when one is competitive and otherwise **all** ordering-maximal literals — the
>   Bachmair-Ganzinger-admissible choices, so the calculus stays refutation-complete. The "first negative
>   literal, else the first literal" rule described here survives as `FirstNegativeSelector`, which is *not*
>   BG-complete on all-positive clauses and is used only as a portfolio slice. See `Selectors.scala`.
> - **Canonicalisation timing.** Sorting/dedup happens in `Inference.canonicalize`, called from
>   `Discount.addPassive` — as planned — but a clause selected from passive is re-canonicalised after forward
>   demodulation, since rewriting can create a tautology or a duplicate literal.
>
> `Discount.scala` and `Selectors.scala` are authoritative.

In this phase we implement Ordered Resolution via the DISCOUNT loop.

We first define our inference: At this stage this is Resolution and Factorization.

The loop has a set of active clause and a set of passive clauses. We pick passive clause alternatively by age and weight. In particular weight needs to be efficiently computed.
We do ordered resolution, so only the selected literal of each clause needs to be considered for resolution. The selected literal is the first negative literal (cause literals are sorted in the clause) if it exists, otherwise the first literal.

Clauses need to be cacnonicalized: sorted and duplicates removed. This is done at the time of insertion in the passive set, so that we can easily check for tautologies and subsumption. This also needs to be done optimally, without unnecessary allocations or steps. 

We also need to do factorization (a clause with itself)