# SC-proof backport ledger

Base: upstream `a234fb842ef8ab875647b7c83099b9dd47a716ba`.
Source: `lcf-hol-ex` at `c8fc28f`, plus its accepted working-tree changes.
Status: in progress. No automatic rebases or merge of the previous backport.

Run `bash bin/check-backport-boundary.sh` after every batch. Keep the SC proof
kernel, basic steps, and old tactic API. Translate proof recipes, never LCF
carriers. Preserve upstream tests, normalization fixes, and build configuration.

## Batches

| Donor | Scope | Result |
| --- | --- | --- |
| — | Architectural guard | Added; kernel and basic steps unchanged |

## Validation

- Upstream baseline: running; log `/tmp/lisa-backport-baseline.log`.
- Serialization, HOL, typing, imports and parity validation: pending.

## Deferred decisions

- Shared HOL step storage needs independently checked SC proofs/justifications,
  not reused local proof indices or an LCF carrier.
- Do not include experimental A/B/C/E caching proposals from the performance
  study in the accepted baseline.
- Do not import the proof-recomputing accessors of `c6567fa` without a separate
  lifecycle/cache review.
