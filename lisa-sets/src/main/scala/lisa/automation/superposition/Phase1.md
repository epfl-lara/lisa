In this phase we implement Ordered Resolution via the DISCOUNT loop.

We first define our inference: At this stage this is Resolution and Factorization.

The loop has a set of active clause and a set of passive clauses. We pick passive clause alternatively by age and weight. In particular weight needs to be efficiently computed.
We do ordered resolution, so only the selected literal of each clause needs to be considered for resolution. The selected literal is the first negative literal (cause literals are sorted in the clause) if it exists, otherwise the first literal.

Clauses need to be cacnonicalized: sorted and duplicates removed. This is done at the time of insertion in the passive set, so that we can easily check for tautologies and subsumption. This also needs to be done optimally, without unnecessary allocations or steps. 

We also need to do factorization (a clause with itself)