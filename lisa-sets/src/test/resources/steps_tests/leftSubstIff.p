fof(a1, axiom, [q(s)] --> []).
fof(f1, plain, [q(s) <=> q(t), q(t)] --> [], inference(leftSubstIff, [status(thm), 0, 0, $fof(K), 'K'], [a1])).

fof(a2, axiom, [a & p(s, t)] --> []).
fof(f2, plain, [p(s, t) <=> q(t), a & q(t)] --> [], inference(leftSubstIff, [status(thm), 0, 0, $fof(a & K), 'K'], [a2])).

fof(a3, axiom, [q(s) & (q(t) | q(s))] --> []).
fof(f3, plain, [q(s) <=> q(t), q(t) & (q(t) | q(s))] --> [], inference(leftSubstIff, [status(thm), 0, 0, $fof(K & (q(t) | q(s))), 'K'], [a3])).

fof(a3, axiom, [~(q(s) & q(t)) => q(s)] --> []).
fof(f3, plain, [~(~(a & q(t)) & q(t)) => ~(a & q(t)), q(s) <=> ~(a & q(t))] --> [], inference(leftSubstIff, [status(thm), 1, 0, $fof(~(K & q(t)) => K), 'K'], [a3])).

fof(a4, axiom, [![X] : ~(q(s) & q(X))] --> []).
fof(f4, plain, [q(s) <=> q(X), ![Y] : ~(q(X) & q(Y))] --> [], inference(leftSubstIff, [status(thm), 0, 0, $fof(![X] : ~(K & q(X))), 'K'], [a4])).

