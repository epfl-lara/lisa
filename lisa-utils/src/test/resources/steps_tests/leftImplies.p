fof(a1_1, axiom, [] --> [p, q]).
fof(a1_2, axiom, [q] --> [r]).
fof(f1, plain, [p => q] --> [r, q], inference(leftImplies, [status(thm), 0], [a1_1, a1_2])).

fof(a2_1, axiom, [p] --> [q]).
fof(a2_2, axiom, [s, t] --> []).
fof(f2, plain, [p, q => s, t] --> [], inference(leftImplies, [status(thm), 1], [a2_1, a2_2])).

fof(a3_1, axiom, [q] --> [p]).
fof(a3_2, axiom, [s, t] --> []).
fof(f3, plain, [p => t , q, s] --> [], inference(leftImplies, [status(thm), 0], [a3_1, a3_2])).

fof(a4_1, axiom, [P(X)] --> [R & r(f(g(X, Y))), Q(X)]).
fof(a4_2, axiom, [R & Q(X)] --> [R]).
fof(f4, plain, [P(X), Q(X) => (R & Q(X))] --> [R & r(f(g(X, Y))), R], inference(leftImplies, [status(thm), 1], [a4_1, a4_2])).

fof(a5_1, axiom, [A] --> [(t(X) & u(Z)), v(f(c)), ![X]: (p(X) & q(X))]).
fof(a5_2, axiom, [(r(X) | s(X))] --> [(t(X) & u(Z))]).
fof(f5, plain, [A, ![X]: (p(X) & q(X)) => (r(X) | s(X))] --> [(t(X) & u(Z)), v(f(c))], inference(leftImplies, [status(thm), 1], [a5_1, a5_2])).


