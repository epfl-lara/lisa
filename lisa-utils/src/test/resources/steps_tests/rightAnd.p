fof(a1_1, axiom, [q] --> [p]).
fof(a1_2, axiom, [r] --> [q]).
fof(f1, plain, [r, q] --> [p & q], inference(rightAnd, [status(thm), 0], [a1_1, a1_2])).

fof(a2_1, axiom, [] --> [p, q]).
fof(a2_2, axiom, [] --> [s, t]).
fof(f2, plain, [] --> [p, q & s, t], inference(rightAnd, [status(thm), 1], [a2_1, a2_2])).

fof(a3_1, axiom, [] --> [p, q]).
fof(a3_2, axiom, [] --> [s, t]).
fof(f3, plain, [] --> [p & t , q, s], inference(rightAnd, [status(thm), 0], [a3_1, a3_2])).

fof(a4_1, axiom, [R & r(f(g(X, Y)))] --> [P(X), Q(X)]).
fof(a4_2, axiom, [R] --> [R & Q(X)]).
fof(f4, plain, [R & r(f(g(X, Y))), R] --> [P(X), Q(X) & (R & Q(X))], inference(rightAnd, [status(thm), 1], [a4_1, a4_2])).

fof(a5_1, axiom, [(t(X) & u(Z)), v(f(c))] --> [![X]: (p(X) & q(X)), A]).
fof(a5_2, axiom, [(t(X) & u(Z))] --> [(r(X) | s(X))]).
fof(f5, plain, [(t(X) & u(Z)), v(f(c))] --> [A, ![X]: (p(X) & q(X)) & (r(X) | s(X))], inference(rightAnd, [status(thm), 1], [a5_1, a5_2])).


