fof(a1, axiom, [p, q] --> [r]).
fof(f1, plain, [?[X] : p, q] --> [r], inference(leftExists, [status(thm), 0, 'X'], [a1])).

fof(a2, axiom, [a, p(X)] --> [r]).
fof(f2, plain, [a, ?[X] : p(X)] --> [r], inference(leftExists, [status(thm), 1, 'X'], [a2])).

fof(a3, axiom, [P(Z), Q(Y)] --> [R]).
fof(f3, plain, [P(Z), ?[X] : Q(X)] --> [R], inference(leftExists, [status(thm), 1, 'Y'], [a3])).


fof(a4, axiom, [p(X), q(Z) | q(Y)] --> [r(X, Y)]).
fof(f4, plain, [p(X), ?[X] : (q(X) | q(Y))] --> [r(X, Y)], inference(leftExists, [status(thm), 1, 'Z'], [a4])).


fof(a6, axiom, [?[X]: (p(X) & q(Z)), (r(X) | s(Y))] --> [(t(X) & u(X)), v(X)]).
fof(f6, plain, [?[Y, X]: (p(X) & q(Y)), (r(X) | s(Y))] --> [(t(X) & u(X)), v(X)], inference(leftExists, [status(thm), 0, 'Z'], [a6])).

fof(a7, axiom, [q, ?[X]: (p(X) & q(Z)), s(Y)] --> []).
fof(f7, plain, [q, ?[X, Y]: (p(Y) & q(X)), s(Y)] --> [], inference(leftExists, [status(thm), 1, 'Z'], [a7])).

fof(a8, axiom, [q, ?[X]: (p(X) & r(Z, Z)), s(Y)] --> []).
fof(f8, plain, [q, ?[X, Y]: (p(Y) & r(X, X)), s(Y)] --> [], inference(leftExists, [status(thm), 1, 'Z'], [a8])).
