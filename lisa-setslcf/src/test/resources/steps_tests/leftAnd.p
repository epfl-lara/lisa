fof(a1, axiom, [p, q] --> [r]).
fof(f1, plain, [p & q] --> [r], inference(leftAnd, [status(thm), 0], [a1])).

fof(a2, axiom, [a, p, q] --> [r]).
fof(f2, plain, [a, p & q] --> [r], inference(leftAnd, [status(thm), 1], [a2])).

fof(a3, axiom, [P(X), Q(X)] --> [R]).
fof(f3, plain, [P(X) & Q(X)] --> [R], inference(leftAnd, [status(thm), 0], [a3])).

fof(a4, axiom, [s, p, t, q] --> [u]).
fof(f4, plain, [s, p & q, t] --> [u], inference(leftAnd, [status(thm), 1], [a4])).

fof(a5, axiom, [p(X), q(Y)] --> [r(X, Y)]).
fof(f5, plain, [p(X) & q(Y)] --> [r(X, Y)], inference(leftAnd, [status(thm), 0], [a5])).


fof(a6, axiom, [![X]: (p(X) & q(X)), (r(X) | s(X))] --> [(t(X) & u(X)), v(X)]).
fof(f6, plain, [![X]: (p(X) & q(X)) & (r(X) | s(X)), (r(X) | s(X))] --> [(t(X) & u(X)), v(X)], inference(leftAnd, [status(thm), 0], [a6])).

fof(a7, axiom, [q, ![X]: (p(X) & q(X)), s(Y)] --> []).
fof(f7, plain, [![X]: (p(X) & q(X)), q & s(Y)] --> [], inference(leftAnd, [status(thm), 1], [a7])).
