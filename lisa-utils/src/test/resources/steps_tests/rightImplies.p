fof(a1, axiom, [r, p] --> [q]).
fof(f1, plain, [r] --> [p => q], inference(rightImplies, [status(thm), 0], [a1])).

fof(a2, axiom, [p, r] --> [a, q]).
fof(f2, plain, [r] --> [a, p => q], inference(rightImplies, [status(thm), 1], [a2])).

fof(a3, axiom, [P(X), R] --> [Q(X)]).
fof(f3, plain, [R] --> [P(X) => Q(X)], inference(rightImplies, [status(thm), 0], [a3])).

fof(a4, axiom, [p, u] --> [s, t, q]).
fof(f4, plain, [u] --> [s, p => q, t], inference(rightImplies, [status(thm), 1], [a4])).

fof(a5, axiom, [r(X, Y), p(X)] --> [q(Y)]).
fof(f5, plain, [r(X, Y)] --> [p(X) => q(Y)], inference(rightImplies, [status(thm), 0], [a5])).


fof(a6, axiom, [![X]: (p(X) | q(X)), (t(X) | u(X)), v(X)] --> [(r(X) & s(X))]).
fof(f6, plain, [(t(X) | u(X)), v(X)] --> [![X]: (p(X) | q(X)) => (r(X) & s(X)), (r(X) & s(X))], inference(rightImplies, [status(thm), 0], [a6])).

fof(a7, axiom, [q] --> [![X]: (p(X) | q(X)), s(Y)]).
fof(f7, plain, [] --> [![X]: (p(X) | q(X)), q => s(Y)], inference(rightImplies, [status(thm), 1], [a7])).
