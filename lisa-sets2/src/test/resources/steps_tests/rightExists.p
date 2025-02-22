fof(a1, axiom, [r] --> [p, q]).
fof(f1, plain, [r] --> [?[X] : p, q], inference(rightExists, [status(thm), 0, $fot(X)], [a1])).

fof(a2, axiom, [r] --> [a, p(X)]).
fof(f2, plain, [r] --> [a, ?[X] : p(X)], inference(rightExists, [status(thm), 1, $fot(X)], [a2])).

fof(a3, axiom, [R] --> [P(X), Q(f(c))]).
fof(f3, plain, [R] --> [P(X), ?[X] : Q(X)], inference(rightExists, [status(thm), 1, $fot(f(c))], [a3])).


fof(a4, axiom, [r(X, Y)] --> [p(X), q(g(Y, c)) | q(Y)]).
fof(f4, plain, [r(X, Y)] --> [p(X), ?[X] : (q(X) | q(Y))], inference(rightExists, [status(thm), 1, $fot(g(Y, c))], [a4])).


fof(a6, axiom, [(t(X) & u(X)), v(X)] --> [?[X]: (p(X) & q(f(c))), (r(X) | s(Y))]).
fof(f6, plain, [(t(X) & u(X)), v(X)] --> [?[Y, X]: (p(X) & q(Y)), (r(X) | s(Y))], inference(rightExists, [status(thm), 0, $fot(f(c))], [a6])).

fof(a7, axiom, [] --> [q, ?[X]: (p(X) & q(f(c))), s(Y)]).
fof(f7, plain, [] --> [q, ?[X, Y]: (p(Y) & q(X)), s(Y)], inference(rightExists, [status(thm), 1, $fot(f(c))], [a7])).


fof(a7, axiom, [] --> [q, ?[X]: (p(X) & r(f(c), f(c))), s(Y)]).
fof(f7, plain, [] --> [q, ?[X, Y]: (p(Y) & r(X, X)), s(Y)], inference(rightExists, [status(thm), 1, $fot(f(c))], [a7])).