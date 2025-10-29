fof(a1, axiom, [r] --> [p, q]).
fof(f1, plain, [r] --> [![X] : p, q], inference(rightForall, [status(thm), 0, 'X'], [a1])).

fof(a2, axiom, [r] --> [a, p(X)]).
fof(f2, plain, [r] --> [a, ![X] : p(X)], inference(rightForall, [status(thm), 1, 'X'], [a2])).

fof(a3, axiom, [R] --> [P(X), Q(Y)]).
fof(f3, plain, [R] --> [P(X), ![X] : Q(X)], inference(rightForall, [status(thm), 1, 'Y'], [a3])).


fof(a4, axiom, [r(X, Y)] --> [p(X), q(Z) | q(Y)]).
fof(f4, plain, [r(X, Y)] --> [p(X), ![X] : (q(X) | q(Y))], inference(rightForall, [status(thm), 1, 'Z'], [a4])).


fof(a6, axiom, [(t(X) & u(X)), v(X)] --> [![X]: (p(X) & q(Z)), (r(X) | s(Y))]).
fof(f6, plain, [(t(X) & u(X)), v(X)] --> [![Y, X]: (p(X) & q(Y)), (r(X) | s(Y))], inference(rightForall, [status(thm), 0, 'Z'], [a6])).

fof(a7, axiom, [] --> [q, ![X]: (p(X) & q(Z)), s(Y)]).
fof(f7, plain, [] --> [q, ![X, Y]: (p(Y) & q(X)), s(Y)], inference(rightForall, [status(thm), 1, 'Z'], [a7])).

fof(a8, axiom, [] --> [q, ![X]: (p(X) & r(Z, Z)), s(Y)]).
fof(f8, plain, [] --> [q, ![X, Y]: (p(Y) & r(X, X)), s(Y)], inference(rightForall, [status(thm), 1, 'Z'], [a8])).
