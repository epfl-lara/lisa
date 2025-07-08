fof(a1, axiom, [p, q] --> [r]).
fof(f1, plain, [![X] : p, q] --> [r], inference(leftForall, [status(thm), 0, $fot(X)], [a1])).

fof(a2, axiom, [a, p(X)] --> [r]).
fof(f2, plain, [a, ![X] : p(X)] --> [r], inference(leftForall, [status(thm), 1, $fot(X)], [a2])).

fof(a3, axiom, [P(X), Q(f(c))] --> [R]).
fof(f3, plain, [P(X), ![X] : Q(X)] --> [R], inference(leftForall, [status(thm), 1, $fot(f(c))], [a3])).


fof(a4, axiom, [p(X), q(g(Y, c)) | q(Y)] --> [r(X, Y)]).
fof(f4, plain, [p(X), ![X] : (q(X) | q(Y))] --> [r(X, Y)], inference(leftForall, [status(thm), 1, $fot(g(Y, c))], [a4])).


fof(a6, axiom, [![X]: (p(X) & q(f(c))), (r(X) | s(Y))] --> [(t(X) & u(X)), v(X)]).
fof(f6, plain, [![Y, X]: (p(X) & q(Y)), (r(X) | s(Y))] --> [(t(X) & u(X)), v(X)], inference(leftForall, [status(thm), 0, $fot(f(c))], [a6])).

fof(a7, axiom, [q, ![X]: (p(X) & q(f(c))), s(Y)] --> []).
fof(f7, plain, [q, ![X, Y]: (p(Y) & q(X)), s(Y)] --> [], inference(leftForall, [status(thm), 1, $fot(f(c))], [a7])).

fof(a7, axiom, [q, ![X]: (p(X) & r(f(c), f(c))), s(Y)] --> []).
fof(f7, plain, [q, ![X, Y]: (p(Y) & r(X, X)), s(Y)] --> [], inference(leftForall, [status(thm), 1, $fot(f(c))], [a7])).
