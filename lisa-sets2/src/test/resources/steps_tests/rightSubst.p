fof(a1, axiom, [] --> [q(a)]).
fof(f1, plain, [a = b] --> [q(b)], inference(rightSubst, [status(thm), 0, $fof(q(X)), 'X'], [a1])).

fof(a2, axiom, [] --> [q(g(a, f(c)))]).
fof(f2, plain, [a = b] --> [q(g(b, f(c)))], inference(rightSubst, [status(thm), 0, $fof(q(g(X, f(c)))), 'X'], [a2])).

fof(a3, axiom, [] --> [q(g(a, f(a)))]).
fof(f3, plain, [a = b] --> [q(g(b, f(a)))], inference(rightSubst, [status(thm), 0, $fof(q(g(X, f(a)))), 'X'], [a3])).

fof(a3, axiom, [] --> [q(g(a, f(a)))]).
fof(f3, plain, [a = b] --> [q(g(b, f(b)))], inference(rightSubst, [status(thm), 0, $fof(q(g(X, f(X)))), 'X'], [a3])).

fof(a4, axiom, [] --> [![X] : q(g(X, f(c)))]).
fof(f4, plain, [f(c) = g(c, c)] --> [![X] : q(g(X, g(c, c)))], inference(rightSubst, [status(thm), 0, $fof(![Z] : q(g(Z, X))), 'X'], [a4])).

