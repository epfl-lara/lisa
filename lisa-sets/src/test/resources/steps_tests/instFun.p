fof(a1, axiom, [q(X)] --> []).
fof(f1, plain, [q(b)] --> [], inference(instFun, [status(thm), 'X', $fot(b), []], [a1])).

fof(a2, axiom, [q(g(X, f(X)))] --> []).
fof(f2, plain, [q(g(f(c), f(f(c))))] --> [], inference(instFun, [status(thm), 'X', $fot(f(c)), []], [a2])).

fof(a3, axiom, [q(X), q(g(X, f(X)))] --> [q(g(f(X, Y)))]).
fof(f3, plain, [q(f(b)), q(g(f(b), f(f(b))))] --> [q(g(f(f(b), Y)))], inference(instFun, [status(thm), 'X', $fot(f(b)), []], [a3])).


fof(a4, axiom, [![X] : q(g(X, f(Y)))] --> [q(g(f(X, Y)))]).
fof(f4, plain, [![Z] : q(g(Z, f(f(X))))] --> [q(g(f(X, f(X))))], inference(instFun, [status(thm), 'Y', $fot(f(X)), []], [a4])).

fof(a5, axiom, [![X] : q(g(X, f(Y)))] --> [q(g(f(X, Y)))]).
fof(f5, plain, [![Y] : q(g(Y, f(f(X))))] --> [q(g(f(X, f(X))))], inference(instFun, [status(thm), 'Y', $fot(f(X)), []], [a5])).

fof(a6, axiom, [q(F(c))] --> []).
fof(f6, plain, [q(g(c, c))] --> [], inference(instFun, [status(thm), 'F', $fot(g(X, X)), ['X']], [a6])).

fof(a7, axiom, [q(G(X, f(c)))] --> []).
fof(f7, plain, [q(g(F(f(c)), F(F(X))))] --> [], inference(instFun, [status(thm), 'G', $fot(g(F(Y), F(F(X)))), ['X', 'Y']], [a7])).

fof(a8, axiom, [![X] : q(G(X, f(c)))] --> []).
fof(f8, plain, [![X] : q(g(F(f(c)), F(F(X))))] --> [], inference(instFun, [status(thm), 'G', $fot(g(F(Y), F(F(X)))), ['X', 'Y']], [a8])).


fof(a9, axiom, [![X] : q(G(X, f(c)))] --> [?[Y] : q(G(b, f(Y)))]).
fof(f9, plain, [![X] : q(g(F(f(c)), F(F(X))))] --> [?[Y] : q(g(F(f(Y)), F(F(b))))], inference(instFun, [status(thm), 'G', $fot(g(F(Y), F(F(X)))), ['X', 'Y']], [a9])).


