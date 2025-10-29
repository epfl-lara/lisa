fof(a1, axiom, [q(X)] --> []).
fof(f1, plain, [q(b)] --> [], inference(instMult, [status(thm), [tuple3('X', $fot(b), [])]], [a1])).

fof(a2, axiom, [q(g(X, f(X)))] --> []).
fof(f2, plain, [q(g(f(c), f(f(c))))] --> [], inference(instMult, [status(thm), [tuple3('X', $fot(f(c)), [])]], [a2])).

fof(a3, axiom, [q(X), q(g(X, f(X)))] --> [q(g(f(X, Y)))]).
fof(f3, plain, [q(f(b)), q(g(f(b), f(f(b))))] --> [q(g(f(f(b), Y)))], inference(instMult, [status(thm), [tuple3('X', $fot(f(b)), [])]], [a3])).


fof(a4, axiom, [![X] : q(g(X, f(Y)))] --> [q(g(f(X, Y)))]).
fof(f4, plain, [![Z] : q(g(Z, f(f(X))))] --> [q(g(f(X, f(X))))], inference(instMult, [status(thm), [tuple3('Y', $fot(f(X)), [])]], [a4])).

fof(a5, axiom, [![X] : q(g(X, f(Y)))] --> [q(g(f(X, Y)))]).
fof(f5, plain, [![Y] : q(g(Y, f(f(X))))] --> [q(g(f(X, f(X))))], inference(instMult, [status(thm), [tuple3('Y', $fot(f(X)), [])]], [a5])).


fof(a6, axiom, [~(A | ~A)] --> []).
fof(f6, plain, [~(~p(b) | ~(~p(b)) )] --> [], inference(instMult, [status(thm), [tuple3('A', $fof(~p(b)), [])]], [a6])).

fof(a7, axiom, [A, (A & ~p(b))] --> [(~A) => B]).
fof(f7, plain, [~p(B), (~p(B) & ~p(b))] --> [(~~p(B)) => B], inference(instMult, [status(thm), [tuple3('A', $fof(~p(B)), [])]], [a7])).

fof(a8, axiom, [![X] : P(b, X)] --> []).
fof(f8, plain, [![A] : p(A, Z)] --> [], inference(instMult, [status(thm), [tuple3('P', $fof(p(Y, Z)), ['X', 'Y'])]], [a8])).


fof(a9, axiom, [![X] : P(Y, X)] --> []).
fof(f9, plain, [![A] : p(A, f(X))] --> [], inference(instMult, [status(thm), [tuple3('P', $fof(p(Y, X)), ['X', 'Y']), tuple3('Y', $fot(f(X)), [])]], [a9])).


