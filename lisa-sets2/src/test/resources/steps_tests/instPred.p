fof(a1, axiom, [A] --> []).
fof(f1, plain, [p(b, c) ] --> [], inference(instPred, [status(thm), 'A', $fof(p(b, c)), []], [a1])).

fof(a2, axiom, [~(A | ~A)] --> []).
fof(f2, plain, [~(~p(b) | ~(~p(b)) )] --> [], inference(instPred, [status(thm), 'A', $fof(~p(b)), []], [a2])).

fof(a3, axiom, [A, (A & ~p(b))] --> [(~A) => B]).
fof(f3, plain, [~p(B), (~p(B) & ~p(b))] --> [(~~p(B)) => B], inference(instPred, [status(thm), 'A', $fof(~p(B)), []], [a3])).

fof(a4, axiom, [![X] : P(b, X)] --> []).
fof(f4, plain, [![A] : p(A, Z)] --> [], inference(instPred, [status(thm), 'P', $fof(p(Y, Z)), ['X', 'Y']], [a4])).

fof(a5, axiom, [![X] : P(X, f(Y))] --> []).
fof(f5, plain, [![X] : P(f(Y), f(f(X)))] --> [], inference(instPred, [status(thm), 'P', $fof(P(Y, f(f(X)))), ['X', 'Y']], [a5])).

fof(a6, axiom, [P(a, b) & ~P(c, d)] --> []).
fof(f6, plain, [P(X, f(a)) & ~P(X, f(c))] --> [], inference(instPred, [status(thm), 'P', $fof(P(X, f(Y))), ['Y', 'Z']], [a6])).

fof(a7, axiom, [![X] : P(X, c)] --> []).
fof(f7, plain, [![X] :( q(X) | ![Y] : p(Y, c))] --> [], 
      inference(instPred, [status(thm), 'P', $fof(q(X) | ![X] : p(X, Y)), ['X', 'Y']], [a7])).

fof(a8, axiom, [![X] : P(X, f(c))] --> [?[Y] : P(b, f(Y))]).
fof(f8, plain, [![X] : (q(X) | ![Y] : ~q(Y, f(f(c))))] --> [?[Z] : (q(b) | ![X] : ~(q(X, f(f(Z)))))], 
      inference(instPred, [status(thm), 'P', $fof(q(X) | ![X] : ~(q(X, f(Y)))), ['X', 'Y']], [a8])).


%fof(a8, axiom, [![X] : P(X, #[Y] : (Q(X) & P(X, Y)))] --> []).
%fof(f8, plain, [![X] :( q(X) | ![Z] : p(Z, #[Y] : (Q(X) & P(X, Y))))] --> [], 
%      inference(instPred, [status(thm), 'P', $fof(q(X) | ![X] : p(X, Y)), ['X', 'Y']], [a8])).