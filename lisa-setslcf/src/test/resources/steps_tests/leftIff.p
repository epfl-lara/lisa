fof(a1, axiom, [p=>q, q=>p] --> [r]).
fof(f1, plain, [p<=>q] --> [r], inference(leftIff, [status(thm), 0], [a1])).

fof(a2, axiom, [a, p=>q, q=>p] --> [r]).
fof(f2, plain, [a, p <=> q] --> [r], inference(leftIff, [status(thm), 1], [a2])).

fof(a3, axiom, [P(X)=>Q(X), Q(X)=>P(X)] --> [R]).
fof(f3, plain, [P(X) <=> Q(X)] --> [R], inference(leftIff, [status(thm), 0], [a3])).

fof(a4, axiom, [s, p=>q, t, q=>p] --> [u]).
fof(f4, plain, [s, p <=> q, t] --> [u], inference(leftIff, [status(thm), 1], [a4])).

fof(a5, axiom, [p(X)=>q(Y), q(Y)=>p(X)] --> [r(X, Y)]).
fof(f5, plain, [p(X) <=> q(Y)] --> [r(X, Y)], inference(leftIff, [status(thm), 0], [a5])).


fof(a6, axiom, [![X]: (p(X)) => (r(X) | s(X)), (r(X) | s(X)) => ![X]: (p(X))] --> [(t(X) & u(X)), v(X)]).
fof(f6, plain, [![X]: (p(X)) <=> (r(X) | s(X)), (r(X) | s(X)) => ![X]: (p(X))] --> [(t(X) & u(X)), v(X)], inference(leftIff, [status(thm), 0], [a6])).

fof(a7, axiom, [q=>s(Y), ![X]: (p(X) & q(X)), s(Y)=>q] --> []).
fof(f7, plain, [![X]: (p(X) & q(X)), q <=> s(Y)] --> [], inference(leftIff, [status(thm), 1], [a7])).
