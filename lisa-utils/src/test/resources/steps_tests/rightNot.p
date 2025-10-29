fof(a1, axiom, [p] --> []).
fof(f1, plain, [] --> [~p], inference(rightNot, [status(thm), 0], [a1])).

fof(a2, axiom, [r] --> [q]).
fof(f2, plain, [] --> [~r, q], inference(rightNot, [status(thm), 0], [a2])).

fof(a3, axiom, [r, p] --> [q]).
fof(f3, plain, [p] --> [~r, q], inference(rightNot, [status(thm), 0], [a3])).

fof(a4, axiom, [q(X)] --> [p(X)]).
fof(f4, plain, [] --> [p(X), ~q(X)], inference(rightNot, [status(thm), 1], [a4])).

fof(a5, axiom, [![Y] : q(Y)] --> [p(X, Y)]).
fof(f5, plain, [] --> [~![Y] : q(Y), p(X, Y)], inference(rightNot, [status(thm), 0], [a5])).

fof(a6, axiom, [r(Z), ![X] : (p(X) & q(Y))] --> [p(X) & q(Y)]).
fof(f6, plain, [r(Z)] --> [p(X) & q(Y), ~![X] :( p(X) & q(Y))], inference(rightNot, [status(thm), 1], [a6])).

fof(a7, axiom, [r(c), ![X] : p(X)] --> []).
fof(f7, plain, [r(c)] --> [~![Y] : p(Y)], inference(rightNot, [status(thm), 0], [a7])).
