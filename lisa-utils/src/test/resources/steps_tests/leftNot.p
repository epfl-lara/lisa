fof(a1, axiom, [] --> [p]).
fof(f1, plain, [~p] --> [], inference(leftNot, [status(thm), 0], [a1])).

fof(a2, axiom, [q] --> [r]).
fof(f2, plain, [~r, q] --> [], inference(leftNot, [status(thm), 0], [a2])).

fof(a3, axiom, [p, q] --> [r]).
fof(f3, plain, [~r, p, q] --> [], inference(leftNot, [status(thm), 0], [a3])).

fof(a4, axiom, [p(X)] --> [q(X)]).
fof(f4, plain, [~q(X), p(X)] --> [], inference(leftNot, [status(thm), 0], [a4])).

fof(a5, axiom, [p(X, Y)] --> [![Y] : q(Y)]).
fof(f5, plain, [~![Y] : q(Y), p(X, Y)] --> [], inference(leftNot, [status(thm), 0], [a5])).

fof(a6, axiom, [p(X) & q(Y)] --> [r(Z), ![X] : p(X) & q(Y)]).
fof(f6, plain, [p(X) & q(Y), ~r(Z)] --> [![X] : p(X) & q(Y)], inference(leftNot, [status(thm), 1], [a6])).

fof(a7, axiom, [] --> [r(c), ![X] : p(X)]).
fof(f7, plain, [~![Y] : p(Y)] --> [r(c)], inference(leftNot, [status(thm), 0], [a7])).