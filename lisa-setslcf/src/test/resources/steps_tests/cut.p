fof(a1_1, axiom, [p] --> [q]).
fof(a1_2, axiom, [q] --> [r]).
fof(f1, plain, [p] --> [r], inference(cut, [status(thm), 0], [a1_1, a1_2])).

fof(a2_1, axiom, [p, q] --> [r, s]).
fof(a2_2, axiom, [s, t] --> [u, v]).
fof(f2, plain, [p, q, t] --> [r, u, v], inference(cut, [status(thm), 1], [a2_1, a2_2])).

fof(a3_1, axiom, [p(X) & Q(X, Y), r(Y)] --> [s(X, c)]).
fof(a3_2, axiom, [s(X, c)] --> [r(t)]).
fof(f3, plain, [p(X) & Q(X, Y), r(Y)] --> [r(t)], inference(cut, [status(thm), 0], [a3_1, a3_2])).


fof(a4_1, axiom, [![X, Y] : (p(X) & Q(X, Y)), r(Y)] --> [![X] : s(X, c)]).
fof(a4_2, axiom, [![X] : s(X, c)] --> [![Y] : r(f(t))]).
fof(f4, plain, [![X, Y] : (p(X) & Q(X, Y)), r(Y)] --> [![Y] : r(f(t))], inference(cut, [status(thm), 0], [a4_1, a4_2])).


%fof(a4_1, axiom, [![X, Y] : (p(X) & Q(#[X] : p(X), Y)), r(Y)] --> [![X] : s(X, c)]).
%fof(a4_2, axiom, [![X] : s(X, c)] --> [![Y] : r(f(t))]).
%fof(f4, plain, [![X, Y] : (p(X) & Q(#[X] : p(X), Y)), r(Y)] --> [![Y] : r(f(t))], inference(cut, [status(thm), 0], [a4_1, a4_2])).