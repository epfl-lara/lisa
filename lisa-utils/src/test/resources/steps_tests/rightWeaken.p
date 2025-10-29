
fof(a1, axiom, [p] --> []).
fof(f1, plain, [p] --> [q], inference(rightWeaken, [status(thm), 0], [a1])).
fof(f2, plain, [p] --> [q, P(X)], inference(rightWeaken, [status(thm), 1], [f1])).
fof(f3, plain, [p] --> [q, P(X), Q(X, c)], inference(rightWeaken, [status(thm), 2], [f2])).
fof(f4, plain, [p] --> [q, ![X] : (P(X) | Q(a, X)), P(X), Q(X, c)], inference(rightWeaken, [status(thm), 1], [f3])).
fof(f5, plain, [p] --> [q, ![X] : (P(X) | Q(a, X)), P(X), Q(X, c)], inference(rightWeaken, [status(thm), 2], [f4])).
fof(f6, plain, [p] --> [q, ![Y] : (P(Y) | Q(a, Y)), P(X), Q(X, c), p1 => p2], inference(rightWeaken, [status(thm), 4], [f5])).




