fof(f1, plain, [p] --> [p], inference(hyp, [status(thm), 0], [])).
fof(f3, plain, [p, q] --> [p], inference(hyp, [status(thm), 0], [])).
fof(f4, plain, [q] --> [p, q], inference(hyp, [status(thm), 0], [])).
fof(f5, plain, [p, q] --> [r, q], inference(hyp, [status(thm), 1], [])).
fof(f6, plain, [p & q] --> [p & q], inference(hyp, [status(thm), 0], [])).
fof(f7, plain, [p | q] --> [p | q], inference(hyp, [status(thm), 0], [])).
fof(f8, plain, [p => q] --> [p => q], inference(hyp, [status(thm), 0], [])).
fof(f9, plain, [p(X, c) => q(X)] --> [p(X, c) => q(X)], inference(hyp, [status(thm), 0], [])).
fof(f10, plain, [![X] :( p(X, c) => q(X))] --> [![X] : (p(X, c) => q(X))], inference(hyp, [status(thm), 0], [])).
fof(f11, plain, [![X] : (p(X, c) => q(X))] --> [![Y] : (p(Y, c) => q(Y))], inference(hyp, [status(thm), 0], [])).
fof(f12, plain, [?[Y] : ![X] : (p(X, c) => q(X))] --> [?[X] : ![Y] : (p(Y, c) => q(Y))], inference(hyp, [status(thm), 0], [])).
fof(f13, plain, [?[Y] : ![X] : (p(X, c) => q(Y))] --> [?[X] : ![Y] : (p(Y, c) => q(X))], inference(hyp, [status(thm), 0], [])).

