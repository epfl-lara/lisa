% SZS status Theorem for SEU140+2.p
% SZS output start CNFRefutation for SEU140+2.p
fof(d3_tarski, axiom, ! [X0] : ! [X1] : ((subset(X0,X1) <=> ! [X2] : ((in(X2,X0) => in(X2,X1)))))).
fof(symmetry_r1_xboole_0, axiom, ! [X0] : ! [X1] : ((disjoint(X0,X1) => disjoint(X1,X0)))).
fof(t3_xboole_0, lemma, ! [X0] : ! [X1] : ((~((~disjoint(X0,X1) & ! [X2] : ~((in(X2,X0) & in(X2,X1))))) & ~((? [X2] : ((in(X2,X0) & in(X2,X1))) & disjoint(X0,X1)))))).
fof(t63_xboole_1, conjecture, ! [X0] : ! [X1] : ! [X2] : (((subset(X0,X1) & disjoint(X1,X2)) => disjoint(X0,X2)))).
fof(negated_conjecture, negated_conjecture, ~! [X0] : ! [X1] : ! [X2] : (((subset(X0,X1) & disjoint(X1,X2)) => disjoint(X0,X2))), inference(negate_conjecture, [status(cth)], [t63_xboole_1])).
cnf(c20, plain, ~subset(X0,X1) | ~in(X2,X0) | in(X2,X1), inference(clausification, [status(esa)], [d3_tarski])).
cnf(c61, plain, ~disjoint(X0,X1) | disjoint(X1,X0), inference(clausification, [status(esa)], [symmetry_r1_xboole_0])).
cnf(c81, plain, disjoint(X0,X1) | in(sK90(X0,X1),X0), inference(clausification, [status(esa)], [t3_xboole_0])).
cnf(c82, plain, disjoint(X0,X1) | in(sK90(X0,X1),X1), inference(clausification, [status(esa)], [t3_xboole_0])).
cnf(c83, plain, ~in(X0,X1) | ~in(X0,X2) | ~disjoint(X1,X2), inference(clausification, [status(esa)], [t3_xboole_0])).
cnf(c97, plain, subset(sK116,sK117), inference(clausification, [status(esa)], [negated_conjecture])).
cnf(c98, plain, disjoint(sK117,sK118), inference(clausification, [status(esa)], [negated_conjecture])).
cnf(c99, plain, ~disjoint(sK116,sK118), inference(clausification, [status(esa)], [negated_conjecture])).
cnf(d0, plain, in(X0,sK117) | ~in(X0,sK116), inference(resolution, [status(thm)], [c20,c97])).
cnf(d1, plain, disjoint(X0,sK116) | in(sK90(X0,sK116),sK117), inference(resolution, [status(thm)], [c82,d0])).
cnf(d2, plain, disjoint(sK118,sK117), inference(resolution, [status(thm)], [c61,c98])).
cnf(d3, plain, ~in(X0,sK118) | ~in(X0,sK117), inference(resolution, [status(thm)], [c83,d2])).
cnf(d4, plain, ~in(sK90(sK118,X0),sK117) | disjoint(sK118,X0), inference(resolution, [status(thm)], [d3,c81])).
cnf(d5, plain, disjoint(sK118,sK116) | disjoint(sK118,sK116), inference(resolution, [status(thm)], [d4,d1])).
cnf(d6, plain, disjoint(sK116,sK118), inference(resolution, [status(thm)], [d5,c61])).
cnf(d7, plain, $false, inference(resolution, [status(thm)], [c99,d6])).
% SZS output end CNFRefutation for SEU140+2.p