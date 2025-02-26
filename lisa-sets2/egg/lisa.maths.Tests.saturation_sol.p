%--------------------------------------------------------------------------
% File     : lisa.maths.Tests.saturation : TPTP v8.0.0.
% Domain   : None
% Problem  : question0
% Version  : None
% English  : 

% Refs     : https://github.com/epfl-lara/lisa
%          : lisa.utils.tptp.ProofParser
% Source   : [Lisa, lisa.maths.Tests.saturation]
% Names    : 

% Status   : Theorem
% Rating   : ?
% Syntax   : ?
% SPC      : FOF_UNK_RFO_SEQ

% Comments : This problem, was printed from a statement in a proof of a theorem by the Lisa theorem prover for submission to proof-producing ATPs.
% Solver   : egg v0.9.5
%          : egg-sc-tptp v0.1.0
%--------------------------------------------------------------------------
fof(a1, axiom, (! [Xx]: ((Xx = sf(sf(sf(Xx))))))).
fof(a2, axiom, (! [Xx]: ((! [Xy]: ((Xx = sf(sf(Xx)))))))).
fof(c3, conjecture, (cemptySet = sf(cemptySet))).


fof(f0, plain, [] --> [(cemptySet = cemptySet)], inference(rightRefl, [status(thm), 0], [])).
fof(f1, plain, [(cemptySet = sf(sf(sf(cemptySet))))] --> [(cemptySet = sf(sf(sf(cemptySet))))], inference(rightSubst, [status(thm), 0, 0, $fof((cemptySet = HOLE)), 'HOLE'], [f0])).
fof(f2, plain, [![Xx] : (Xx = sf(sf(sf(Xx))))] --> [(cemptySet = sf(sf(sf(cemptySet))))], inference(leftForall, [status(thm), 0, $fot(cemptySet)], [f1])).
fof(f3, plain, [] --> [(cemptySet = sf(sf(sf(cemptySet))))], inference(cut, [status(thm), 0], [a1, f2])).
fof(f4, plain, [(sf(cemptySet) = sf(sf(sf(cemptySet))))] --> [(cemptySet = sf(cemptySet))], inference(rightSubst, [status(thm), 0, 1, $fof((cemptySet = HOLE)), 'HOLE'], [f3])).
fof(f5, plain, [![Xy] : (sf(cemptySet) = sf(sf(sf(cemptySet))))] --> [(cemptySet = sf(cemptySet))], inference(leftForall, [status(thm), 0, $fot(Xy)], [f4])).
fof(f6, plain, [![Xx, Xy] : (Xx = sf(sf(Xx)))] --> [(cemptySet = sf(cemptySet))], inference(leftForall, [status(thm), 0, $fot(sf(cemptySet))], [f5])).
fof(f7, plain, [] --> [(cemptySet = sf(cemptySet))], inference(cut, [status(thm), 0], [a2, f6])).