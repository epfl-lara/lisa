%--------------------------------------------------------------------------
% File     : lisa.maths.Tests.testThm : TPTP v8.0.0.
% Domain   : None
% Problem  : question0
% Version  : None
% English  :

% Refs     : https://github.com/epfl-lara/lisa
%          : lisa.utils.tptp.ProofParser
% Source   : [Lisa, lisa.maths.Tests.testThm]
% Names    : 

% Status   : Unknown
% Rating   : ?
% Syntax   : ?
% SPC      : FOF_UNK_RFO_SEQ

% Comments : This problem, was printed from a statement in a proof of a theorem by the Lisa theorem prover for submission to proof-producing ATPs.
%--------------------------------------------------------------------------
fof(a1, axiom, (Xx = sf(sf(sf(sf(sf(sf(sf(sf(Xx)))))))))).
fof(a2, axiom, (Xx = sf(sf(sf(sf(sf(Xx))))))).
fof(c3, conjecture, (Xx = sf(Xx))).


fof(f0, plain, [Xx = sf(sf(sf(sf(sf(sf(sf(sf(Xx)))))))), Xx = sf(sf(sf(sf(sf(Xx)))))] --> [Xx = Xx], inference(rightRefl, param(0), [])).
fof(f1, plain, [Xx = sf(sf(sf(sf(sf(sf(sf(sf(Xx)))))))), Xx = sf(sf(sf(sf(sf(Xx)))))] --> [Xx = sf(sf(sf(sf(sf(sf(sf(sf(Xx))))))))], inference(rightSubstEq, param(0, $fof(Xx = HOLE), $fot(HOLE)), [f0])).
fof(f2, plain, [Xx = sf(sf(sf(sf(sf(sf(sf(sf(Xx)))))))), Xx = sf(sf(sf(sf(sf(Xx)))))] --> [Xx = sf(sf(sf(Xx)))], inference(rightSubstEq, param(1, $fof(Xx = sf(sf(sf(HOLE)))), $fot(HOLE)), [f1])).
fof(f3, plain, [Xx = sf(sf(sf(sf(sf(sf(sf(sf(Xx)))))))), Xx = sf(sf(sf(sf(sf(Xx)))))] --> [Xx = sf(sf(sf(sf(sf(sf(sf(sf(sf(sf(sf(Xx)))))))))))], inference(rightSubstEq, param(0, $fof(Xx = sf(sf(sf(HOLE)))), $fot(HOLE)), [f2])).
fof(f4, plain, [Xx = sf(sf(sf(sf(sf(sf(sf(sf(Xx)))))))), Xx = sf(sf(sf(sf(sf(Xx)))))] --> [Xx = sf(sf(sf(sf(sf(sf(Xx))))))], inference(rightSubstEq, param(1, $fof(Xx = sf(sf(sf(sf(sf(sf(HOLE))))))), $fot(HOLE)), [f3])).
fof(f5, plain, [Xx = sf(sf(sf(sf(sf(sf(sf(sf(Xx)))))))), Xx = sf(sf(sf(sf(sf(Xx)))))] --> [Xx = sf(Xx)], inference(rightSubstEq, param(1, $fof(Xx = sf(HOLE)), $fot(HOLE)), [f4])).
fof(f6, plain, [Xx = sf(sf(sf(sf(sf(sf(sf(sf(Xx))))))))] --> [Xx = sf(Xx)], inference(cut, param(0, 1), [a2, f5])).
fof(f7, plain, [] --> [Xx = sf(Xx)], inference(cut, param(0, 0), [a1, f6])).