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


%fof(a1, axiom, ![Xx]: Xx = sf(sf(Xx))).
%fof(a2, axiom, [] --> [![Xx, Yy]: Yy = sf(sf(sf(Yy)))]).
fof(c3, conjecture, [sp(Zz), ![Xx, Yy]: Yy = sf(sf(sf(Yy))), ![Xx]: Xx = sf(sf(Xx))] --> [sg(cx) = sf(sg(cx))]).
fof(f0, plain, [sp(Zz), ![Xx,Yy]:Yy=sf(sf(sf(Yy))), ![Xx]:Xx=sf(sf(Xx))] --> [sg(cx) = sg(cx)], inference(rightRefl, param(0), [])).
fof(f1, plain, [sg(cx) = sf(sf(sf(sg(cx)))), sp(Zz), ![Xx,Yy]:Yy=sf(sf(sf(Yy))), ![Xx]:Xx=sf(sf(Xx))] --> [sg(cx) = sf(sf(sf(sg(cx))))], inference(rightSubstEq, param(0, $fof(sg(cx) = HOLE), $fot(HOLE)), [f0])).
fof(f2, plain, [![Yy]: Yy = sf(sf(sf(Yy))), sp(Zz), ![Xx,Yy]:Yy=sf(sf(sf(Yy))), ![Xx]:Xx=sf(sf(Xx))] --> [sg(cx) = sf(sf(sf(sg(cx))))], inference(leftForall, param(0, $fot(sg(cx))), [f1])).
fof(f3, plain, [sp(Zz), ![Xx,Yy]:Yy=sf(sf(sf(Yy))), ![Xx]:Xx=sf(sf(Xx))] --> [sg(cx) = sf(sf(sf(sg(cx))))], inference(leftForall, param(1, $fot(Xx)), [f2])).

fof(f4, plain, [sf(sg(cx)) = sf(sf(sf(sg(cx)))), sp(Zz), ![Xx,Yy]:Yy=sf(sf(sf(Yy))), ![Xx]:Xx=sf(sf(Xx))] --> [sg(cx) = sf(sg(cx))], inference(rightSubstEq, param(0, $fof(sg(cx) = HOLE), $fot(HOLE)), [f3])).
fof(f5, plain, [sp(Zz), ![Xx,Yy]:Yy=sf(sf(sf(Yy))), ![Xx]:Xx=sf(sf(Xx))] --> [sg(cx) = sf(sg(cx))], inference(leftForall, param(2, $fot(sf(sg(cx)))), [f4])).
