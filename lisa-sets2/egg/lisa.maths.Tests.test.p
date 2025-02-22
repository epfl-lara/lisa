%--------------------------------------------------------------------------
% File     : lisa.maths.Tests.test : TPTP v8.0.0.
% Domain   : None
% Problem  : question0
% Version  : None
% English  :

% Refs     : https://github.com/epfl-lara/lisa
%          : lisa.utils.tptp.ProofParser
% Source   : [Lisa, lisa.maths.Tests.test]
% Names    : 

% Status   : Unknown
% Rating   : ?
% Syntax   : ?
% SPC      : FOF_UNK_RFO_SEQ

% Comments : This problem, was printed from a statement in a proof of a theorem by the Lisa theorem prover for submission to proof-producing ATPs.
%--------------------------------------------------------------------------
fof(a1, axiom, ((! [Xy]: ((Xy = sf(sf(sf(sf(sf(Xy)))))))) => (cemptySet = sf(cemptySet)))).
fof(c2, conjecture, ($true => (! [Xx]: ((Xx = sf(sf(sf(sf(sf(sf(sf(sf(Xx))))))))))))).

