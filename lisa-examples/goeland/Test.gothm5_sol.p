
% SZS output start Proof for Test.gothm5.p


fof(c_Test_gothm5_p, conjecture, ((! [Xx4] : (sE(Xx4, Xx4))) => (! [Xx6] : (sE(sf(Xx6), sf(Xx6)))))).

fof(f6, plain, [~(((! [Xx4] : (sE(Xx4, Xx4))) => (! [Xx6] : (sE(sf(Xx6), sf(Xx6)))))), (! [Xx4] : (sE(Xx4, Xx4))), ~((! [Xx6] : (sE(sf(Xx6), sf(Xx6))))), ~(sE(sf(Sko_0), sf(Sko_0))), sE(sf(Sko_0), sf(Sko_0))] --> [], inference(leftHyp, param(4, 3), [])).

fof(f5, plain, [~(((! [Xx4] : (sE(Xx4, Xx4))) => (! [Xx6] : (sE(sf(Xx6), sf(Xx6)))))), (! [Xx4] : (sE(Xx4, Xx4))), ~((! [Xx6] : (sE(sf(Xx6), sf(Xx6))))), ~(sE(sf(Sko_0), sf(Sko_0)))] --> [], inference(leftForall, param(1, $fot(sf(Sko_0))), [f6])).

fof(f4, plain, [~(((! [Xx4] : (sE(Xx4, Xx4))) => (! [Xx6] : (sE(sf(Xx6), sf(Xx6)))))), (! [Xx4] : (sE(Xx4, Xx4))), ~((! [Xx6] : (sE(sf(Xx6), sf(Xx6)))))] --> [], inference(leftNotForall, param(2, $fot(Sko_0)), [f5])).

fof(f3, plain, [~(((! [Xx4] : (sE(Xx4, Xx4))) => (! [Xx6] : (sE(sf(Xx6), sf(Xx6))))))] --> [], inference(leftNotImp, param(0), [f4])).

fof(f2, plain, [((! [Xx4] : (sE(Xx4, Xx4))) => (! [Xx6] : (sE(sf(Xx6), sf(Xx6)))))] --> [((! [Xx4] : (sE(Xx4, Xx4))) => (! [Xx6] : (sE(sf(Xx6), sf(Xx6)))))], inference(hyp, param(0, 0), [])).

fof(f1, plain, [] --> [((! [Xx4] : (sE(Xx4, Xx4))) => (! [Xx6] : (sE(sf(Xx6), sf(Xx6))))), ~(((! [Xx4] : (sE(Xx4, Xx4))) => (! [Xx6] : (sE(sf(Xx6), sf(Xx6))))))], inference(rightNot, param(1), [f2])).

fof(f0, plain, [] --> [((! [Xx4] : (sE(Xx4, Xx4))) => (! [Xx6] : (sE(sf(Xx6), sf(Xx6)))))], inference(cut, param(1, 0), [f1, f3])).



% SZS output end Proof for Test.gothm5.p
