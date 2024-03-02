
% SZS output start Proof for Test.gothm6.p


fof(c_Test_gothm6_p, conjecture, ((! [Xy6] : ((! [Xx8] : (sE(Xx8, Xy6))))) => (! [Xy10] : ((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Xy10)))))))).

fof(f8, plain, [~(((! [Xy6] : ((! [Xx8] : (sE(Xx8, Xy6))))) => (! [Xy10] : ((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Xy10)))))))), (! [Xy6] : ((! [Xx8] : (sE(Xx8, Xy6))))), ~((! [Xy10] : ((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Xy10))))))), ~((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Sko_0))))), ~(sE(sf(Sko_1), sh(Sko_1, Sko_0))), (! [Xx8] : (sE(Xx8, sh(Sko_1, Sko_0)))), sE(sf(Sko_1), sh(Sko_1, Sko_0))] --> [], inference(leftHyp, param(6, 4), [])).

fof(f7, plain, [~(((! [Xy6] : ((! [Xx8] : (sE(Xx8, Xy6))))) => (! [Xy10] : ((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Xy10)))))))), (! [Xy6] : ((! [Xx8] : (sE(Xx8, Xy6))))), ~((! [Xy10] : ((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Xy10))))))), ~((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Sko_0))))), ~(sE(sf(Sko_1), sh(Sko_1, Sko_0))), (! [Xx8] : (sE(Xx8, sh(Sko_1, Sko_0))))] --> [], inference(leftForall, param(5, $fot(sf(Sko_1))), [f8])).

fof(f6, plain, [~(((! [Xy6] : ((! [Xx8] : (sE(Xx8, Xy6))))) => (! [Xy10] : ((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Xy10)))))))), (! [Xy6] : ((! [Xx8] : (sE(Xx8, Xy6))))), ~((! [Xy10] : ((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Xy10))))))), ~((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Sko_0))))), ~(sE(sf(Sko_1), sh(Sko_1, Sko_0)))] --> [], inference(leftForall, param(1, $fot(sh(Sko_1, Sko_0))), [f7])).

fof(f5, plain, [~(((! [Xy6] : ((! [Xx8] : (sE(Xx8, Xy6))))) => (! [Xy10] : ((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Xy10)))))))), (! [Xy6] : ((! [Xx8] : (sE(Xx8, Xy6))))), ~((! [Xy10] : ((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Xy10))))))), ~((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Sko_0)))))] --> [], inference(leftNotForall, param(3, $fot(Sko_1)), [f6])).

fof(f4, plain, [~(((! [Xy6] : ((! [Xx8] : (sE(Xx8, Xy6))))) => (! [Xy10] : ((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Xy10)))))))), (! [Xy6] : ((! [Xx8] : (sE(Xx8, Xy6))))), ~((! [Xy10] : ((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Xy10)))))))] --> [], inference(leftNotForall, param(2, $fot(Sko_0)), [f5])).

fof(f3, plain, [~(((! [Xy6] : ((! [Xx8] : (sE(Xx8, Xy6))))) => (! [Xy10] : ((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Xy10))))))))] --> [], inference(leftNotImp, param(0), [f4])).

fof(f2, plain, [((! [Xy6] : ((! [Xx8] : (sE(Xx8, Xy6))))) => (! [Xy10] : ((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Xy10)))))))] --> [((! [Xy6] : ((! [Xx8] : (sE(Xx8, Xy6))))) => (! [Xy10] : ((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Xy10)))))))], inference(hyp, param(0, 0), [])).

fof(f1, plain, [] --> [((! [Xy6] : ((! [Xx8] : (sE(Xx8, Xy6))))) => (! [Xy10] : ((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Xy10))))))), ~(((! [Xy6] : ((! [Xx8] : (sE(Xx8, Xy6))))) => (! [Xy10] : ((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Xy10))))))))], inference(rightNot, param(1), [f2])).

fof(f0, plain, [] --> [((! [Xy6] : ((! [Xx8] : (sE(Xx8, Xy6))))) => (! [Xy10] : ((! [Xx12] : (sE(sf(Xx12), sh(Xx12, Xy10)))))))], inference(cut, param(1, 0), [f1, f3])).



% SZS output end Proof for Test.gothm6.p
