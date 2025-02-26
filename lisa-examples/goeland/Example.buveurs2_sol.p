
% SZS output start Proof for Example.buveurs2.p


fof(c_Example_buveurs2_p, conjecture, ($true => (? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6)))))))).

fof(f9, plain, [~(($true => (? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6)))))))), $true, ~((? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6))))))), ~((sP(XX4_8) => (! [Xy6] : (sP(Xy6))))), sP(XX4_8), ~((! [Xy6] : (sP(Xy6)))), ~(sP(Sko_0)), ~((sP(Sko_0) => (! [Xy6] : (sP(Xy6))))), sP(Sko_0)] --> [], inference(leftHyp, param(8, 6), [])).

fof(f8, plain, [~(($true => (? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6)))))))), $true, ~((? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6))))))), ~((sP(XX4_8) => (! [Xy6] : (sP(Xy6))))), sP(XX4_8), ~((! [Xy6] : (sP(Xy6)))), ~(sP(Sko_0)), ~((sP(Sko_0) => (! [Xy6] : (sP(Xy6)))))] --> [], inference(leftNotImp, param(7), [f9])).

fof(f7, plain, [~(($true => (? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6)))))))), $true, ~((? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6))))))), ~((sP(XX4_8) => (! [Xy6] : (sP(Xy6))))), sP(XX4_8), ~((! [Xy6] : (sP(Xy6)))), ~(sP(Sko_0))] --> [], inference(leftNotEx, param(2, $fot(Sko_0)), [f8])).

fof(f6, plain, [~(($true => (? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6)))))))), $true, ~((? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6))))))), ~((sP(XX4_8) => (! [Xy6] : (sP(Xy6))))), sP(XX4_8), ~((! [Xy6] : (sP(Xy6))))] --> [], inference(leftNotForall, param(5, $fot(Sko_0)), [f7])).

fof(f5, plain, [~(($true => (? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6)))))))), $true, ~((? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6))))))), ~((sP(XX4_8) => (! [Xy6] : (sP(Xy6)))))] --> [], inference(leftNotImp, param(3), [f6])).

fof(f4, plain, [~(($true => (? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6)))))))), $true, ~((? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6)))))))] --> [], inference(leftNotEx, param(2, $fot(XX4_8)), [f5])).

fof(f3, plain, [~(($true => (? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6))))))))] --> [], inference(leftNotImp, param(0), [f4])).

fof(f2, plain, [($true => (? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6)))))))] --> [($true => (? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6)))))))], inference(hyp, param(0, 0), [])).

fof(f1, plain, [] --> [($true => (? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6))))))), ~(($true => (? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6))))))))], inference(rightNot, param(1), [f2])).

fof(f0, plain, [] --> [($true => (? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6)))))))], inference(cut, param(1, 0), [f1, f3])).



% SZS output end Proof for Example.buveurs2.p
