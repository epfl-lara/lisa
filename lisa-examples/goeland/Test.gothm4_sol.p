
% SZS output start Proof for Test.gothm4.p


fof(c_Test_gothm4_p, conjecture, ($true => (? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6)))))))).

fof(f10, plain, [~(($true => (? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6)))))))), $true, ~((? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6))))))), ~((! [Xy6] : ((sQ(XX4_8) => sQ(Xy6))))), ~((sQ(XX4_8) => sQ(Sko_0))), sQ(XX4_8), ~(sQ(Sko_0)), ~((! [Xy6] : ((sQ(Sko_0) => sQ(Xy6))))), ~((sQ(Sko_0) => sQ(Sko_1))), sQ(Sko_0), ~(sQ(Sko_1))] --> [], inference(leftHyp, param(9, 6), [])).

fof(f9, plain, [~(($true => (? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6)))))))), $true, ~((? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6))))))), ~((! [Xy6] : ((sQ(XX4_8) => sQ(Xy6))))), ~((sQ(XX4_8) => sQ(Sko_0))), sQ(XX4_8), ~(sQ(Sko_0)), ~((! [Xy6] : ((sQ(Sko_0) => sQ(Xy6))))), ~((sQ(Sko_0) => sQ(Sko_1)))] --> [], inference(leftNotImp, param(8), [f10])).

fof(f8, plain, [~(($true => (? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6)))))))), $true, ~((? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6))))))), ~((! [Xy6] : ((sQ(XX4_8) => sQ(Xy6))))), ~((sQ(XX4_8) => sQ(Sko_0))), sQ(XX4_8), ~(sQ(Sko_0)), ~((! [Xy6] : ((sQ(Sko_0) => sQ(Xy6)))))] --> [], inference(leftNotForall, param(7, $fot(Sko_1)), [f9])).

fof(f7, plain, [~(($true => (? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6)))))))), $true, ~((? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6))))))), ~((! [Xy6] : ((sQ(XX4_8) => sQ(Xy6))))), ~((sQ(XX4_8) => sQ(Sko_0))), sQ(XX4_8), ~(sQ(Sko_0))] --> [], inference(leftNotEx, param(2, $fot(Sko_0)), [f8])).

fof(f6, plain, [~(($true => (? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6)))))))), $true, ~((? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6))))))), ~((! [Xy6] : ((sQ(XX4_8) => sQ(Xy6))))), ~((sQ(XX4_8) => sQ(Sko_0)))] --> [], inference(leftNotImp, param(4), [f7])).

fof(f5, plain, [~(($true => (? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6)))))))), $true, ~((? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6))))))), ~((! [Xy6] : ((sQ(XX4_8) => sQ(Xy6)))))] --> [], inference(leftNotForall, param(3, $fot(Sko_0)), [f6])).

fof(f4, plain, [~(($true => (? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6)))))))), $true, ~((? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6)))))))] --> [], inference(leftNotEx, param(2, $fot(XX4_8)), [f5])).

fof(f3, plain, [~(($true => (? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6))))))))] --> [], inference(leftNotImp, param(0), [f4])).

fof(f2, plain, [($true => (? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6)))))))] --> [($true => (? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6)))))))], inference(hyp, param(0, 0), [])).

fof(f1, plain, [] --> [($true => (? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6))))))), ~(($true => (? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6))))))))], inference(rightNot, param(1), [f2])).

fof(f0, plain, [] --> [($true => (? [Xx4] : ((! [Xy6] : ((sQ(Xx4) => sQ(Xy6)))))))], inference(cut, param(1, 0), [f1, f3])).



% SZS output end Proof for Test.gothm4.p
