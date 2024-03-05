
% SZS output start Proof for Test.gothm3.p


fof(c_Test_gothm3_p, conjecture, ($true => (~(ss(cemptySet)) => ~((! [Xx4] : (ss(Xx4))))))).

fof(f7, plain, [~(($true => (~(ss(cemptySet)) => ~((! [Xx4] : (ss(Xx4))))))), $true, ~((~(ss(cemptySet)) => ~((! [Xx4] : (ss(Xx4)))))), ~(ss(cemptySet)), ~(~((! [Xx4] : (ss(Xx4))))), (! [Xx4] : (ss(Xx4))), ss(cemptySet)] --> [], inference(leftHyp, param(6, 3), [])).

fof(f6, plain, [~(($true => (~(ss(cemptySet)) => ~((! [Xx4] : (ss(Xx4))))))), $true, ~((~(ss(cemptySet)) => ~((! [Xx4] : (ss(Xx4)))))), ~(ss(cemptySet)), ~(~((! [Xx4] : (ss(Xx4))))), (! [Xx4] : (ss(Xx4)))] --> [], inference(leftForall, param(5, $fot(cemptySet)), [f7])).

fof(f5, plain, [~(($true => (~(ss(cemptySet)) => ~((! [Xx4] : (ss(Xx4))))))), $true, ~((~(ss(cemptySet)) => ~((! [Xx4] : (ss(Xx4)))))), ~(ss(cemptySet)), ~(~((! [Xx4] : (ss(Xx4)))))] --> [], inference(leftNotNot, param(4), [f6])).

fof(f4, plain, [~(($true => (~(ss(cemptySet)) => ~((! [Xx4] : (ss(Xx4))))))), $true, ~((~(ss(cemptySet)) => ~((! [Xx4] : (ss(Xx4))))))] --> [], inference(leftNotImp, param(2), [f5])).

fof(f3, plain, [~(($true => (~(ss(cemptySet)) => ~((! [Xx4] : (ss(Xx4)))))))] --> [], inference(leftNotImp, param(0), [f4])).

fof(f2, plain, [($true => (~(ss(cemptySet)) => ~((! [Xx4] : (ss(Xx4))))))] --> [($true => (~(ss(cemptySet)) => ~((! [Xx4] : (ss(Xx4))))))], inference(hyp, param(0, 0), [])).

fof(f1, plain, [] --> [($true => (~(ss(cemptySet)) => ~((! [Xx4] : (ss(Xx4)))))), ~(($true => (~(ss(cemptySet)) => ~((! [Xx4] : (ss(Xx4)))))))], inference(rightNot, param(1), [f2])).

fof(f0, plain, [] --> [($true => (~(ss(cemptySet)) => ~((! [Xx4] : (ss(Xx4))))))], inference(cut, param(1, 0), [f1, f3])).



% SZS output end Proof for Test.gothm3.p
