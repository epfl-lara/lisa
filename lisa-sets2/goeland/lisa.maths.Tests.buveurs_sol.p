
% SZS output start Proof for lisa.maths.Tests.buveurs.p


fof(c_lisa_maths_Tests_buveurs_p, conjecture, (? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6))))))).

fof(f8, plain, [~((? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6))))))), ~((sP(XX4_8) => (! [Xy6] : (sP(Xy6))))), sP(XX4_8), ~((! [Xy6] : (sP(Xy6)))), ~(sP(Sko_0)), ~((sP(Sko_0) => (! [Xy6] : (sP(Xy6))))), sP(Sko_0)] --> [], inference(leftHyp, [status(thm), 4], [])).

fof(f7, plain, [~((? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6))))))), ~((sP(XX4_8) => (! [Xy6] : (sP(Xy6))))), sP(XX4_8), ~((! [Xy6] : (sP(Xy6)))), ~(sP(Sko_0)), ~((sP(Sko_0) => (! [Xy6] : (sP(Xy6)))))] --> [], inference(leftNotImplies, [status(thm), 5], [f8])).

fof(f6, plain, [~((? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6))))))), ~((sP(XX4_8) => (! [Xy6] : (sP(Xy6))))), sP(XX4_8), ~((! [Xy6] : (sP(Xy6)))), ~(sP(Sko_0))] --> [], inference(leftNotEx, [status(thm), 0, $fot(Sko_0)], [f7])).

fof(f5, plain, [~((? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6))))))), ~((sP(XX4_8) => (! [Xy6] : (sP(Xy6))))), sP(XX4_8), ~((! [Xy6] : (sP(Xy6))))] --> [], inference(leftNotAll, [status(thm), 3, $fot(Sko_0)], [f6])).

fof(f4, plain, [~((? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6))))))), ~((sP(XX4_8) => (! [Xy6] : (sP(Xy6)))))] --> [], inference(leftNotImplies, [status(thm), 1], [f5])).

fof(f3, plain, [~((? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6)))))))] --> [], inference(leftNotEx, [status(thm), 0, $fot(XX4_8)], [f4])).

fof(f2, plain, [(? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6))))))] --> [(? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6))))))], inference(hyp, [status(thm), 0], [])).

fof(f1, plain, [] --> [(? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6)))))), ~((? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6)))))))], inference(rightNot, [status(thm), 1], [f2])).

fof(f0, plain, [] --> [(? [Xx4] : ((sP(Xx4) => (! [Xy6] : (sP(Xy6))))))], inference(cut, [status(thm), 1], [f1, f3])).



% SZS output end Proof for lisa.maths.Tests.buveurs.p
