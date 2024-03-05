
% SZS output start Proof for Test.gothm2.p


fof(c_Test_gothm2_p, conjecture, (((sQ(Xx) => sR(Xy)) & sQ(Xx)) => sR(Xy))).

fof(f6, plain, [~((((sQ(Xx) => sR(Xy)) & sQ(Xx)) => sR(Xy))), ((sQ(Xx) => sR(Xy)) & sQ(Xx)), ~(sR(Xy)), (sQ(Xx) => sR(Xy)), sQ(Xx), ~(sQ(Xx))] --> [], inference(leftHyp, param(5, 4), [])).

fof(f7, plain, [~((((sQ(Xx) => sR(Xy)) & sQ(Xx)) => sR(Xy))), ((sQ(Xx) => sR(Xy)) & sQ(Xx)), ~(sR(Xy)), (sQ(Xx) => sR(Xy)), sQ(Xx), sR(Xy)] --> [], inference(leftHyp, param(5, 2), [])).

fof(f5, plain, [~((((sQ(Xx) => sR(Xy)) & sQ(Xx)) => sR(Xy))), ((sQ(Xx) => sR(Xy)) & sQ(Xx)), ~(sR(Xy)), (sQ(Xx) => sR(Xy)), sQ(Xx)] --> [], inference(leftImp2, param(3), [f6, f7])).

fof(f4, plain, [~((((sQ(Xx) => sR(Xy)) & sQ(Xx)) => sR(Xy))), ((sQ(Xx) => sR(Xy)) & sQ(Xx)), ~(sR(Xy))] --> [], inference(leftAnd, param(1), [f5])).

fof(f3, plain, [~((((sQ(Xx) => sR(Xy)) & sQ(Xx)) => sR(Xy)))] --> [], inference(leftNotImp, param(0), [f4])).

fof(f2, plain, [(((sQ(Xx) => sR(Xy)) & sQ(Xx)) => sR(Xy))] --> [(((sQ(Xx) => sR(Xy)) & sQ(Xx)) => sR(Xy))], inference(hyp, param(0, 0), [])).

fof(f1, plain, [] --> [(((sQ(Xx) => sR(Xy)) & sQ(Xx)) => sR(Xy)), ~((((sQ(Xx) => sR(Xy)) & sQ(Xx)) => sR(Xy)))], inference(rightNot, param(1), [f2])).

fof(f0, plain, [] --> [(((sQ(Xx) => sR(Xy)) & sQ(Xx)) => sR(Xy))], inference(cut, param(1, 0), [f1, f3])).



% SZS output end Proof for Test.gothm2.p
