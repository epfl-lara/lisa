
% SZS output start Proof for Test.gothm1.p


fof(c_Test_gothm1_p, conjecture, ((sp & (sq | sr)) => ((sp & sq) | (sp & sr)))).

fof(f9, plain, [~(((sp & (sq | sr)) => ((sp & sq) | (sp & sr)))), (sp & (sq | sr)), ~(((sp & sq) | (sp & sr))), sp, (sq | sr), ~((sp & sq)), ~((sp & sr)), sq, ~(sp)] --> [], inference(leftHyp, param(8, 3), [])).

fof(f10, plain, [~(((sp & (sq | sr)) => ((sp & sq) | (sp & sr)))), (sp & (sq | sr)), ~(((sp & sq) | (sp & sr))), sp, (sq | sr), ~((sp & sq)), ~((sp & sr)), sq, ~(sq)] --> [], inference(leftHyp, param(8, 7), [])).

fof(f7, plain, [~(((sp & (sq | sr)) => ((sp & sq) | (sp & sr)))), (sp & (sq | sr)), ~(((sp & sq) | (sp & sr))), sp, (sq | sr), ~((sp & sq)), ~((sp & sr)), sq] --> [], inference(leftNotAnd, param(5), [f9, f10])).

fof(f11, plain, [~(((sp & (sq | sr)) => ((sp & sq) | (sp & sr)))), (sp & (sq | sr)), ~(((sp & sq) | (sp & sr))), sp, (sq | sr), ~((sp & sq)), ~((sp & sr)), sr, ~(sp)] --> [], inference(leftHyp, param(8, 3), [])).

fof(f13, plain, [~(((sp & (sq | sr)) => ((sp & sq) | (sp & sr)))), (sp & (sq | sr)), ~(((sp & sq) | (sp & sr))), sp, (sq | sr), ~((sp & sq)), ~((sp & sr)), sr, ~(sq), ~(sp)] --> [], inference(leftHyp, param(9, 3), [])).

fof(f14, plain, [~(((sp & (sq | sr)) => ((sp & sq) | (sp & sr)))), (sp & (sq | sr)), ~(((sp & sq) | (sp & sr))), sp, (sq | sr), ~((sp & sq)), ~((sp & sr)), sr, ~(sq), ~(sr)] --> [], inference(leftHyp, param(9, 7), [])).

fof(f12, plain, [~(((sp & (sq | sr)) => ((sp & sq) | (sp & sr)))), (sp & (sq | sr)), ~(((sp & sq) | (sp & sr))), sp, (sq | sr), ~((sp & sq)), ~((sp & sr)), sr, ~(sq)] --> [], inference(leftNotAnd, param(6), [f13, f14])).

fof(f8, plain, [~(((sp & (sq | sr)) => ((sp & sq) | (sp & sr)))), (sp & (sq | sr)), ~(((sp & sq) | (sp & sr))), sp, (sq | sr), ~((sp & sq)), ~((sp & sr)), sr] --> [], inference(leftNotAnd, param(5), [f11, f12])).

fof(f6, plain, [~(((sp & (sq | sr)) => ((sp & sq) | (sp & sr)))), (sp & (sq | sr)), ~(((sp & sq) | (sp & sr))), sp, (sq | sr), ~((sp & sq)), ~((sp & sr))] --> [], inference(leftOr, param(4), [f7, f8])).

fof(f5, plain, [~(((sp & (sq | sr)) => ((sp & sq) | (sp & sr)))), (sp & (sq | sr)), ~(((sp & sq) | (sp & sr))), sp, (sq | sr)] --> [], inference(leftNotOr, param(2), [f6])).

fof(f4, plain, [~(((sp & (sq | sr)) => ((sp & sq) | (sp & sr)))), (sp & (sq | sr)), ~(((sp & sq) | (sp & sr)))] --> [], inference(leftAnd, param(1), [f5])).

fof(f3, plain, [~(((sp & (sq | sr)) => ((sp & sq) | (sp & sr))))] --> [], inference(leftNotImp, param(0), [f4])).

fof(f2, plain, [((sp & (sq | sr)) => ((sp & sq) | (sp & sr)))] --> [((sp & (sq | sr)) => ((sp & sq) | (sp & sr)))], inference(hyp, param(0, 0), [])).

fof(f1, plain, [] --> [((sp & (sq | sr)) => ((sp & sq) | (sp & sr))), ~(((sp & (sq | sr)) => ((sp & sq) | (sp & sr))))], inference(rightNot, param(1), [f2])).

fof(f0, plain, [] --> [((sp & (sq | sr)) => ((sp & sq) | (sp & sr)))], inference(cut, param(1, 0), [f1, f3])).



% SZS output end Proof for Test.gothm1.p
