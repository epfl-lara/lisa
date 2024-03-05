
% SZS output start Proof for Test.gothm0.p


fof(c_Test_gothm0_p, conjecture, (((sp & sq) | (sp & sr)) => (sp & (sq | sr)))).

fof(f8, plain, [~((((sp & sq) | (sp & sr)) => (sp & (sq | sr)))), ((sp & sq) | (sp & sr)), ~((sp & (sq | sr))), (sp & sq), sp, sq, ~(sp)] --> [], inference(leftHyp, param(6, 4), [])).

fof(f10, plain, [~((((sp & sq) | (sp & sr)) => (sp & (sq | sr)))), ((sp & sq) | (sp & sr)), ~((sp & (sq | sr))), (sp & sq), sp, sq, ~((sq | sr)), ~(sq), ~(sr)] --> [], inference(leftHyp, param(7, 5), [])).

fof(f9, plain, [~((((sp & sq) | (sp & sr)) => (sp & (sq | sr)))), ((sp & sq) | (sp & sr)), ~((sp & (sq | sr))), (sp & sq), sp, sq, ~((sq | sr))] --> [], inference(leftNotOr, param(6), [f10])).

fof(f7, plain, [~((((sp & sq) | (sp & sr)) => (sp & (sq | sr)))), ((sp & sq) | (sp & sr)), ~((sp & (sq | sr))), (sp & sq), sp, sq] --> [], inference(leftNotAnd, param(2), [f8, f9])).

fof(f5, plain, [~((((sp & sq) | (sp & sr)) => (sp & (sq | sr)))), ((sp & sq) | (sp & sr)), ~((sp & (sq | sr))), (sp & sq)] --> [], inference(leftAnd, param(3), [f7])).

fof(f12, plain, [~((((sp & sq) | (sp & sr)) => (sp & (sq | sr)))), ((sp & sq) | (sp & sr)), ~((sp & (sq | sr))), (sp & sr), sp, sr, ~(sp)] --> [], inference(leftHyp, param(6, 4), [])).

fof(f14, plain, [~((((sp & sq) | (sp & sr)) => (sp & (sq | sr)))), ((sp & sq) | (sp & sr)), ~((sp & (sq | sr))), (sp & sr), sp, sr, ~((sq | sr)), ~(sq), ~(sr)] --> [], inference(leftHyp, param(8, 5), [])).

fof(f13, plain, [~((((sp & sq) | (sp & sr)) => (sp & (sq | sr)))), ((sp & sq) | (sp & sr)), ~((sp & (sq | sr))), (sp & sr), sp, sr, ~((sq | sr))] --> [], inference(leftNotOr, param(6), [f14])).

fof(f11, plain, [~((((sp & sq) | (sp & sr)) => (sp & (sq | sr)))), ((sp & sq) | (sp & sr)), ~((sp & (sq | sr))), (sp & sr), sp, sr] --> [], inference(leftNotAnd, param(2), [f12, f13])).

fof(f6, plain, [~((((sp & sq) | (sp & sr)) => (sp & (sq | sr)))), ((sp & sq) | (sp & sr)), ~((sp & (sq | sr))), (sp & sr)] --> [], inference(leftAnd, param(3), [f11])).

fof(f4, plain, [~((((sp & sq) | (sp & sr)) => (sp & (sq | sr)))), ((sp & sq) | (sp & sr)), ~((sp & (sq | sr)))] --> [], inference(leftOr, param(1), [f5, f6])).

fof(f3, plain, [~((((sp & sq) | (sp & sr)) => (sp & (sq | sr))))] --> [], inference(leftNotImp, param(0), [f4])).

fof(f2, plain, [(((sp & sq) | (sp & sr)) => (sp & (sq | sr)))] --> [(((sp & sq) | (sp & sr)) => (sp & (sq | sr)))], inference(hyp, param(0, 0), [])).

fof(f1, plain, [] --> [(((sp & sq) | (sp & sr)) => (sp & (sq | sr))), ~((((sp & sq) | (sp & sr)) => (sp & (sq | sr))))], inference(rightNot, param(1), [f2])).

fof(f0, plain, [] --> [(((sp & sq) | (sp & sr)) => (sp & (sq | sr)))], inference(cut, param(1, 0), [f1, f3])).



% SZS output end Proof for Test.gothm0.p
