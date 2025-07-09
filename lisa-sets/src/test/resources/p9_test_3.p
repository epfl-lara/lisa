
fof(conj, conjecture, [] --> [? [X]: ! [Y]: (p(Y) | ~p(X))]).
fof(neg_conjecture, assumption, [~? [X]: ! [Y]: (p(Y) | ~p(X))] --> [~? [X]: ! [Y]: (p(Y) | ~p(X))], inference(hyp, [status(thm), 0], [])).
fof(r1, let, ~? [X]: ! [Y]: (p(Y) | ~p(X))).
fof(neg_conjecture_nnf, plain, [$r1] --> [! [X]: ? [Y]: (~p(Y) & p(X))], inference(rightNnf, [status(thm), 0, 0], [neg_conjecture])).
fof(sko_iff5, plain, [$r1] --> [! [X]: (? [Y]: (~p(Y) & p(X)) <=> (~p(# [Y]: ((~p(Y) & p(X)))) & p(X)))], inference(existsIffEpsilon, [status(thm), 0], [])).
fof(eps_subst5, plain, [! [X]: (? [Y]: (~p(Y) & p(X)) <=> (~p(# [Y]: ((~p(Y) & p(X)))) & p(X))),$r1] --> [! [X]: (~p(# [Y]: ((~p(Y) & p(X)))) & p(X))], inference(rightSubstPred, [status(thm), 0, 0, $fof(! [X]: HOLE(X)), 'HOLE'], [neg_conjecture_nnf])).
fof(sko_cut5, plain, [$r1] --> [! [X]: (~p(# [Y]: ((~p(Y) & p(X)))) & p(X))], inference(cut, [status(thm), 0], [sko_iff5, eps_subst5])).
fof(sko_subst5, plain, [! [X]: # [Y]: ((~p(Y) & p(X))) = Sk5(X),$r1] --> [! [X]: (~p(Sk5(X)) & p(X))], inference(rightSubstFun, [status(thm), 0, 0, $fof(! [X]: (~p(THOLE(X)) & p(X))), 'THOLE'], [sko_cut5])).
fof(r2, let, ! [X]: # [Y]: ((~p(Y) & p(X))) = Sk5(X)).
fof(neg_conjecture_pre, plain, [$r2,$r1] --> [! [V0]: (~p(Sk5(V0)) & p(V0))], inference(rightPrenex, [status(thm), 0, 0], [sko_subst5])).
fof(neg_conjecture_V0, plain, [$r2,$r1] --> [(~p(Sk5(V0)) & p(V0))], inference(instForall, [status(thm), 0, $fot(V0)], [neg_conjecture_pre])).
fof(ts_cla1, plain, [(Ts1(V0) <=> (~p(Sk5(V0)) & p(V0))),$r2,$r1] --> [~Ts1(V0),~p(Sk5(V0))], inference(clausify, [status(thm), 0], [])).
fof(ts_claQ1_1, plain, [! [V0]: (Ts1(V0) <=> (~p(Sk5(V0)) & p(V0))),$r2,$r1] --> [~Ts1(V0),~p(Sk5(V0))], inference(leftForall, [status(thm), 0, $fot(V0)], [ts_cla1])).
fof(ts_clb1, plain, [(Ts1(V0) <=> (~p(Sk5(V0)) & p(V0))),$r2,$r1] --> [~Ts1(V0),p(V0)], inference(clausify, [status(thm), 0], [])).
fof(ts_clbQ1_1, plain, [! [V0]: (Ts1(V0) <=> (~p(Sk5(V0)) & p(V0))),$r2,$r1] --> [~Ts1(V0),p(V0)], inference(leftForall, [status(thm), 0, $fot(V0)], [ts_clb1])).
fof(ts_ax_just1, plain, [(Ts1(V0) <=> (~p(Sk5(V0)) & p(V0))),$r2,$r1] --> [Ts1(V0)], inference(rightSubstIff, [status(thm), 0, 1, $fof(HOLE), 'HOLE'], [neg_conjecture_V0])).
fof(ts_axQ1_1, plain, [! [V0]: (Ts1(V0) <=> (~p(Sk5(V0)) & p(V0))),$r2,$r1] --> [Ts1(V0)], inference(leftForall, [status(thm), 0, $fot(V0)], [ts_ax_just1])).
fof(r3, let, ! [V0]: (Ts1(V0) <=> (~p(Sk5(V0)) & p(V0)))).
fof(ts_claQ1_1_p9_rename_var, plain, [$r3,$r2,$r1] --> [~Ts1(V0),~p(Sk5(V0))], inference(instMult, [status(thm), [tuple3('V0', $fot(V0), [])]], [ts_claQ1_1])).
fof(ts_clbQ1_1_p9_rename_var, plain, [$r3,$r2,$r1] --> [~Ts1(V0),p(V0)], inference(instMult, [status(thm), [tuple3('V0', $fot(V0), [])]], [ts_clbQ1_1])).
fof(ts_axQ1_1_p9_rename_var, plain, [$r3,$r2,$r1] --> [Ts1(V0)], inference(instMult, [status(thm), [tuple3('V0', $fot(V0), [])]], [ts_axQ1_1])).
fof(8, plain, [$r3,$r2,$r1] --> [Ts1(V100)], inference(instMult, [status(thm), [tuple3('V0', $fot(V100), [])]], [ts_axQ1_1_p9_rename_var])).
fof(9, plain, [$r3,$r2,$r1] --> [~Ts1(V100),p(V100)], inference(instMult, [status(thm), [tuple3('V0', $fot(V100), [])]], [ts_clbQ1_1_p9_rename_var])).
fof(10, plain, [$r3,$r2,$r1] --> [p(V100)], inference(res, [status(thm), 0], [8, 9])).
fof(5, plain, [$r3,$r2,$r1] --> [p(V0)], inference(instMult, [status(thm), [tuple3('V100', $fot(V0), [])]], [10])).
fof(11, plain, [$r3,$r2,$r1] --> [Ts1(V100)], inference(instMult, [status(thm), [tuple3('V0', $fot(V100), [])]], [ts_axQ1_1_p9_rename_var])).
fof(12, plain, [$r3,$r2,$r1] --> [~Ts1(V100),~p(Sk5(V100))], inference(instMult, [status(thm), [tuple3('V0', $fot(V100), [])]], [ts_claQ1_1_p9_rename_var])).
fof(13, plain, [$r3,$r2,$r1] --> [~p(Sk5(V100))], inference(res, [status(thm), 0], [11, 12])).
fof(6, plain, [$r3,$r2,$r1] --> [~p(Sk5(V0))], inference(instMult, [status(thm), [tuple3('V100', $fot(V0), [])]], [13])).
fof(14, plain, [$r3,$r2,$r1] --> [p(Sk5(V100))], inference(instMult, [status(thm), [tuple3('V0', $fot(Sk5(V100)), [])]], [5])).
fof(15, plain, [$r3,$r2,$r1] --> [~p(Sk5(V100))], inference(instMult, [status(thm), [tuple3('V0', $fot(V100), [])]], [6])).
fof(ts_sp1, plain, [$r3,$r2,$r1] --> [], inference(res, [status(thm), 0], [14, 15])).
fof(ts_inst1, plain, [! [V0]: ((~p(Sk5(V0)) & p(V0)) <=> (~p(Sk5(V0)) & p(V0))),$r2,$r1] --> [], inference(instPred, [status(thm), 'Ts1', $fof((~p(Sk5(V0)) & p(V0))), ['V0']], [ts_sp1])).
fof(sko_sp9, plain, [$r2,$r1] --> [], inference(elimIffRefl, [status(thm), 0], [ts_inst1])).
fof(sko_inst9, plain, [! [X]: # [Y]: ((~p(Y) & p(X))) = # [Y]: ((~p(Y) & p(X))),$r1] --> [], inference(instFun, [status(thm), 'Sk5', $fot(# [Y]: ((~p(Y) & p(X)))), ['X']], [sko_sp9])).
fof(sp_neg_conj, plain, [$r1] --> [], inference(elimEqRefl, [status(thm), 0], [sko_inst9])).
fof(nc_elim_1, assumption, [? [X]: ! [Y]: (p(Y) | ~p(X))] --> [? [X]: ! [Y]: (p(Y) | ~p(X))], inference(hyp, [status(thm), 0], [])).
fof(nc_elim_2, plain, [] --> [? [X]: ! [Y]: (p(Y) | ~p(X)),~? [X]: ! [Y]: (p(Y) | ~p(X))], inference(rightNot, [status(thm), 1], [nc_elim_1])).
fof(nc_elim_3, plain, [] --> [? [X]: ! [Y]: (p(Y) | ~p(X))], inference(cut, [status(thm), 1], [nc_elim_2, sp_neg_conj])).