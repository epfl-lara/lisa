fof(c1, conjecture, [] --> [((! [X]: p(X) | ! [Y]: q(Y)) => (p(c) | q(c)))]).
fof(phi, let, ~((! [X]: p(X) | ! [Y]: q(Y)) => (p(c) | q(c)))).
fof(negated_conjecture, assumption, [~((! [X]: p(X) | ! [Y]: q(Y)) => (p(c) | q(c)))] --> [~((! [X]: p(X) | ! [Y]: q(Y)) => (p(c) | q(c)))], inference(hyp, [status(thm), 0], [])).
fof(nnf_step, plain, [$phi] --> [((! [X]: p(X) | ! [Y]: q(Y)) & (~p(c) & ~q(c)))], inference(rightNnf, [status(thm), 0, 0], [negated_conjecture])).
fof(prenex_step, plain, [$phi] --> [! [X]: ! [Y]: ((p(X) | q(Y)) & (~p(c) & ~q(c)))], inference(rightPrenex, [status(thm), 0, 0], [nnf_step])).
fof(i0, plain, [$phi] --> [! [Y]: ((p(V0) | q(Y)) & (~p(c) & ~q(c)))], inference(instForall, [status(thm), 0, $fot(V0)], [prenex_step])).
fof(i1, plain, [$phi] --> [((p(V0) | q(V1)) & (~p(c) & ~q(c)))], inference(instForall, [status(thm), 0, $fot(V1)], [i0])).
fof(tsStep0, let, (Ts5 <=> (~p(c) & ~q(c)))).
fof(tsStep1, let, ! [V1]: ! [V0]: (Ts2(V0,V1) <=> (p(V0) | q(V1)))).
fof(tsStep2, let, ! [V1]: ! [V0]: (Ts3(V0,V1) <=> (Ts2(V0,V1) & Ts5))).
fof(tsStepExpl0, plain, [$phi,$tsStep0] --> [((p(V0) | q(V1)) & Ts5)], inference(rightSubstIff, [status(thm), 1, 1, $fof(((p(V0) | q(V1)) & A)), 'A'], [i1])).
fof(tsStepExpl1, plain, [$phi,$tsStep0,(Ts2(V0,V1) <=> (p(V0) | q(V1)))] --> [(Ts2(V0,V1) & Ts5)], inference(rightSubstIff, [status(thm), 2, 1, $fof((A & Ts5)), 'A'], [tsStepExpl0])).
fof(tsStepExpl2, plain, [$phi,$tsStep0,! [V0]: (Ts2(V0,V1) <=> (p(V0) | q(V1)))] --> [(Ts2(V0,V1) & Ts5)], inference(leftForall, [status(thm), 2, $fot(V0)], [tsStepExpl1])).
fof(tsStepExpl3, plain, [$phi,$tsStep0,$tsStep1] --> [(Ts2(V0,V1) & Ts5)], inference(leftForall, [status(thm), 2, $fot(V1)], [tsStepExpl2])).
fof(tsStepExpl4, plain, [$phi,$tsStep0,$tsStep1,(Ts3(V0,V1) <=> (Ts2(V0,V1) & Ts5))] --> [Ts3(V0,V1)], inference(rightSubstIff, [status(thm), 3, 1, $fof(A), 'A'], [tsStepExpl3])).
fof(tsStepExpl5, plain, [$phi,$tsStep0,$tsStep1,! [V0]: (Ts3(V0,V1) <=> (Ts2(V0,V1) & Ts5))] --> [Ts3(V0,V1)], inference(leftForall, [status(thm), 3, $fot(V0)], [tsStepExpl4])).
fof(3, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [Ts3(V0,V1)], inference(leftForall, [status(thm), 3, $fot(V1)], [tsStepExpl5])).
fof(a2s2, plain, [$phi,$tsStep0,$tsStep1,(Ts3(V0,V1) <=> (Ts2(V0,V1) & Ts5))] --> [~Ts3(V0,V1),Ts2(V0,V1)], inference(clausify, [status(thm), 3], [])).
fof(a2s1, plain, [$phi,$tsStep0,$tsStep1,! [V0]: (Ts3(V0,V1) <=> (Ts2(V0,V1) & Ts5))] --> [~Ts3(V0,V1),Ts2(V0,V1)], inference(leftForall, [status(thm), 3, $fot(V0)], [a2s2])).
fof(2, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [~Ts3(V0,V1),Ts2(V0,V1)], inference(leftForall, [status(thm), 3, $fot(V1)], [a2s1])).
fof(a5s2, plain, [$phi,$tsStep0,$tsStep1,(Ts3(V0,V1) <=> (Ts2(V0,V1) & Ts5))] --> [~Ts3(V0,V1),Ts5], inference(clausify, [status(thm), 3], [])).
fof(a5s1, plain, [$phi,$tsStep0,$tsStep1,! [V0]: (Ts3(V0,V1) <=> (Ts2(V0,V1) & Ts5))] --> [~Ts3(V0,V1),Ts5], inference(leftForall, [status(thm), 3, $fot(V0)], [a5s2])).
fof(5, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [~Ts3(V0,V1),Ts5], inference(leftForall, [status(thm), 3, $fot(V1)], [a5s1])).
fof(a7s2, plain, [$phi,$tsStep0,$tsStep1,(Ts2(V0,V1) <=> (p(V0) | q(V1)))] --> [~Ts2(V0,V1),p(V0),q(V1)], inference(clausify, [status(thm), 3], [])).
fof(a7s1, plain, [$phi,$tsStep0,$tsStep1,! [V0]: (Ts2(V0,V1) <=> (p(V0) | q(V1)))] --> [~Ts2(V0,V1),p(V0),q(V1)], inference(leftForall, [status(thm), 3, $fot(V0)], [a7s2])).
fof(7, plain, [$phi,$tsStep0,! [V1]: ! [V0]: (Ts2(V0,V1) <=> (p(V0) | q(V1))),$tsStep2] --> [~Ts2(V0,V1),p(V0),q(V1)], inference(leftForall, [status(thm), 2, $fot(V1)], [a7s1])).
fof(19, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [~Ts3(V100,V101),Ts2(V100,V101)], inference(instMult, [status(thm), [tuple3('V0', $fot(V100), []), tuple3('V1', $fot(V101), [])]], [2])).
fof(20, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [Ts3(V100,V101)], inference(instMult, [status(thm), [tuple3('V0', $fot(V100), []), tuple3('V1', $fot(V101), [])]], [3])).
fof(21, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [Ts2(V100,V101)], inference(res, [status(thm), 0], [20, 19])).
fof(9, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [Ts2(V0,V1)], inference(instMult, [status(thm), [tuple3('V100', $fot(V0), []), tuple3('V101', $fot(V1), [])]], [21])).
fof(10, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [~Ts5,~p(c)], inference(clausify, [status(thm), 1], [])).
fof(22, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [Ts2(V100,V101)], inference(instMult, [status(thm), [tuple3('V0', $fot(V100), []), tuple3('V1', $fot(V101), [])]], [9])).
fof(23, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [~Ts2(V100,V101),p(V100),q(V101)], inference(instMult, [status(thm), [tuple3('V0', $fot(V100), []), tuple3('V1', $fot(V101), [])]], [7])).
fof(24, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [p(V100),q(V101)], inference(res, [status(thm), 0], [22, 23])).
fof(12, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [p(V0),q(V1)], inference(instMult, [status(thm), [tuple3('V100', $fot(V0), []), tuple3('V101', $fot(V1), [])]], [24])).
fof(25, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [p(c),q(V1)], inference(instMult, [status(thm), [tuple3('V0', $fot(c), [])]], [12])).
fof(26, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [q(V1),~Ts5], inference(res, [status(thm), 0], [25, 10])).
fof(13, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [q(V0),~Ts5], inference(instMult, [status(thm), [tuple3('V1', $fot(V0), [])]], [26])).
fof(14, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [~Ts5,~q(c)], inference(clausify, [status(thm), 1], [])).
fof(27, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [~Ts3(V100,V101),Ts5], inference(instMult, [status(thm), [tuple3('V0', $fot(V100), []), tuple3('V1', $fot(V101), [])]], [5])).
fof(28, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [Ts3(V100,V101)], inference(instMult, [status(thm), [tuple3('V0', $fot(V100), []), tuple3('V1', $fot(V101), [])]], [3])).
fof(15, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [Ts5], inference(res, [status(thm), 0], [28, 27])).
fof(29, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [q(c),~Ts5], inference(instMult, [status(thm), [tuple3('V0', $fot(c), [])]], [13])).
fof(16, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [~Ts5,~Ts5], inference(res, [status(thm), 0], [29, 14])).
fof(17, plain, [$phi,$tsStep0,$tsStep1,$tsStep2] --> [], inference(res, [status(thm), 0], [15, 16])).
fof(psi, let, ((! [X]: p(X) | ! [Y]: q(Y)) => (p(c) | q(c)))).
fof(addPsi0, assumption, [$psi] --> [$psi], inference(hyp, [status(thm), 0], [])).
fof(addPsi1, plain, [] --> [$psi,$phi], inference(rightNot, [status(thm), 0], [addPsi0])).
fof(addPsi2, plain, [$tsStep0,$tsStep1,$tsStep2] --> [$psi], inference(cut, [status(thm), 1], [addPsi1, 17])).
fof(removeTseitin0, plain, [$tsStep0,$tsStep1,! [V1]: ! [V0]: ((Ts2(V0,V1) & Ts5) <=> (Ts2(V0,V1) & Ts5))] --> [$psi], inference(instPred, [status(thm), 'Ts3', $fof((Ts2(V0,V1) & Ts5)), ['V0','V1']], [addPsi2])).
fof(removeTseitin1, plain, [$tsStep0,$tsStep1] --> [$psi], inference(elimIffRefl, [status(thm), 2], [removeTseitin0])).
fof(removeTseitin2, plain, [$tsStep0,! [V1]: ! [V0]: ((p(V0) | q(V1)) <=> (p(V0) | q(V1)))] --> [$psi], inference(instPred, [status(thm), 'Ts2', $fof((p(V0) | q(V1))), ['V0','V1']], [removeTseitin1])).
fof(removeTseitin3, plain, [$tsStep0] --> [$psi], inference(elimIffRefl, [status(thm), 1], [removeTseitin2])).
fof(removeTseitin4, plain, [((~p(c) & ~q(c)) <=> (~p(c) & ~q(c)))] --> [$psi], inference(instPred, [status(thm), 'Ts5', $fof((~p(c) & ~q(c))), []], [removeTseitin3])).
fof(removeTseitin5, plain, [] --> [$psi], inference(elimIffRefl, [status(thm), 0], [removeTseitin4])).