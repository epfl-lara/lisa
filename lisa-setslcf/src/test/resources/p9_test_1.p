fof(test_minimaliste, conjecture, [] --> [(! [X]: p(X) => (p(a) & p(b)))]).
fof(phi, let, ~(! [X]: p(X) => (p(a) & p(b)))).
fof(negated_conjecture, assumption, [~(! [X]: p(X) => (p(a) & p(b)))] --> [~(! [X]: p(X) => (p(a) & p(b)))], inference(hyp, [status(thm), 0], [])).
fof(nnf_step, plain, [$phi] --> [(! [X]: p(X) & (~p(a) | ~p(b)))], inference(rightNnf, [status(thm), 0, 0], [negated_conjecture])).
fof(prenex_step, plain, [$phi] --> [! [X]: (p(X) & (~p(a) | ~p(b)))], inference(rightPrenex, [status(thm), 0, 0], [nnf_step])).
fof(i0, plain, [$phi] --> [(p(V0) & (~p(a) | ~p(b)))], inference(instForall, [status(thm), 0, $fot(V0)], [prenex_step])).
fof(tsStep0, let, (Ts3 <=> (~p(a) | ~p(b)))).
fof(tsStep1, let, ! [V0]: (Ts1(V0) <=> (p(V0) & Ts3))).
fof(tsStepExpl1, plain, [$phi,$tsStep0] --> [(p(V0) & Ts3)], inference(rightSubstIff, [status(thm), 1, $fof((p(V0) & A)), 'A'], [i0])).
fof(tsStepExpl2, plain, [$phi,$tsStep0,(Ts1(V0) <=> (p(V0) & Ts3))] --> [Ts1(V0)], inference(rightSubstIff, [status(thm), 2, $fof(A), 'A'], [tsStepExpl1])).
fof(4, plain, [$phi,$tsStep0,$tsStep1] --> [Ts1(V0)], inference(leftForall, [status(thm), 2, $fot(V0)], [tsStepExpl2])).
fof(a3, plain, [$phi,$tsStep0,(Ts1(V0) <=> (p(V0) & Ts3))] --> [~Ts1(V0),p(V0)], inference(clausify, [status(thm), 2], [])).
fof(3, plain, [$phi,$tsStep0,$tsStep1] --> [~Ts1(V0),p(V0)], inference(leftForall, [status(thm), 2, $fot(V0)], [a3])).
fof(a6, plain, [$phi,$tsStep0,(Ts1(V0) <=> (p(V0) & Ts3))] --> [~Ts1(V0),Ts3], inference(clausify, [status(thm), 2], [])).
fof(6, plain, [$phi,$tsStep0,$tsStep1] --> [~Ts1(V0),Ts3], inference(leftForall, [status(thm), 2, $fot(V0)], [a6])).
fof(7, plain, [$phi,$tsStep0,$tsStep1] --> [~Ts3,~p(a),~p(b)], inference(clausify, [status(thm), 1], [])).
fof(15, plain, [$phi,$tsStep0,$tsStep1] --> [~Ts1(V100),p(V100)], inference(instMult, [status(thm), [tuple3('V0', $fot(V100), [])]], [3])).
fof(16, plain, [$phi,$tsStep0,$tsStep1] --> [Ts1(V100)], inference(instMult, [status(thm), [tuple3('V0', $fot(V100), [])]], [4])).
fof(17, plain, [$phi,$tsStep0,$tsStep1] --> [p(V100)], inference(res, [status(thm), 0], [16, 15])).
fof(10, plain, [$phi,$tsStep0,$tsStep1] --> [p(V0)], inference(instMult, [status(thm), [tuple3('V100', $fot(V0), [])]], [17])).
fof(18, plain, [$phi,$tsStep0,$tsStep1] --> [~Ts1(V100),Ts3], inference(instMult, [status(thm), [tuple3('V0', $fot(V100), [])]], [6])).
fof(19, plain, [$phi,$tsStep0,$tsStep1] --> [Ts1(V100)], inference(instMult, [status(thm), [tuple3('V0', $fot(V100), [])]], [4])).
fof(11, plain, [$phi,$tsStep0,$tsStep1] --> [Ts3], inference(res, [status(thm), 0], [19, 18])).
fof(a012, plain, [$phi,$tsStep0,$tsStep1] --> [~p(a),~p(b)], inference(res, [status(thm), 0], [11, 7])).
fof(20, plain, [$phi,$tsStep0,$tsStep1] --> [p(a)], inference(instMult, [status(thm), [tuple3('V0', $fot(a), [])]], [10])).
fof(a112, plain, [$phi,$tsStep0,$tsStep1] --> [~p(b)], inference(res, [status(thm), 0], [20, a012])).
fof(21, plain, [$phi,$tsStep0,$tsStep1] --> [p(b)], inference(instMult, [status(thm), [tuple3('V0', $fot(b), [])]], [10])).
fof(12, plain, [$phi,$tsStep0,$tsStep1] --> [], inference(res, [status(thm), 0], [21, a112])).
fof(psi, let, (! [X]: p(X) => (p(a) & p(b)))).
fof(addPsi0, assumption, [$psi] --> [$psi], inference(hyp, [status(thm), 0], [])).
fof(addPsi1, plain, [] --> [$psi,$phi], inference(rightNot, [status(thm), 0], [addPsi0])).
fof(addPsi2, plain, [$tsStep0,$tsStep1] --> [$psi], inference(cut, [status(thm), 1], [addPsi1, 12])).
fof(removeTseitin0, plain, [$tsStep0,! [V0]: ((p(V0) & Ts3) <=> (p(V0) & Ts3))] --> [$psi], inference(instPred, [status(thm), 'Ts1', $fof((p(V0) & Ts3)), ['V0']], [addPsi2])).
fof(removeTseitin1, plain, [$tsStep0] --> [$psi], inference(elimIffRefl, [status(thm), 1], [removeTseitin0])).
fof(removeTseitin2, plain, [((~p(a) | ~p(b)) <=> (~p(a) | ~p(b)))] --> [$psi], inference(instPred, [status(thm), 'Ts3', $fof((~p(a) | ~p(b))), []], [removeTseitin1])).
fof(removeTseitin3, plain, [] --> [$psi], inference(elimIffRefl, [status(thm), 0], [removeTseitin2])).