fof(c_simple_p, conjecture, ((! [X5] : (p_2(X5))) => (p_2(a_3) & p_2(b_4)))).

fof(f7, plain, [~(((! [X5] : (p_2(X5))) => (p_2(a_3) & p_2(b_4)))), (! [X5] : (p_2(X5))), ~((p_2(a_3) & p_2(b_4))), ~(p_2(a_3)), p_2(a_3)] --> [], inference(leftHyp, [status(thm), 3], [])).

fof(f5, plain, [~(((! [X5] : (p_2(X5))) => (p_2(a_3) & p_2(b_4)))), (! [X5] : (p_2(X5))), ~((p_2(a_3) & p_2(b_4))), ~(p_2(a_3))] --> [], inference(leftForall, [status(thm), 1, $fot(a_3)], [f7])).

fof(f8, plain, [~(((! [X5] : (p_2(X5))) => (p_2(a_3) & p_2(b_4)))), (! [X5] : (p_2(X5))), ~((p_2(a_3) & p_2(b_4))), ~(p_2(b_4)), p_2(b_4)] --> [], inference(leftHyp, [status(thm), 3], [])).

fof(f6, plain, [~(((! [X5] : (p_2(X5))) => (p_2(a_3) & p_2(b_4)))), (! [X5] : (p_2(X5))), ~((p_2(a_3) & p_2(b_4))), ~(p_2(b_4))] --> [], inference(leftForall, [status(thm), 1, $fot(b_4)], [f8])).

fof(f4, plain, [~(((! [X5] : (p_2(X5))) => (p_2(a_3) & p_2(b_4)))), (! [X5] : (p_2(X5))), ~((p_2(a_3) & p_2(b_4)))] --> [], inference(leftNotAnd, [status(thm), 2], [f5, f6])).

fof(f3, plain, [~(((! [X5] : (p_2(X5))) => (p_2(a_3) & p_2(b_4))))] --> [], inference(leftNotImplies, [status(thm), 0], [f4])).

fof(f2, plain, [((! [X5] : (p_2(X5))) => (p_2(a_3) & p_2(b_4)))] --> [((! [X5] : (p_2(X5))) => (p_2(a_3) & p_2(b_4)))], inference(hyp, [status(thm), 0], [])).

fof(f1, plain, [] --> [((! [X5] : (p_2(X5))) => (p_2(a_3) & p_2(b_4))), ~(((! [X5] : (p_2(X5))) => (p_2(a_3) & p_2(b_4))))], inference(rightNot, [status(thm), 1], [f2])).

fof(f0, plain, [] --> [((! [X5] : (p_2(X5))) => (p_2(a_3) & p_2(b_4)))], inference(cut, [status(thm), 1], [f1, f3])).