Require Import
        CoqSat.Formula
        CoqSat.Solver.

Inductive In_formula (v: nat) : formula -> Prop :=
  in_formula_one: In_formula v (Var v)
| in_formula_orl: forall f1 f2,
    In_formula v f1 -> In_formula v (Or f1 f2)
| in_formula_orr: forall f1 f2,
    In_formula v f2 -> In_formula v (Or f1 f2)
| in_formula_andl: forall f1 f2,
    In_formula v f1 -> In_formula v (And f1 f2)
| in_formula_andr: forall f1 f2,
    In_formula v f2 -> In_formula v (And f1 f2)
| in_formula_implyl: forall f1 f2,
    In_formula v f1 -> In_formula v (Imply f1 f2)
| in_formula_implyr: forall f1 f2,
    In_formula v f2 -> In_formula v (Imply f1 f2)
| in_formula_negate: forall f,
    In_formula v f -> In_formula v (Negate f).

(* This is basically just a hint of the completeness to show
 * that find_vars is sound and complete *)
Lemma find_vars_correct: forall f v,
     In_formula v f  <->  List.In v (find_vars f).
Proof.
  intros f v.
  split.
  (* -> *)
  {
    induction 1.
    * simpl. left. reflexivity.
    * simpl. revert IHIn_formula. rewrite -> List.app_nil_r. intro.
      apply List.in_or_app. left. exact IHIn_formula.
    * simpl. revert IHIn_formula. rewrite -> List.app_nil_r. intro.
      apply List.in_or_app. right. exact IHIn_formula.
    * simpl. revert IHIn_formula. rewrite -> List.app_nil_r. intro.
      apply List.in_or_app. left. exact IHIn_formula.
    * simpl. revert IHIn_formula. rewrite -> List.app_nil_r. intro.
      apply List.in_or_app. right. exact IHIn_formula.
    * simpl. revert IHIn_formula. rewrite -> List.app_nil_r. intro.
      apply List.in_or_app. left. exact IHIn_formula.
    * simpl. revert IHIn_formula. rewrite -> List.app_nil_r. intro.
      apply List.in_or_app. right. exact IHIn_formula.
    * simpl. exact IHIn_formula.
  }
  (* <- *)
  {
    induction f.
    - simpl. intro. case H.
      * intro. rewrite H0.
        apply in_formula_one.
      * intro. inversion H0.
    - simpl. intro. inversion H.
    - simpl. rewrite -> List.app_nil_r.
      intro. apply List.in_app_or in H. case H.
      * intro. apply in_formula_andl. apply IHf1. exact H0.
      * intro. apply in_formula_andr. apply IHf2. exact H0.
    - simpl. rewrite -> List.app_nil_r.
      intro. apply List.in_app_or in H. case H.
      * intro. apply in_formula_orl. apply IHf1. exact H0.
      * intro. apply in_formula_orr. apply IHf2. exact H0.
    - simpl. rewrite -> List.app_nil_r.
      intro. apply List.in_app_or in H. case H.
      * intro. apply in_formula_implyl. apply IHf1. exact H0.
      * intro. apply in_formula_implyr. apply IHf2. exact H0.
    - simpl. intro. apply in_formula_negate. apply IHf. exact H.
  }
Qed.

Lemma find_valuation_sound':
  forall form vars valuat valuat0,
    find_valuation form valuat0 vars = Some valuat ->
    simplify_and_valuate valuat form = Const true.
Proof.
  intros f vs vl.
  induction vs.
  {
    intro.
    simpl. unfold formula_to_sat. case_eq (simplify_and_valuate valuat0 f);
                                    intro; try discriminate.
    case_eq (b); try discriminate.
    intros. inversion H1. rewrite <- H3. exact H0.    
  }
  { 
    simpl. intro. case_eq (find_valuation f (update_valuation valuat0 a false) vs).
    - intro. intro. intro. inversion H0. revert H. rewrite -> H2. apply IHvs.
    - intro. apply IHvs.
  }
Qed.
  
Lemma find_valuation_sound :
  forall form vars valuat,
    find_valuation form empty_valuation vars = Some valuat ->
    satisfiable form.
Proof.
  intros. unfold satisfiable. exists valuat.
  apply formula_to_bool_correct. revert H. apply find_valuation_sound'.
Qed.

(* Main correctness theorem *)
Theorem solver_sound: forall f,
    solver f = true -> satisfiable f.
  intro.
  unfold solver.
  case_eq (find_valuation f empty_valuation (find_vars f));
    intro; intro; try discriminate.
  intro. revert H. apply find_valuation_sound.
Qed.

(* TODO completeness proof *)
Theorem solver_complete: forall f,
    satisfiable f -> solver f = true.
Admitted.

