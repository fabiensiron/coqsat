(*
 * Formula definition and simplification
 *)
Require Import
        Coq.Bool.Bool
        Coq.Arith.PeanoNat.

Definition id := nat.

Definition valuation := id -> bool.
Definition empty_valuation (id: id) := true.
Definition update_valuation (v: valuation) (id: id) (b: bool) := 
 fun y => if y =? id then b else v y.

Inductive formula : Type :=
| Var : id -> formula
| Const : bool -> formula
| And : formula -> formula -> formula
| Or : formula -> formula -> formula
| Imply : formula -> formula -> formula
| Negate : formula -> formula.

Definition ftrue := Const true.
Definition ffalse := Const false.

Definition X := Var 0.
Definition Y := Var 1.

Definition ex_a :=
  And (Or X (Negate Y))
      (Or (Negate X) Y).

Definition ex_b :=
  Imply (Negate Y)
        (Or X Y).

Definition ex_c :=
  And X (And X ftrue).

Definition ex_d :=
  Or (Or X (Negate Y)) (Or (Negate X) Y).

Definition simplify_negate f_simp: formula :=
  match f_simp with
  | Const false => ftrue
  | Const true => ffalse
  | _ => Negate f_simp
  end.

Definition simplify_and
           (f1_simp: formula)
           (f2_simp: formula) : formula :=
  match (f1_simp, f2_simp) with
  | (Const true, Const true) => ftrue
  | (_, Const false) => ffalse
  | (Const false, _) => ffalse
  | (Const true, _) => f2_simp
  | (_, Const true) => f1_simp
  | (_, _) => And f1_simp f2_simp
  end.

Definition simplify_or
           (f1_simp: formula)
           (f2_simp: formula) : formula :=
  match (f1_simp, f2_simp) with
  | (Const false, Const false) => ffalse
  | (_, Const true) => ftrue
  | (Const true, _) => ftrue
  | (Const false, _) => f2_simp
  | (_, Const false) => f1_simp
  | (_, _) => Or f1_simp f2_simp
  end.

Definition simplify_imply
           (f1_simp: formula)
           (f2_simp: formula) : formula :=
  match (f1_simp, f2_simp) with
  | (Const true, Const false) => ffalse
  | (Const true, Const true) => ftrue
  | (Const false, _) => ftrue
  | (_, Const true) => ftrue
  | (Const true, _) => f2_simp
  | (_, Const false) => simplify_negate f1_simp
  | (_, _) => Imply f1_simp f2_simp
  end.

Definition simplify_var (valuation: valuation) (key: nat) :=
  Const (valuation key).

Fixpoint simplify_and_valuate (v: valuation) (f: formula) :=
  match f with
  | Var k => simplify_var v k
  | Const b => Const b
  | Negate f1 => simplify_negate (simplify_and_valuate v f1)
  | Or f1 f2 => simplify_or (simplify_and_valuate v f1)
                            (simplify_and_valuate v f2)
  | And f1 f2 => simplify_and (simplify_and_valuate v f1)
                              (simplify_and_valuate v f2)
  | Imply f1 f2 => simplify_imply (simplify_and_valuate v f1)
                                  (simplify_and_valuate v f2)
  end.

Fixpoint simplify f: formula :=
  simplify_and_valuate empty_valuation f.

Example ex_simplify_1 :
  simplify (Negate ftrue) = ffalse.
Proof.
  reflexivity.
Qed.

Example ex_simplify_2 :
  simplify (And ftrue ffalse) = ffalse.
Proof.
  reflexivity.
Qed.

Definition formula_to_bool (f:formula) :=
  match f with
  | Const b => Some b
  | _ => None
  end.

Lemma formula_to_bool_correct:
  forall f v, simplify_and_valuate f v = Const true ->
              formula_to_bool (simplify_and_valuate f v) = Some true.
Proof. 
  intros f v. intro H.
  unfold formula_to_bool. rewrite H. reflexivity.
Qed.

Definition satisfiable (f:formula) :=
  exists V:valuation,
    formula_to_bool (simplify_and_valuate V f) = Some true.

Definition valid (f:formula) :=
  forall V:valuation,
    formula_to_bool (simplify_and_valuate V f) = Some true.

Lemma ex_a_satisfiable :
  satisfiable ex_a.
Proof.
  unfold ex_a.
  now exists (fun x => false).
Qed.

Lemma ex_b_satisfiable :
  satisfiable ex_b.
Proof.
  unfold ex_b.
  now exists (fun x => true).
Qed.

Lemma ex_d_valid :
  valid ex_d.
Proof.
  unfold ex_d.
  unfold valid.
  intro V.
  simpl. case_eq (simplify_var V 0); case_eq (simplify_var V 1);
           try repeat unfold simplify_var; try discriminate.
  intros. case_eq b; case_eq b0;
            inversion H; inversion H0; intros;
              rewrite H1; rewrite H4; simpl; reflexivity.
Qed.

