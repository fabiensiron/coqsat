Require Import Coq.Lists.List.
Import ListNotations.

Require Import CoqSat.Formula.

Definition formula_to_sat (f: formula) (v: valuation): option valuation :=
  match (simplify_and_valuate v f) with
  | Const true => Some v
  | _ => None                       
  end.

Fixpoint find_valuation (f: formula) (v: valuation) (vars: list nat): option valuation :=
  match vars with
  | var::vars' =>
    let ffalse_valuation := update_valuation v var false in
    let ftrue_valuation := update_valuation v var true in
    match (find_valuation f ffalse_valuation vars') with
    | Some v' => Some v'
    | None => find_valuation f ftrue_valuation vars'
    end
  | nil => formula_to_sat f v
  end.

Fixpoint find_vars (f: formula): list nat :=
  match f with
  | Var k => cons k nil
  | Const _ => nil
  | Negate f' => find_vars f'
  | Or f1 f2 => concat [(find_vars f1); (find_vars f2)]
  | And f1 f2 => concat [(find_vars f1); (find_vars f2)]
  | Imply f1 f2 => concat [(find_vars f1); (find_vars f2)]
  end.
                                      
Definition solver (f: formula): bool :=
  let vars := find_vars f in
  match (find_valuation f empty_valuation vars) with
  | None => false
  | Some _ => true
  end.

