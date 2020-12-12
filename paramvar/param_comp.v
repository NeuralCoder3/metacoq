(**  **)

(*** param_comp: compares old parametricity version with the new one ***)

Load param_unary.

(** lifts everything after n **)
(** morally identity **)
(** LEGACY code for comparison **)
Fixpoint tsl_rec0 (n : nat) (t : term) {struct t} : term :=
  match t with
  | tRel k => if n <= k then tRel (2*k-n+1) else t
  | tEvar k ts => tEvar k (map (tsl_rec0 n) ts)
  | tCast t c a => tCast (tsl_rec0 n t) c (tsl_rec0 n a)
  | tProd na A B => tProd na (tsl_rec0 n A) (tsl_rec0 (n+1) B)
  | tLambda na A t => tLambda na (tsl_rec0 n A) (tsl_rec0 (n+1) t)
  | tLetIn na t A u => tLetIn na (tsl_rec0 n t) (tsl_rec0 n A) (tsl_rec0 (n+1) u)
  | tApp t lu => tApp (tsl_rec0 n t) (map (tsl_rec0 n) lu)
  | tCase ik t u br => tCase ik (tsl_rec0 n t) (tsl_rec0 n u)
                            (map (fun x => (fst x, tsl_rec0 n (snd x))) br)
  | tProj p t => tProj p (tsl_rec0 n t)
  | _ => t
  end.

(** LEGACY code for comparison **)
Fixpoint tsl_rec1_app (app : option term) (E : tsl_table) (t : term) : term :=
  let tsl_rec1 := tsl_rec1_app None in
  let debug case symbol :=
      debug_term ("tsl_rec1: " ^ case ^ " " ^ symbol ^ " not found") in
  match t with
  | tLambda na A t =>
    let A0 := tsl_rec0 0 A in
    let A1 := tsl_rec1_app None E A in
    tLambda na A0 (tLambda (tsl_name tsl_ident na)
                           (subst_app (lift0 1 A1) [tRel 0])
                           (tsl_rec1_app (option_map (lift 2 2) app) E t))
  | t => let t1 :=
  match t with
  | tRel k => tRel (2 * k)
  | tSort s => tLambda (nNamed "A") (tSort s) (tProd nAnon (tRel 0) (tSort s))

  | tProd na A B =>
    let A0 := tsl_rec0 0 A in
    let A1 := tsl_rec1 E A in
    let B0 := tsl_rec0 1 B in
    let B1 := tsl_rec1 E B in
    let ΠAB0 := tProd na A0 B0 in
    tLambda (nNamed "f") ΠAB0
      (tProd na (lift0 1 A0)
             (tProd (tsl_name tsl_ident na)
                    (subst_app (lift0 2 A1) [tRel 0])
                    (subst_app (lift 1 2 B1)
                               [tApp (tRel 2) [tRel 1]])))
  | tApp t us =>
    let us' := concat (map (fun v => [tsl_rec0 0 v; tsl_rec1 E v]) us) in
    mkApps (tsl_rec1 E t) us'

  | tLetIn na t A u =>
    let t0 := tsl_rec0 0 t in
    let t1 := tsl_rec1 E t in
    let A0 := tsl_rec0 0 A in
    let A1 := tsl_rec1 E A in
    let u0 := tsl_rec0 0 u in
    let u1 := tsl_rec1 E u in
    tLetIn na t0 A0 (tLetIn (tsl_name tsl_ident na) (lift0 1 t1)
                            (subst_app (lift0 1 A1) [tRel 0]) u1)

  | tCast t c A => let t0 := tsl_rec0 0 t in
                  let t1 := tsl_rec1 E t in
                  let A0 := tsl_rec0 0 A in
                  let A1 := tsl_rec1 E A in
                  tCast t1 c (mkApps A1 [tCast t0 c A0]) (* apply_subst ? *)

  | tConst s univs =>
    match lookup_tsl_table E (ConstRef s) with
    | Some t => t
    | None => debug "tConst" (string_of_kername s)
    end
  | tInd i univs =>
    match lookup_tsl_table E (IndRef i) with
    | Some t => t
    | None => debug "tInd" (match i with mkInd s _ => string_of_kername s end)
    end
  | tConstruct i n univs =>
    match lookup_tsl_table E (ConstructRef i n) with
    | Some t => t
    | None => debug "tConstruct" (match i with mkInd s _ => string_of_kername s end)
    end
  | tCase ik t u brs as case =>
    let brs' := List.map (on_snd (lift0 1)) brs in
    let case1 := tCase ik (lift0 1 t) (tRel 0) brs' in
    match lookup_tsl_table E (IndRef (fst ik)) with
    | Some (tInd i _univ) =>
      tCase (i, (snd ik) * 2)%nat
            (tsl_rec1_app (Some (tsl_rec0 0 case1)) E t)
            (tsl_rec1 E u)
            (map (on_snd (tsl_rec1 E)) brs)
    | _ => debug "tCase" (match (fst ik) with mkInd s _ => string_of_kername s end)
    end
  | tProj _ _ => todo "tsl"
  | tFix _ _ | tCoFix _ _ => todo "tsl"
  | tVar _ | tEvar _ _ => todo "tsl"
  | tLambda _ _ _ => tVar "impossible"
  end in
  match app with Some t' => mkApp t1 (t' {3 := tRel 1} {2 := tRel 0})
               | None => t1 end
  end.

Compute (tsl_rec1' false (fun n => n) (fun n => n) [] 
  ((tProd (nNamed "y") (tVar "Y") (tRel 0)))
  ).
Compute (tsl_rec1' false (fun n => n) (fun n => n) [] 
  ((tProd (nNamed "y") (tVar "Y") (tRel 1)))
  ).
Compute (tsl_rec1' false (fun n => n) (fun n => n) [] 
  (tProd (nNamed "x") (tRel 0) (tProd (nNamed "y") (tRel 1) (tRel 0)))
  ).
Compute (tsl_rec1' false (fun n => n) (fun n => n) [] 
  (tProd (nNamed "x") (tRel 0) (tProd (nNamed "y") (tRel 1) (tRel 1)))
  ).

Compute (tsl_rec1' false (fun n => n) (fun n => n) [] 
  (tProd (nNamed "x") (tVar "X") (tProd (nNamed "y") (tVar "Y") (tRel 0)))
  ).
Compute (tsl_rec1' false (fun n => n) (fun n => n) [] 
  (tProd (nNamed "x") (tVar "X") (tProd (nNamed "y") (tVar "Y") (tRel 1)))
  ).

Definition tsl_rec1_org := tsl_rec1_app None.

Load de_bruijn_print.
Definition pretty_print := print_term (empty_ext []) [] true.

From MetaCoq Require Import Checker.

Ltac testTerm test :=
let testᵗ := constr:(tsl_rec1' 
  false
  (fun n => S(2*n))
  (fun n => 2*n)%nat
  [] test) in
let testᵗp := constr:(tsl_rec1' 
  true
  (fun n => S(2*n))
  (fun n => 2*n)%nat
  [] test) in
let testᵗ2 := constr:(tsl_rec1_org [] test) in
run_template_program (
    print_nf test;;
    bruijn_print test;;
    bruijn_print testᵗ;;
    bruijn_print testᵗ2;;
    bruijn_print testᵗp) (fun _ => 
let eq := eval hnf in (eq_term init_graph testᵗ testᵗ2) in
idtac "";idtac "equal: " eq;idtac "=====================";idtac ""
). 

Ltac testTerms xs :=
    lazymatch xs with 
    | [] => idtac "finished"
    | ?x::?xs => testTerm x;testTerms xs
    end.

Compute (ltac:(testTerms [
(tRel 0); (** test base term **)
(tProd nAnon (tRel 0) (tRel 1)); (** translation outside the scope **)
(** (tProd nAnon (tVar "None") (tProd nAnon (tVar "None") (tProd nAnon (tRel 0) (tRel 1)))); **) (** todo tsl is not printable **)
<% forall (A:Type), forall (a:A), Type %>; (** dependent prods and type translation application **)
<% forall (A:Type), forall (a:nat), Type %>; (** prod with constants **)
<% forall (f:nat -> Type) (n:nat), f n %>; (** application and body translation **)
<% forall (T:Type), Type %>; (** type translation **)
<% fun (P:Type->Type) => fun (Q:Type) => P Q %>; (** lambda with applications **)
<% fun (P:Type) => forall (p:P), P %>; (** access of outer binder **)
<% fun (P:Type) => forall (p:P) (q:P), P %>; (** multiple arguments **)
<% fun (P:Type) (Q:Type) => forall (p:P), P %>; (** multiple lambdas **)
<% fun (P:Type->Type) => fun (Q:Type) => forall (X:P Q), forall (q:Q), P Q %>; (** application and interleaved binder **)
<% fun (P:Type) => let X := P in let Y := X in forall (Q:Type->Type->Type), Q Y X %>; (** complex let in test **)
<% Type %>
])).

(** equal: true for all **)

(** takes 2min 30s with eq_term **)