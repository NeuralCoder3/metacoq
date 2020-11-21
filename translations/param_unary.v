(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils All.
From MetaCoq.Translations Require Import translation_utils.
From MetaCoq.Template Require Import Pretty.

Local Infix "<=" := Nat.leb.

Definition default_term := tVar "constant_not_found".
Definition debug_term msg:= tVar ("debug: " ^ msg).



(* Definition subst_app := mkApps. *)
  (* Definition todo := tVar. *)


(* lifts everything after n *)
(* morally identity *)
(* TODO: general nested lifting *)
(* TODO: term mapping on base terms (like tRel) *)
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
  (* | tFix : mfixpoint term -> nat -> term *)
  (* | tCoFix : mfixpoint term -> nat -> term *)
  | _ => t
  end.

Definition tsl_rec0' (n : nat) (t : term) : term := t.




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




(* the unary parametricity translation of an object is
a relation over the objects *)
(* X_1 is the unary parametricity translation
where the identifiers are Xᵗ *)
(*
types T are translated into relations of objects of type T
  (using lambas for the objects)
terms are translated to proofs of the relations
*)
(* Definition up (relTrans:nat->nat) (n:nat) :nat :=
  pred (relTrans n). *)
  (* match n with
  1 => O
  | _ => n
  end. *)
Print lift.




(* Fixpoint tsl_rec0_2 (rel:nat->nat) (from : nat) (t : term) {struct t} : term :=
  match t with
  | tRel k => if from <= k then tRel (from+rel (k-from)) else t
  | tEvar k ts => tEvar k (map (tsl_rec0_2 rel from) ts)
  | tCast t c a => tCast (tsl_rec0_2 rel from  t) c (tsl_rec0_2 rel from a)
  | tProd na A B => tProd na (tsl_rec0_2 rel from A) (tsl_rec0_2 rel (from+1) B)
  | tLambda na A t => tLambda na (tsl_rec0_2 rel from A) (tsl_rec0_2 rel (from+1) t)
  | tLetIn na t A u => tLetIn na (tsl_rec0_2 rel from t) (tsl_rec0_2 rel from A) (tsl_rec0_2 rel (from+1) u)
  | tApp t lu => tApp (tsl_rec0_2 rel from t) (map (tsl_rec0_2 rel from) lu)
  | tCase ik t u br => tCase ik (tsl_rec0_2 rel from t) (tsl_rec0_2 rel from u)
                            (map (fun x => (fst x, tsl_rec0_2 rel from (snd x))) br)
  | tProj p t => tProj p (tsl_rec0_2 rel from  t)
  (* | tFix : mfixpoint term -> nat -> term *)
  (* | tCoFix : mfixpoint term -> nat -> term *)
  | _ => t
  end. *)

Definition Env := nat -> nat.
Definition EnvUp (E:Env) : Env :=
  fun n => match n with
  | O =>  O
  | S x => S (E x)
  end.

Definition EnvLift (E:Env) (n:nat) (k:nat) : Env :=
  fun x => let y := E x in
  if k<=y then n+y else y.

Definition EnvLift0 E n := EnvLift E n 0.

Fixpoint tsl_rec0_2 (rel:Env) (t : term) {struct t} : term :=
  match t with
  | tRel k => tRel (rel k)
  | tEvar k ts => tEvar k (map (tsl_rec0_2 rel ) ts)
  | tCast t c a => tCast (tsl_rec0_2 rel t) c (tsl_rec0_2 rel a)
  | tProd na A B => tProd na (tsl_rec0_2 rel A) (tsl_rec0_2 (EnvUp rel) B)
  | tLambda na A t => tLambda na (tsl_rec0_2 (EnvUp rel) A) (tsl_rec0_2 (EnvUp rel) t)
  | tLetIn na t A u => tLetIn na (tsl_rec0_2 rel t) (tsl_rec0_2 rel A) (tsl_rec0_2 (EnvUp rel) u)
  | tApp t lu => tApp (tsl_rec0_2 rel t) (map (tsl_rec0_2 rel) lu)
  | tCase ik t u br => tCase ik (tsl_rec0_2 rel t) (tsl_rec0_2 rel u)
                            (map (fun x => (fst x, tsl_rec0_2 rel (snd x))) br)
  | tProj p t => tProj p (tsl_rec0_2 rel t)
  (* | tFix : mfixpoint term -> nat -> term *)
  (* | tCoFix : mfixpoint term -> nat -> term *)
  | _ => t
  end.

(* Goal forall r n k E, EnvUp (EnvLift E n k) r = EnvLift E n (S k) r.
Proof.
  induction r;cbn;intros.
  - unfold EnvLift.
  induction t using term_forall_list_ind;cbn;
  try rewrite IHt1;try rewrite IHt2;try easy;intros n0 k E.

Goal forall t n k E, tsl_rec0_2 (EnvLift E n k) t = lift n k (tsl_rec0_2 E t).
Proof.
  induction t using term_forall_list_ind;cbn;
  try rewrite IHt1;try rewrite IHt2;try easy;intros n0 k E.
  - admit.
  - f_equal.
    + apply IHt1.
    + apply IHt2. *)

(* Goal forall t, tsl_rec0_2 (fun n => n) t = t.
Proof.
  induction t using term_forall_list_ind;cbn;
  try rewrite IHt1;try rewrite IHt2;try easy.
  - admit.
  - now rewrite IHt1, IHt2. *)

  Compute(EnvUp (EnvLift (fun n => n) 2 0) 1).
  Compute(EnvLift (EnvUp (fun n => n)) 2 1 1).

(* Goal forall n E, (forall n, E n >= n) -> EnvUp (EnvLift E 2 0) n = EnvLift (EnvUp E) 2 1 n.
Proof.
intros n E H.
  induction n;trivial;cbn.
  unfold EnvLift, EnvUp.
  assert(1<=E n) as -> by lia.
  rewrite <- IHn. *)


Fixpoint tsl_rec1' (Env Envt: nat -> nat) (E : tsl_table) (t : term) : term :=
  let debug case symbol :=
      debug_term ("tsl_rec1: " ^ case ^ " " ^ symbol ^ " not found") in
  match t with
  (* types *)
  | tSort s => (* s ⇒ λ (A:s). A → s *)
  (* s_1: s -> s' and for A:s, s_1 A holds and A_1 : s_1 A *)
  (* a relation over types A of sort s, the s in the end is the property *)
    tLambda (nNamed "X") (tSort s) (tProd nAnon (tRel 0) (tSort s))
  | tProd na A B =>
  (* ∀ (x:A). B ⇒ λ(f:∀(x:A_0,B_0)). ∀(x:A_0) (xᵗ:A_1 x). B_1 (f x) *)
  (* the translation relates functions A->B 
    by the relation of their results (B) on related inputs (x) *)

    tLambda (nNamed "f") (tProd na (tsl_rec0_2 Env A) (tsl_rec0_2 (EnvUp Env) B))
      (tProd na (tsl_rec0_2 (EnvLift0 Env 1) A)
      (*     x  :  A      *)
                (* lift over f *)
             (tProd (tsl_name tsl_ident na)
                    (subst_app (tsl_rec1' (EnvLift0 Env 2) (EnvLift0 Envt 2) E A) [tRel 0])
                    (* xᵗ           Aᵗ           x  *)
                               (* lift over x, f *)
                    (* (subst_app (lift0 0 (lift 1 2 B1)) *)
                    (* (subst_app (tsl_rec1' (EnvLift 1 0 (EnvLift 1 1 Env)) (EnvLift 2 1 Envt) E B) *)
                    (* (subst_app (tsl_rec1' (EnvLift (EnvLift Env 1 1) 1 0) (EnvLift (EnvUp Envt) 2 1) E B) *)
                    (subst_app (tsl_rec1' (EnvLift (EnvLift (EnvUp Env) 1 1) 1 0) (EnvLift (EnvUp Envt) 2 1) E B)
                    (* (subst_app (lift0 1 (lift 1 2 B1)) *)
                    (* (subst_app (lift0 1 (lift 0 2 B1)) *)
                                (* lift after x over f and all over x^t *)
                               [tApp (tRel 2) [tRel 1]])))

(* old
  (* for A^t take relations like A -> lift up to position of A *)
  (* for apply to tRel 0 which is A *)
    (* let A0 := lift0 1 (tsl_rec0' 0 A) in *)
    let A0 := (tsl_rec0_2 liftTsl0 A) in
    (* let B0 := lift 1 1 (tsl_rec0' 1 B) in *)
    let B0 := (tsl_rec0_2 liftTsl0 B) in
    (* let A1 := tsl_rec1' (up 0 liftTsl0) liftTsl1 E A in *)
    let B1 := tsl_rec1' (up 1 1 liftTsl0) liftTsl1 E B in
    let ΠAB0 := tProd na A0 B0 in (* could (maybe) & should be infered *)
    tLambda (nNamed "f") ΠAB0
      (tProd na (tsl_rec0_2 (up 1 0 liftTsl0) A0)
      (*     x  :  A      *)
                (* lift over f *)
             (tProd (tsl_name tsl_ident na)
                    (subst_app (tsl_rec1' (up 2 0 liftTsl0) (up 2 0 liftTsl1) E A) [tRel 0])
                    (* xᵗ           Aᵗ           x  *)
                               (* lift over x, f *)
                    (* (subst_app (lift0 0 (lift 1 2 B1)) *)
                    (subst_app (tsl_rec1' (up 1 0 (up 1 1 liftTsl0)) (up 2 1 liftTsl1) E B)
                    (* (subst_app (lift0 1 (lift 1 2 B1)) *)
                    (* (subst_app (lift0 1 (lift 0 2 B1)) *)
                                (* lift after x over f and all over x^t *)
                               [tApp (tRel 2) [tRel 1]]))) *)
                               (*       f        x *)


    (* let A0 := tsl_rec0 0 A in
    let A1 := tsl_rec1 E A in
    let B0 := tsl_rec0 1 B in
    let B1 := tsl_rec1 E B in
    let ΠAB0 := tProd na A0 B0 in (* could (maybe) & should be infered *)
    tLambda (nNamed "f") ΠAB0
      (tProd na (lift0 1 A0)
             (tProd (tsl_name tsl_ident na)
                    (subst_app (lift0 2 A1) [tRel 0])
                    (subst_app (lift 1 2 B1)
                               [tApp (tRel 2) [tRel 1]]))) *)

  (* values *)
  (* | tRel (S k) => (* x ⇒ xᵗ *)
    tRel k *)
  | tRel k => (* x ⇒ xᵗ *)
  (* TODO: maybe wrong
  Q x, T  -> Q x x^t, T
  0(x) => 0(x^t)

  Q y z, T -> Q y y^t z z^t, T
  1(y) => 2(y^t)
  *)
    (* tRel k *)
    (* tRel (liftTsl1 k) *)
    tRel (Envt k)
    (* tRel (pred k) *)
    (* tRel (relTrans k) *)
    (* tRel (2 * k) *)
  | tLambda na A t =>  (* ignore firt *)
  (* TODO: type of result *)
    (* λ(x:A).t ⇒ λ(x:A_0)(xᵗ:A_1 x). t_1 *)

    (* proof of function A->B is translated to proof 
      of a relation of B taking related arguments
    *)
    (* todo "tsl lam" *)
    tLambda na (tsl_rec0_2 Env A) 
      (tLambda (tsl_name tsl_ident na)
               (subst_app (tsl_rec1' (EnvLift0 Env 1) (EnvLift0 Envt 1) E A) [tRel 0])
                           (* (tsl_rec1' (EnvLift0 1 Env) (EnvLift 1 1 Envt)  E t)) *)
                           (tsl_rec1' (EnvLift (EnvUp Env) 1 0) (EnvLift (EnvUp Envt) 1 1)  E t))
    (* let A0 := tsl_rec0' 0 A in
    let A1 := tsl_rec1' relTrans E A in
    tLambda na A0 (tLambda (tsl_name tsl_ident na)
                           (subst_app (lift0 1 A1) [tRel 0])
                           (tsl_rec1' relTrans E t)) *)
  | tApp t us =>
  (* t1 t2 ⇒ t1_1 t2_0 t2_1 *)
  (* for every argument t2 the relation of t1 is supplied with
   the argument t2 and the relation over t2 *)
    (* todo "tsl tApp" *)
    let us' := concat (map (fun v => [tsl_rec0_2 Env v; tsl_rec1' Env Envt E v]) us) in
    mkApps (tsl_rec1' Env Envt E t) us'
    (* let us' := concat (map (fun v => [tsl_rec0' 0 v; tsl_rec1' relTrans E v]) us) in
    mkApps (tsl_rec1' relTrans E t) us' *)

  | tLetIn na t A u =>
  (* TODO: documentation *)
    tLetIn na (tsl_rec0_2 Env t) (tsl_rec0_2 Env A) 
    (tLetIn (tsl_name tsl_ident na) 
          (tsl_rec1' (EnvLift0 Env 1) (EnvLift0 Envt 1) E t)
          (subst_app (tsl_rec1' (EnvLift0 Env 1) (EnvLift0 Envt 1) E A) [tRel 0]) 
          (tsl_rec1' (EnvLift (EnvUp Env) 1 0) (EnvLift (EnvUp Envt) 1 1)  E u))

    (* let t0 := tsl_rec0 0 t in
    let t1 := tsl_rec1 E t in
    let A0 := tsl_rec0 0 A in
    let A1 := tsl_rec1 E A in
    let u0 := tsl_rec0 0 u in
    let u1 := tsl_rec1 E u in
    tLetIn na t0 A0 (tLetIn (tsl_name tsl_ident na) (lift0 1 t1)
                            (subst_app (lift0 1 A1) [tRel 0]) u1) *)

  | tCast t c A => 
  (* TODO: documentation *)
  tCast (tsl_rec1' Env Envt E t) c 
    (mkApps (tsl_rec1' Env Envt E A) 
      [tCast (tsl_rec0_2 Env t) c (tsl_rec0_2 Env A)])
    (* let t0 := tsl_rec0 0 t in
    let t1 := tsl_rec1 E t in
    let A0 := tsl_rec0 0 A in
    let A1 := tsl_rec1 E A in(* apply_subst instead of mkApps? *)
    tCast t1 c (mkApps A1 [tCast t0 c A0])  *)
  (* | tCast _ _ _ | tLetIn _ _ _ _ => todo "tsl" *)


    (* TODO: combine and use 
        lookupConstant, 
        constantRef (t:term) {H:isConstant t}, 
        isConstant *)
  (* all three constants are translated by a lookup in the table *)
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
  (* TODO: documentation, code *)
    let brs' := List.map (on_snd (lift0 1)) brs in
    let case1 := tCase ik (lift0 1 t) (tRel 0) brs' in
    match lookup_tsl_table E (IndRef (fst ik)) with
    (* | Some (tInd i _univ) =>
      tCase (i, (snd ik) * 2)%nat
            (tsl_rec1_app (Some (tsl_rec0 0 case1)) E t)
            (tsl_rec1 E u)
            (map (on_snd (tsl_rec1 E)) brs) *)
    | _ => debug "tCase" (match (fst ik) with mkInd s _ => string_of_kername s end)
    end
  (* TODO: documentation, code *)
  | tProj _ _ => todo "tsl"
  | tFix _ _ | tCoFix _ _ => todo "tsl"
  | tVar _ | tEvar _ _ => todo "tsl var"
  end.
(* Tests for manual prod lifting
Compute (tsl_rec1' (fun n => n) (fun n => n) [] 
  ((tProd (nNamed "y") (tVar "Y") (tRel 0)))
  ).
Compute (tsl_rec1' (fun n => n) (fun n => n) [] 
  ((tProd (nNamed "y") (tVar "Y") (tRel 1)))
  ).
Compute (tsl_rec1' (fun n => n) (fun n => n) [] 
  (tProd (nNamed "x") (tRel 0) (tProd (nNamed "y") (tRel 1) (tRel 0)))
  ).
Compute (tsl_rec1' (fun n => n) (fun n => n) [] 
  (tProd (nNamed "x") (tRel 0) (tProd (nNamed "y") (tRel 1) (tRel 1)))
  ).
*)

(* Compute (tsl_rec1' (fun n => n) (fun n => n) [] 
  (tProd (nNamed "x") (tVar "X") (tProd (nNamed "y") (tVar "Y") (tRel 0)))
  ).
Compute (tsl_rec1' (fun n => n) (fun n => n) [] 
  (tProd (nNamed "x") (tVar "X") (tProd (nNamed "y") (tVar "Y") (tRel 1)))
  ). *)

Definition tsl_rec1_org := tsl_rec1_app None.
(* Definition tsl_rec1 := tsl_rec1'. *)

(* Definition closeTerm () *)

Load de_bruijn_print.
Definition pretty_print := print_term (empty_ext []) [] true.
(* Definition test := <% Type %>. *)
(* Definition test := (tRel 0). *)
(* Problems *)
(* Definition test := (tProd nAnon (tRel 0) (tRel 1)). *)
(* Definition test := (tProd nAnon (tVar "None") (tProd nAnon (tVar "None") (tProd nAnon (tRel 0) (tRel 1)))). *)
(* Definition test := <% forall (A:Type), forall (a:A), Type %>. *)
(* Definition test := <% forall (T:Type), Type %>. *)
(* Definition test := <% fun (P:Type->Type) => fun (Q:Type) => P Q %>. *)
(* Definition test := <% fun (P:Type) => forall (p:P), P %>. *)
(* Definition test := <% fun (P:Type) => forall (p:P) (q:P), P %>. *)
(* Definition test := <% fun (P:Type) (Q:Type) => forall (p:P), P %>. *)
(* Definition test := <% fun (P:Type->Type) => fun (Q:Type) => forall (X:P Q), forall (q:Q), P Q %>. *)
Definition test := <% fun (P:Type) => let X := P in let Y := X in forall (Q:Type->Type->Type), Q Y X %>.

Definition idEnv : Env := fun n => n.
Notation "'if' x 'is' p 'then' A 'else' B" :=
  (match x with p => A | _ => B end)
    (at level 200, p pattern,right associativity).
(* Definition testᵗ := tsl_rec1' idEnv idEnv [] test. *)
Definition testᵗ := tsl_rec1' 
  (* (fun n => if n is 0 then 1 else (if n is 1 then 3 else n)) 
  (fun n => if n is 1 then 2 else n)  *)
  (fun n => S(2*n))
  (fun n => 2*n)%nat
  [] test.
Definition testᵗ2 := tsl_rec1_org [] test.
(* Print test.
Compute testᵗ. *)

(* Compute testᵗ.
Compute testᵗ2. *)

MetaCoq Run (print_nf test).
MetaCoq Run (bruijn_print testᵗ).
MetaCoq Run (bruijn_print testᵗ2).

Compute (pretty_print (testᵗ)).


Definition tsl_rec1 := tsl_rec1' (fun n => S(2*n)) (fun n => 2*n)%nat.
(* Definition tsl_rec1 := tsl_rec1_org. *)


(* deletes lambdas in front of a term *)
(* ued for product relation function *)
Fixpoint remove_lambda (t : term) : term :=
  match t with
  | tLambda _ _ B => remove_lambda B
  | _ => t
  end.

(* collect prods into context list and remaining term *)
(* inverse (up to reversion) of it_mkProd_or_LetIn 
  (for vass in back direction) *)
Fixpoint decompose_prod_context (t : term) : context * term :=
  match t with
  | tProd n A B => let (Cs, B) := decompose_prod_context B in
                  (vass n A :: Cs, B)
  | _ => ([], t)
  end.

(* translates a parameter list *)
(* moves parameters as prods in front of Type,
  translates it,
  removes first relation lambda, converts back to context (declaration list)
  and deletes sort translation prod at the end
*)
(* the parameters are stored in reverse order,
but the it_mkProd_or_LetIn uses a reversed list
in the end a reversion is needed as decompose
is in correct order *)
Definition transformParams (E:tsl_table) (params:context) : context :=
    (let paramType := it_mkProd_or_LetIn params <% Type %> in (* TODO: does Type always work *)
    let transformRel := tsl_rec1 E paramType in
    let prods := fst(decompose_prod_context (remove_lambda transformRel)) in
    tl (rev prods)).

(* translates a mutual inductive definition *)
(* the translation is constructed in proof mode 
to follow the structure, keep track of types,
avoid deep nesting and delay application arguments
*)
Definition tsl_mind_body (E : tsl_table) (mp : modpath) (kn : kername)
           (mind : mutual_inductive_body) : tsl_table * list mutual_inductive_body.
  (* computes the new parameters *)
  (* the unquoting does not care about the parameters but only about the length
  of ind_params *)
  (* for a pure unary parametricity translation even
  mind.(ind_params) ++ mind.(ind_params) workds *)
 (* the universe of the inductive and the variance are not changed by the translation *)
  set(paramlist := transformParams E mind.(ind_params)).
  refine (_, [{| ind_npars := #|paramlist|;
                 ind_params := paramlist;
                 ind_bodies := _;
                 ind_finite := mind.(ind_finite);
                 ind_universes := mind.(ind_universes);
                 ind_variance := mind.(ind_variance)|}]).
  - (* new translations for the one_inductive_bodies in the 
     mutual inductive definition *)
    refine (let kn' : kername := (mp, tsl_ident kn.2) in
            fold_left_i (fun E i ind => _ :: _ ++ E) mind.(ind_bodies) []).
    (* for each one_inductive ind with index i, add new table *)
    + (* translation reference of inductive *)
      (* the new type kn' does not exists yet, but will in future translations *)
      exact (IndRef (mkInd kn i), tInd (mkInd kn' i) []).
    + (* translation references of ctors of ind *)
    (* create reference for each constructor k *)
      refine (fold_left_i (fun E k _ => _ :: E) ind.(ind_ctors) []).
      exact (ConstructRef (mkInd kn i) k, tConstruct (mkInd kn' i) k []).
  - (* translate the one_inductive_bodys individually *)
    refine (mapi _ mind.(ind_bodies)).
    intros i ind. (* number of inductive body and body *)
    refine {| ind_name := tsl_ident ind.(ind_name);
              ind_type := _;
              ind_kelim := ind.(ind_kelim);
              ind_ctors := _;
              ind_projs := [] |}. (* TODO: projections *)
    + (* translate the type (with parameters) of the inductive body *)
      refine (subst_app (tsl_rec1 E ind.(ind_type))
                                  [tInd (mkInd kn i) []]).
    + (* constructors *)
      (* definition as function for better control flow overview *)
    refine(
      mapi 
      (
        fun k '((name,typ,nargs)) => 
        let ctor_type :=
        subst_app 
        (* possibility: add nat -> tRel 0 in table for 
          fill-in and then translate *)
          ((fold_left_i 
            (* fill in implicit tRel for 
                mutual types and inductive type itself *)
            (fun t0 i u  => t0 {S i := u})
            (rev (mapi (fun i _ => tInd (mkInd kn i) [])
                              mind.(ind_bodies)))
            (tsl_rec1 E typ)) (* first translate s.t. tRel 0 => tRel 0 ; tRel 1 
              instead of nat => nat ; nat^t (does not exists) *)
          )
         [tConstruct (mkInd kn i) k []] 
         (* place original constructor in generated relation as tRel 0 *) in
        (tsl_ident name, (* translate constructor name *)
        ctor_type, (* translated constructor type *)
        #|fst (decompose_prod_context ctor_type)|) (* all prods are arguments *)
      )
      ind.(ind_ctors)
    ).
Defined.


(* one way to get the dot character '.' *)
Definition dot : Ascii.ascii.
destruct "." eqn:H;[discriminate|assumption].
Defined.

(* computes last part after dot *)
(* needed to find identifies of, for example, local definitions *)
(* definitions and fresh names can not be generated 
  when a modpath-part with '.' is present *)
Fixpoint lastPart (id:ident) :=
  match id with
  | EmptyString => (id,false)
  | String a id' => 
    let (idr,b) := lastPart id' in
    if b then (idr,b) else
    (
      if Ascii.eqb a dot then (idr,true) else (String a idr,false) 
    )
  end.

  
Definition tsl_ident' id := tsl_ident(fst(lastPart id)).

(* registeres the unary parametricity translations as translation instance *)
Instance param : Translation :=
  {| tsl_id := tsl_ident' ;
     tsl_tm := fun ΣE t => ret (tsl_rec1 (snd ΣE) t) ;
     (* Implement and Implement Existing cannot be used with this translation *)
     tsl_ty := None ;
     tsl_ind := fun ΣE mp kn mind => 
     ret (tsl_mind_body (snd ΣE) mp kn mind) |}.


(* stores translation of definitions *)
(* global context is not important => always use empty_ext [] *)
(* better would be the translated global_reference but 
  this is not accessible from the outside *)
Class translated (ref:global_reference) := 
{
  (* content : term  *) (* would be enough for constant *)
  content : tsl_table (* needed for inductive translations *)
  (* for constants this degenerates to [(ref,contentTerm)] *)
}.

(* lookup a global reference in the translation database and add its
  translation table to the context *)
Definition checkTranslation (ΣE:tsl_context) (ref:global_reference) : TemplateMonad tsl_context :=
      match lookup_tsl_table (snd ΣE) ref with
      | Some _ => ret ΣE
      | None => 
      (* lookup if a translation exists *)
          opt <- tmInferInstance None (translated ref);;
          match opt with (* match over custom option type for inference results *)
          | my_Some x => 
            let Σ' := fst ΣE in
            let E' := ((@content _ x)  ++ (snd ΣE))%list in (* TODO: can contain duplicates (see below) *)
            Σ' <- tmEval lazy Σ' ;;
            E' <- tmEval lazy E' ;;
            ret (Σ', E')
          | my_None => ret ΣE
          end
      end.

(* quotes the environment and adds translations of declarations 
  from it to the context *)
(* for additional creation of missing translations,
use TranslateRec with constructed table as seed *)
Definition ConstructTable {A} (t:A) : TemplateMonad tsl_context :=
  p <- tmQuoteRec t ;;
  tmPrint "~~~~~~~~~~~~~~~~~~" ;;
  monad_fold_right (fun ΣE '(kn, decl) =>
    print_nf ("Looking up " ^ string_of_kername kn) ;;
    match decl with
    | ConstantDecl decl => checkTranslation ΣE (ConstRef kn)
    | InductiveDecl d => checkTranslation ΣE (IndRef (mkInd kn 0))
    end)
  (fst p) (emptyTC).

(* the cases could be all in one and the command with 
  distinction on references/other terms could be a Template command
 *)
Definition getIdentKername {A} (t:A)  : TemplateMonad kername :=
  q <- tmQuote t;;
  tmReturn match q with
  (* handle all cases in one *)
  | tInd (mkInd kername _) _
  | tConst kername _
  | tConstruct (mkInd kername _) _ _ => 
    kername
  | _ => (MPfile [],"") (* dummy value *)
  end.

(* gets the local identifier (short name) *)
Definition getIdent {A} (t:A)  : TemplateMonad string :=
  kername <- getIdentKername t;;
  tmReturn (snd kername).

(* full mod path and identifier (separated by '.') *)
Definition getIdentComplete {A} (t:A)  : TemplateMonad string :=
  kername <- getIdentKername t;;
  tmReturn (string_of_kername kername).

  (* retrieves a reference from a coq term of a definition *)
Definition tmLookup {A} (t:A) : TemplateMonad global_reference :=
  getIdentComplete t >>= tmLocate1.

(* generates a table with all translations possibly needed for lookup *)
Definition persistentTranslate {A} (t:A) : TemplateMonad tsl_context :=
  tc <- ConstructTable t;; (* get table *)
  id <- getIdentComplete t;;
  idname <- getIdent t;;
  tc' <- Translate tc id;; (* translate new definition *)

  gr <- tmLookup t;;
  (* extend table *)
  (* TODO: too large only needs new part *)
  (* easiest way would be to undup (or track what is new) *)
  (* variant 1: new-old *)
  (* variant 2: undup in creation *)
  (* variant 3: tracking *)
      nameString <- tmEval lazy (append idname "_tableLookup");;
      newName <- tmFreshName nameString;;
      tmDefinition newName (
        {|
            content := snd tc';
        |} : translated gr
      );;
  (* save new table for the translation definition t *)
  tmExistingInstance (VarRef newName);;
  tmReturn tc'
  .

