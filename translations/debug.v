From MetaCoq.Template Require Import utils All.

Definition testProgram : TemplateMonad unit :=
  tmPrint "Start";;
  (if true then
    tmPrint "A"
  else
    tmPrint "B");;
  tmPrint "End".

Definition test2 : TemplateMonad unit :=
  tmPrint "S1";;
  testProgram;;
  tmPrint "S2".

(* Print run_template_program. *)

(* Ltac debugger {A} (p:TemplateMonad A) := *)
(* Ltac debugger' p :=
  (* idtac p. *)
  match p with
  | tmBind ?P ?FQ => idtac "program step: " P;
    run_template_program P (fun a => debugger' (FQ a))
  | ?Q => idtac "basecase " Q;
    run_template_program Q (fun a => idtac "Result" a)
  end. *)

(* Ltac debugger' p cont :=
  (* idtac p. *)
  match p with
  | tmBind ?P ?FQ => idtac "program step: " P;
    match type of P with
    TemplateMonad ?A => 
    (* idtac A *)
    debugger' P 42
    (* (fun (a:A) => ltac:(debugger' (FQ a) cont)) *)
    (* debugger' p (fun (a:A) => ltac:(debugger' (FQ a) cont)) *)
    end
    (* run_template_program P (fun a => debugger' (FQ a)) *)
  | ?Q => idtac "basecase: " Q
  (* cont unit constr:(tt) *)
    (* run_template_program Q (fun a => idtac "Result" a) *)
  end. *)

(* Compute (ltac:(run_template_program (tmPrint "H") (fun _ => constr:(42)))). *)

(* Ltac debugger' p f :=
  (* idtac p. *)
  match p with
  | tmBind ?P ?FQ => 
  (* idtac "program step: " P; *)
    match type of P with
    TemplateMonad ?A => 

    let f a := 
      (* idtac "f inside " P; *)
      let Q := constr:(FQ a) in
      let Q' := eval lazy in Q in
      debugger' Q' f
    in
    debugger' P f


    (* idtac A *)
    (* let o := debugger' P in
    (* debugger' (FQ o) *)
    idtac o *)
    (* (fun (a:A) => ltac:(debugger' (FQ a) cont)) *)
    (* debugger' p (fun (a:A) => ltac:(debugger' (FQ a) cont)) *)
    end
    (* run_template_program P (fun a => debugger' (FQ a)) *)
  | ?Q => idtac "basecase: " Q;
    run_template_program Q f

  (* cont unit constr:(tt) *)
    (* run_template_program Q (fun a => idtac "Result" a) *)
  end. *)


Ltac debugger' p f :=
  match p with
  | tmBind ?P ?FQ => 
    match type of P with
    TemplateMonad ?A => 

    let f a := 
      let Q := constr:(FQ a) in
      let Q' := eval lazy in Q in
      debugger' Q' f (* does not matter *)
    in
    debugger' P f
    end
  | ?Q => idtac "basecase: " Q;
     (* (run_template_program Q f + idtac "Failure at " Q) *)
     first [run_template_program Q f | idtac "Failure at " Q;fail 100]
  end.


Ltac debugger p :=
  let q := eval lazy in p in
  let f a := idtac a in
  debugger' q f.
  (* (fun (a:unit) => ltac:(idtac)). *)

Ltac lindebugger' p :=
  match p with
  | tmBind ?P ?FQ => 
  (* idtac "program step: " P; *)
    let f a := 
      let Q := constr:(FQ a) in
      let Q' := eval lazy in Q in
      lindebugger' Q'
    in
     first [run_template_program P f 
     | idtac "Failure at " P;fail 100]
  | ?Q => 
  (* idtac "basecase " Q; *)
     first [run_template_program Q (fun a => idtac "Result" a) 
     | idtac "Failure at " Q;fail 100]
  end.

Ltac lindebugger p :=
  let q := eval lazy in p in
  lindebugger' q.

(* Compute ltac:(lindebugger (test2)). *)
(* Compute ltac:(debugger (testProgram)). *)

(* Compute ltac:(debugger (test2)). *)
(* Compute ltac:(debugger (@tmFail unit "End")). *)


(* MetaCoq Run (TC <- Translate emptyTC "list" ;;
                tmDefinition "list_TC" TC ).
Inductive rose := node (xs:list rose).
Fail MetaCoq Run (TC <- Translate list_TC "rose" ;;
                tmDefinition "rose_TC" TC).
Compute ltac:(debugger (TC <- Translate list_TC "rose" ;;
                tmDefinition "rose_TC" TC)). *)






(* debug printer *)

Definition debugMessage (m:string) (t:term) :=
    mkApp (tLambda (nNamed m) <% unit %> (lift0 1 t)) <% tt %>.

Search "red" "beta".
Lemma red_beta' 
  (Σ : global_env) (Γ : context) (na : name) 
  (t b a : term) (l : list term) (x:term):
  x=mkApps (b {0 := a}) l ->
  red1 Σ Γ (tApp (tLambda na t b) (a :: l)) x.
  intros ->;apply red_beta.
Qed.


Lemma subst1Nothing t t2: Ast.wf t -> (lift0 1 t) {0:=t2} = t.
intros H.
unfold subst1.
rewrite simpl_subst;trivial.
now rewrite lift0_id.
Qed.

Lemma debugId Σ Γ m t: Ast.wf t -> red Σ Γ (debugMessage m t) t.
Proof.
    intros H.
    eapply trans_red;[apply refl_red|].
    unfold debugMessage. unfold mkApp.
    apply red_beta'.
    now rewrite subst1Nothing.
Qed.

Print term.
Print monad_iter.

Print mfixpoint.
Print def.


From MetaCoq Require Import Checker.
(* Print Checker.eq_term. *)

(* Existing Instance config.default_checker_flags. *)
Definition dcf := config.default_checker_flags.
Definition ig := init_graph.


Fixpoint debugPrint (t:term) : TemplateMonad unit :=
  match t with
  | tEvar _ tl => monad_iter debugPrint tl
  | tCast t1 _ t2
  | tProd _ t1 t2
  | tLambda _ t1 t2 => debugPrint t1;;debugPrint t2
  | tLetIn _ t1 t2 t3 => debugPrint t1;;debugPrint t2;;debugPrint t3
  | tApp t tl => 
    match t,tl with
    | tLambda (nNamed msg) t1 b,[t2] =>
    if @Checker.eq_term dcf ig t1 <% unit %> && @Checker.eq_term dcf ig t2 <% tt %> then
      tmMsg (append "Debug Message: " msg);;
      print_nf b
    else
      debugPrint t;;monad_iter debugPrint tl
    | _,_ =>
      debugPrint t;;monad_iter debugPrint tl
    end
  | tProj _ t => debugPrint t
  | tCoFix mf _
  | tFix mf _ =>
    monad_iter (fun d => debugPrint (dtype d);;debugPrint (dbody d)) mf
  | _ => tmReturn tt
  end.

MetaCoq Run (debugPrint (tLambda nAnon <% nat %> (debugMessage "inner body" <% bool %>))).