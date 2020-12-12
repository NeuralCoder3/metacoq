(**  **)

(*** debug: Debug commands for programs and terms ***)

From MetaCoq.Template Require Import utils All.


(** print at which position an error occurs in a TemplateMonad programm **)
(** does not work with tmDefinition **)
(** see old commits for more variants **)
Ltac debugger' p f g :=
  lazymatch p with
  | tmBind ?P ?FQ => 
    match type of P with
    TemplateMonad ?A => 

    let f a := 
      let Q := constr:(FQ a) in
      let Q' := eval lazy in Q in
      debugger' Q' g g
    in
    debugger' P f g
    end
  | ?Q => idtac "basecase: " Q;
  run_template_program Q f
  end.

Ltac debugger p :=
  let f v := idtac "Return value: " v in
  run_template_program (tmEval cbn p) (fun q => debugger' q f f).


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

(** call: Compute ltac:(lindebugger (testProgram)). **)


(** debug messages in terms **)
Definition debugMessage (m:string) (t:term) :=
    mkApp (tLambda (nNamed m) <% unit %> (lift0 1 t)) <% tt %>.

Lemma red_beta' 
  (Σ : global_env) (Γ : context) (na : name) 
  (t b a : term) (l : list term) (x:term):
  x=mkApps (b {0 := a}) l ->
  red1 Σ Γ (tApp (tLambda na t b) (a :: l)) x.
  intros ->;apply red_beta.
Qed.

Lemma subst1Nothing t t2: Ast.wf t -> (lift0 1 t) {0:=t2} = t.
Proof.
  intros H.
  unfold subst1.
  rewrite simpl_subst;trivial.
  now rewrite lift0_id.
Qed.

(** the message does not change meaning of programs **)
Lemma debugId Σ Γ m t: Ast.wf t -> red Σ Γ (debugMessage m t) t.
Proof.
    intros H.
    eapply trans_red;[apply refl_red|].
    unfold debugMessage. unfold mkApp.
    apply red_beta'.
    now rewrite subst1Nothing.
Qed.



From MetaCoq Require Import Checker.

Definition dcf := config.default_checker_flags.
Definition ig := init_graph.

(** print all messages in a term **)
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

(* MetaCoq Run (debugPrint (tLambda nAnon <% nat %> (debugMessage "inner body" <% bool %>))). *)