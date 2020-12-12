
From MetaCoq.Template Require Import utils All.


Definition mkFreshName (n:name) : TemplateMonad name :=
  match n with
  | nAnon => tmReturn nAnon
  | nNamed m => m' <- tmFreshName m;; tmReturn (nNamed m')
  end.
Definition mkFreshContextDecl (x:context_decl) : TemplateMonad context_decl :=
  name' <- mkFreshName (decl_name x);;
  tmReturn {|
    decl_name := name';
    decl_body := decl_body x;
    decl_type := decl_type x
  |}.

Definition mkFreshOneInd (x:one_inductive_body) : TemplateMonad one_inductive_body :=
  ident' <- tmFreshName (ind_name x);;
  ctors' <- monad_map (fun '(id,t,n) => id' <- tmFreshName id;;tmReturn ((id',t),n)) (ind_ctors x);;
  projs' <- monad_map (fun '(id,t) => id' <- tmFreshName id;;tmReturn (id',t)) (ind_projs x);;
  tmReturn {|
    ind_name := ident';
    ind_type := ind_type x;
    ind_kelim := ind_kelim x;
    ind_ctors := ctors';
    ind_projs := projs'
  |}.

Definition mkFreshMutual (x:mutual_inductive_body) : TemplateMonad mutual_inductive_body :=
  param' <- monad_map mkFreshContextDecl (ind_params x);;
  bodies' <- monad_map mkFreshOneInd (ind_bodies x);;
  tmReturn
   {|
    ind_finite := ind_finite x;
    ind_npars := ind_npars x;
    ind_params := param';
    ind_bodies := bodies';
    ind_universes := ind_universes x;
    ind_variance := ind_variance x
  |}.