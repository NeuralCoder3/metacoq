(**  **)

(*** param_all: Top level interface with user commands and combination of translations ***)

From MetaCoq.Template Require Import utils All.
From MetaCoq.Translations Require Import translation_utils.
From MetaCoq.Template Require Import Pretty.

From MetaCoq.Translations Require Import param_unary param_exists param_other.



(** define one translation to be an alias to another translation **)
(** general enough for arbitrary alias definitions **)
(** with (fun _ => "A") **)
Definition aliasDef {A} (t:A) (from to:ident->ident) :=
    id <- getIdent t;;
    na <- tmEval lazy (from id);;
    tm <- getDefTerm na;;
    tmMkDefinition (to id) tm.

(** run all translations together **)
Definition translateAll {A} (t:A) :=
    persistentTranslate_prune t true;;
    persistentExistsTranslate t;;
    existsAllParam t;;
    allExistsParam t;;
    aliasDef t tsl_ident_unparam tsl_ident_allall;;
    aliasDef t tsl_ident_exists tsl_ident_existsexists;;
    id <- getIdent t;;
    (* real name is more complicated *)
    let s := "Derived "^
    (tsl_ident_unparam id)^"="^
    (tsl_ident_allall id)^", "^
    (tsl_ident_allexists id)^", "^
    (tsl_ident_existsall id)^", and "^
    (tsl_ident_exists id)^"="^
    (tsl_ident_existsexists id)^"."
    in
    tmMsg s.

(** Userinterface = notations for the commands **)

Definition getName (x : nat -> nat) :=
  x <- tmEval cbv x;;
  t <- tmQuote x;;
  match t with 
  | Ast.tLambda (nNamed na) _ _ => tmReturn na
  | _ => tmReturn "" 
  end.

Notation name_of n := (ltac:(let k x := exact x in run_template_program (getName (fun n : nat => 0)) k)).

Notation "'Derive' 'Translations' 'for' T" := (translateAll T)(at level 8).
Notation "'Derive' 'pruned' 'Parametricity' 'for' T" := (persistentTranslate_prune T true)(at level 8).
Notation "'Derive' 'full' 'Parametricity' 'for' T" := (persistentTranslate_prune T false)(at level 8).
Notation "'Derive' 'existential' 'Parametricity' 'for' T" := (persistentExistsTranslate T true)(at level 8).
Notation "'Derive' '∃∃' 'for' T" := (persistentExistsTranslate T)(at level 8).
Notation "'Derive' '∀∀' 'for' T" := (persistentTranslate_prune T true)(at level 8).
