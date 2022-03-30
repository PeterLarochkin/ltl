(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                            Solange Coupet-Grimal                         *)
(*                                                                          *)
(*                                                                          *)
(*           Laboratoire d'Informatique Fondamentale de Marseille           *)
(*                   CMI-Technopole de Chateau-Gombert                      *)
(*                       39, Rue F. Joliot Curie                            *)
(*                       13453 MARSEILLE Cedex 13                           *)
(*                    Solange.Coupet@cmi.univ-mrs.fr                        *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V7.0                                  *)
(*                             Juillet  2002                                *)
(*                                                                          *)
(****************************************************************************)
(*                                  safety.v                                *)
(****************************************************************************)

(* Require Import List. *)
(* Check list.

Inductive list(A : Set) : Set :=
| nil : list A
| cons : A -> list A -> list A
. *)






Section safety.

Require Export ltl.
Variables (state label : Set) (transition : label -> relation state)
  (init_state : state -> Prop).

  
Notation Stream := (stream state) (only parsing).
Notation State_formula := (state_formula state) (only parsing).
Notation Stream_formula := (stream_formula state) (only parsing).
Notation Invariant := (invariant transition) (only parsing).
Notation None_or_one_step := (none_or_one_step transition) (only parsing).
Notation Trace := (trace transition) (only parsing).
Notation Safe := (safe init_state transition) (only parsing).
Notation Run := (run init_state transition) (only parsing).


(***************************** Always idempotence ***************************)

Lemma always_assumption :
 forall P Q : stream_formula state,
 (forall str : stream state, always Q str -> P str) ->
 forall str : stream state, always Q str -> always P str.
Proof. 
intros P Q. cofix str.
intros H_Q_P str0.
case str0; clear str0.
intros s str1 always_Q.
constructor; auto.
apply str; auto.
inversion always_Q; assumption.
Qed.
Print always_assumption.
Hint Resolve always_assumption.

Lemma always_idempotence :
 forall (Q : stream_formula state) (str : stream state),
 always Q str -> always (always Q) str.
 Proof.
eauto.
Qed.

(***************************** Safety  Lemmas *******************************)
(* не понятно, *)
Lemma inv_clos :
 forall P : state_formula state,
 invariant transition P ->
 forall s t : state, none_or_one_step transition s t -> P s -> P t.
Proof.
simple induction 2.
auto.
clear H0 t; intros t Hstep Ps; apply H with (s := s); assumption.
Qed.


(* Lemma 4.3 *)
Lemma induct :
 forall P : state_formula state,
 invariant transition P ->
 forall str : stream state,
 trace transition str ->
 P (head_str str) -> always (state2stream_formula P) str.
Proof.
  (* разбивает forall (->) *)
intro P. 
(* разбивает -> *)
intro Inv. 
unfold state2stream_formula in |- *.
(* индукция по коиндуктивной конструкции,  *)
 cofix induct.
 
  intro str.
(* представим str как составные части с forall *)
  case str.
 simpl in |- *.
intros h tl Htrace Hhead.
 simpl. 
 (* чтобы доказать always, нужно доказать его аргументы *)
 constructor.
 simpl.
 apply Hhead.
  (* try assumption. *)
  (* тут *)
apply induct.
  (* применили индакт к цели (1->2->3), therefore for (3) need proof (1),(2) *)
 clear induct.
 (* тактика, которая выводит всевозможные выводы из гипотезы *)
inversion Htrace.

(* Definition trace : stream -> Prop :=
  always
    (fun str : stream =>
     none_or_one_step (head_str str) (head_str (tl_str str))). *)


 assumption.

 (* make Htrace -> anything *)
generalize Htrace.

(* представим tl как составные части с forall *)
 case tl. 
 simpl in |- *.
clear Htrace tl.
 (* далее просто все сводится к предыдущей лемме *)
 intros h' tl Htrace.
inversion_clear Htrace.
 apply inv_clos with (s := h).
 apply Inv.
 apply H.
 apply Hhead.
  (* assumption.
  assumption.
  assumption. *)
Qed.

(* Theorem 4.2 *)
Lemma safety :
 forall P : state_formula state,
 (forall s : state, init_state s -> P s) ->
 invariant transition P ->
 safe init_state transition (state2stream_formula P).
Proof.
intros P H Inv.
unfold safe in |- *.
intros T Hrun. unfold run in Hrun.
(* следующая строка разбивает HRun *)
(* elim Hrun; clear Hrun; intros H1 H2. *)
destruct Hrun.
(* применили индакт к цели (1->2->3), therefore for (3) need proof (1),(2) *)
apply induct. auto.
auto.
apply H.
apply H0.
Qed.

(******************************* Run management *******************************)

Lemma always_on_run :
 forall F P I : stream_formula state,
 safe init_state transition I ->
 (forall str : stream state,
  trace transition str -> always F str -> always I str -> P str) ->
 forall str : stream state,
 run init_state transition str -> always F str -> always P str.
Proof.
unfold safe in |- *; unfold run in |- *; intros F P I H_safe H str str_safe;
 elim str_safe.
intro h; clear h; cut (always I str); auto.
clear str_safe; generalize str; clear str H_safe.
cofix always_on_run.
intro str; case str; clear str.
intros s str always_I H_trace always_F.
inversion always_I.
inversion H_trace.
inversion always_F.
constructor.
2: apply always_on_run; auto. 
apply H; auto.
Qed.

Lemma trace_assumption :
 forall P : stream_formula state,
 (forall str : stream state, trace transition str -> P str) ->
 forall str : stream state, trace transition str -> always P str.
Proof.
unfold trace in |- *.
intros P H str H_trace.
apply
 always_assumption
  with
    (Q := fun str : stream state =>
          none_or_one_step transition (head_str str) (head_str (tl_str str)));
 assumption.
Qed.


End safety.

