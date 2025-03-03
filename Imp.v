(** * Imp: Simple Imperative Programs *)


Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.
From QuickChick Require Import QuickChick.
Import QcNotation QcDefaultNotation.
Require Export ExtLib.Structures.Monads.
Export MonadNotation. Open Scope monad_scope.
Open Scope qc_scope.
Require Import
        Coq.FSets.FMapList
        Coq.Structures.OrderedTypeEx
        Coq.FSets.FMapFacts.


Module Import M := FMapList.Make(String_as_OT).

(* Instantiate a map type using strings as keys *)
Module P := WProperties_fun String_as_OT M.
Module F := P.F.

(* Optionals are moands  *)
Instance option_monad : Monad option :=
  {
  ret X v := @Some X v;
  bind T U mt f :=
    match mt with
    | Some v => f v
    | None => None
  end
  }.

(* some list combinators *)
Fixpoint foldr {X B}
           (f : X -> B -> B) (b : B) (l : list X) : B :=
  match l with
  | [] => b
  | (x::l) => (f x (foldr f b l))
  end.

Definition andmap {X} (p : X -> bool) :=
  foldr (fun x b => (p x) && b) true.

Definition ormap {X} (p : X -> bool) :=
  foldr (fun x b => (p x) || b) false.

Fixpoint zip {X Y} (l1 : list X) (l2 : list Y)
  : list (X * Y) :=
  match l1, l2 with
  | _, [] => []
  | [], _ => []
  | (x::xs), (y::ys) => (x,y) :: (zip xs ys)
end.

Open Scope string_scope.
Instance string_arb : Gen string :=
  {
  arbitrary := ret "random"
  }.
Instance shrink_str : Shrink string :=
  {
  shrink s := []
  }.
Close Scope string_scope.

(* ================================================================= *)
(* Labels, for controlling priviledge *)

Inductive label : Type :=
  | Secret
  | Public.

Derive (Arbitrary, Show) for label.
Instance eq_dec_label (l1 l2 : label) : Dec (l1 = l2).
Proof. dec_eq. Defined.

(* Reflection setup *)
Definition label_eqb l1 l2 :=
  match l1, l2 with
| Secret, Secret => true
| Public, Public => true
| _, _ => false
  end.

Definition label_eqb_eq : forall l1 l2,
    label_eqb l1 l2 = true -> l1 = l2.
Proof.
  intros.
  destruct l1; destruct l2; auto; inversion H.
Qed.

Definition label_eqb_neq : forall l1 l2,
    label_eqb l1 l2 = false -> l1 <> l2.
Proof.
  intros.
  destruct l1; destruct l2; auto; congruence.
Qed.

Definition merge (l1 l2 : label) : label :=
  match l1, l2 with
  | Public, Public => Public
  | _, _ => Secret
  end.

(* Conjecture merge_secret : forall l, merge l Secret = Secret. *)
(* QuickChick merge_secret. *)

Theorem merge_secret : forall l1,
    merge l1 Secret = Secret.
Proof.
  intros. destruct l1; auto.
Qed.

Theorem merge_public : forall l1,
    merge l1 Public = l1.
Proof.
  intros.
  destruct l1; auto.
Qed.

Theorem merge_commutative : forall l1 l2,
    merge l1 l2 = merge l2 l1.
Proof.
  destruct l1; destruct l2; auto.
Qed.

(* This class drives the entire implementation of IFC-Imp *)

Class Distinguishable X :=
  {
  indist : X -> X -> Prop
  }.

Notation "x1 == x2" := (indist x1 x2)
                         (at level 40).


Definition value (X:Type) : Type := (X * label).

Instance value_indist {X} : Distinguishable (value X) :=
  {
  indist x1 x2 :=
    match x1, x2 with
    | (_, Secret), (_, Secret) => True
    | (n1, Public), (n2, Public) => n1 = n2
    | _, _ => False
    end
  }.


Definition nat_value : Type := value nat.

Instance dec_value_indist (v1 v2 : nat_value) :
  Dec (v1 == v2).
Proof.
  constructor. unfold ssrbool.decidable.
  destruct v1. destruct v2.
  destruct l; destruct l0;
    try (right; auto; fail).
  - left. simpl. tauto.
  - destruct (Nat.eqb n n0) eqn:Heq.
    + apply Nat.eqb_eq in Heq.
      subst. left. simpl. auto.
    + apply Nat.eqb_neq in Heq. right. simpl. auto.
Qed.


Definition bool_value : Type := value bool.

Instance bool_value_indist (v1 v2 : bool_value) :
  Dec (v1 == v2).
Proof.
  constructor. unfold ssrbool.decidable.
  destruct v1. destruct v2.
  destruct l; destruct l0;
    try (right; auto; fail).
  - left. simpl. tauto.
  - destruct (Bool.eqb b b0) eqn:Heq.
    + assert (b = b0).
      apply Bool.eqb_eq. unfold Is_true. rewrite Heq. tauto.
      subst. left. simpl. auto.
    + assert (b <> b0).
      apply Bool.eqb_false_iff. assumption.
      right. simpl. assumption.
Qed.


Definition state := M.t nat_value.
Close Scope string_scope.

Instance indist_state : Distinguishable state :=
  {
  indist s1 s2 := forall (x1 : string) (v1 v2: nat_value),
        (MapsTo x1 v1 s1 ->
         (exists (v2' : nat_value),
             MapsTo x1 v2' s2 /\ v1 == v2'))
        /\
        (MapsTo x1 v2 s2 ->
         exists (v1' : nat_value),
           MapsTo x1 v1' s1 /\ v1' == v2)
  }.

     
Theorem indist_comm : forall (st1 st2 : state),
    st1 == st2 -> st2 == st1.
Proof.
  intros.
  unfold "==". simpl.
  intros.
  split.
  - intros.
    simpl "==" in H. simpl in H.
    destruct H with
        (x1 := x1)
        (v1 := v2)
        (v2 := v1).
    destruct H2 as [v1']. assumption.
    clear H1. clear H.
    destruct H2.
    exists v1'. split.
    + assumption.
    + destruct v1'. destruct v1.
      destruct l; destruct l0;
        try assumption; auto.
  - intros.
    simpl "==" in H.
    destruct H with
        (x1 := x1)
        (v1 := v2)
        (v2 := v1).
    clear H2. clear H.
    destruct H1 as [v2']. assumption.
    destruct H.
    exists v2'. split.
    + assumption.
    + destruct v2'. destruct v2.
      destruct l; destruct l0;
        try assumption; auto.
Qed.


Theorem indist_trans : forall (st1 st2 st3 : state),
    st1 == st2 ->
    st2 == st3 ->
    st1 == st3.
Proof.
  intros.
  simpl "==". intros.
  split.
  - intros.
    simpl "==" in *.
    specialize (H x1 v1 v2).
    destruct H. destruct H as [v2']. assumption.
    destruct H. clear H2.
    specialize (H0 x1 v2' v2).
    destruct H0. destruct H0 as [ v2'0 ]. assumption.
    destruct H0. exists v2'0. split.
    + assumption.
    + destruct v1. destruct v2'0. destruct v2.
      destruct v2'.
      destruct l; destruct l0;
        destruct l1; destruct l2; try assumption;
          try tauto; try (exfalso; assumption);
            subst; auto.
  - intros.
    simpl "==" in *.
    specialize (H0 x1 v1 v2).
    destruct H0. destruct H2 as [v1']. assumption.
    destruct H2.
    specialize (H x1 v1 v1').
    destruct H. destruct H4 as [v2']. assumption.
    destruct H4. exists v2'. split.
    + assumption.
    + destruct v2'. destruct v2. destruct v1'. destruct v1.
      destruct l; destruct l0; destruct l1; destruct l2;
        try tauto;
        try (exfalso; assumption);
        subst; auto.
Qed.

  


Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Instance aexp_dec_eq (a1 a2 : aexp) :
  Dec (a1 = a2).
Proof. dec_eq. Defined.
Derive (Show, Shrink, Arbitrary) for aexp.


Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).
Instance bexp_eq_dec (b1 b2 : bexp) :
  Dec (b1 = b2).
Proof. dec_eq. Defined.
Derive (Show, Shrink, Arbitrary) for bexp.

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y"  := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"  := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.


Definition example_aexp : aexp := <{ 3 + (X * 2) }>.
Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.

Close Scope string_scope.
(* ================================================================= *)
(** ** Evaluation *)

Inductive aevalR : state -> aexp -> nat_value -> Prop :=
  | A_Value : forall state (n : nat),
      aevalR state (ANum n) (n, Public)
  | A_Id : forall state x v,
      MapsTo x v state ->
      aevalR state (AId x) v
  | A_EPlus : forall state a1 a2 n1 n2 l1 l2,
      aevalR state a1 (n1, l1) ->
      aevalR state a2 (n2, l2) ->
      aevalR state <{a1 + a2}> (n1 + n2, merge l1 l2)
  | A_EMinus : forall state a1 a2 n1 n2 l1 l2,
      aevalR state a1 (n1, l1) ->
      aevalR state a2 (n2, l2) ->
      aevalR state <{a1 - a2}> (n1 - n2, merge l1 l2)
  | A_EMult : forall state a1 a2 n1 n2 l1 l2,
      aevalR state a1 (n1, l1) ->
      aevalR state a2 (n2, l2) ->
      aevalR state <{a1 * a2}> (n1 * n2, merge l1 l2).

Fixpoint aeval (fuel : nat) (st : state) (a : aexp) : option nat_value :=
  match fuel with
| 0 => None
| S n' => match a with
       | (ANum n) => Some (n, Public)
       | (AId x) => find x st
       | (APlus a1 a2) =>
         '(n1, l1) <- aeval n' st a1;;
         '(n2, l2) <- aeval n' st a2;;
         ret (n1 + n2, merge l1 l2)
       | (AMinus a1 a2) =>
         '(n1, l1) <- aeval n' st a1;;
         '(n2, l2) <- aeval n' st a2;;
         ret (n1 - n2, merge l1 l2)
       | (AMult a1 a2) =>
         '(n1, l1) <- aeval n' st a1;;
         '(n2, l2) <- aeval n' st a2;;
         ret (n1 * n2, merge l1 l2)
         end
  end.

Theorem aeval_implies_aevalR : forall fuel st a v,
    aeval fuel st a = Some v ->
    aevalR st a v.
Proof.
  intros.
  generalize dependent st.
  generalize dependent fuel.
  generalize dependent v.
  induction a; intros;
    try destruct fuel; try (inversion H).
  - apply A_Value.
  - apply A_Id. apply find_2. assumption.
  - destruct (aeval fuel st a1) eqn:Heq1.
    + destruct n as [n1 l2].
      destruct (aeval fuel st a2) eqn:Heq2.
      * destruct n as [n2 l3].
        injection H1. intros. subst.
        apply A_EPlus.
        -- eapply IHa1. eauto.
        -- eapply IHa2. eauto.
      * congruence.
    + congruence.
  - destruct (aeval fuel st a1) eqn:Heq1.
    + destruct n as [n1 l2].
      destruct (aeval fuel st a2) eqn:Heq2.
      * destruct n as [n2 l3].
        injection H1. intros. subst.
        apply A_EMinus.
        -- eapply IHa1. eauto.
        -- eapply IHa2. eauto.
      * congruence.
    + congruence.
  - destruct (aeval fuel st a1) eqn:Heq1.
    + destruct n as [n1 l2].
      destruct (aeval fuel st a2) eqn:Heq2.
      * destruct n as [n2 l3].
        injection H1. intros. subst.
        apply A_EMult.
        -- eapply IHa1. eauto.
        -- eapply IHa2. eauto.
      * congruence.
    + congruence.
Qed.






Inductive bevalR : state -> bexp -> bool_value -> Prop :=
  | E_True : forall st,
      bevalR st <{true}> (true, Public)
  | E_False : forall st,
      bevalR st <{false}> (false, Public)
  | E_Eq : forall st a1 a2 n1 n2 l1 l2,
      aevalR st a1 (n1, l1) ->
      aevalR st a2 (n2, l2) ->
      bevalR st <{a1 = a2}> (n1 =? n2, merge l1 l2)
  | E_Lt : forall st a1 a2 n1 n2 l1 l2,
      aevalR st a1 (n1, l1) ->
      aevalR st a2 (n2, l2) ->
      bevalR st <{a1 <= a2}> (n1 <=? n2, merge l1 l2)
  | E_not__true : forall st b l1,
      bevalR st b (true, l1) ->
      bevalR st <{~ b}> (false, l1)
  | E_not__false : forall st b l1,
      bevalR st b (false, l1) ->
      bevalR st <{~ b}> (true, l1)
  | E_and : forall st b1 b2 bool1 bool2 l1 l2,
      bevalR st b1 (bool1, l1) ->
      bevalR st b2 (bool2, l2) ->
      bevalR st <{b1 && b2}> (bool1 && bool2, merge l1 l2).

  



Definition empty_st : state := (M.empty nat_value).

Notation "x '!->' v" := (add x v (M.empty nat_value))
                          (at level 100).
Example aexp0 :
  aevalR (X !-> (5, Public)) <{ X * 2 }> (10, Public).
Proof.
  replace (10, Public) with (5 * 2, merge Public Public).
  apply A_EMult.
  apply A_Id.
  apply find_2. auto.
  apply A_Value.
  auto.
Qed.


Example aexp1 :
    aevalR (X !-> (5, Public)) <{ (3 + (X * 2))}> (13, Public).
Proof.
  replace (13, Public) with (3 + 10, merge Public Public).
  apply A_EPlus.
  apply A_Value.
  replace (10, Public) with (5 * 2, merge Public Public).
  apply A_EMult.
  apply A_Id.
  apply find_2. auto.
  apply A_Value.
  auto.
  auto.
Qed.


Example bexp1 :
  bevalR (X !-> (5, Secret)) <{ true && ~(X <= 4)}>
  (true, Secret).
Proof.
  replace (true, Secret) with
      (true && true, merge Public Secret).
  apply E_and.
  apply E_True.
  apply E_not__false.
  replace (false, Secret) with
      (5 <=? 4, merge Secret Public).
  apply E_Lt.
  apply A_Id. apply find_2. auto.
  apply A_Value.
  auto.
  auto.
Qed.


(* ################################################################# *)
(** * Commands *)


(* ================================================================= *)
(** ** Syntax *)


Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp) (l : label)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com).
  (* | CWhile (b : bexp) (c : com). *)

Fixpoint com_indist_f c1 c2 :=
  match c1, c2 with
| CSkip, CSkip => True
| CAss x1 a1 Public, CAss x2 a2 Public =>
  x1 = x2 /\ a1 = a2
| CAss x1 a1 Secret, CAss x2 a2 Secret => x1 = x2
| CSeq c1 c2, CSeq c1' c2' =>
  com_indist_f c1 c1' /\ com_indist_f c2 c2'
| CIf b c1 c2, CIf b' c1' c2' =>
  b = b' /\ com_indist_f c1 c1' /\ com_indist_f c2 c2'
| _, _ => False
  end.


Instance com_indist : Distinguishable com :=
  {
  indist := com_indist_f
  }.

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x ':=' y ',' l"  :=
         (CAss x y l)
           (in custom com at level 0,
               x constr at level 0,
                y at level 85,
                no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
(* Notation "'while' x 'do' y 'end'" := *)
(*          (CWhile x y) *)
(*             (in custom com at level 89, x at level 99, y at level 99) : com_scope. *)



Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Definition sec_context : Type := (state * label).

Instance sec_context_indist : Distinguishable sec_context :=
  {
  indist c1 c2 :=
    match c1, c2 with
    | (s1, l1), (s2, l2) => l2 = l1  /\ indist s1 s2
    end
  }.

Definition merge_list (l : list label) : label :=
  foldr (fun l1 l2 => merge l1 l2) Public l.


Definition writing_valid (x : string) (st : state) (l : label)
  : Prop :=
  (exists (n' : nat) (l' : label),
      l = l' /\
      MapsTo x (n', l') st).

Inductive ceval : com -> sec_context -> sec_context -> Prop :=
  | E_Skip : forall ctxt,
      ctxt=[ skip ]=> ctxt
  | E_Ass  : forall (st : M.t nat_value) a n x l l__v l__s,
      aevalR st a (n, l__v) ->
      In x st ->
      writing_valid x st (merge l__v l) ->
      (st,l) =[ x := a , l__s ]=>
      (add x (n, merge_list [l__v;l__s; l]) st, l)
  | E_Seq : forall c1 c2 ctxt ctxt' ctxt'',
      ctxt  =[ c1 ]=> ctxt'  ->
      ctxt' =[ c2 ]=> ctxt'' ->
      ctxt  =[ c1 ; c2 ]=> ctxt''
  | E_IfTrue : forall st st' b l__guard l__begin c1 c2,
      bevalR st b (true, l__guard) ->
      (st, merge l__begin l__guard) =[ c1 ]=>
    (st', l__begin ) ->
      (st,l__begin) =[ if b then c1 else c2 end]=> (st', l__begin)
  | E_IfFalse : forall st st' l__guard l__begin b c1 c2,
      bevalR st b (false, l__guard) ->
      (st, merge l__begin l__guard) =[ c2 ]=>
    (st', merge l__begin l__guard) ->
      (st, l__begin) =[ if b then c1 else c2 end]=> (st', l__begin)
  where "st =[ c ]=> st'" := (ceval c st st').
  (* | E_WhileFalse : forall b st c, *)
  (*     beval st b = false -> *)
  (*     st =[ while b do c end ]=> st *)
  (* | E_WhileTrue : forall st st' st'' b c, *)
  (*     beval st b = true -> *)
  (*     st  =[ c ]=> st' -> *)
  (*     st' =[ while b do c end ]=> st'' -> *)
  (*     st  =[ while b do c end ]=> st'' *)

Definition default_ctxt (xs : list (string * label)) :
  sec_context :=

  let st :=
      foldr (fun '(x, l) st => add x (0, l) st)
            (M.empty nat_value) xs in
  (st, Public).


Definition v_eq (v1 v2 : nat_value) : bool :=
  match v1, v2 with
  | (n1, l1), (n2, l2) => (l1 = l2 ?) && (n1 =? n2)
  end.

Definition build_st (entries : list (string * (nat * label)))
  : M.t nat_value :=
  foldr
    (fun '(key, value) m' => add key value m')
    (empty nat_value)
    entries.


Definition ceval_example1state : sec_context :=
  default_ctxt [(X, Public); (Y, Public); (Z, Public)].

Example ceval_example1:
  ceval_example1state =[
     X := 2, Public;
     if (X <= 1)
       then Y := 3, Public
       else Z := 4, Public
     end
  ]=> (build_st [(Z, (4, Public));(X, (2, Public)); (Y, (0, Public))], Public).
Proof.
  remember (add X (0, Public) (add Y (0, Public) (Z !-> (0, Public)))).
  eapply E_Seq.
  - eapply E_Ass.
    + simpl. rewrite <- Heqt0.
      exact (A_Value t0 2).
    + simpl. apply mem_2. auto.
    + simpl. rewrite <- Heqt0.
      unfold writing_valid.
      Admitted.








Lemma public_indist : forall {X} (n : X),
    (n, Public) == (n, Public).
Proof.
  intros.
  unfold indist. simpl.
  reflexivity.
Qed.

Lemma secret_indist : forall {X} (n1 n2 : X),
    (n1, Secret) == (n2, Secret).
Proof.
  intros.
  unfold indist. simpl. tauto.
Qed.

Lemma diff_dist : forall {X} (n1 n2 : X),
    not ((n1, Secret) == (n2, Public)).
Proof.
  intros. unfold not. intros.
  unfold indist in H. simpl in H.
  auto.
Qed.

Lemma indist_commut :
  forall {X:Type} `{forall (x1 x2 : X), Dec (x1 = x2)}
    (n1 n2 : X) (l1 l2 : label),
    (n1, l1) == (n2, l2) ->
    (n2, l2) == (n1, l1).
Proof.
  intros.
  unfold indist in H. simpl in H0.
  destruct l1; destruct l2.
  - apply secret_indist.
  - apply H0.
  - apply H0.
  - specialize (H n1 n2). destruct H.
    destruct dec.
    + rewrite H0. apply public_indist.
    + congruence.
Qed.


Lemma MapsTo_eq :
  forall (st : state) (x : string) (v1 v2 : nat_value),
    MapsTo x v1 st ->
    MapsTo x v2 st ->
    v1 = v2.
Proof.
  intros.
  apply find_1 in H.
  apply find_1 in H0. rewrite H0 in H. injection H.
  intros. auto.
Qed.

Lemma map_add_eq :
  forall (st : state) (x : string) (v1 v2 : nat_value),
    MapsTo x v1 (add x v2 st) ->
    v1 = v2.
Proof.
  intros.
  assert (MapsTo x v2 (add x v2 st)).
  {
    apply add_1. reflexivity.
  }
  apply MapsTo_eq with (st := add x v2 st) (x := x);
    assumption.
Qed.

Lemma indist_implies_indist :
  forall (st1 st2 : state) (x : string) (v1 v2 : nat_value),
    st1 == st2 ->
    MapsTo x v1 st1 ->
    MapsTo x v2 st2 ->
    v1 == v2.
Proof.
  intros. simpl "==" in H.
  specialize (H x v1 v2).
  destruct H. destruct H as [v2']. assumption.
  destruct H.
  replace v2' with v2 in *.
  - destruct v1. destruct v2.
    destruct l; destruct l0;
      try tauto;
      try (exfalso; assumption);
      subst; auto.
  - apply MapsTo_eq with (st := st2) (x := x);
      assumption.
Qed.


Theorem indist_split : forall {X} (n1 n2 : X) (l1 l2 : label),
    (n1, l1) == (n2, l2) ->
    (l1 = Secret /\ l2 = Secret) \/
    (l1 = Public /\ l2 = Public /\ n1 = n2).
Proof.
  intros.
  destruct l1; destruct l2;
    auto;
    contradict H.
Qed.


Theorem aexp_EENI :
  forall (st1 st2 : state) (a : aexp) (v1 v2 : nat_value),
    st1 == st2 ->
    aevalR st1 a v1 ->
    aevalR st2 a v2 ->
    v1 == v2.
Proof.
  intros.
  generalize dependent v1.
  generalize dependent v2.
  induction a; intros;
    inversion H0; inversion H1; subst;
    try (
       assert ((n1, l1) == (n0, l0)); auto;
    assert ((n2, l2) == (n3, l3)); auto;
    apply indist_split in H2;
    apply indist_split in H3;
    destruct H2; destruct H3;
      destruct H2 as [Hl1 Hl0];
      destruct H3 as [Hl2 Hl3];
      subst; simpl; try tauto;
        destruct Hl0; subst; simpl; try tauto;
          destruct Hl3; subst; simpl; tauto).
  - apply public_indist.
  - eapply indist_implies_indist.
    apply H. apply H4. apply H8.
Qed.

Theorem bexp_EENI :
  forall (st1 st2 : state) (b : bexp) (v1 v2 : bool_value),
    st1 == st2 ->
    bevalR st1 b v1 ->
    bevalR st2 b v2 ->
    v1 == v2.
Proof.
  intros.
  generalize dependent v1.
  generalize dependent v2.
  induction b; intros;
    inversion H0; inversion H1; subst;
      try (apply public_indist).
  -
    assert ((n1, l1) == (n0, l0)).
    apply aexp_EENI with
        (st1 := st1)
        (st2 := st2)
        (a := a1); assumption.
    assert ((n2, l2) == (n3, l3)).
    apply aexp_EENI with
        (st1 := st1)
        (st2 := st2)
        (a := a2); assumption.
    apply indist_split in H2.
    apply indist_split in H3.
    destruct H2; destruct H3;
      destruct H2; destruct H3; subst; simpl; try tauto;
        destruct H4; subst; simpl; try tauto;
          destruct H6; subst; auto; tauto.
  - assert ((n1, l1) == (n0, l0)).
    apply aexp_EENI with
        (st1 := st1)
        (st2 := st2)
        (a := a1); assumption.
    assert ((n2, l2) == (n3, l3)).
    apply aexp_EENI with
        (st1 := st1)
        (st2 := st2)
        (a := a2); assumption.
    apply indist_split in H2.
    apply indist_split in H3.
    destruct H2; destruct H3;
      destruct H2; destruct H3; subst; simpl; try tauto;
        destruct H4; subst; simpl; try tauto;
          destruct H6; subst; simpl; tauto.
  - assert ((true, l1) == (true, l0)).
    apply IHb; assumption.
    apply indist_split in H2.
    destruct H2.
    + destruct H2. subst. apply secret_indist.
    + destruct H2. destruct H3. subst. apply public_indist.
  - assert ((true, l1) == (false, l0)).
    apply IHb; assumption.
    apply indist_split in H2.
    destruct H2.
    + destruct H2. subst. apply secret_indist.
    + destruct H2 as [_ [_ Contra]]. congruence.
  - assert ((false, l1) == (true, l0)).
    apply IHb; assumption.
    apply indist_split in H2.
    destruct H2.
    + destruct H2. subst. apply secret_indist.
    + destruct H2 as [_ [_ Contra]]. congruence.
  - assert ((false, l1) == (false, l0)).
    apply IHb; assumption.
    apply indist_split in H2.
    destruct H2.
    + destruct H2. subst. apply secret_indist.
    + destruct H2 as [H21 [H22 H23]].
      subst. simpl. tauto.
  - assert ((bool1, l1) == (bool0, l0)).
    apply IHb1; assumption.
    assert ((bool2, l2) == (bool3, l3)).
    apply IHb2; assumption.
    apply indist_split in H2.
    apply indist_split in H3.
    destruct H2; destruct H3;
      destruct H2; destruct H3; subst; simpl; try tauto;
        destruct H4; subst; simpl; try tauto.
    destruct H6. subst. simpl. tauto.
Qed.

Theorem secret_doms : forall (ls : list label),
    List.In Secret ls ->
    merge_list ls = Secret.
Proof.
  intros.
  unfold merge_list.
  induction ls as [| l ls' IH].
  - inversion H.
  - destruct l.
    + auto.
    + assert (List.In Secret ls').
      {
        inversion H.
        + congruence.
        + assumption.
      }
      simpl.
      assert
        ((foldr (fun l1 l2 : label => merge l1 l2) Public ls')
         = Secret).
      apply IH. assumption.
      rewrite H1. reflexivity.
Qed.


Theorem map_add_congruence : forall (l1 l2 : label) (n1 n2 : nat)
                               (st : state) (x : string),
    l1 <> l2 ->
    MapsTo x (n1, l1) (add x (n2, l2) st) ->
    False.
Proof.
  intros.
  assert (MapsTo x (n2, l2) (add x (n2, l2) st)).
  {
    apply add_1. auto.
  }
  assert ((n1, l1) = (n2, l2)).
  {
    apply MapsTo_eq with
        (st := (add x (n2, l2) st))
        (x := x); auto.
  }
  injection H2. intros. congruence.
Qed.


(* the no wrote down rule is sound*)
Theorem add_secret :
  forall (x : string) (n : nat) (st : state),
    writing_valid x st Secret ->
    st == (add x (n, Secret) st).
Proof.
  intros.
  unfold writing_valid in H.
  destruct H as [n']. destruct H as [l']. destruct H.
  subst. simpl "==". intros.
  destruct (String.eqb x x1) eqn:Heq.
  - apply String.eqb_eq in Heq.
    split.
    + intros. exists (n, Secret).
      split; subst.
      * apply add_1. auto.
      * destruct v1. destruct l.
        -- tauto.
        -- assert ((n', Secret) = (n0, Public)).
           {
             apply MapsTo_eq with (st := st) (x := x1);
               assumption.
           }
           injection H1. intros. congruence.
    + intros. subst.
      exists (n', Secret). destruct v1. destruct v2.
      split.
      * assumption.
      * destruct l; destruct l0;
          try tauto; try (exfalso; assumption);
            apply map_add_congruence with
                (l1 := Public)
                (l2 := Secret)
                (n1 := n1)
                (n2 := n)
                (st := st)
                (x := x1); auto; discriminate.
  - apply String.eqb_neq in Heq.
    split.
    + intros. exists v1. split.
      * apply add_2; assumption.
      * destruct v1. destruct l; auto.
    + intros. exists v2. split.
      * apply add_3 with (x := x) (e' := (n, Secret)); auto.
      * destruct v2. destruct l; auto.
Qed.

Theorem add_indist :
  forall (x : string) (v1 v2 : nat_value) (st1 st2 : state),
    st1 == st2 ->
    v1 == v2 ->
    (add x v1 st1) == (add x v2 st2).
Proof.
  intros x v1 v2 st1 st2 Hstindist Hvindist.
  simpl "==". intros.
  destruct (String.eqb x x1) eqn:Heqx.
  - apply String.eqb_eq in Heqx.
    split.
    + intros. subst.
      apply MapsTo_eq with (v1 := v1) in H.
      * subst. exists v2. split.
        -- apply add_1. auto.
        -- destruct v0. destruct v2.
           destruct l; destruct l0;
             inversion Hvindist; auto.
      * apply add_1. auto.
    + intros. subst.
      apply MapsTo_eq with (v1 := v2) in H.
      * subst. exists v1. split.
        -- apply add_1. auto.
        -- destruct v1. destruct v3.
           destruct l; destruct l0;
             inversion Hvindist; auto.
      * apply add_1. auto.
  - apply String.eqb_neq in Heqx.
    split.
    + intros.
      apply add_3 with (x := x) (e' := v1) in H.
      simpl "==" in Hstindist.
      specialize (Hstindist x1 v0 v2).
      destruct Hstindist. destruct H0 as [v2']. assumption.
      destruct H0. exists v2'.
      split.
      * apply add_2 with
            (x := x)
            (e' := v2) in H0; assumption.
      * destruct v0. destruct v2'.
        destruct l; destruct l0;
          auto; exfalso; auto.
      * assumption.
    + intros.
      apply add_3 with (x := x) (e' := v2) in H.
      simpl "==" in Hstindist.
      specialize (Hstindist x1 v0 v3).
      destruct Hstindist.
      destruct H1 as [v1']. assumption.
      destruct H1.
      exists v1'. split.
      * apply add_2 with (x := x) (e' := v1) in H1;
          assumption.
      * destruct v1'. destruct v3.
        destruct l; destruct l0;
          auto; exfalso; auto.
      * assumption.
Qed.




Ltac secret_merge :=
  symmetry; apply secret_doms; simpl; auto.

Ltac open_indist H :=
  unfold "==" in H; simpl in H.

Lemma indist_f : forall (c1 c2 : com),
    com_indist_f c1 c2 ->
    c1 == c2.
Proof.
  intros. unfold "==". simpl. assumption.
Qed.

Theorem com_indist_refl : forall (c : com),
    c == c.
Proof.
  intros. induction c;
            unfold "=="; simpl; try tauto.
  - destruct l; auto.
Qed.

Theorem state_indist_refl : forall (st : state),
    st == st.
Proof.
  intros.
  simpl "==".
  intros.
  split; intros.
  - exists v1. split. auto.
    destruct v1. destruct l; auto.
  - exists v2. split. auto.
    destruct v2. destruct l; auto.
Qed.


Lemma ctxt_split : forall (st1 st2 : state) (l1 l2 : label),
    (st1, l1) == (st2, l2) ->
    st1 == st2 /\ l1 = l2.
Proof.
  intros.
  unfold "==" in *. simpl in *.
  destruct H. subst. split; auto.
Qed.

Theorem ctxt_indist_refl : forall (ctxt : sec_context),
    ctxt == ctxt.
Proof.
  intros. unfold "==". simpl.
  destruct ctxt. split.
  - reflexivity.
  - apply state_indist_refl.
Qed.

Lemma indist_neq_secret : forall {X} (x1 x2 : X) (l1 l2 : label),
    x1 <> x2 ->
    (x1, l1) == (x2, l2) ->
    l1 = l2 /\ l1 = Secret.
Proof.
  intros. unfold "==" in *. simpl in *.
  destruct l1; destruct l2;
    auto; exfalso; auto.
Qed.

Lemma indist_samelabel : forall {X} (x1 x2 : X) (l1 l2 : label),
    (x1, l1) == (x2, l2) ->
    l1 = l2.
Proof.
  intros.
  unfold "==" in H. simpl in H.
  destruct l1; destruct l2; subst;
    auto; exfalso; auto.
Qed.

Ltac simpl_indist :=
  unfold "=="; simpl; split; auto.



Theorem label_const : forall c (st st' : state) (l l' : label),
    (st, l) =[ c ]=> (st', l') ->
    l = l'.
Proof.
  intros c.
  induction c; intros.
  - inversion H. auto.
  - inversion H. subst. auto.
  - inversion H. subst.
    rename l' into l''.
    rename st' into st''.
    destruct ctxt' as [ st' l' ].
    assert (l = l').
    {
      apply IHc1 with (st := st) (st' := st').
      assumption.
    }
    subst.
    apply IHc2 with (st := st') (st' := st'').
    assumption.
  - inversion H; subst; auto.
Qed.


Theorem secret_step : forall (c : com) (st st': state),
    (st, Secret) =[ c ]=> (st', Secret) ->
    st == st'.
Proof.
  intros c.
  induction c; intros.
  - inversion H. subst. apply state_indist_refl.
  - inversion H. subst.
    replace (merge_list [l__v; l; Secret]) with Secret in *.
    + apply add_secret.
      replace (merge l__v Secret) with Secret in *.
      assumption.
      destruct l__v; auto.
    + symmetry. apply secret_doms. simpl. auto.
  - rename st' into st''.
    inversion H. subst.
    destruct ctxt' as [ st' l ].
    destruct l.
    + apply indist_trans with (st2 := st').
      * apply IHc1. assumption.
      * apply IHc2. assumption.
    + assert (Secret = Public).
      {
        apply (label_const c1 st st'). assumption.
      }
      congruence.
  - inversion H; subst;
      replace (merge Secret l__guard) with Secret in *;
      auto.
Qed.

Theorem leak_step : forall (c : com) (st st' : state),
    (st, Secret) =[ c ]=> (st', Public) -> False.
Proof.
  intros.
  generalize dependent st.
  generalize dependent st'.
  induction c; intros; inversion H.
  - inversion H. subst. destruct ctxt'.
    destruct l.
    + eapply IHc2. eauto.
    + eapply IHc1. eauto.
Qed.


Lemma indist_diff_label : forall (st1 st2 : state) (n1 n2 : nat)
                            (l1 l2 : label) (x : string),
    st1 == st2 ->
    l1 <> l2 ->
    MapsTo x (n1, l1) st1 ->
    MapsTo x (n2, l2) st2 ->
    False.
Proof.
  intros.
  simpl "==" in H.
  specialize (H x (n1, l1) (n2, l2)). destruct H.
  destruct H as [v2']. assumption.
  destruct H.
  replace v2' with (n2, l2) in *.
  - destruct l1; destruct l2;
      try tauto;
      try (exfalso; assumption).
  - apply MapsTo_eq with (st := st2) (x := x); assumption.
Qed.




Theorem aeval_diverges : forall (a : aexp) (st1 st2 : state)
                           (l1 l2 : label) (n1 n2 : nat),
    st1 == st2 ->
    n1 <> n2 ->
    aevalR st1 a (n1, l1) ->
    aevalR st2 a (n2, l2) ->
    l1 = Secret /\ l2 = Secret.
Proof.
  intros.
  destruct (label_eqb l1 l2) eqn:Heq.
  - apply label_eqb_eq in Heq.
    subst.
    assert ((n1, l2) == (n2, l2)).
    eapply aexp_EENI; eauto.
    simpl "==" in H3. destruct l2.
    + auto.
    + congruence.
  - apply label_eqb_neq in Heq.
    assert ((n1, l1) == (n2, l2)).
    eapply aexp_EENI; eauto.
    simpl "==" in H3.
    destruct l1; destruct l2;
      auto; exfalso; auto.
Qed.

Theorem beval_diverges : forall (b : bexp) (st1 st2 : state)
                           (l1 l2 : label) (b1 b2 : bool),
    st1 == st2 ->
    bevalR st1 b (b1, l1) ->
    bevalR st2 b (b2, l2) ->
    b1 <> b2 ->
    l1 = Secret /\ l2 = Secret.
Proof.
  intros.
  destruct (label_eqb l1 l2) eqn:Heq.
  - apply label_eqb_eq in Heq.
    subst.
    assert ((b1, l2) == (b2, l2)).
    eapply bexp_EENI; eauto.
    simpl "==" in H3. destruct l2.
    + auto.
    + congruence.
  - apply label_eqb_neq in Heq.
    assert ((b1, l1) == (b2, l2)).
    eapply bexp_EENI; eauto.
    simpl "==" in H3.
    destruct l2; destruct l1; auto; exfalso; auto.
Qed.

Ltac brute l1 l2 :=
  destruct l1; destruct l2;
  auto; exfalso; auto.



Theorem com_EENI :
  forall (c1 c2 : com)
    (ctxt1 ctxt2 ctxt1' ctxt2' : sec_context),
    c1 == c2 ->
    ctxt1 == ctxt2 ->
    ctxt1 =[ c1 ]=> ctxt1' ->
    ctxt2 =[ c2 ]=> ctxt2' ->
    ctxt1' == ctxt2'.
Proof.
  intros c1.
  induction c1; intros.
  - inversion H1. subst. unfold "==" in H. simpl in H.
    destruct c2 eqn:Hc2;
      try (exfalso; assumption).
    + subst. inversion H2. subst. assumption.
  - unfold "==" in H. simpl in H.
    destruct c2 eqn:Hc2;
      try (destruct l; exfalso; assumption).
    + subst.
      destruct l; destruct l0;
        try (exfalso; assumption).
      * inversion H1. subst. inversion H2. subst.
        replace (merge_list [l__v; Secret; l]) with Secret in *;
          try secret_merge.
        replace (merge_list [l__v0; Secret; l0]) with Secret in *;
          try secret_merge.
        -- inversion H0. subst.
           unfold "==". simpl. split.
           ++ reflexivity.
           ++ apply add_indist. assumption.
              apply secret_indist.
      * destruct H. subst. inversion H1. inversion H2. subst.
        inversion H0. subst.
        assert (l__v0 = l__v).
        {
          assert ((n, l__v) == (n0, l__v0)).
          apply aexp_EENI with
              (st1 := st)
              (st2 := st0)
              (a := a0); assumption.
          unfold "==" in H. simpl in H.
          destruct l__v; destruct l__v0; auto; exfalso; assumption.
        }
        subst.
        destruct l eqn:Hl.
        -- split. reflexivity.
           apply add_indist.
           assumption.
           destruct l__v; simpl; tauto.
        -- destruct l__v.
           ++ unfold "==". simpl. split. auto.
              apply add_indist. assumption.
              simpl. tauto.
           ++ unfold "==". simpl. split. auto.
              apply add_indist. assumption.
              simpl. assert ((n, Public) == (n0, Public)).
              apply aexp_EENI with
                  (st1 := st)
                  (st2 := st0)
                  (a := a0); assumption.
              unfold "==" in H. simpl in H. subst.
              auto.
  - open_indist H. destruct c2;
                     try (exfalso; assumption).
    + inversion H1. inversion H2. subst.
      assert (ctxt' == ctxt'0) as Hindist1.
      {
        apply IHc1_1 with
            (c2 := c2_1)
            (ctxt1 := ctxt1)
            (ctxt2 := ctxt2); try assumption.
        inversion H. unfold "==". simpl. assumption.
      }
      apply IHc1_2 with
          (c2 := c2_2)
          (ctxt1 := ctxt')
          (ctxt2 := ctxt'0); try assumption.
      inversion H. unfold "==". simpl. assumption.
  - (* Conditionals *)
    destruct c2; try inversion H.
    inversion H. subst.
    clear H5 H6. destruct H4.
    apply indist_f in H3.
    apply indist_f in H4.
    destruct ctxt1 as [ st1 l1 ].
    destruct ctxt2 as [ st2 l2 ].
    destruct ctxt1' as [ st1' l1' ].
    destruct ctxt2' as [ st2' l2' ].
    apply ctxt_split in H0. destruct H0. subst.
    inversion H1; inversion H2;
      destruct l2'; subst.
    + (* both eval to true, secret *)
      replace l__guard0 with l__guard in *.
      * replace (merge Secret l__guard) with Secret in *.
        -- apply IHc1_1 with
               (c2 := c2_1)
               (ctxt1 := (st1, Secret))
               (ctxt2 := (st2, Secret));
             try assumption. simpl_indist.
        -- auto.
      * apply indist_samelabel with
            (x1 := true) (x2 := true).
        apply bexp_EENI with (st1 := st1) (st2 := st2)
                             (b := b0);
          assumption.
    + (* both eval to true, public *)
      replace l__guard0 with l__guard in *.
      * eapply IHc1_1; eauto.
        simpl "==".
        split.
        -- destruct l__guard; auto.
        -- assumption.
      * assert ((true, l__guard) == (true, l__guard0)).
        eapply bexp_EENI; eauto.
        simpl "==" in H5.
        destruct l__guard; destruct l__guard0;
          auto; exfalso; auto.
    + assert (l__guard = Secret /\ l__guard0 = Secret).
      eapply beval_diverges; eauto.
      destruct H5. subst. simpl in H13. simpl in H22.
      apply secret_step in H13.
      apply secret_step in H22.
      clear H1. clear H2. clear H7. clear H16. clear H.
      clear H3. clear H4.
      assert (st1 == st2').
      {
        eapply indist_trans.
        apply H0. apply H22.
      }
      apply indist_comm in H13.
      assert (st1' == st2').
      {
        eapply indist_trans.
        apply H13. assumption.
      }
      simpl "==". split. auto. apply H1.
    + assert (l__guard = Secret /\ l__guard0 = Secret).
      eapply beval_diverges; eauto.
      destruct H5. subst.
      simpl in H13. simpl in H22.
      exfalso. eapply leak_step. apply H13.
    + assert (l__guard = Secret /\ l__guard0 = Secret).
      eapply beval_diverges; eauto.
      destruct H5. subst.
      simpl in H13. simpl in H22.
      clear H1. clear H2. clear H7. clear H16. clear H.
      clear H3. clear H4.
      apply secret_step in H13. apply secret_step in H22.
      assert (st1 == st2').
      {
        eapply indist_trans.
        apply H0. apply H22.
      }
      apply indist_comm in H13.
      assert (st1' == st2').
      {
        eapply indist_trans.
        apply H13. assumption.
      }
      simpl "==". split. auto. apply H1.
    + assert (l__guard = Secret /\ l__guard0 = Secret).
      eapply beval_diverges; eauto.
      destruct H5. subst.
      simpl in H13. simpl in H22.
      exfalso. eapply leak_step. apply H22.
    + replace (merge Secret l__guard) with Secret in *.
      replace (merge Secret l__guard0) with Secret in *.
      * eapply IHc1_2; eauto.
        simpl "==". split. auto. assumption.
      * destruct l__guard0; auto.
      * destruct l__guard; auto.
    + replace l__guard0 with l__guard in *.
      destruct l__guard.
      * simpl in H13. simpl in H22.
        apply secret_step in H13. apply secret_step in H22.
        assert (st1 == st2').
        eapply indist_trans.
        apply H0. apply H22.
        apply indist_comm in H13.
        assert (st1' == st2').
        eapply indist_trans.
        apply H13. assumption. simpl. split. auto.
        assumption.
      * simpl in H13. simpl in H22.
        assert ((st1, Public) == (st2, Public)).
        simpl. split. auto. assumption.
        eapply IHc1_2; eauto.
      * assert ((false, l__guard) == (false, l__guard0)).
        eapply bexp_EENI; eauto. simpl in H5.
        brute l__guard l__guard0.
Qed.
