Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.

(* Syntax of binary choice calculus expressions with global dimensions.
   The object language is binary trees. *)
Section Syntax.

Definition dim  := nat.
Definition tag  := bool.
Definition L : tag := true.
Definition R : tag := false.

Inductive cc : Type :=
  | leaf : nat -> cc
  | node : nat -> cc -> cc -> cc
  | chc  : dim -> cc -> cc -> cc.

End Syntax.


(* The semantics of a choice calculus expression is a function from
   selections to plain binary trees.  A selection is a total function
   from a dimension name to the tag to select. *)
Section Semantics.

Definition selection  := dim -> tag.
Definition denotation := selection -> cc.

Fixpoint sem (e:cc) : denotation := fun s =>
  match e with
    | leaf a     => leaf a
    | node a l r => node a (sem l s) (sem r s)
    | chc  d l r => if s d then sem l s else sem r s
  end.

Definition sel (t:tag) (d:dim) (s:selection) : selection :=
  fun d' => if beq_nat d d' then t else s d'.
Definition selR : list dim -> selection :=
  fold_right (sel R) (fun _ => L).
Definition selL : list dim -> selection :=
  fold_right (sel L) (fun _ => R).

End Semantics.


(* Proofs of the semantics preserving transformation laws from the
   TOSEM paper.  Note that since we are using a much simpler syntax,
   only a few of the rules are applicable, namely C-C-Swap, C-C-Merge,
   C-Idemp, and C-S.  I also provide proofs of the reflexivity,
   symmetry, and transitivity of semantic equivalence. *)
Section Transform.

(* Two expressions are semantically equivalent if they yield the same
   plain trees for all possible selections. *)
Definition equiv e1 e2 := forall s, sem e1 s = sem e2 s.
Notation "e1 <=> e2" := (equiv e1 e2) (at level 75).

(* Choice idempotency *)
Theorem cIdemp d e :
  chc d e e <=> e.
Proof.
  unfold equiv. intros s. unfold sem.
  destruct (s d); reflexivity. Qed.

(* C-C-Merge for the case when the nested choice appears in the
   left alternative. *)
Theorem ccMergeL d e1 e2 e3 :
  chc d (chc d e1 e2) e3 <=> chc d e1 e3.
Proof.
  unfold equiv. intros s. unfold sem.
  destruct (s d); reflexivity. Qed.

(* C-C-Merge for the case when the nested choice appears in the
   right alternative. *)
Theorem ccMergeR d e1 e2 e3 :
  chc d e1 (chc d e2 e3) <=> chc d e1 e3.
Proof.
  unfold equiv. intros s. unfold sem.
  destruct (s d); reflexivity. Qed.

(* C-C-Swap for the case when the nested choice appears in the
   left alternative of the simpler form. *)
Theorem ccSwapL d d' e1 e2 e3 :
  chc d' (chc d e1 e3) (chc d e2 e3) <=> chc d (chc d' e1 e2) e3.
Proof.
  unfold equiv. intros s. unfold sem.
  destruct (s d); destruct (s d'); reflexivity. Qed.

(* C-C-Swap for the case when the nested choice appears in the
   right alternative of the simpler form. *)
Theorem ccSwapR d d' e1 e2 e3 :
  chc d' (chc d e1 e2) (chc d e1 e3) <=> chc d e1 (chc d' e2 e3).
Proof.
  unfold equiv. intros s. unfold sem.
  destruct (s d); destruct (s d'); reflexivity. Qed.

(* C-S for the case when the nested choice appears in the
   left alternative of the simpler form. *)
Theorem csL d a e1 e2 e3 :
  chc d (node a e1 e3) (node a e2 e3) <=> node a (chc d e1 e2) e3.
Proof.
  unfold equiv. intros s. unfold sem.
  destruct (s d); reflexivity. Qed.

(* C-S for the case when the nested choice appears in the
   right alternative of the simpler form. *)
Theorem csR d a e1 e2 e3 :
  chc d (node a e1 e2) (node a e1 e3) <=> node a e1 (chc d e2 e3).
Proof.
  unfold equiv. intros s. unfold sem.
  destruct (s d); reflexivity. Qed.

(* Reflexivity of semantic equivalence. *)
Theorem equiv_refl e :
  e <=> e.
Proof. unfold equiv. reflexivity. Qed.

(* Symmetry of semantic equivalence. *)
Theorem equiv_symm e e' :
  e <=> e' -> e' <=> e.
Proof.
  unfold equiv. intros H s.
  symmetry. apply H. Qed.

(* Transitivity of semantic equivalence. *)
Theorem equiv_trans e1 e2 e3 :
  e1 <=> e2 /\ e2 <=> e3 -> e1 <=> e3.
Proof.
  unfold equiv. intros H.
  elim H. intros H1 H2 s.
  rewrite -> H1. rewrite <- H2. reflexivity. Qed.

(* 
Theorem equiv_cong e e' :
  forall (C:cc -> cc), e <=> e' -> C e <=> C e'.
*)

End Transform.



Section Examples.

Definition A : dim := 1.
Definition B : dim := 2.

Definition e1 := node 4 (chc A (leaf 7) (leaf 8)) (leaf 9). 
Definition e2 := chc A e1 (leaf 10).
Definition e3 := chc B e2 e1.

(* tests *)
Example sem_e1 :
  sem e1 (selR nil)        :: sem e1 (selL nil)        :: nil =
  node 4 (leaf 7) (leaf 9) :: node 4 (leaf 8) (leaf 9) :: nil.
Proof. compute. reflexivity. Qed.

Example sem_e2 :
  sem e2 (selR nil)        :: sem e2 (selL nil) :: nil =
  node 4 (leaf 7) (leaf 9) :: (leaf 10)         :: nil.
Proof. compute. reflexivity. Qed.

Example sem_e3 :
  sem e3 (selR nil)        :: sem e3 (selR (A :: nil)) :: 
  sem e3 (selR (B :: nil)) :: sem e3 (selL nil)        :: nil =
  node 4 (leaf 7) (leaf 9) :: (leaf 10)                ::
  node 4 (leaf 7) (leaf 9) :: node 4 (leaf 8) (leaf 9) :: nil.
Proof. compute. reflexivity. Qed.

End Examples.