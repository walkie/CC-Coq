Require Import SfLib.

(* Syntax of binary choice calculus with sharing and Selection.
   The object language is binary trees. *)
Section Syntax.

  Definition Dim := id.
  Definition Tag := bool.
  Definition Var := id.
  Definition L : Tag := true.
  Definition R : Tag := false.
  
  (* Choice calculus expressions. *)
  Inductive CC : Type :=
    | Leaf : nat -> CC
    | Node : nat -> CC -> CC -> CC
    | Decl : Dim -> CC -> CC
    | Chc  : Dim -> CC -> CC -> CC
    | Sel  : Dim -> Tag -> CC -> CC
    | Shr  : Var -> CC -> CC -> CC
    | Ref  : Var -> CC.
  
  (* Configuration types. *)
  Inductive CT : Type :=
    | Full : CT               (* Fully configured *)
    | Cons : Dec -> CT -> CT  (* Add a required decision *)
  with Dec : Type := Req : Dim -> CT -> CT -> Dec.

  (* The dimension associated with a decision. *)
  Definition decDim (dec:Dec) :=
    match dec with
      | Req d _ _ => d
    end.

  (* Sequence of two configuration types. *)
  Inductive Seq : CT -> CT -> CT -> Type :=
    | Seq_Full : forall r,
                 Seq Full r r
    | Seq_Cons : forall d l' r r',
                 Seq l' r r' ->
                 Seq (Cons d l') r (Cons d r').
  Hint Constructors Seq.

  Lemma Seq_Full_l : forall t, Seq Full t t.
  Proof. induction t; apply Seq_Full. Qed.

  Lemma Seq_Full_r : forall t, Seq t Full t.
  Proof.
    induction t as [| d t iH].
      apply Seq_Full.
      apply Seq_Cons. apply iH.
  Qed.

  Tactic Notation "CC_cases" tactic(first) ident(c) := first;
    [ Case_aux c "Leaf" | Case_aux c "Node" 
    | Case_aux c "Decl" | Case_aux c "Chc"
    | Case_aux c "Sel"
    | Case_aux c "Shr"  | Case_aux c "Ref" ].
  Tactic Notation "CT_cases" tactic(first) ident(c) := first;
    [ Case_aux c "Full" | Case_aux c "Cons"  ].

End Syntax.


(* Type system for choice calculus expressions. *)
Section TypeSystem.

  (* Dimension environment D: Dim -> Tag. *)
  Definition denv := partial_map Tag.

  (* Typing environment G: Var -> CT. *)
  Definition tenv := partial_map CT.

  (* Configuration typing rules *)
  Inductive hasType (D:denv) (G:tenv) : CC -> CT -> Prop :=
    | CT_Leaf : forall a,
                hasType D G (Leaf a) Full
    | CT_Node : forall a l r Tl Tr T,
                Seq Tl Tr T ->
                hasType D G l Tl ->
                hasType D G r Tr ->
                hasType D G (Node a l r) T
    | CT_Decl : forall d e Tl Tr,
                hasType (extend D d L) G e Tl ->
                hasType (extend D d R) G e Tr ->
                hasType D G (Decl d e) (Cons (Req d Tl Tr) Full)
    | CT_ChcL : forall d l r T,
                D d = Some L ->
                hasType D G l T ->
                hasType D G (Chc d l r) T
    | CT_ChcR : forall d l r T,
                D d = Some R ->
                hasType D G r T ->
                hasType D G (Chc d l r) T
    | CT_Sel  : forall d t e dec T,
                not (d = decDim dec) ->
                hasType D G (Sel d t e) T ->
                hasType D G (Sel d t e) (Cons dec T)
    | CT_SelL : forall d e Tl Tr Tt T,
                Seq Tl Tt T ->
                hasType D G e (Cons (Req d Tl Tr) Tt) ->
                hasType D G (Sel d L e) T
    | CT_SelR : forall d e Tl Tr Tt T,
                Seq Tr Tt T ->
                hasType D G e (Cons (Req d Tl Tr) Tt) ->
                hasType D G (Sel d R e) T
    | CT_Shr  : forall v e' e T' T,
                hasType D G e' T' ->
                hasType D (extend G v T') e T ->
                hasType D G (Shr v e' e) T
    | CT_Ref  : forall v T,
                G v = Some T ->
                hasType D G (Ref v) T.

  (* A well-formed expression is typable in an empty enivoronment. *)
  Definition wellFormed (e:CC) : Prop :=
    exists T, hasType empty empty e T.

  (* An expression is fully configured in some enivornment if its
     configuration type is Full. *)
  Definition fullConfig (D:denv) (G:tenv) (e:CC) : Prop :=
    hasType D G e Full.

  (* An expression is singular if it is fully configured in an
     empty environment. *)
  Definition singular (e:CC) : Prop :=
    hasType empty empty e Full.

  Tactic Notation "hasType_cases" tactic(first) ident(c) := first;
    [ Case_aux c "CT_Leaf" | Case_aux c "CT_Node" 
    | Case_aux c "CT_Decl" | Case_aux c "CT_ChcL" | Case_aux c "CT_ChcR"
    | Case_aux c "CT_Sel"  | Case_aux c "CT_SelL" | Case_aux c "CT_SelR"
    | Case_aux c "CT_Shr"  | Case_aux c "CT_Ref"  ].
  Hint Constructors hasType.

End TypeSystem.


Section Examples.

  Definition A := (Id 0). Hint Unfold A.
  Definition B := (Id 1). Hint Unfold B.
  Definition v := (Id 0). Hint Unfold v.
  Definition w := (Id 1). Hint Unfold w.
  
  Definition e1 := Decl A (Chc A (Leaf 1) (Leaf 2)).
  Definition t1 := Cons (Req A Full Full) Full.
  
  Lemma e1_hasType_t1 : hasType empty empty e1 t1.
  Proof.
    apply CT_Decl.    
      apply CT_ChcL. auto. apply CT_Leaf.
      apply CT_ChcR. auto. apply CT_Leaf.
  Qed.
          
  Lemma e1_is_wellFormed : wellFormed e1.
  Proof.
    unfold wellFormed.
    exists t1. apply e1_hasType_t1.
  Qed.
  
  Definition e2 := Shr v e1 (Node 0 (Sel A L (Ref v)) (Sel A R (Ref v))).
  Definition t2 := Full.
  
  Lemma e2_hasType_t2 : hasType empty empty e2 t2.
  Proof.
    unfold e2. unfold t2.
    apply CT_Shr with t1. apply e1_hasType_t1.
    apply CT_Node with Full Full. apply Seq_Full.
      apply CT_SelL with Full Full Full. apply Seq_Full.
        apply CT_Ref. auto.
      apply CT_SelR with Full Full Full. apply Seq_Full.
        apply CT_Ref. auto.
  Qed.
          
  Lemma e2_is_singular : singular e2.
  Proof.
    unfold singular.
    apply e2_hasType_t2.
  Qed.
  
  Definition e3 := Shr v e1 (Sel A L (Node 0 (Leaf 3) (Node 4 (Ref v) (Ref v)))).
  Definition t3 := Cons (Req A Full Full) Full.

  Lemma e3_hasType_t3 : hasType empty empty e3 t3.
  Proof.
    unfold e3. unfold t3.
    apply CT_Shr with t1. apply e1_hasType_t1.
    apply CT_SelL with Full Full t1. apply Seq_Full.
    apply CT_Node with Full (Cons (Req A Full Full) t1). apply Seq_Full.
      apply CT_Leaf.
      apply CT_Node with t1 t1. apply Seq_Cons. apply Seq_Full.
        apply CT_Ref. auto.
        apply CT_Ref. auto.
  Qed.

  (* 
  Definition e4 := Shr v e1 (Sel A L (Node 0 (Decl B (Chc B (Leaf 3) (Leaf 4))) (Ref v))).
  Definition t4 := Cons (Req B Full Full) Full.

  Lemma e4_hasType_t4 : hasType empty empty e4 t4.
  Proof.
    unfold e4. unfold t4.
    apply CT_Shr with t1. apply e1_hasType_t1.
    apply CT_Sel. apply beq_id_false_not_eq. auto.
    apply CT_SelL with Full Full t1. apply Seq_Full.
  *)

End Examples.
