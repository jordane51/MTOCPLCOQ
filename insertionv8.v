(* A sorting example : 
   (C) Yves Bertot, Pierre Castéran 
*)

Require Import List.
Require Import ZArith.
Open Scope Z_scope.

Fixpoint insert (z:Z) (l:list Z) {struct l} : list Z :=
  match l with
  | nil => z :: nil
  | cons a l' => if Z.leb z a
      then z :: a :: l'
      else a :: insert z l'
 end.

   

Compute  insert 4 (2 :: 5 :: nil).

Compute insert 4 (24 :: 50 ::nil).

Fixpoint insertion_sort (l:list Z) : list Z :=
match l with
| nil => nil
| z::l' => insert z (insertion_sort l')
end.

Compute insertion_sort (4::9::7::9::12::3::nil).




Inductive sorted : list Z -> Prop :=
  | sorted0 : sorted nil
  | sorted1 : forall z:Z, sorted (z :: nil)
  | sorted2 :
      forall (z1 z2:Z) (l:list Z),
        z1 <= z2 ->
        sorted (z2 :: l) -> sorted (z1 :: z2 :: l).

Hint Resolve sorted0 sorted1 sorted2 : sort.

Lemma sort_2357 :
 sorted (2 :: 3 :: 5 :: 7 :: nil).
Proof.
 auto with sort zarith.
Qed.


Theorem sorted_inv :
 forall (z:Z) (l:list Z), sorted (z :: l) -> sorted l.
Proof.
 intros z l H.
 inversion H; auto with sort.
Qed.

(*  Number of occurrences of z in l *)

Check Z.eqb.

Fixpoint nb_occ (z:Z) (l:list Z) {struct l} : nat :=
  match l with
  | nil => 0%nat
  | (z' :: l') =>
      if Z.eqb z z' 
      then S (nb_occ z l')
      else nb_occ z l'
   end.

Eval compute in (nb_occ 3 (3 :: 7 :: 3 :: nil)).

Eval compute in (nb_occ 36725 (3 :: 7 :: 3 :: nil)).


(* list l' is a permutation of list l *)

Definition equiv (l l':list Z) := 
    forall z:Z, nb_occ z l = nb_occ z l'.

(* equiv is an equivalence ! *)

Lemma equiv_refl : forall l:list Z, equiv l l.
Proof.
 unfold equiv; trivial.
Qed.

Lemma equiv_sym : forall l l':list Z, equiv l l' -> equiv l' l.
Proof.
  unfold equiv; auto.
Qed.

Lemma equiv_trans :
 forall l l' l'':list Z, equiv l l' -> 
                         equiv l' l'' -> 
                         equiv l l''.
Proof.
 intros l l' l'' H H0 z.
 eapply trans_eq; eauto.
Qed.

Lemma equiv_cons :
 forall (z:Z) (l l':list Z), equiv l l' -> 
                             equiv (z :: l) (z :: l').
Proof.
 intros z l l' H z'.
 simpl; case_eq  (Z.eqb z' z); auto. 
Qed.


Lemma equiv_perm :
 forall (a b:Z) (l l':list Z),
   equiv l l' -> 
   equiv (a :: b :: l) (b :: a :: l').
Proof.
 intros a b l l' H z; simpl.
 case_eq (Z.eqb z a); case_eq (Z.eqb z b); 
  simpl; case (H z); auto.
Qed.

Hint Resolve equiv_cons equiv_refl equiv_perm : sort.


(* insertion of z into l at the right place 
   (assuming l is sorted) 
*)







(** Correlation between Z.leb and Z.le *)

SearchAbout (Z.leb _ _ = true).
(*
Zle_bool_imp_le: forall n m : Z, (n <=? m) = true -> n <= m
Zle_imp_le_bool: forall n m : Z, n <= m -> (n <=? m) = true
...
Z.leb_le: forall n m : Z, (n <=? m) = true <-> n <= m
*)
SearchAbout (Z.leb _ _ = false).
 

Ltac le_from_bool := repeat (rewrite Z.leb_le in * || rewrite Z.leb_gt in *).
(** Z.leb_gt: forall x y : Z, (x <=? y) = false <-> y < x *)


(* the insert function seems to be a good tool for sorting ... *)

Lemma insert_equiv : forall (l:list Z) (x:Z), 
                  equiv (x :: l) (insert x l).
Proof.
 induction l as [|a l0 H]; simpl ; auto with sort.
 intros x; case_eq (Z.leb x a);
   simpl; auto with sort.
  intro; apply equiv_trans with (a :: x :: l0); 
   auto with sort.
Qed.


Lemma insert_sorted :
 forall (l:list Z) (x:Z), sorted l -> sorted (insert x l).
Proof.
  intros l x H; elim H; simpl; auto with sort.
  -  intro z; case_eq (Z.leb x z); simpl; intros; 
     le_from_bool;  auto with sort zarith.
  -  intros z1 z2; case_eq (Z.leb x z2); simpl; intros; 
     case_eq (Z.leb x z1);intros; le_from_bool;  auto with sort zarith.
Qed.


Lemma sort_equiv : forall l, equiv l (insertion_sort l).
Proof.
 induction l;simpl;auto with sort.
 SearchAbout equiv.
apply equiv_trans with (a:: insertion_sort l).
 apply equiv_cons;auto.
 apply insert_equiv.
Qed.

Lemma sort_sorted : forall l, sorted (insertion_sort l).
induction l;simpl;auto with sort.
now apply insert_sorted.
Qed.


Extraction "insert-sort" insert insertion_sort.

(**

 Projet :

 Specifier de la facon la plus generique possible ce qu'est une fonction
 correcte de tri polymorphe sur des listes:

 Construire une version polymorphe du tri par insertion, et prouver qu'elle 
 realise la specification ci-dessus

 Afin d'illustrer la genericite de votre construction, montrer qu'elle
 permet de trier des listes de divers types de  données, et comment 
 realiser les transformations suivantes :
  + tri par ordre decroissant 
  + tri sur un produit lexicographique
  + tri selon les valeurs d'une fonction 


*)