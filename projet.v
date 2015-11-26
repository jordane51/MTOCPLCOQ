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

Require Import List.
Require Import ZArith.
Section poly.

Variables (T:Type)
          (leb:T->T->bool)
          (eqb:T->T->bool).

Fixpoint insert (z:T) (l:list T) {struct l} : list T :=
  match l with
  | nil => z :: nil
  | cons a l' => if leb z a
      then z :: a :: l'
      else a :: insert z l'
 end.

Fixpoint insertion_sort (l:list T) : list T :=
match l with
| nil => nil
| z::l' => insert z (insertion_sort l')
end.

Inductive sorted : list T -> Prop :=
  | sorted0 : sorted nil
  | sorted1 : forall t:T, sorted (t :: nil)
  | sorted2 :
      forall (t1 t2:T) (l:list T),
        (leb t1 t2) = true ->
        sorted (t2 :: l) -> sorted (t1 :: t2 :: l).

Fixpoint nb_occ (z:T) (l:list T) {struct l} : nat :=
  match l with
  | nil => 0%nat
  | (z' :: l') =>
      if eqb z z' 
      then S (nb_occ z l')
      else nb_occ z l'
  end.

Definition equiv (l l':list T) := 
    forall z:T, nb_occ z l = nb_occ z l'.

Hint Resolve sorted0 sorted1 sorted2 : sort.
Theorem sorted_inv :
 forall (z:T) (l:list T), sorted (z :: l) -> sorted l.
Proof.
 intros z l H.
 inversion H; auto with sort.
Qed.

Lemma equiv_refl : forall l:list T, equiv l l.
Proof.
 unfold equiv; trivial.
Qed.

Lemma equiv_sym : forall l l':list T, equiv l l' -> equiv l' l.
Proof.
  unfold equiv; auto.
Qed.

Lemma equiv_trans :
 forall l l' l'':list T, equiv l l' -> 
                         equiv l' l'' -> 
                         equiv l l''.
Proof.
 intros l l' l'' H H0 z.
 eapply trans_eq; eauto.
Qed.

Lemma equiv_cons :
 forall (t:T) (l l':list T), equiv l l' -> 
                             equiv (t :: l) (t :: l').
Proof.
 intros t l l' H t'.
 simpl; case_eq  (eqb t' t); auto. 
Qed.

Lemma equiv_perm :
 forall (a b:T) (l l':list T),
   equiv l l' -> 
   equiv (a :: b :: l) (b :: a :: l').
Proof.
 intros a b l l' H t; simpl.
 case_eq (eqb t a); case_eq (eqb t b); 
  simpl; case (H t); auto.
Qed.

Hint Resolve equiv_cons equiv_refl equiv_perm : sort.

End poly.

About insert.
Open Scope Z_scope.

Hint Resolve sorted0 sorted1 sorted2 : sort.
Lemma sort_2357 :
 sorted Z Z.leb (2 :: 3 :: 5 :: 7 :: nil).
Proof.
 auto with sort zarith.
Qed.

Section Tests.
Compute insert Z Z.leb 4 (2 :: 5 :: nil).
Compute insertion_sort Z Z.leb (4::9::7::9::12::3::nil).
Eval compute in (nb_occ Z Z.eqb 3 (3 :: 7 :: 3 :: nil)).

Compute insert Z Z.geb 4 (5 :: 2 :: nil).
Compute insertion_sort Z Z.geb (4::9::7::9::12::3::nil).

Require Import Ascii.

End Tests.