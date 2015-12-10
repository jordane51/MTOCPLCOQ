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

About insertion_sort.

(* manque les théormes qui disent que la liste sera triée et équivalente à l*)


Lemma insert_equiv : forall (l:list T) (x:T), 
                  equiv (x :: l) (insert x l).
Proof.
 induction l as [|a l0 H]; simpl ; auto with sort.
 intros x; apply equiv_refl; case_eq (leb x a);
   simpl; auto with sort.
  intro; apply equiv_trans with (a :: x :: l0); 
   auto with sort.
   - apply equiv_perm. apply equiv_refl.
   - case (leb x a).
     + apply equiv_perm. apply equiv_refl.
     + .
Qed.

Lemma insert_sorted :
 forall (l:list T) (x:T), sorted l -> sorted (insert x l).
Proof.
  intros l x H; elim H; simpl; auto with sort.
  -  intro z; case_eq (leb x z); simpl; intros; 
     le_from_bool;  auto with sort zarith.
  -  intros z1 z2; case_eq (leb x z2); simpl; intros; 
     case_eq (leb x z1);intros; le_from_bool;  auto with sort zarith.
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

.Hint Resolve equiv_cons equiv_refl equiv_perm : sort.

End poly.

Check insertion_sort.
Check 

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

Variable (E:Type)
         (F:Type)
         (lebE:E->E->bool)
         (lebF:F->F->bool)
         (eqbE:E->E->bool)
         (eqbF:F->F->bool).

Definition lexCompare (x y : E*F) : bool :=
   if eqbE (fst x) (fst y)
      then lebF (snd x) (snd y)
      else lebE (fst x) (fst y).

(*
Fixpoint lexInsert (z:E*F) (l:list (E*F)) {struct l} : list (E*F) :=
  match l with
  | nil => z :: nil
  | cons a l' => if lexCompare z a
      then z :: a :: l'
      else a :: lexInsert z l'
 end.

Fixpoint lexInsertion_sort (l:list (E*F)) : list (E*F) :=
match l with
| nil => nil
| z::l' => lexInsert z (lexInsertion_sort l')
end.

Inductive lexSorted : list (E*F) -> Prop :=
  | lexSorted0 : lexSorted nil
  | lexSorted1 : forall t:E*F, lexSorted (t :: nil)
  | lexSorted2 :
      forall (t1 t2:E*F) (l:list (E*F)),
        (lexCompare t1 t2) = true ->
        lexSorted (t2 :: l) -> lexSorted (t1 :: t2 :: l).

Fixpoint lexNb_occ (z:E*F) (l:list (E*F)) {struct l} : nat :=
  match l with
  | nil => 0%nat
  | (z' :: l') =>
      if andb (eqbE (fst z) (fst z')) (eqbF (snd z) (snd z'))
      then S (lexNb_occ z l')
      else lexNb_occ z l'
  end.

Definition lexEquiv (l l':list (E*F)) := 
    forall z:E*F, lexNb_occ z l = lexNb_occ z l'.

Hint Resolve lexSorted0 lexSorted1 lexSorted2 : lexSort.
Theorem lexSorted_inv :
 forall (z:E*F) (l:list (E*F)), lexSorted (z :: l) -> lexSorted l.
Proof.
 intros z l H.
 inversion H; auto with lexSort.
Qed.

Lemma lexEquiv_refl : forall l:list (E*F), lexEquiv l l.
Proof.
 unfold lexEquiv; trivial.
Qed.

Lemma lexEquiv_sym : forall l l':list (E*F), lexEquiv l l' -> lexEquiv l' l.
Proof.
  unfold lexEquiv; auto.
Qed.

Lemma lexEquiv_trans :
 forall l l' l'':list (E*F), lexEquiv l l' -> 
                         lexEquiv l' l'' -> 
                         lexEquiv l l''.
Proof.
 intros l l' l'' H H0 z.
 eapply trans_eq; eauto.
Qed.

Definition lexCompareEq (x y : E*F) : bool :=
   if eqbE (fst x) (fst y)
      then eqbF (snd x) (snd y)
      else false.



Inductive IlexEquiv : list (E*F) -> list (E*F) -> Prop :=
  | IlexEquiv0 : IlexEquiv nil nil
  | IlexEquiv1 : 
    forall (l1 l2 : list (E*F)) (t1 t2: (E*F)),
      (lexCompareEq t1 t2) = true ->
      IlexEquiv (t1 :: l1)  (t2 :: l2) -> 
      IlexEquiv l1 l2.

Lemma lexEquiv_cons :
 forall (t:E*F) (l l':list (E*F)), lexEquiv l l' -> 
                             lexEquiv (t :: l) (t :: l').
Proof.
 intros t l l' H t'.
 simpl.  case_eq (eqbE (fst t) (fst t')); auto.
  -case_eq (eqbF (snd t) (snd t')); auto.
Qed.

Lemma lexEquiv_perm :
 forall (a b:E*F) (l l':list (E*F)),
   lexEquiv l l' -> 
   lexEquiv (a :: b :: l) (b :: a :: l').
Proof.
 intros a b l l' H t; simpl.
 case_eq (andb (eqbE (fst t) (fst a)) (eqbF (snd t) (snd a)));
 case_eq (andb (eqbE (fsttz) (fst b)) (eqbF (snd t) (snd b))); 
  simpl; case (H t); auto.
Qed.

Hint Resolve equiv_cons equiv_refl equiv_perm : sort.
*)



End Tests.