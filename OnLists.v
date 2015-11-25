Require Import List.

Print list.

Check list_ind.

Definition tl {A:Type} (l: list A) : list A :=
match l with
| nil => nil
| a::l' => l'
end.
Compute tl (3::5::8::nil).

(**
Fixpoint app {A:Type} (l l' : list A) : list A :=
match l with 
| nil => l'
| a:: m => a :: (app m l')
end.
*)



Compute (1::2::3::nil) ++ (5::6::nil).

Lemma app_assoc {A:Type} :
 forall l l' l'' : list A, (l ++ l') ++ l'' = l ++ (l' ++ l'').
Proof.
  induction l.
  - simpl. intros;reflexivity.
  - simpl. intros.  rewrite IHl.
    reflexivity.
Qed.

Fixpoint In {A:Type} (x:A)(l : list A) : Prop  :=
match l with
| nil => False
| y :: l' => x = y \/ In x l'
end.

Inductive mem {A:Type} (x:A) : list A -> Prop  :=
| mem_hd : forall l', mem x (x::l')
| mem_tl : forall y l', mem x l' -> mem x (y::l').

Fixpoint memb  {A:Type} (eqb : A -> A -> bool) (x:A) (l : list A) :=
match l with
| nil => false
| y :: l' => if eqb x y then true else memb eqb x l'
end.


Lemma mem_In : forall A (x:A) l, mem x l -> In x l.
Proof.
  intros A x l H.
  induction H.
  - simpl.
    left;trivial.
  -  simpl.
    right;assumption.
Qed.

Lemma In_mem : forall A (x:A) l, In x l -> mem x l.
Proof.
  induction l.
  - intro H.
    inversion H.  
  -  intro H; inversion H.
     + subst x; constructor.
     + constructor. 
      apply IHl; assumption.
Qed. 

Lemma memb_In {A:Type}(eqb: A -> A -> bool)
      : forall (x:A) l, memb eqb x l = true -> In x l.
Proof.
 induction l.
 - simpl.
   discriminate.
 - simpl.
   intro H; case_eq (eqb x a).
   + Abort.

Definition correct_eq {A:Type}(eqb : A -> A -> bool) :=
 forall x y : A, eqb x y = true <-> x = y.
 
Lemma memb_In {A:Type}(eqb: A -> A -> bool)(Ok : correct_eq eqb) 
      : forall (x:A) l, memb eqb x l = true -> In x l.
Proof.
 induction l.
 - simpl.
   discriminate.
 - simpl.
   intro H; case_eq (eqb x a).
   + rewrite (Ok x a).
     auto.
   +  intro H0;rewrite H0 in H.  
      auto.
Qed.

Lemma In_memb {A:Type}(eqb: A -> A -> bool)(Ok : correct_eq eqb) 
      : forall (x:A) l, In x l -> memb eqb x l = true.
Proof.
 induction l.
 - simpl.
  contradiction.
 - simpl. intro H.
   destruct H.
   rewrite <- (Ok x a) in H.
   now rewrite H.
   rewrite IHl.
   now  destruct (eqb x a).   
   assumption.
Qed.

