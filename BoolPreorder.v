 Generalizable All Variables.

Class BoolPreorder {A:Type}(leb : A -> A -> bool) :=
  { leb_refl : forall a:A, leb a a = true;
    leb_trans :
      forall a b c, leb a b = true -> leb b c = true -> leb a c = true;
    leb_false : forall a b, leb a b = false -> leb b a = true}.


Definition ltb {A:Type}{leb : A -> A -> bool}{P: BoolPreorder leb}:=
fun a b => if leb a b then negb (leb b a) else false.


Definition equivb  {A:Type}{leb : A -> A -> bool}{P: BoolPreorder leb}:=
 fun a b => if leb a b then leb b a else false.

Definition le {A:Type}{leb : A -> A -> bool}{P: BoolPreorder leb}:=
fun a b => leb a b = true.

Definition lt {A} {leb: A -> A -> bool} {P : BoolPreorder leb} (a b: A) :=
ltb a b = true.

Definition equiv {A} {leb: A -> A -> bool} {P : BoolPreorder leb} (a b: A) :=
equivb a b = true.

Section Properties.
Variables (A: Type) (leb : A -> A -> bool).
Context (P: BoolPreorder leb).

 Lemma le_refl : forall a, le a a.
 Proof.
   intro a; unfold le; now rewrite leb_refl.
 Qed.

 Lemma le_trans : forall a b c, le a b -> le b c -> le a c.
 Proof.
  intros a b c H H0; unfold le.
  rewrite (leb_trans a b c H H0); trivial.
 Qed.


 Lemma ltb_irrefl : forall a, ltb a a = false.
 Proof.
 intro a; unfold ltb.
 now rewrite leb_refl.  
 Qed. 


 Lemma lt_irrefl : forall a:A , ~ lt a a.
 Proof.
  intros a H; unfold lt in H.
  rewrite ltb_irrefl in H.
  discriminate.
 Qed.
  
  Lemma le_lt_or_equiv :  forall a b, le a b -> lt a b \/ equiv a b.
  Proof.
 unfold le, lt, ltb, equiv, equivb;intros.
 case_eq (leb a b); case_eq (leb b a); intros; auto.
 - congruence.  
 -   congruence.  
 Qed. 

 Lemma lt_not_equiv : forall a b, lt a b -> ~ equiv a b.
 Proof.
   unfold lt, equiv, ltb, equivb.
  intros a b;case_eq (leb a b); case_eq (leb b a);auto; try discriminate. 
 Qed.


 Lemma le_or_lt : forall a b, le a b \/ lt b a.
 Proof.
   unfold le, lt, ltb.
   intros a b; case_eq (leb a b); auto. 
   right. 
   now rewrite (leb_false _ _ H).
 Qed.

 Lemma lt_not_le : forall a b, lt a b -> ~ le b a.
 Proof.
  unfold le, lt, ltb.
   intros a b; case_eq (leb a b); auto. 
    case (leb b a);
    discriminate.
  discriminate.   
Qed.

  Lemma lt_trans : forall a b c:A , lt a b -> lt b c -> lt a c.
  Proof.
    unfold lt, ltb.
    intros a b c; case  (leb a b); case_eq (leb b c); try discriminate. 
   intros.
   Admitted.


End Properties.

