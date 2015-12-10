Require Import Setoid.

Generalizable All Variables.

Module PO.

  Class BoolPreorder {A:Type}(leb : A -> A -> bool) :=
    { leb_refl : forall a:A, leb a a = true;
      leb_trans :
        forall a b c, leb a b = true -> leb b c = true -> leb a c = true;
      leb_false : forall a b, leb a b = false -> leb b a = true}.

  (** derivate boolean functions *)

  Definition ltb {A:Type}{leb : A -> A -> bool}{P: BoolPreorder leb}:=
    fun a b => if leb a b then negb (leb b a) else false.


  Definition equivb  {A:Type}{leb : A -> A -> bool}{P: BoolPreorder leb}:=
    fun a b => if leb a b then leb b a else false.

  (** Derivate Predicates *)

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

    Lemma ltb_lt : forall a b, ltb a b = true <-> lt a b.
    Proof.
      unfold lt; tauto.
    Qed.
    Lemma leb_le : forall a b, leb a b = true <-> le a b.
    Proof.
      unfold le; tauto.
    Qed.
    Lemma equivb_equiv : forall a b, equivb a b = true <-> equiv a b.
    Proof.
      unfold equiv; tauto.
    Qed.

    Lemma lt_irrefl : forall a:A , ~ lt a a.
    Proof.
      intros a H; unfold lt in H.
      rewrite ltb_irrefl in H.
      discriminate.
    Qed.

    Hint Resolve le_refl le_trans lt_irrefl.


    Lemma le_lt_or_equiv :  forall a b, le a b -> lt a b \/ equiv a b.
    Proof.
      unfold le, lt, ltb, equiv, equivb;intros.
      case_eq (leb a b); case_eq (leb b a); intros; auto.
      - congruence.  
      - congruence.  
    Qed. 

    Lemma lt_not_equiv : forall a b, lt a b -> ~ equiv a b.
    Proof.
      unfold lt, equiv, ltb, equivb.
      intros a b;case_eq (leb a b); case_eq (leb b a);auto; try discriminate. 
    Qed.

    Lemma equiv_refl : forall a, equiv a a.
    Proof.
      intros ; unfold equiv, equivb; now rewrite leb_refl.
    Qed.

    Lemma equiv_trans: forall a b c, equiv a b -> equiv b c -> equiv a c.
    Proof.
      unfold equiv, equivb; intros.
      case_eq (leb a b);case_eq (leb b c).
      - intros ;  rewrite H1, H2 in *;  rewrite (leb_trans  a b c H2 H1);
        now rewrite (leb_trans  c b a H0 H).
      -  intros;   rewrite H1, H2 in *;    discriminate.
      -  intros;   rewrite H1, H2 in *;    discriminate.
      -  intros;   rewrite H1, H2 in *;    discriminate.
    Qed.

    Lemma equiv_sym: forall a b , equiv a b -> equiv b a.
    Proof.
      unfold equiv, equivb; intros.
      case_eq (leb a b).
      - intro H0; rewrite H0 in *.
        now rewrite H.
      -  intro H0; rewrite H0 in H.
         discriminate.
    Qed.

    Hint Resolve equiv_sym equiv_trans.

    Lemma le_or_lt : forall a b, le a b \/ lt b a.
    Proof.
      unfold le, lt, ltb.
      intros a b; case_eq (leb a b); auto. 
      right;   now rewrite (leb_false _ _ H).
    Qed.

    Lemma negb_inv : forall b, negb b = true <-> b = false.
    Proof.
      destruct b;split;auto.
    Qed.

    Lemma lt_trans : forall a b c:A , lt a b -> lt b c -> lt a c.
    Proof.
      unfold lt, ltb.
      intros a b c; case  (leb a b); case_eq (leb b c); try discriminate. 
      intros.
      rewrite negb_inv in H0, H1.
      case_eq (leb c a).
      intro H2.
      rewrite (leb_trans _ _ _ H H2) in H0; discriminate.
      intro H2; apply leb_false in H2; now rewrite H2.
    Qed.

    Hint Resolve lt_trans.

    Lemma lt_not_le : forall a b, lt a b -> ~ le b a.
    Proof.
      intros a b H H0; destruct (le_lt_or_equiv _ _ H0).
      - destruct (lt_irrefl a);eauto.
      -  destruct (lt_not_equiv a b);auto.
    Qed.

    Hint Resolve lt_not_le.
    
    Lemma lt_iff : forall a b, lt a b <-> le a b /\ ~ equiv a b.
    Proof.
      split; intros.
      - split.
        red; apply leb_false;auto.
        red in H.
        unfold ltb in H.
        case_eq (leb a b); intro H0; rewrite H0 in *.
        +  now  rewrite negb_inv in H.
        +   discriminate.
        +  unfold lt, equiv, ltb, equivb  in *.
           case_eq (leb a b).   
           *  intro H0; rewrite H0 in *; rewrite negb_inv in H;
              rewrite H;discriminate.
           *   discriminate.
      - 
        destruct H;  unfold lt, equiv, ltb, equivb  in *.
        case_eq (leb a b).   
        +  intro H1; rewrite H1 in *; rewrite negb_inv;  destruct (leb b a);auto.
           * now destruct H0.
        + intro H1; rewrite H1 in *.
          red in H;rewrite H in H1; discriminate.
    Qed.


    Lemma equiv_iff : forall a b, equiv a b <-> le a b /\ le b a.
    Proof.
      split; intros  H.
      - unfold le, equiv in *.
        unfold equivb in H.
        case_eq (leb a b).
        + intro H0; rewrite H0 in *; auto.
        +   intro H0; rewrite H0 in *; auto.
            discriminate.
      - unfold le, equiv, equivb  in *.
        destruct H as [H0 H1]; now rewrite H0, H1 in *.
    Qed.


    Lemma equiv_lt : forall a b c, equiv a b -> lt b c -> lt a c.
      intros.
      rewrite lt_iff in *.
      destruct H0;split. 
      rewrite equiv_iff in H1.
      apply le_trans with b;auto.
      rewrite equiv_iff in H; tauto.
      intro H2; destruct H1.
      apply equiv_trans with a.
      now apply equiv_sym.
      auto.
    Qed.

    Lemma lt_equiv : forall a b c, lt a b -> equiv b c -> lt a c.
      intros.
      rewrite lt_iff in *.
      rewrite equiv_iff in H0.
      destruct H, H0; split.
      
      apply le_trans with b;auto.
      intro H3; destruct H1.
      apply equiv_trans with c; trivial. rewrite  equiv_iff; auto.
    Qed.

    Lemma le_lt_trans : forall a b c, le a b -> lt b c -> lt a c.
    Proof.
      intros a b c H H0.
      destruct (le_lt_or_equiv _ _ H).
      now apply lt_trans with b.
      apply equiv_lt with b;auto.
    Qed.

    Lemma lt_le_trans : forall a b c, lt a b -> le b c -> lt a c.
    Proof.
      intros a b c H H0.
      destruct (le_lt_or_equiv _ _ H0).
      now apply lt_trans with b.
      apply lt_equiv with b;auto.
    Qed.

  End Properties.

  Instance BoolReverse {A}{leb : A -> A -> bool}(P: BoolPreorder leb):
    BoolPreorder (fun x y => leb y x).
  Proof.
    split.
    -  apply leb_refl.
    - intros; now apply (@leb_trans A leb P c b a).
    - intros; now apply (@leb_false A leb P   b a).
  Qed.


  Definition lexico_leb {A B : Type} {lebA : A -> A -> bool}
             {lebB : B -> B -> bool} (PA: BoolPreorder lebA)
             (PB: BoolPreorder lebB)
  : A * B -> A * B -> bool :=
    fun p q =>
      if ltb (fst p) (fst q)
      then true
      else  if equivb (fst p) (fst q)
            then lebB (snd p) (snd q)
            else false.

  Instance Lexico {A B : Type} {lebA : A -> A -> bool}
           {lebB : B -> B -> bool} (PA: BoolPreorder lebA)
           (PB: BoolPreorder lebB) : BoolPreorder (lexico_leb PA PB).

  unfold lexico_leb; split.
  - intro a; rewrite ltb_irrefl. unfold equivb. now repeat rewrite leb_refl.
  - intros a b c ;
    case_eq (ltb (fst a) (fst b)); case_eq  (ltb (fst b) (fst c)); intros.

    repeat (rewrite ltb_lt in * ||
            rewrite leb_le in * ||
            rewrite equivb_equiv in *) .
            generalize (lt_trans _ _ _ _ _ _ H0 H).
            rewrite <- ltb_lt; intro H3;rewrite H3; trivial.
            
 Admitted.

End PO.
            
Require Import ZArith. 
Import PO.

Instance Z_leb : BoolPreorder Z.leb.
Proof.
  split.
  -  intros; now rewrite Z.leb_refl.
  -   intros; eapply Zle_bool_trans; eauto.
  -   intros a b H; rewrite    Z.leb_gt in H. 
      apply Zle_imp_le_bool; auto with zarith.
Qed.

Definition Z_down := BoolReverse Z_leb.
About ltb.
            
Compute ltb (P:= Z_down) 8%Z (-4)%Z.

Definition  Z2 : BoolPreorder (lexico_leb Z_leb Z_leb).
Proof.
  apply Lexico.
Qed.

Compute ltb  (5,8900)%Z (6,0)%Z.

Compute ltb  (5,8900)%Z (5,0)%Z.

About lt.
Goal lt (5,8900)%Z (6,0)%Z.
  unfold lt.
  reflexivity.
Qed.

Locate le_lt_trans.

About Top.le_lt_trans.

(** Must be re-declared ouside the Section *)

Hint Resolve lt_trans.
Goal forall a b c : Z * Z, lt a b -> lt b c -> lt a c.
  eauto.
Qed.

(** Exemple *)

Require Import List.
Fixpoint mini_aux {A} {leb: A -> A -> bool}
         {P: BoolPreorder leb} x (l:list A) :=
  match l with
    | nil => x
    | (a::l') => if ltb a x then mini_aux a l' else mini_aux x l'
  end.

Definition mini {A} {leb: A -> A -> bool}{P: BoolPreorder leb}
           (l:list A) : option A :=
  match l with 
    | nil => None
    | x::l' => Some (@mini_aux A leb P  x l')
  end.


Compute mini (P:= Z_down)  (4::6::2::nil)%Z.


Compute mini (P:= Z_leb)  (4::6::2::nil)%Z.


Compute mini ((4,8)::(4,9)::(3,999)::nil)%Z.

Compute mini (P:= BoolReverse Z2) ((4,8)::(4,9)::(3,999)::nil)%Z. Generalizable All Variables.

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

