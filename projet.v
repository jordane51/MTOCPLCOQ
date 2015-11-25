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
          (leb:T->T->bool).

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

End poly.


About insert.
Open Scope Z_scope.
Compute insert Z Z.leb 4 (2 :: 5 :: nil).
Compute insertion_sort Z Z.leb (4::9::7::9::12::3::nil).