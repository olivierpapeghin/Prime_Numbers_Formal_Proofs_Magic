From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Program.Equality.
Require Import List String.

Import ListNotations.

Inductive ManaColor := White | Blue | Black | Red | Green | Generic.

Record Mana := mkMana {
  color : ManaColor;
  quantity : nat
}.

Record Creature := mkCreature {
  power : nat;
  toughness : nat
}.

Record Enchantement := mkEnchantement {
  
}.

Record Artifact := mkArtifact {

}.

Record Land := mkLand {
  producing : ManaColor
}.


(* Définition d'une carte permanente *)
Record Permanent := mkPermanent {
  creature : option Creature;
  enchantement : option Enchantement;
  land : option Land;
  artifact : option Artifact;
  token : bool;
  legendary : bool;
}.

Record Sorcery := mkSorcery {
  Spell : list nat;
}.

(* Définition d'une carte éphémère *)
Record Instant := mkInstant {
  spell : list nat;
}.

(* Définition d'une carte *)
Record Card := mkCard {
  permanent : option Permanent;
  instant : option Instant;
  sorcery : option Sorcery;
  manacost : list Mana;
  name : string
}.

Inductive CardOrPair :=
| CardItem : Card -> CardOrPair
| PairItem : string -> nat -> CardOrPair.


Record GameState := mkGameState {
  battlefield : list Permanent;
  hand : list Card;
  library : list Card;
  graveyard : list Card;
  exile : list Card;
  opponent : nat;
  manapool : list Mana;
  stack : list CardOrPair;
}.


(* Définition des différentes fonctions pour jouer un sort*)

(* Fonctions de comparaison *)
(* Fonction qui compare les listes d'entiers *)
Fixpoint eq_list_nat (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => Nat.eqb x y && eq_list_nat xs ys
  | _, _ => false
  end.

(* Fonction de comparaison pour les couleurs de mana *)
Definition eq_manacolor (mc1 mc2 : ManaColor) : bool :=
  match mc1, mc2 with
  | Generic, _ => true
  | _, Generic => true
  | White, White => true
  | Blue, Blue => true
  | Black, Black => true
  | Red, Red => true
  | Green, Green => true
  | _, _ => false
  end.

Definition eq_mana (m1 m2 : Mana) : bool :=
  eq_manacolor m1.(color) m2.(color) && Nat.eqb m1.(quantity) m2.(quantity).

(* Fonction de comparaison pour les listes de Mana *)
Fixpoint eq_list_mana (l1 l2 : list Mana) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => (eq_mana x y) && eq_list_mana xs ys
  | _, _ => false
  end.

(* Fonction de comparaison pour les options *)
Definition eq_option {A : Type} (eqA : A -> A -> bool) (o1 o2 : option A) : bool :=
  match o1, o2 with
  | None, None => true
  | Some x, Some y => eqA x y
  | _, _ => false
  end.

(* Fonction de comparaison pour Creature *)
Definition eq_creature (c1 c2 : Creature) : bool :=
  (c1.(power) =? c2.(power)) && (c1.(toughness) =? c2.(toughness)).

(* Fonction de comparaison pour Land *)
Definition eq_land (l1 l2 : Land) : bool :=
  eq_manacolor l1.(producing) l2.(producing).

(* Fonction de comparaison pour Permanent *)
Definition eq_permanent (p1 p2 : Permanent) : bool :=
  eq_option eq_creature p1.(creature) p2.(creature) &&
  eq_option eq_land p1.(land) p2.(land) &&
  eq_option (fun _ _ => true) p1.(enchantement) p2.(enchantement) && (* Supposition : tous les enchantements sont identiques *)
  eq_option (fun _ _ => true) p1.(artifact) p2.(artifact) && (* Supposition : tous les artefacts sont identiques *)
  Bool.eqb p1.(token) p2.(token) &&
  Bool.eqb p1.(legendary) p2.(legendary).

(* Fonction de comparaison pour Instant *)
Definition eq_instant (i1 i2 : Instant) : bool :=
  eq_list_nat i1.(spell) i2.(spell).

(* Fonction de comparaison pour Sorcery *)
Definition eq_sorcery (s1 s2 : Sorcery) : bool :=
  eq_list_nat s1.(Spell) s2.(Spell).

(* Fonction principale de comparaison de deux cartes *)
Definition eq_card (c1 c2 : Card) : bool :=
  eq_option eq_permanent c1.(permanent) c2.(permanent) &&
  eq_option eq_instant c1.(instant) c2.(instant) &&
  eq_option eq_sorcery c1.(sorcery) c2.(sorcery) &&
  eq_list_mana c1.(manacost) c2.(manacost) &&
  String.eqb c1.(name) c2.(name).



(* Fonctions pour vérifier et payer le coût en mana de la carte qu'on joue *)
Definition ManaColor_eq (mc1 mc2 : ManaColor) : bool :=
  match mc1, mc2 with
  | Generic, _ => true
  | _, Generic => true
  | White, White => true
  | Blue, Blue => true
  | Black, Black => true
  | Red, Red => true
  | Green, Green => true
  | _, _ => false
  end.



(* Fonction count_occ qui compte le nombre d'occurrences d'un élément dans une liste *)
Fixpoint count_occ (A : Type) (eqb : A -> A -> bool) (l : list A) (x : A) : nat :=
  match l with
  | [] => 0
  | h :: t => if eqb x h then 1 + count_occ A eqb t x else count_occ A eqb t x
  end.

Fixpoint remove_mana (pool : list Mana) (cost : Mana) : list Mana :=
  match pool with
  | [] => [] (* Si le pool est vide, rien à retirer *)
  | h :: t =>
      if ManaColor_eq h.(color) cost.(color) then
        (* Si c'est le même type de mana, on essaie de le consommer *)
        if Nat.leb cost.(quantity) h.(quantity) then
          (* Si la quantité du mana est suffisante pour le coût, on réduit ou on retire *)
          if Nat.eqb cost.(quantity) h.(quantity) then
            t (* On retire le mana si la quantité est exactement la même *)
          else
            {| color := h.(color); quantity := h.(quantity) - cost.(quantity) |} :: t (* On ajuste la quantité restante *)
        else
          (* Si le mana n'est pas suffisant, on le laisse dans le pool *)
          remove_mana t cost
      else
        (* Si ce n'est pas le mana de la bonne couleur, on continue avec le reste du pool *)
        h :: remove_mana t cost
  end.

Fixpoint Can_Pay (cost : list Mana) (pool : list Mana) : bool :=
  match cost with
  | [] => true (* Tout le coût est couvert, on retourne vrai *)
  | c :: cs =>
      if ManaColor_eq c.(color) Generic then
        (* Si le coût est générique, on cherche un mana de n'importe quelle couleur dans le pool *)
        match pool with
        | [] => false (* Pas assez de mana dans le pool *)
        | h :: t =>
            (* On consomme n'importe quel mana coloré pour couvrir le coût générique *)
            Can_Pay cs t (* Continue à chercher les autres coûts, après avoir retiré un mana du pool *)
        end
      else
        (* Si c'est un mana coloré spécifique, on cherche un mana correspondant dans le pool *)
        match find (fun m => ManaColor_eq m.(color) c.(color)) pool with
        | Some m =>
            (* Si on trouve un mana de la bonne couleur, on le consomme *)
            if Nat.leb c.(quantity) m.(quantity) then
              Can_Pay cs (remove_mana pool c) (* Consommer le mana et vérifier les autres coûts *)
            else
              false (* Pas assez de mana de cette couleur, on échoue *)
        | None => false (* Pas de mana correspondant dans le pool, on échoue *)
        end
  end.

(* On doit ensuite manipuler les zones dans lesquels les cartes vont passer *)
(* Fonction remove_card qui retire la première occurrence de c dans la liste l *)
Fixpoint remove_card (l : list Card) (c : Card) : list Card :=
  match l with
  | [] => [] (* Si la liste est vide, retourne une liste vide *)
  | h :: t => if eq_card h c then t (* Si on trouve la carte, on la retire *)
              else h :: remove_card t c (* Sinon, on continue à chercher *)
  end.

Definition Cast (c:Card) (gs:GameState) : (GameState) :=
  let cost := c.(manacost) in
  let pool := gs.(manapool) in
  if Can_Pay cost pool then
    let new_pool := fold_left remove_mana cost pool in
    let new_hand := remove_card gs.(hand) c in
    let new_stack := CardItem c :: gs.(stack) in
    let new_gs := mkGameState gs.(battlefield) new_hand gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) new_pool new_stack in
    (new_gs)
  else
    (gs)
  .

(* Enfin pour vérifier notre théorème on doit pouvoir vérifier qu'un permanent est sur le champ de bataille *)
Fixpoint is_on_battlefield (bf : list Card) (c : Card) : bool :=
  match bf with
  | [] => false
  | h :: t => if eq_card h c then true else is_on_battlefield t c
  end.

