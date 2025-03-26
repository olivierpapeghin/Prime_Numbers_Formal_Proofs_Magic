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

(* Définition du type de carte *)
Inductive CardType :=
  | PermanentType
  | InstantType
  | SorceryType
  | UnknownType. (* Si aucun type n'est défini *)

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
  sorcery_spell : list nat;
}.

(* Définition d'une carte éphémère *)
Record Instant := mkInstant {
  instant_spell : list nat;
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
  battlefield : list Card;
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
  eq_list_nat i1.(instant_spell) i2.(instant_spell).

(* Fonction de comparaison pour Sorcery *)
Definition eq_sorcery (s1 s2 : Sorcery) : bool :=
  eq_list_nat s1.(sorcery_spell) s2.(sorcery_spell).

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

(* On peut déjà vérifer que toutes les étapes marchent bien en testant si un cast est bien fonctionnel *)

(* Instanciation de la carte *)
Definition colossal_dreadmaw : Card := 
  mkCard 
  (Some (mkPermanent (* Est un permanent *)
    (Some (mkCreature 6 6)) (* Est une créature 6/6*)
    None (* N'est pas un enchantement *)
    None (* N'est pas un artifact *)
    None (* N'est pas une land *)
    false (* N'est pas tapped *)
    false)) (* N'est pas légendaire *)
  None (* N'est pas un instant *)
  None (* N'est pas un sorcery *)
  [mkMana Green 1; mkMana Generic 5] (* Coûte 5 mana générique et 1 mana vert *)
  "Colossal Dreadmaw". (* Nom de la carte *)

(* Instanciation du GameState initial *)
Definition initial_gamestate : GameState := 
  mkGameState
  nil (* Le champ de bataille est vide *)
  [colossal_dreadmaw]
  nil (* La bibliothèque est vide *)
  nil (* Le cimetière est vide *)
  nil (* L'exil est vide *)
  20 (* L'opposant est à 20 PV *)
  [mkMana White 20; mkMana Blue 20; mkMana Black 20; mkMana Red 20; mkMana Green 20] (* On se donne assez de mana pour pouvoir lancer le sort *)
  nil (* La pile est vide *).

Definition gamestate_proof1 : GameState := Cast colossal_dreadmaw initial_gamestate.


(* Lemme : Si une carte est dans la stack et qu'il n'y a aucune carte dans la main, alors cette carte existe bien dans la stack et la main est vide. *)
Lemma card_on_stack_no_hand :
  forall (c : CardOrPair) (gs : GameState),
    In c (stack gs) ->
    gs.(hand) = [] ->
    exists c', In c' (stack gs) /\ gs.(hand) = [].
Proof.
  (* Introduction des variables et des hypothèses *)
  intros c gs Hstack Hhand.

  (* On affirme que la carte c satisfait la propriété *)
  exists c.

  (* Démonstration des deux conditions : *)
  split.
  - (* Première condition : la carte est sur le champ de bataille *)
    exact Hstack.
  - (* Deuxième condition : la main est vide *)
    exact Hhand.
Qed.

(* On va maintenant resolve la pile pour que notre carte arrive sur le champ de bataille *)

(* Fonction qui retourne le dernier élément d'une liste *)
Fixpoint last_option {A : Type} (l : list A) : option A :=
  match l with
  | [] => None                 (* Si la liste est vide, retourne None *)
  | [x] => Some x              (* Si un seul élément, retourne Some x *)
  | _ :: xs => last_option xs  (* Sinon, continue sur le reste de la liste *)
  end.

(* Fonction qui vérifie si un élément est une carte *)
Definition is_card (x : CardOrPair) : bool :=
  match x with
  | CardItem _ => true
  | PairItem _ _ => false
  end.

(* Fonction pour enlever le dernier élément d'une liste *)
Fixpoint remove_last {A : Type} (l : list A) : list A :=
  match l with
  | [] => []                  (* Si la liste est vide, on retourne une liste vide *)
  | [x] => []                 (* Si un seul élément, on l'enlève en retournant [] *)
  | x :: xs => x :: remove_last xs (* Sinon, on reconstruit la liste sans le dernier élément *)
  end.

(* Fonction qui détermine le type d'une carte *)
Definition card_type (c : Card) : CardType :=
  match c with
  | mkCard (Some _) None None _ _ => PermanentType
  | mkCard None (Some _) None _ _ => InstantType
  | mkCard None None (Some _) _ _ => SorceryType
  | _ => UnknownType
  end.

(* Fonction qui extrait une Card si présente dans un CardOrPair *)
Definition extract_card (cop : CardOrPair) : option Card :=
  match cop with
  | CardItem c => Some c
  | PairItem _ _ => None
  end.

(* Fonction qui gère la résolution de la stack *)
Definition Resolve (gs : GameState) : GameState :=
  match last_option gs.(stack) with
  | Some (CardItem c) => (* Si c'est une carte *)
      match card_type c with
      | PermanentType => (* Si c'est un permanent *)
        let new_stack : list CardOrPair:= remove_last gs.(stack) in
        let new_battlefield : list Card := gs.(battlefield) in
        mkGameState new_battlefield gs.(hand) gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) gs.(manapool) new_stack
      | InstantType => gs (* On ne gère pas encore cette éventualité *)
      | SorceryType => gs (* On ne gère pas encore cette éventualité *)
      | UnknownType => gs (* Si on ne reconnait pas le type de la carte on ne fait rien *)
      end
  | Some (PairItem i d) => gs (* Si le dernier élément est une capacité, on ne la traite pas encore *)
  | None => gs (* Si la stack est vide, on ne fait rien *)
  end.

Definition gamestate_proof2 : GameState := Resolve gamestate_proof1.

Lemma card_on_battlefield_no_stack :
  forall (c : Card) (gs : GameState),
    In c (battlefield gs) ->
    gs.(stack) = [] ->
    exists c', In c' (battlefield gs) /\ gs.(stack) = [].
Proof.
  (* Introduction des variables et des hypothèses *)
  intros c gs Hbattle Hstack.

  (* On affirme que la carte c satisfait la propriété *)
  exists c.

  (* Démonstration des deux conditions : *)
  split.
  - (* Première condition : la carte est sur le champ de bataille *)
    exact Hbattle.
  - (* Deuxième condition : la stack est vide *)
    exact Hstack.
Qed.