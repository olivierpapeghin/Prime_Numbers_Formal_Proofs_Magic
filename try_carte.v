From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Program.Equality.
Require Import List String.
Require Import String.
Require Import List.
Import ListNotations.
Require Import type_definitions.
Import type_definition.
Require Import utility_functions.
Import utility_function.
Require Import card_instances.
Import card_instance.
Module Try_card.


(* Fonction pour sacrifier des cartes et les déplacer vers le cimetière *)
Definition sacrifice_cards (targets : option (list Card)) (gs : GameState) : GameState :=
  match targets with
  | None => gs (* Si aucune cible n'est fournie, retourner l'état du jeu inchangé *)
  | Some target_cards =>
    fold_left
      (fun new_gs target =>
        match target.(permanent) with
        | None => new_gs (* Si la carte n'est pas un permanent, ne rien faire *)
        | Some target_perm =>
          let new_battlefield := remove_card new_gs.(battlefield) target in
          let new_graveyard := target :: new_gs.(graveyard) in
          mkGameState new_battlefield new_gs.(hand) new_gs.(library) new_graveyard new_gs.(exile)
                        new_gs.(opponent) new_gs.(manapool) new_gs.(stack)
        end)
      target_cards
      gs
  end.

(* Définition d'une capacité qui ajoute un mana noir au manapool *)
Definition add_black_mana (targets : option (list Card)) (gs : GameState) : GameState :=
  let new_manapool := (mkMana Black 1) :: gs.(manapool) in
  mkGameState gs.(battlefield) gs.(hand) gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) new_manapool gs.(stack).

(* Définition des sous-dictionnaires *)
Definition OnCast : Dict := [(1, add_black_mana)].
Definition OnPhase : Dict := nil.
Definition OnDeath : Dict := nil.
Definition OnEnter : Dict := [(1, sacrifice_cards)].


(* Définition du dictionnaire principal avec des clés de type string *)
Definition Triggered_Abilities : list (nat * Dict) :=
  ( 1 , OnCast) :: (2 , OnPhase) :: (3 , OnDeath) :: (4, OnEnter) :: nil.

(* Fonction pour trouver un sous-dictionnaire par sa clé *)
Fixpoint find_sub_dict (dicts : list (nat * Dict)) (key1 : nat) : option Dict :=
  match dicts with
  | nil => None
  | (k, sub_dict) :: rest =>
    if Nat.eqb k key1 then Some sub_dict else find_sub_dict rest key1
  end.

(* Fonction pour trouver une capacité par sa clé dans un sous-dictionnaire *)
Fixpoint find_ability_in_sub_dict (sub_dict : Dict) (key2 : nat) : option Ability :=
  match sub_dict with
  | nil => None
  | (k, ability) :: rest =>
    if Nat.eqb k key2 then Some ability else find_ability_in_sub_dict rest key2
  end.

(* Fonction principale pour trouver une capacité dans le dictionnaire principal *)
Definition find_ability_in_triggered_abilities (triggered_abilities : list (nat * Dict)) (pair : nat * nat) : option Ability :=
  let (key1, key2) := pair in
  match find_sub_dict triggered_abilities key1 with
  | None => None
  | Some sub_dict => find_ability_in_sub_dict sub_dict key2
  end.
 
(* Fonction pour activer une seule capacité à partir d'une clé avec des cibles *)
Fixpoint activate_ability (triggered_abilities : list (nat * Dict)) (event_type : nat) (key : nat) (targets : option (list Card)) (gs : GameState) : GameState :=
  match find_ability_in_triggered_abilities triggered_abilities (event_type, key) with
  | None => gs (* Aucune capacité trouvée, retourner l'état du jeu inchangé *)
  | Some ability =>
    let new_gs := ability targets gs in
    new_gs (* Retourner l'état du jeu mis à jour après activation de la capacité *)
  end.
(* Fonction pour activer une seule capacité à partir d'une carte avec des cibles *)
Definition activate_ability_from_card (triggered_abilities : list (nat * Dict)) (card : Card) (event_type : nat) (targets : option (list Card)) (gs : GameState) : GameState :=
  match permanent card with
  | None => gs (* Si la carte n'est pas un permanent, retourner l'état du jeu inchangé *)
  | Some perm =>
    let ability_key :=
      match event_type with
      | 1 =>
        (* Activer la première capacité OnCast *)
        match Abilities perm with
        | key :: _ => key
        | _ => 0 (* Clé par défaut si aucune capacité n'est trouvée *)
        end
      
      | _ => 0 (* Par défaut, aucune capacité *)
      end
    in
    activate_ability triggered_abilities event_type ability_key targets gs
  end.




(* Définition des différentes fonctions pour jouer un sort*)
Definition Cast (c:Card) (gs:GameState) : (GameState) :=
  let cost := c.(manacost) in
  let pool := gs.(manapool) in
  if Can_Pay cost pool && card_in_list c gs.(hand) then
    let new_pool := fold_left remove_mana cost pool in
    let new_hand := remove_card gs.(hand) c in
    let new_stack := CardItem c :: gs.(stack) in
    let new_gs := mkGameState gs.(battlefield) new_hand gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) new_pool new_stack in
    (new_gs)
  else
    (gs)
  .

(* Fonction qui gère la résolution de la stack avec capacité OnEnter *)
Definition Resolve (targets : option (list Card)) (gs : GameState) : GameState :=
  match last_option gs.(stack) with
  | Some (CardItem c) => (* Si c'est une carte *)
      match card_type c with
      | PermanentType => (* Si c'est un permanent *)
        let new_stack := remove_last gs.(stack) in
        let new_battlefield := c :: gs.(battlefield) in

        (* Ajouter la capacité OnEnter à la pile *)
        let on_enter_key :=
          match permanent c with
          | Some perm =>
            match perm.(Abilities) with
            | key :: _ => key
            | _ => 0 (* Clé par défaut si aucune capacité n'est trouvée *)
            end
          | None => 0
          end
        in
        let new_stack_with_on_enter := (PairItem on_enter_key (OnEnterDict c)) :: new_stack in

        mkGameState new_battlefield gs.(hand) gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) gs.(manapool) new_stack_with_on_enter
      | InstantType => gs (* On ne gère pas encore cette éventualité *)
      | SorceryType => gs (* On ne gère pas encore cette éventualité *)
      | UnknownType => gs (* Si on ne reconnait pas le type de la carte on ne fait rien *)
      end
  | Some (PairItem i d) => activate_ability Triggered_Abilities i d targets gs (* Si le dernier élément est une capacité, on l'active *)
  | None => gs (* Si la stack est vide, on ne fait rien *)
  end.





Definition Cast_gs : GameState := Cast destructeur Test_gs.
Compute Resolve (Some [colossal_dreadmaw]) Test_gs.


End Try_card.
Export Try_card.


