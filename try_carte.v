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
Definition sacrifice_cards_ability_function (targets : option (list Card)) (gs : GameState) : GameState :=
  match targets with
  | None => gs (* Si aucune cible n'est fournie, retourner l'état du jeu inchangé *)
  | Some target_cards =>
    fold_left
      (fun new_gs target =>
        match target.(permanent) with
        | None => new_gs (* Si la carte n'est pas un permanent, ne rien faire *)
        | Some target_perm =>
          let new_battlefield := remove_card_from_hand new_gs.(battlefield) target in
          let new_graveyard := target :: new_gs.(graveyard) in
          mkGameState new_battlefield new_gs.(hand) new_gs.(library) new_graveyard new_gs.(exile)
                        new_gs.(opponent) new_gs.(manapool) new_gs.(stack)
        end)
      target_cards
      gs
  end.



(* Définition des sous-dictionnaires *)
Definition OnCast : Dict := [(1, sacrifice_cards_ability_function)].
Definition OnPhase : Dict := nil.
Definition OnDeath : Dict := nil.


(* Définition du dictionnaire principal avec des clés de type string *)
Definition Triggered_Abilities : list (nat * Dict) :=
  ( 1 , OnCast) :: (2 , OnPhase) :: (3 , OnDeath) :: nil.

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


(* Fonction pour activer les capacités à partir d'une liste de clés avec des cibles *)
Fixpoint activate_abilities_from_list_with_targets (triggered_abilities : list (nat * Dict)) (event_type : nat) (keys : list nat) (targets : option (list Card)) (gs : GameState) : GameState :=
  match keys with
  | [] => gs
  | key :: rest =>
    match find_ability_in_triggered_abilities triggered_abilities (event_type, key) with
    | None => activate_abilities_from_list_with_targets triggered_abilities event_type rest targets gs
    | Some ability =>
      let new_gs := ability targets gs in
      activate_abilities_from_list_with_targets triggered_abilities event_type rest targets new_gs
    end
  end.

(* Fonction générique pour activer une capacité à partir d'une carte avec des cibles *)
Definition activate_ability_from_card_with_targets (triggered_abilities : list (nat * Dict)) (card : Card) (event_type : nat) (targets : option (list Card)) (gs : GameState) : GameState :=
  match card.(permanent) with
  | None => gs (* Si la carte n'est pas un permanent, retourner l'état du jeu inchangé *)
  | Some perm =>
    let ability_keys :=
      match event_type with
      | 1 => perm.(ListOnCast)
      | 2 => perm.(ListOnPhase)
      | 3 => perm.(ListOnDeath)
      | _ => [] (* Par défaut, aucune capacité *)
      end
    in
    activate_abilities_from_list_with_targets triggered_abilities event_type ability_keys targets gs
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



Compute Test_gs.
Compute tap_land card_forest Test_gs. 

End Try_card.
Export Try_card.


