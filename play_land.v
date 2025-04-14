From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Require Import Coq.Bool.Bool.
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
Require Import abilities_effects.
Import abilities_effects.
Require Import passive_ability.
Import passive_ability.
Require Import game_actions.
Import game_action.
Require Import Land_cards_def.
Import Land_cards.

Module Proof_play_land.

(* Instanciation du GameState initial *)
Definition initial_gamestate : GameState := 
  mkGameState
  [(colossal_dreadmaw 1)]
  [(Swamp 1); (Swamp 2)]
  nil (* La bibliothèque est vide *)
  [] (* Le cimetière est vide *)
  nil (* L'exil est vide *)
  20 (* L'opposant est à 20 PV *)
  [mkMana White 20; mkMana Blue 100; mkMana Black 20; mkMana Red 20; mkMana Green 200; mkMana Generic 200] (* On se donne assez de mana pour pouvoir lancer le sort *)
  nil (* La pile est vide *)
  DefaultListPassiveAbility  
  MainPhase1.

Definition gamestate_proof1 : GameState := Play_land (Swamp 1) initial_gamestate.

Definition gamestate_proof2 : GameState := Play_land (Swamp 2) gamestate_proof1.

Compute (tap_land (Swamp 2) gamestate_proof2).
(* Compute (update_passive_ability_in_dict initial_gamestate.(passive_abilities) LandPlayed (S (find_passive_ability_in_dict initial_gamestate.(passive_abilities) LandPlayed))). *) 
End Proof_play_land.

