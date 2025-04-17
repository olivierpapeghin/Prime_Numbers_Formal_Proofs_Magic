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
Import game_actions.
Require Import Land_cards_def.
Import Land_cards.

Definition initial_gamestate : GameState := 
  mkGameState
  []
  [(abuelos_awakening 1)]
  nil (* La bibliothèque est vide *)
  [(mirror_room 1)] (* Le cimetière est vide *)
  nil (* L'exil est vide *)
  20 (* L'opposant est à 20 PV *)
  [mkMana White 20; mkMana Blue 100; mkMana Black 20; mkMana Red 20; mkMana Green 200; mkMana Generic 200] (* On se donne assez de mana pour pouvoir lancer le sort *)
  nil (* La pile est vide *)
  DefaultListPassiveAbility  
  MainPhase1.

Definition gs2 : GameState := Resolve (Cast (abuelos_awakening 1) initial_gamestate) 1 (Some [mirror_room 1]).
(* Compute  Resolve (Resolve (Cast (colossal_dreadmaw 3) gs5) 0 None) 0 None. *)
Compute activate_triggered_ability Triggered_Abilities 4 2 (Some [(mirror_room 1)]) gs2.
Compute get_base_card (mirror_room 1) 99.

