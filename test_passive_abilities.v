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

Definition initial_gamestate : GameState := 
  mkGameState
  [(colossal_dreadmaw 1)]
  [(colossal_dreadmaw 3);(birgi 1); (leyline_of_transformation 1); (life_and_limb 1); (fractured_realm 1); (fractured_realm 2); (fractured_realm 3)]
  nil (* La bibliothèque est vide *)
  [] (* Le cimetière est vide *)
  nil (* L'exil est vide *)
  20 (* L'opposant est à 20 PV *)
  [mkMana White 20; mkMana Blue 100; mkMana Black 20; mkMana Red 20; mkMana Green 200; mkMana Generic 200] (* On se donne assez de mana pour pouvoir lancer le sort *)
  nil (* La pile est vide *)
  DefaultListPassiveAbility  
  MainPhase1.

(* Definition gs2 : GameState := Resolve (Cast (leyline_of_transformation 1) initial_gamestate) 0 None.

Definition gs3 : GameState := Resolve (Cast (life_and_limb 1) gs2) 0 None.
Compute Resolve (Cast (colossal_dreadmaw 3) gs3) 0 None.
 *)

(* Definition gs2 : GameState := Resolve (Cast (fractured_realm 1) initial_gamestate) 0 None.
Definition gs3 : GameState := Resolve (Cast (fractured_realm 2) gs2) 0 None.
Definition gs4 : GameState := Resolve (Cast (fractured_realm 3) gs3) 0 None. *)
Definition gs5 : GameState := Resolve (Cast (birgi 1) initial_gamestate) 0 None.
Compute  Resolve (Resolve (Cast (colossal_dreadmaw 3) gs5) 0 None) 0 None.
(* Compute Resolve (Resolve (Resolve (Resolve (Cast (colossal_dreadmaw 3) gs5) 0 None) 0 None) 0 None). *)



