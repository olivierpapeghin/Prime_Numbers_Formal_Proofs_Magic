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

Definition initial_gamestate : GameState := 
  mkGameState
  [(colossal_dreadmaw 1); (colossal_dreadmaw 2)]
  [(colossal_dreadmaw 3); (leyline_of_transformation 1)]
  nil (* La bibliothèque est vide *)
  [] (* Le cimetière est vide *)
  nil (* L'exil est vide *)
  20 (* L'opposant est à 20 PV *)
  [mkMana White 20; mkMana Blue 20; mkMana Black 20; mkMana Red 20; mkMana Green 20] (* On se donne assez de mana pour pouvoir lancer le sort *)
  nil (* La pile est vide *)
  DefaultListPassiveAbility  
  MainPhase1.
  
Compute Resolve (Cast (leyline_of_transformation 1) initial_gamestate).