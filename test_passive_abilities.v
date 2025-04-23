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
Require Import game_actions.
Import game_actions.
Require Import Land_cards_def.
Import Land_cards.

Definition initial_gamestate : GameState := 
  mkGameState
  []
  [(abuelos_awakening 1)]
  nil (* La bibliothèque est vide *)
  [(mirror_room_fractured_realm_locked 1)] (* Le cimetière est vide *)
  nil (* L'exil est vide *)
  20 (* L'opposant est à 20 PV *)
  [mkMana White 20; mkMana Blue 100; mkMana Black 20; mkMana Red 20; mkMana Green 200; mkMana Generic 200] (* On se donne assez de mana pour pouvoir lancer le sort *)
  nil (* La pile est vide *)
  DefaultListPassiveAbility  
  MainPhase1.

 Definition gs1 : GameState := Resolve (Cast (abuelos_awakening 1) initial_gamestate) 1 (Some [mirror_room_fractured_realm_locked 1]).

Compute gs1.

Definition gs2 : GameState := activate_ability 7 None (Some [(mkMana Generic 1)]) ( Some [(mirror_room_fractured_realm_locked 1); (mirror_room_fractured_realm_locked 1)]) (mirror_room_fractured_realm_locked 1) Dict_AA gs1.

Compute gs2.

(* Definition gs3 : GameState := activate_ability 8 None (Some [(mkMana Generic 1)]) ( Some [(mirror_room 1)]) (mirror_room 1) Dict_AA gs2.

Compute gs3.

Definition gs4 : GameState := activate_ability 7 None (Some [(mkMana Generic 1)]) ( Some [(mirror_room_fractured_realm_locked 2); (mirror_room_fractured_realm_unlocked 1)]) (mirror_room_fractured_realm_locked 2) Dict_AA gs3.

Compute gs4.

Definition gs5 : GameState := activate_ability 8 None (Some [(mkMana Generic 1)]) ( Some [(mirror_room 2)]) (mirror_room 2) Dict_AA gs4.

Compute gs5. *)
