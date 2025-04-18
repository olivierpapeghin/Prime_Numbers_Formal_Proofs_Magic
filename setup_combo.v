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
Require Import Land_cards_def.
Import Land_cards.
Require Import game_actions.
Import game_actions.

Local Open Scope string_scope.

Module setup_combo.
(* On va effectuer les premières étapes du combo et les stocker dans des variables différentes à chaque fois pour pouvoir les
   réuitliser par la suite *)

Definition initial_gamestate : GameState := mkGameState
  [leyline_of_anticipation 1;leyline_of_transformation 1; Darksteel_citadel 1;
    Plains 1;Island 1; Swamp 1; Mountain 1] (* Les deux leylines sont en jeu et un nombre premier de land dont la Darksteel citadel*)
  [sanctum_weaver 1; freed_from_the_realm 1 1 "Sanctum Weaver"; abuelos_awakening 1;
   birgi 1; zimone 1; myrkul 1; siege_zombie 1; desecration_elemental 1;
   mirror_gallery 1; clock_of_omens 1; parallel_lives 1; life_and_limb 1;
   isochron_scepter 1; narsets_reversal 1; molten_duplication 1] (* On met toutes les cartes nécessaires en main *)
  nil
  [mirror_room_fractured_realm_locked 1]
  nil
  20
  [mkMana White 0; mkMana Blue 1; mkMana Black 0; mkMana Red 0; mkMana Green 1; mkMana Generic 3] (* On se donne pile assez de mana pour faire du mana infini *)
  nil
  [(AllSaprolings, 1); (AllFlash, 1); (DoubleToken, 0); (AdditionalTrigger, 0); (NoLegendaryRule, 0);(SaprolingsLands, 0); (LandPlayed, 1)]
  MainPhase2.

Definition gs_sanctum_weaver := Resolve (Cast (freed_from_the_realm 1 1 "Sanctum Weaver") (Resolve (Cast (sanctum_weaver 1) initial_gamestate) 0 None)) 0 None.

(* Nous pouvons désormais faire du mana à l'infini, pour voir la preuve, checker le fichier proof_infinite_mana *)
(* On génère donc une quantité arbitrairement grande de mana pour s'affranchir de cette contrainte pour la suite *)
Definition gs_sanctum_weaver_infinite := add_mana (add_mana (add_mana (add_mana (add_mana (add_mana gs_sanctum_weaver White 1000) Blue 1000) Black 1000) Red 1000) Green 1000) Generic 1000.


Definition gs_mirror_room := Resolve (Cast (abuelos_awakening 1) gs_sanctum_weaver_infinite) 1 (Some [mirror_room_fractured_realm_locked 1]).

(* On peut désormais avoir une infinité de mirror_room et donc de débloquer une infinité de fractured_realm 
   pour avoir une infinité de copie de chaque triggered ability.
   La preuve est disponnible dans le fichier proof_infinite_mirror_room *)

(* Ici on va faire 5 copies *)


End setup_combo.
Export setup_combo.
