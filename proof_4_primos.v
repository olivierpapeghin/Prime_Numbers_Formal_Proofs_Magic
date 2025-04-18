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
Require Import passive_ability.
Import passive_ability.
Require Import abilities_effects.
Import abilities_effects.
Require Import Land_cards_def.
Import Land_cards.
Require Import game_actions.
Import game_actions.

Local Open Scope string_scope.

(* On va prouver que l'on génère 4 tokens primos en en résolvant deux trigger de Zimone si le nombre de land est
   la première partie d'une paire de nombre premiers jumeaux *)

Lemma zimone_creates_tokens_if_conditions_met :
  forall gs,
    is_prime (count_lands gs.(battlefield)) = true ->
    land_played_this_turn gs = true ->
    zimone_ability None gs = create_token (primo 0) (count_lands gs.(battlefield)) gs.
