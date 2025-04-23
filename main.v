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
Require Import Coq.Arith.Arith.
Require Import proof_legendary_rule_bypass.
Import proof_legendary_rule_bypass.
Require Import proof_infinite_mana.
Import proof_infinite_mana.
Require Import proof__infinite_situation.
Import proof__infinite_situation.
Require Import proof_4_primos.
Import proof_4_primos.

Local Open Scope string_scope.





Definition can_activate_siege_zombie (gs : GameState) : bool :=
  let untapped_creatures :=
    filter (fun c => andb (is_creature c) (negb c.(tapped))) gs.(battlefield) in
  Nat.leb 3 (length untapped_creatures).

