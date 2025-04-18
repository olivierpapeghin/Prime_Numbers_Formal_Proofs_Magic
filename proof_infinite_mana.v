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
Require Import setup_combo.
Import setup_combo.

Local Open Scope string_scope.

(* L'objectif est de prouver qu'on peut générer une infinité de mana avec les deux cartes
  Sanctum Weaver et Freed From the Realm (une aura attachée au Sanctum Weaver) *)

(* On définit l'étape qu'on doit répéter indéfiniment, ici tapper le Sanctum Weaver pour du mana
  et le détaper avec un mana bleu grace à Freed From the Realm *)
Inductive step : GameState -> GameState -> Prop :=
| step_mana :
    forall gs gs1 gs2 card,
      sanctum_weaver_ability (Some [card]) None None gs = gs1 ->
      freed_from_the_realm_ability_2 (Some [card]) None None gs1 = gs2 ->
      step gs gs2.

(* On peut maintenant définir la boucle infinie *)
CoInductive can_loop_infinitely : GameState -> Prop :=
| loop_step :
    forall gs gs',
      step gs gs' ->
      can_loop_infinitely gs' ->
      can_loop_infinitely gs.

(* On définit une proposition récursive qui va vérifier qu'on peut générer du mana infini *)
CoFixpoint infinite_loop (gs : GameState) : can_loop_infinitely gs :=
  let card := sanctum_weaver 1 in
  let gs1 := sanctum_weaver_ability (Some [card]) None None gs in
  let gs2 := freed_from_the_realm_ability_2 (Some [card]) None None gs1 in
  loop_step gs gs2 (step_mana gs gs1 gs2 card eq_refl eq_refl) (infinite_loop gs2).

(* Il ne reste plus qu'à savoir si l'état initial défini plus haut peut boucler à l'infini *)
Theorem infinite_blue_mana_possible :
  can_loop_infinitely gs_sanctum_weaver.
Proof.
  exact (infinite_loop gs_sanctum_weaver).
Qed.



