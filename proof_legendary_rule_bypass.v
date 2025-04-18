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

(* Prédicat qui dit si une carte donnée est légendaire ou non *)
Definition is_legendary (c: Card) : bool :=
  match c.(permanent) with
  | None => false
  | Some perm =>
    if perm.(legendary) then
      true
    else 
      false
  end.

(* Prédicat qui dit si la mirror gallery est en jeu *)
Definition is_mirror_gallery_on_bf (bf : list Card) : Prop :=
  exists c, In c bf /\ name c = "Mirror Gallery".

(* On définit les deux permanents légendaires qu'on utilise dans notre preuve, ici on prend Zimone arbitrairement *)
Definition legendary_card1 := Zimone 1.
Definition legendary_card2 := Zimone 2.

Definition gs1 := Resolve (Cast gs_with_mirror legendary_card1).
Definition gs2 := Resolve (Cast gs1 legendary_card2).


(* L'objectif est de prouver qu'on peut bypass la règle légendaire quand la mirror gallery est sur le champ de bataille *)
Theorem mirror_gallery_disables_legend_rule :
  forall gs card1 card2,
    card1.(name) = card2.(name) ->
    card1.(id) <> card2.(id) ->
    is_legendary card1 = true ->
    is_legendary card2 = true ->
    find_passive_ability_in_dict gs.(passive_abilities) NoLegendaryRule <> 0 ->
    is_mirror_gallery_on_bf gs.(battlefield) ->
    let gs1 := Resolve (Cast card1 gs) 0 None in
    let gs2 := Resolve (Cast card2 gs1) 0 None in
    In card1 gs2.(battlefield) /\ In card2 gs2.(battlefield).

