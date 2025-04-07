From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Program.Equality.
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

Module game_action.




Definition Cast (c:Card) (gs:GameState) : GameState :=
  let cost := c.(manacost) in
  let pool := gs.(manapool) in
  let current_phase := gs.(phase) in
  if Can_Pay cost pool && card_in_list c gs.(hand) && check_legendary_rule gs c && can_cast c current_phase then
    let new_pool := fold_left remove_mana cost pool in
    let new_hand := remove_card gs.(hand) c in
    let new_stack := CardItem c :: gs.(stack) in
    let intermediate_gs := mkGameState gs.(battlefield) new_hand gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) new_pool new_stack gs.(passive_abilities) gs.(phase) in
    (* Ajouter les abilities des permanents sur le battlefield au stack *)
    let final_gs := fold_left (fun gs' perm =>
      match perm.(permanent) with
      | Some perm_data => add_abilities_to_stack 1 perm_data gs'
      | None => gs'
      end
    )  gs.(battlefield) intermediate_gs in
    final_gs
  else
    gs.



End game_action.
Export game_action.