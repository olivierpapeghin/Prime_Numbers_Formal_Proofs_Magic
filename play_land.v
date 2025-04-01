From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Require Import Coq.Bool.Bool.
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
Require Import Land_cards_def.
Import Land_cards.



Module Play_land.

Definition Play_land (c : Card) (gs : GameState) : GameState :=
  if card_in_list c gs.(hand) then
    let new_battlefield := c :: gs.(battlefield) in
    let new_hand := remove_card gs.(hand) c in
    let new_gs := mkGameState new_battlefield new_hand gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) gs.(manapool) gs.(stack) in
    new_gs
  else
    gs.
    

End Play_land.

Export Play_land.

Module Proof_play_land.

Import Play_land.

(* Instanciation du GameState initial *)
Definition initial_gamestate : GameState := 
  mkGameState
  nil (* Le champ de bataille est vide *)
  [Swamp 1; Swamp 2]
  nil (* La bibliothèque est vide *)
  nil (* Le cimetière est vide *)
  nil (* L'exil est vide *)
  20 (* L'opposant est à 20 PV *)
  [] 
  nil (* La pile est vide *).

Definition gamestate_proof1 : GameState := Play_land (Swamp 1) initial_gamestate.

Definition gamestate_proof2 : GameState := Play_land (Swamp 2) gamestate_proof1.

Compute tap_land (Swamp 1) (tap_land (Swamp 2) gamestate_proof2).

End Proof_play_land.

