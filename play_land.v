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

Fixpoint add_mana (pool : list Mana) (new_mana : Mana) : list Mana :=
  match pool with
  | [] => [new_mana] (* Si le pool est vide, on ajoute simplement le nouveau mana *)
  | h :: t =>
      if eq_mana_color h.(color) new_mana.(color) then
        (* Si c'est le même type de mana, on additionne les quantités *)
        {| color := h.(color); quantity := h.(quantity) + new_mana.(quantity) |} :: t
      else
        (* Sinon, on garde l'élément et on continue *)
        h :: add_mana t new_mana
  end.

Definition Play_land (c : Card) (gs : GameState) : GameState :=
  if mem_card c gs.(hand) then
    let new_battlefield := c :: gs.(battlefield) in
    let new_hand := remove_card_from_hand gs.(hand) c in
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
  [Swamp_land]
  nil (* La bibliothèque est vide *)
  nil (* Le cimetière est vide *)
  nil (* L'exil est vide *)
  20 (* L'opposant est à 20 PV *)
  [] 
  nil (* La pile est vide *).

Definition gamestate_proof1 : GameState := Play_land Swamp_land initial_gamestate.

Compute gamestate_proof1.

End Proof_play_land.

