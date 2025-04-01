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

Module Passive_Cards.

Definition add_black_mana (targets : option (list Card)) (gs : GameState) : GameState :=
  let new_manapool := (mkMana Black 1) :: gs.(manapool) in
  mkGameState gs.(battlefield) gs.(hand) gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) new_manapool gs.(stack).

Record Entry := {
  index : nat;
  def : string;
  flag : bool
}.

Definition ListPassiveAbility : List := [(1, add_black_mana, false)].

End Passive_Cards.

