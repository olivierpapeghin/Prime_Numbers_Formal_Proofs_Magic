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
Require Import game_actions.
Import game_action.
Require Import card_instances.
Import card_instance.

Module Passive_Cards.

(* État de jeu initial avec des cartes dans le battlefield *)
Definition Test_gs : GameState := mkGameState 
  [] 
  [(MirrorGallery 1)] 
  nil 
  nil 
  nil 
  0 
  [mkMana White 10] 
  nil 
  DefaultListPassiveAbility
  MainPhase1.

(* Definition Transform_all_creature (new_type : string) (gs : GameState) : gs :=
  match
  . *)
  
(* Fixpoint Transform_all_creature_in (new_type : string) (l : list Card) : list Card :=
  match gs.(hand) with
  | [] => gs
  | c :: rest => 
    match c.(permanent) with
    | None => Transform_all_creature_in new_type rest
    | Some perm =>
      match perm.(creature) with
      | None => Transform_all_creature_in new_type rest
      | Some creature =>
        perm.(subtype) :: new_type in
        Transform_all_creature_in new_type rest
      end
    end
  end. *)

Compute Resolve (Cast (MirrorGallery 1) Test_gs) 0.



End Passive_Cards.

