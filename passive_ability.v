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
Require Import try_carte.
Import Try_card.

Module Passive_Cards.

Definition MirrorGallery (id : nat) : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    nil
    (Some NoLegendaryRule)
    nil
    None
    None
    None
    (Some mkArtifact)
    false
    false
    false))
  None
  None
  [mkMana Generic 5]
  "Mirror Gallery"
  id
  nil.

Definition BobLegend (id : nat) : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    nil
    None
    nil
    None
    None
    None
    None
    false
    true
    false))
  None
  None
  []
  "Bob"
  id
  nil.

(* État de jeu initial avec des cartes dans le battlefield *)
Definition Test_gs : GameState := mkGameState 
  [(BobLegend 1)] 
  [(BobLegend 2)] 
  nil 
  nil 
  nil 
  0 
  [] 
  nil 
  DefaultListPassiveAbility
  BeginningPhase.

(* Definition Transform_all_creature (new_type : string) (gs : GameState) : gs :=
  match
  . *)
  
Fixpoint Transform_all_creature_in (new_type : string) (l : list Card) : list Card :=
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
  end.
  

Compute Cast (BobLegend 2) Test_gs.



End Passive_Cards.

