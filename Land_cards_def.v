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

Module Land_cards.

Definition Plains (id : nat) : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    nil
    None
    nil
    None
    None
    (Some (mkLand (mkMana White 1)))
    None
    false
    false
    false))
  None
  None
  nil
  "Plains"
  id
  nil.

Definition Island (id : nat) : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    nil
    None
    nil
    None
    None
    (Some (mkLand (mkMana Blue 1)))
    None
    false
    false
    false))
  None
  None
  nil
  "Island"
  id
  nil.

Definition Forest (id : nat) : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    nil
    None
    nil
    None
    None
    (Some (mkLand (mkMana Green 1)))
    None
    false
    false
    false))
  None
  None
  nil
  "Forest"
  id
  nil.

Definition Mountain (id : nat) : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    nil
    None
    nil
    None
    None
    (Some (mkLand (mkMana Red 1)))
    None
    false
    false
    false))
  None
  None
  nil
  "Mountain"
  id
  nil.

Definition Swamp (id : nat) : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    nil
    None
    nil
    None
    None
    (Some (mkLand (mkMana Black 1)))
    None
    false
    false
    false))
  None
  None
  nil
  "Swamp"
  id
  nil.

Definition lands_gs : GameState := mkGameState [Forest 1; Forest 2; Forest 3] nil nil nil nil 20 [mkMana Green 0; mkMana Red 0; mkMana Blue 0 ;mkMana White 0 ; mkMana Black 0 ;mkMana Generic 0] nil DefaultListPassiveAbility BeginningPhase.




End Land_cards.

Export Land_cards.