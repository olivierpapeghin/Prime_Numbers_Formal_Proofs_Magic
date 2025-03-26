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
Require Import try_carte.
Import Try_card. (* Assurez-vous que votre module est bien nommé TryCarte *)

Module Land_cards.

Definition plains_land : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    nil
    nil
    None
    None
    (Some (mkLand Plain))
    None
    false
    false
    false))
  None
  None
  nil
  "Plains".

Definition island_land : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    nil
    nil
    None
    None
    (Some (mkLand Ocean))
    None
    false
    false
    false))
  None
  None
  nil
  "Island".

Definition forest_land : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    nil
    nil
    None
    None
    (Some (mkLand Forest))
    None
    false
    false
    false))
  None
  None
  nil
  "Forest".

Definition Mountain_land : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    nil
    nil
    None
    None
    (Some (mkLand Mountain))
    None
    false
    false
    false))
  None
  None
  nil
  "Mountain".

Definition Swamp_land : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    nil
    nil
    None
    None
    (Some (mkLand Swamp))
    None
    false
    false
    false))
  None
  None
  nil
  "Swamp".

End Land_cards.

Export Land_cards.