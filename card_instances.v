From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Program.Equality.
Require Import List String.
Local Open Scope string_scope.
Require Import String.
Require Import List.
Import ListNotations.
Require Import type_definitions.
Import type_definition.
Require Import utility_functions.
Import utility_function.
Module card_instance.

(* Instanciation de la carte *)
Definition colossal_dreadmaw (id : nat) : Card := 
  mkCard 
  (Some (mkPermanent (* Est un permanent *)
    nil
    nil
    None
    ["Dinosaur"]
    (Some (mkCreature 6 6)) (* Est une créature 6/6*)
    None (* N'est pas un enchantement *)
    None (* N'est pas un artifact *)
    None (* N'est pas une land *)
    false (* N'est pas un token *)
    false (* N'est pas tapped *)
    false)) (* N'est pas légendaire *)
  None (* N'est pas un instant *)
  None (* N'est pas un sorcery *)
  [mkMana Green 1; mkMana Generic 5]
  "Colossal Dreadmaw"
  id
  ["Trample"].

Definition birgi (id : nat) : Card := 
  mkCard 
  (Some (mkPermanent (* Est un permanent *)
    [(1,1)] (* La liste des capacités déclenchées *)
    nil
    None
    ["God"]
    (Some (mkCreature 3 3)) (* Est une créature 6/6*)
    None (* N'est pas un enchantement *)
    None (* N'est pas un artifact *)
    None (* N'est pas une land *)
    false (* N'est pas un token *)
    true (* Est légendaire *)
    false)) (* N'est pas tapped *)
  None (* N'est pas un instant *)
  None (* N'est pas un sorcery *)
  [mkMana Red 1; mkMana Generic 2]
  "Birgi, God of Storytelling"
  id
  nil.

Definition siege_zombie (id : nat): Card :=
  mkCard 
  (Some (mkPermanent
    nil
    [1]
    None
    ["Zombie"]
    (Some (mkCreature 2 2))
    None
    None
    None
    false
    false
    false))
  None
  None
  [mkMana Black 1; mkMana Generic 1 ]
  "Siege Zombie"
  id
  nil.

Definition mirror_gallery (id : nat) : Card :=
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
  
Definition leyline_of_transformation (id : nat) : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    nil
    (Some AllSaprolings)
    nil
    None
    (Some mkEnchantement)
    None
    None
    false
    false
    false))
  None
  None
  [(mkMana Blue 2); (mkMana Generic 2) ]
  "Leyline of Transformation"
  id
  nil.

Definition desecration_elemental (id : nat) : Card :=
  mkCard 
  (Some (mkPermanent
    [(1,2)]
    nil
    None
    nil
    (Some (mkCreature 8 8))
    None
    None
    None
    false
    false
    false))
  None
  None
  [(mkMana Black 1); (mkMana Generic 3) ]
  "Desecreation Elemental"
  id
  ["Fear"].


End card_instance.
Export card_instance.