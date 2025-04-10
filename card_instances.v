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
Definition colossal_dreadmaw : Card := 
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
  2
  ["Trample"].

Definition birgi : Card := 
  mkCard 
  (Some (mkPermanent (* Est un permanent *)
    [] (* La liste des capacités déclenchées *)
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
  3
  nil.


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

Definition forest_land : Land := mkLand (mkMana Green 1).
Definition forest_perm : Permanent := mkPermanent nil nil None ["essai"] None None (Some forest_land) None false false false.
Definition card_forest : Card := mkCard (Some forest_perm) None None [] "Forest" 3 nil.

(* Exemple de création d'une autre carte permanente *)
Definition creature_perm : Permanent := mkPermanent [(1,1)] [1] None ["pui"] (Some (mkCreature 2 2)) None None None false false false.
Definition card_creature : Card := mkCard (Some creature_perm) None None [] "Creature" 4 nil.

Definition crea_perm : Permanent := mkPermanent nil nil None ["perm"] (Some (mkCreature 2 2)) None None None false false false.
Definition destructeur : Card := mkCard (Some crea_perm) None None [mkMana Red 2; mkMana Green 2; mkMana Generic 4] "Destructeur" 5 nil.


(* État de jeu initial avec des cartes dans le battlefield *)
Definition Test_gs : GameState := mkGameState [card_creature;colossal_dreadmaw] [card_forest;destructeur] nil nil nil 0 [mkMana Green 5; mkMana Red 5; mkMana Blue 5 ;mkMana White 5 ; mkMana Black 5 ; mkMana Generic 10] nil DefaultListPassiveAbility MainPhase1.



End card_instance.
Export card_instance.