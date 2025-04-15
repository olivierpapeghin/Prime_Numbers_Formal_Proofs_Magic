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

Definition abuelos_awakening (id : nat) : Card :=
mkCard
  None
  None
  (Some (mkSorcery [1]))
  [mkMana White 1; mkMana Generic 2]
  "Abuelo's Awakening"
  id
  nil.

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
    (Some (mkArtifact None))
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
    (Some (mkEnchantement None))
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

Definition leyline_of_anticipation (id : nat) : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    nil
    (Some AllFlash)
    nil
    None
    (Some (mkEnchantement None))
    None
    None
    false
    false
    false))
  None
  None
  [(mkMana Blue 2); (mkMana Generic 2) ]
  "Leyline of Anticipation"
  id
  nil.

Definition life_and_limb (id : nat) : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    nil
    (Some SaprolingsLands)
    nil
    None
    (Some (mkEnchantement None))
    None
    None
    false
    false
    false))
  None
  None
  [(mkMana Green 1); (mkMana Generic 3) ]
  "Life and Limb"
  id
  nil.
  
Definition fractured_realm (id : nat) : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    nil
    (Some AdditionalTrigger)
    nil
    None
    (Some (mkEnchantement None))
    None
    None
    false
    false
    false))
  None
  None
  [(mkMana Blue 2); (mkMana Generic 5) ]
  "Fractured Realm"
  id
  nil.
  
Definition parallel_lives (id : nat) : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    nil
    (Some DoubleToken)
    nil
    None
    (Some (mkEnchantement None))
    None
    None
    false
    false
    false))
  None
  None
  [(mkMana Blue 2); (mkMana Generic 5) ]
  "Parallel Lives"
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

Definition clock_of_omens (id : nat) : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    [2]
    None
    nil
    None
    None
    None
    (Some (mkArtifact None))
    false
    false
    false))
  None
  None
  [(mkMana Generic 4)]
  "Clock of Omens"
  id
  nil.

Definition narsets_reversal (id : nat) : Card :=
  mkCard
    None 
    (Some (mkInstant [2]))
    None
    [(mkMana Blue 2)]
    "Narset's Reversal"
    id
    nil.

Definition molten_duplication (id : nat) : Card :=
  mkCard
  None
  None
  (Some (mkSorcery[3]))
  [(mkMana Red 1)]
  "Molten Duplication"
  id
  nil.

Definition sanctum_weaver (id : nat) : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    [3]
    None
    ["Dryad"]
    (Some (mkCreature 0 2))
    (Some (mkEnchantement None))
    None
    None
    false
    false
    false))
  None
  None
  [(mkMana Green 1);(mkMana Generic 1) ]
  "Sanctum Weaver"
  id
  nil.

Definition freed_from_the_realm (id : nat) (id_card : nat) (card_name : string) : Card :=
  mkCard 
  (Some (mkPermanent
    nil
    [4;5]
    None
    nil
    None
    (Some (mkEnchantement (Some (card_name, id_card))))
    None
    None
    false
    false
    false))
  None
  None
  [(mkMana Blue 1);(mkMana Generic 2) ]
  "Freed from the realm"
  id
  nil.

Definition isochron_scepter (id: nat) : Card :=
  mkCard
  (Some (mkPermanent
  [(4,1)]
  [6]
  None
  nil
  None
  None
  None
  (Some (mkArtifact ( None)))
  false
  false
  false))
  None
  None
  [ (mkMana Generic 2)]
  "Isochron Scepter"
  id
  ["Imprint"].
Definition zimone (id : nat) : Card := 
  mkCard 
  (Some (mkPermanent (* Est un permanent *)
    [(2,2)] (* La liste des capacités déclenchées *)
    nil
    None
    ["Human Wizard"]
    (Some (mkCreature 1 1)) (* Est une créature 6/6*)
    None (* N'est pas un enchantement *)
    None (* N'est pas un artifact *)
    None (* N'est pas une land *)
    false (* N'est pas un token *)
    true (* Est légendaire *)
    false)) (* N'est pas tapped *)
  None (* N'est pas un instant *)
  None (* N'est pas un sorcery *)
  [mkMana Green 1; mkMana Generic 1; mkMana Blue 1]
  "Zimone, All-Questioning"
  id
  nil.

Definition primo (id : nat) : Card := 
  mkCard 
  (Some (mkPermanent (* Est un permanent *)
    nil (* La liste des capacités déclenchées *)
    nil
    None
    ["Fractal"]
    (Some (mkCreature 0 0)) (* Est une créature 6/6*)
    None (* N'est pas un enchantement *)
    None (* N'est pas un artifact *)
    None (* N'est pas une land *)
    true (* Est un token *)
    false (* N'est pas légendaire *)
    false)) (* N'est pas tapped *)
  None (* N'est pas un instant *)
  None (* N'est pas un sorcery *)
  []
  "Primo, The Indivisible"
  id
  nil.


End card_instance.
Export card_instance.