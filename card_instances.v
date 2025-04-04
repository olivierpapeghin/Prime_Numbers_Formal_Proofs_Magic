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
    ["Graou"]
    (Some (mkCreature 6 6)) (* Est une créature 6/6*)
    None (* N'est pas un enchantement *)
    None (* N'est pas un artifact *)
    None (* N'est pas une land *)
    false (* N'est pas un token *)
    false (* N'est pas tapped *)
    false)) (* N'est pas légendaire *)
  None (* N'est pas un instant *)
  None (* N'est pas un sorcery *)
  [mkMana Green 1; mkMana Generic 5] (* Coûte 5 mana générique et 1 mana vert *)
  "Colossal Dreadmaw"
  2. (* Nom de la carte *)


Definition forest_land : Land := mkLand (mkMana Green 1).
Definition forest_perm : Permanent := mkPermanent nil nil ["essai"] None None (Some forest_land) None false false false.
Definition card_forest : Card := mkCard (Some forest_perm) None None [] "Forest" 3.

(* Exemple de création d'une autre carte permanente *)
Definition creature_perm : Permanent := mkPermanent [(1,1)] nil ["pui"] (Some (mkCreature 2 2)) None None None false false false.
Definition card_creature : Card := mkCard (Some creature_perm) None None [] "Creature" 4.

Definition crea_perm : Permanent := mkPermanent nil nil ["perm"] (Some (mkCreature 2 2)) None None None false false false.
Definition destructeur : Card := mkCard (Some crea_perm) None None [] "Destructeur" 5.


(* État de jeu initial avec des cartes dans le battlefield *)
Definition Test_gs : GameState := mkGameState [card_creature;colossal_dreadmaw] [card_forest;destructeur] nil nil nil 0 [] nil.

(* Liste de cartes cibles à sacrifier *)
Definition target_cards : list Card := [card_forest].



End card_instance.
Export card_instance.