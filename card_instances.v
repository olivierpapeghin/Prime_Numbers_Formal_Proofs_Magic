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
Module card_instance.



Definition forest_land : Land := mkLand (mkMana Green 1).
Definition forest_perm : Permanent := mkPermanent [1] nil nil nil None None (Some forest_land) None false false false.
Definition card_forest : Card := mkCard (Some forest_perm) None None [] "Forest".

(* Exemple de création d'une autre carte permanente *)
Definition creature_perm : Permanent := mkPermanent [1] nil nil nil (Some (mkCreature 2 2)) None None None false false false.
Definition card_creature : Card := mkCard (Some creature_perm) None None [] "Creature".

(* État de jeu initial avec des cartes dans le battlefield *)
Definition Test_gs : GameState := mkGameState [card_creature] [card_forest] nil nil nil 0 [] nil.

(* Liste de cartes cibles à sacrifier *)
Definition target_cards : list Card := [card_forest].


End card_instance.
Export card_instance.