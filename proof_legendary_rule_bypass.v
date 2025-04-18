From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Require Import Coq.Bool.Bool.
Require Import List String.
Require Import String.
Require Import List.
Import ListNotations.
Require Import type_definitions.
Import type_definition.
Require Import utility_functions.
Import utility_function.
Require Import card_instances.
Import card_instance.
Require Import passive_ability.
Import passive_ability.
Require Import abilities_effects.
Import abilities_effects.
Require Import Land_cards_def.
Import Land_cards.
Require Import game_actions.
Import game_actions.
Require Import Coq.Arith.Arith.

Local Open Scope string_scope.

(* Prédicat qui dit si une carte donnée est primo et légendaire ou non *)
Definition is_primo_legendary (c : Card) : bool :=
  andb (String.eqb c.(name) "Primo, The Indivisible")
       (match c.(permanent) with
        | Some p => p.(legendary)
        | None => false
        end).


(* Fonction qui compte le nombre de primos dans une liste *)
Definition count_primos (l : list Card) : nat :=
  length (filter is_primo_legendary l).


(* On va prouver que tant que la mirror_gallery est présente on peut accumuler au moins deux tokens primos 
   en même temps sur le champ de bataille *)
Definition initial_state : GameState :=
  mkGameState
    [mirror_gallery 1; Plains 1; Island 1; Island 2; Swamp 1] (* On ajoute un nombre premier -1 land *)
    [Forest 1] (* Plus une land en main pour la jouer *)
    []
    []
    []
    20
    (* On s'affranchit de la contrainte de mana qui ne nous intéresse pas ici *)
    [mkMana White 100;mkMana Blue 100; mkMana Black 100; mkMana Red 100; mkMana Green 100; mkMana Generic 100]
    [PairItem 2 2;PairItem 2 2] (* On met 2 triggers de Zimone sur la pile pour créer 2 tokens primos *)
    [(NoLegendaryRule, 1);(LandPlayed, 0)] (* La mirror gallery est sur le champ de bataille, donc son abilité passive est active *)
    MainPhase1.

(* On ajoute la forêt qui va permettre aux triggers de Zimone de créer des primos *)
Definition gs_forest := Play_land (Forest 1) initial_state. 

(* On résout les deux triggers de Zimone avec toutes les conditions réunies pour créer deux token primos légendaires *)
Definition gs_primos := Resolve (Resolve gs_forest 0 None) 0 None.

Compute gs_primos.

(* L'objectif est de prouver qu'on peut bypass la règle légendaire quand la mirror gallery est sur le champ de bataille *)
(* Pour ce théorème on va admettre que les fonctions Resolve et check_legendary_rule fonctionnent 
   comme prévu *)
Theorem two_primos_with_mirror_gallery :
    Nat.leb 2 (count_primos gs_primos.(battlefield)) = true.
Proof.
  simpl. reflexivity.
Qed.

