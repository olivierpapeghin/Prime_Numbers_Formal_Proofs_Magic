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
Require Import abilities_effects.
Import abilities_effects.
Require Import Land_cards_def.
Import Land_cards.
Require Import game_actions.
Import game_actions.

Local Open Scope string_scope.

(* On va prouver que l'on génère 4 tokens primos en en résolvant deux trigger de Zimone si le nombre de land est
   la première partie d'une paire de nombre premiers jumeaux, et que ainsi on peut faire 1 dégât à l'opposant avec 
   l'abilité du siege zombie *)

(* Le setup est celui du combo *)
Definition initial_gamestate : GameState := mkGameState
  [leyline_of_anticipation 1;leyline_of_transformation 1; Darksteel_citadel 1;
    Plains 1;Island 1; Swamp 1; Mountain 1; parallel_lives 1; life_and_limb 1;
    zimone 1;siege_zombie 1; mirror_gallery 1; mirror_room_fractured_realm_unlocked 1]
  nil
  nil
  nil
  nil
  20
  [] (* Pas besoin de Mana ici*)
  nil
  [(AllSaprolings, 1); (AllFlash, 1); (DoubleToken, 1); (AdditionalTrigger, 1); (NoLegendaryRule, 1);(SaprolingsLands, 1); (LandPlayed, 1)]
  MainPhase2.

Definition gs1 := advance_phase initial_gamestate.

Definition gs2 := Resolve (Resolve gs1 0 None) 0 None.

Definition gs3 := activate_ability 1 (Some [primo 1; primo 2; primo 3]) None None (siege_zombie 1) Dict_AA gs2.

(* Maintenant nous allons prouver ce qu'on vient de faire *)

Definition is_zimone_trigger (cop : CardOrPair) : bool :=
  match cop with
  | CardItem _ => false
  | PairItem a b =>
    if Nat.eqb a 2 && Nat.eqb b 2 then true else false
  end.

Definition count_zimone_triggers (l : list CardOrPair) : nat :=
  length (filter is_zimone_trigger l).

(* On vérifie qu'il y a bien 2 triggers de Zimone sur la stack au passage à l'endstep *)
Theorem two_zimone_triggers : 
  Nat.eqb 2 (count_zimone_triggers gs1.(stack)) = true.
Proof.
  simpl. reflexivity.
Qed.

(* Prédicat qui dit si une carte donnée est primo ou non *)
Definition is_primo (c : Card) : bool :=
  String.eqb c.(name) "Primo, The Indivisible".

(* Fonction qui compte le nombre de primos dans une liste *)
Definition count_primos (l : list Card) : nat :=
  length (filter is_primo l).

(* On vérifie qu'il y a bien 4 primos sur le champ de bataille *)
Theorem four_primos_on_battlefield : 
  Nat.eqb 4 (count_primos gs2.(battlefield)) = true.
Proof.
  simpl. reflexivity.
Qed.

Theorem one_damage_dealt :
  Nat.eqb gs2.(opponent) (gs3.(opponent)+1) = true.
Proof.
  simpl. reflexivity.
Qed.

