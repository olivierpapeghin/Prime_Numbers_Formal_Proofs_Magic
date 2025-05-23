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

Module proof__infinite_situation.

(* Darksteel Citadel *)
Definition darksteel : Card := Darksteel_citadel 5.

(* Clock of Omens *)
Definition clock : Card := clock_of_omens 1.

(* Parallel Lives *)
Definition parallel : Card := parallel_lives 2.

(* Narset's Reversal *)
Definition narset : Card := narsets_reversal 3.

(* Molten Duplication *)
Definition molten : Card := molten_duplication 6.

(* Isochron Scepter avec imprint de Narset's Reversal *)
Definition isochron_card : Card :=
  let base := isochron_scepter 4 in
  match base.(permanent) with
  | Some p =>
      let new_art := Some {| isochron := Some (mkInstant [2]) |} in
      let new_perm := mkPermanent
        p.(Abilities)
        p.(ListActivated)
        p.(PassiveAbility)
        p.(subtype)
        p.(creature)
        p.(enchantement)
        p.(land)
        new_art
        p.(token)
        p.(legendary)
        p.(tapped)
      in
      mkCard
        (Some new_perm)
        base.(instant)
        base.(sorcery)
        base.(manacost)
        base.(name)
        base.(id)
        base.(keywords)
  | None => base
  end.

Definition test_state : GameState :=
  mkGameState
    [clock; parallel; isochron_card; darksteel]
    [molten]
    [] (* library *)
    [] (* graveyard *)
    [] (* exile *)
    20 (* opponent life *)
    [mkMana Blue 5; mkMana Red 5; mkMana Generic 10]
    [] (* stack *)
    [(DoubleToken, 1)]
    MainPhase1.

Definition after_duplication :=
  Cast molten test_state.



Definition after_isochron_activation : GameState :=
  isochron_scepter_ability
    (Some [isochron_card])
    (Some [isochron_card])
    (Some [mkMana Generic 2])
    after_duplication.

(* Trouver deux tokens artefacts non engagés *)
Definition find_untapped_artifact_tokens (gs : GameState) : list Card :=
  filter (fun c =>
    match c.(permanent) with
    | Some p =>
        isSome p.(artifact) &&
        negb p.(tapped) &&
        p.(token)
    | None => false
    end) gs.(battlefield).

Definition after_first_resolve : GameState :=
  Resolve after_isochron_activation 2 (Some([molten])).

Definition after_second_resolve : GameState :=
  Resolve after_first_resolve 3 (Some([darksteel])).

Definition after_clock_activation : GameState :=
  let candidates := find_untapped_artifact_tokens after_second_resolve in
  match candidates with
  | a :: b :: _ =>
      clock_of_omens_ability
        (Some [a; b])         (* coût : deux artefacts non engagés *)
        (Some [isochron_card]) (* cible à dégager : Isochron Scepter *)
        None
        after_second_resolve
  | _ => after_second_resolve (* pas assez de tokens disponibles *)
  end.

Definition state_eq_ignoring_mana_graveyard (s1 s2 : GameState) : Prop :=
  s1.(hand) = s2.(hand) /\
  s1.(library) = s2.(library) /\
  s1.(exile) = s2.(exile) /\
  s1.(opponent) = s2.(opponent) /\
  s1.(stack) = s2.(stack) /\
  s1.(passive_abilities) = s2.(passive_abilities) /\
  s1.(phase) = s2.(phase).

Definition count_darksteel (battlefield : list Card) : nat :=
  count_occ string String.eqb (map (fun c => c.(name)) battlefield) "Darksteel Citadel".

Theorem combo_preserves_state_with_two_darksteel_more :
  state_eq_ignoring_mana_graveyard test_state after_clock_activation /\
  count_darksteel after_clock_activation.(battlefield) = count_darksteel test_state.(battlefield) + 2.

Proof.
  split.
  - repeat split; reflexivity.
  - simpl. (* Ou unfold si nécessaire *)
    (* Ex: count_darksteel end_state.(battlefield) = ... *)
    reflexivity.
Qed.

Definition add_darksteel_citadel_pair (gs : GameState) : GameState :=
  let gs1 := Cast (molten_duplication 1) gs in
  let gs2 := isochron_scepter_ability (Some [isochron_card]) (Some [isochron_card]) None gs1 in
  let gs3 := Resolve gs2 2 (Some [molten_duplication 1]) in
  let gs4 := Resolve gs3 3 (Some [Darksteel_citadel 1]) in
  match find_untapped_artifact_tokens gs4 with
  | a :: b :: _ =>
      clock_of_omens_ability
        (Some [a; b])           (* coût : deux artefacts non engagés *)
        (Some [isochron_card]) (* cible à dégager : Isochron Scepter *)
        None
        gs4
  | _ => gs4
  end.


Inductive step_add_citadels : GameState -> GameState -> Prop :=
| add_citadels_step :
    forall gs gs1,
      add_darksteel_citadel_pair gs = gs1 ->
      step_add_citadels gs gs1.

CoInductive can_loop_infinitely_citadels : GameState -> Prop :=
| loop_step :
    forall gs gs',
      step_add_citadels gs gs' ->
      can_loop_infinitely_citadels gs' ->
      can_loop_infinitely_citadels gs.

CoFixpoint infinite_darksteel_citadels (gs : GameState) : can_loop_infinitely_citadels gs :=
  let gs1 := add_darksteel_citadel_pair gs in
  loop_step gs gs1 (add_citadels_step gs gs1 eq_refl) (infinite_darksteel_citadels gs1).

Theorem infinite_darksteel_citadels_possible :
  can_loop_infinitely_citadels test_state.
Proof.
  exact (infinite_darksteel_citadels test_state).
Qed.

Inductive reachable_via_land_modification : GameState -> GameState -> Prop :=
| rv_refl :
    forall gs,
      reachable_via_land_modification gs gs
| rv_add_darksteel_pair :
    forall gs gs' gs'',
      add_darksteel_citadel_pair gs = gs' ->
      reachable_via_land_modification gs' gs'' ->
      reachable_via_land_modification gs gs''.

Definition is_twin_prime_land_count (gs : GameState) : Prop :=
  let n := count_lands gs.(battlefield) in
  is_prime n = true /\ is_prime (n + 2) = true.

Definition can_reach_twin_prime_land_count (gs : GameState) : Prop :=
  exists gs', reachable_via_land_modification gs gs' /\ is_twin_prime_land_count gs'.


End proof__infinite_situation.
Export proof__infinite_situation.
