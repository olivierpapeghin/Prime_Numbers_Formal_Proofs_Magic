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

Module proof_4_primos.
(* On va prouver que l'on génère 4 tokens primos en en résolvant deux trigger de Zimone si le nombre de land est
   la première partie d'une paire de nombre premiers jumeaux, et que ainsi on peut faire 1 dégât à l'opposant avec 
   l'abilité du siege zombie *)

(* Le setup est celui du combo *)
Definition gs : GameState := mkGameState
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

Definition gs1 := advance_phase gs.

Definition gs2 := Resolve (Resolve gs1 0 None) 0 None.

Compute gs2.

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


(* Prédicat qui dit si une carte donnée est primo ou non *)
Definition is_primo_and_land (c : Card) : bool :=
  andb (String.eqb c.(name) "Primo, The Indivisible")
  (match c.(permanent) with
  | Some p => match p.(land) with | Some _ => true | None => false end
  | None => false end).

(* Fonction qui compte le nombre de primos dans une liste *)
Definition count_primos (l : list Card) : nat :=
  length (filter is_primo_and_land l).

(* Prédicat qui dit si une carte donnée est primo ou non *)
Definition is_primo_and_untapped (c : Card) : bool :=
  andb (String.eqb c.(name) "Primo, The Indivisible")
  (match c.(permanent) with
  | Some p => negb (p.(tapped))
  | None => false end).

(* Fonction qui compte le nombre de primos dans une liste *)
Definition count_untapped_primos (l : list Card) : nat :=
  length (filter is_primo_and_untapped l).

Definition is_primo_and_tapped (c : Card) : bool :=
  andb (String.eqb c.(name) "Primo, The Indivisible")
  (match c.(permanent) with
  | Some p => p.(tapped)
  | None => false end).

(* Fonction qui compte le nombre de primos dans une liste *)
Definition count_tapped_primos (l : list Card) : nat :=
  length (filter is_primo_and_tapped l).





Definition trigger_zimone_twice (gs : GameState) : GameState :=
  if Nat.eqb 1 (find_passive_ability_in_dict gs.(passive_abilities) AdditionalTrigger) && 
    Nat.ltb 0 (find_passive_ability_in_dict gs.(passive_abilities) LandPlayed) &&
    phase_eqb gs.(phase) MainPhase2 && has_card_named "Zimone, All-Questioning" gs.(battlefield)
    then
    advance_phase gs
  else gs.

Definition generate_four_primo_tokens (gs : GameState) : GameState :=
  if Nat.ltb 0 (find_passive_ability_in_dict gs.(passive_abilities) DoubleToken) &&
  Nat.ltb 0 (find_passive_ability_in_dict gs.(passive_abilities) NoLegendaryRule) then
  Resolve (Resolve gs 0 None) 0 None
  else
  gs.

Definition tap_three_creatures_for_siege_zombie (gs : GameState) : GameState :=
  if has_card_named "Zimone, All-Questioning" gs.(battlefield) then
    activate_ability 1 (Some [primo 1; primo 2; primo 3]) None None (siege_zombie 1) Dict_AA gs
  else 
    gs.

Definition zimone_can_deal_one_damage (gs : GameState) : Prop :=
  exists gs1 gs2 gs3,
    trigger_zimone_twice gs = gs1 /\
    generate_four_primo_tokens gs1 = gs2 /\
    tap_three_creatures_for_siege_zombie gs2 = gs3 /\
    gs3.(opponent) = gs2.(opponent)-1.

Axiom siege_zombie_deals_one_damage :
  forall gs,
    has_card_named "Zimone, All-Questioning" gs.(battlefield) = true ->
    let gs' := activate_ability 1 (Some [primo 1; primo 2; primo 3]) None None (siege_zombie 1) Dict_AA gs in
    gs'.(opponent) = gs.(opponent)-1.


Theorem two_zimone_triggers :
  is_prime (count_lands gs.(battlefield)) = true ->
  Nat.ltb 0 (find_passive_ability_in_dict gs.(passive_abilities) LandPlayed) = true ->
  Nat.eqb 1 (find_passive_ability_in_dict gs.(passive_abilities) AdditionalTrigger) = true ->
  Nat.eqb 2 (count_zimone_triggers gs1.(stack)) = true.
Proof.
  simpl. reflexivity.
Qed.
Admitted.

(* On vérifie qu'il y a bien 4 primos sur le champ de bataille
  Pour pouvoir avoir 4 tokens primos qui arrivent sur le champ de bataille en résolvant les deux triggers
  il faut : 
  - Que la règle légendaire soit désactivée
  - Qu'après le premier résolve le nombre de land soit toujours premier
  - Qu'on double la création de tokens
*)
Theorem four_primos_on_battlefield : 
  Nat.eqb 2 (count_zimone_triggers gs1.(stack)) = true ->
  Nat.ltb 0 (find_passive_ability_in_dict gs.(passive_abilities) DoubleToken) = true ->
  Nat.ltb 0 (find_passive_ability_in_dict gs.(passive_abilities) NoLegendaryRule) = true ->
  is_prime (count_lands (Resolve gs1 0 None).(battlefield)) = true ->
  Nat.eqb 4 (count_primos gs2.(battlefield)) = true.
Proof.
  simpl. reflexivity.
Qed.

(* Enfin on peut vérifier qu'on a bien fait un dégât et qu'on a bien tappé 3 des 4 primos
   Pour cela, on a besoin des conditions suivantes : 
   - Il y a 3 primos non tappés avant l'action
   - Le siege zombie est présent
   - Après l'action il y a 3 primos tappés
*)
Theorem one_damage_dealt :
  In (siege_zombie 1) gs2.(battlefield) ->
  Nat.eqb 4 (count_untapped_primos gs2.(battlefield)) = true ->
  Nat.eqb 3 (count_tapped_primos gs3.(battlefield)) = true ->
  Nat.eqb gs2.(opponent) (gs3.(opponent)+1) = true.
Proof.
  simpl. reflexivity.
Qed.


Theorem zimone_combo_deals_one_damage :
  is_prime (count_lands gs.(battlefield)) = true ->
  is_prime (count_lands gs.(battlefield) + 2) = true ->
  Nat.ltb 0 (find_passive_ability_in_dict gs.(passive_abilities) LandPlayed) = true ->
  Nat.eqb 1 (find_passive_ability_in_dict gs.(passive_abilities) AdditionalTrigger) = true ->
  Nat.ltb 0 (find_passive_ability_in_dict gs.(passive_abilities) DoubleToken) = true ->
  Nat.ltb 0 (find_passive_ability_in_dict gs.(passive_abilities) NoLegendaryRule) = true ->
  In (siege_zombie 1) gs2.(battlefield) ->
  Nat.eqb gs2.(opponent) (gs3.(opponent) + 1) = true.
Proof.
  intros Prime PrimePlusTwo LandPlayed AddTrigger DoubleToken NoLegend SiegePresent.
  apply one_damage_dealt.
  - exact SiegePresent.
  - apply four_primos_on_battlefield.
    + apply two_zimone_triggers.
     * exact Prime.
     * exact LandPlayed.
     * exact AddTrigger.
    + exact DoubleToken.
    + exact NoLegend.
    + exact PrimePlusTwo.
  - (* Montrer qu’après activation il y a bien 3 primos engagés *)
    simpl. reflexivity.
Qed.

End proof_4_primos.
Export proof_4_primos.


