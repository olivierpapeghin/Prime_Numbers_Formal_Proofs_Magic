
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

Local Open Scope string_scope.

Module game_action.
  

  (* Fonction pour sacrifier des cartes et les déplacer vers le cimetière *)
Definition Resolve (gs : GameState) (key : nat) (targets : option (list Card)) : GameState :=
  match last_option gs.(stack) with
  | Some (CardItem c) => (* Si c'est une carte *)
      match card_type c with
      | PermanentType => (* Si c'est un permanent *)
        let new_stack : list CardOrPair:= remove_last gs.(stack) in
        let new_battlefield : list Card := c :: gs.(battlefield) in
        let final_gs := mkGameState new_battlefield gs.(hand) gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) gs.(manapool) new_stack gs.(passive_abilities) gs.(phase) in
        match c.(permanent) with
        | None => final_gs
        | Some c_perm =>
          match c_perm.(PassiveAbility) with
          | None => final_gs
          | Some p_ability => 
            mkGameState final_gs.(battlefield) final_gs.(hand) final_gs.(library) final_gs.(graveyard) final_gs.(exile) final_gs.(opponent) final_gs.(manapool) final_gs.(stack) (update_passive_ability_in_dict final_gs.(passive_abilities) p_ability true) final_gs.(phase)
          end
        end
      | InstantType =>
        let new_gs : GameState := activate_spell non_permanent_abilities key targets gs in
        let new_stack : list CardOrPair:= remove_last gs.(stack) in
        let new_graveyard : list Card := c :: new_gs.(graveyard) in
        mkGameState new_gs.(battlefield) new_gs.(hand) new_gs.(library) new_graveyard new_gs.(exile) new_gs.(opponent) new_gs.(manapool) new_stack gs.(passive_abilities) gs.(phase)
      | SorceryType => 
        let new_gs : GameState := activate_spell non_permanent_abilities key targets gs in
        let new_stack : list CardOrPair:= remove_last gs.(stack) in
        let new_graveyard : list Card := c :: new_gs.(graveyard) in
        mkGameState new_gs.(battlefield) new_gs.(hand) new_gs.(library) new_graveyard new_gs.(exile) new_gs.(opponent) new_gs.(manapool) new_stack gs.(passive_abilities) gs.(phase)
      | UnknownType => gs (* Si on ne reconnait pas le type de la carte on ne fait rien *)
      end
  | Some (PairItem dict_id ability_id) =>
      (* Activer l'ability correspondante *)
      let new_gs := activate_triggered_ability Triggered_Abilities dict_id ability_id targets gs in
      let new_stack : list CardOrPair:= remove_last gs.(stack) in
      mkGameState new_gs.(battlefield) new_gs.(hand) new_gs.(library) new_gs.(graveyard) new_gs.(exile) new_gs.(opponent) new_gs.(manapool) new_stack gs.(passive_abilities) gs.(phase)
  | None => gs (* Si la stack est vide, on ne fait rien *)
  end.


Definition Cast (c:Card) (gs:GameState) : GameState :=
  let cost := c.(manacost) in
  let pool := gs.(manapool) in
  let current_phase := gs.(phase) in
  if Can_Pay cost pool && card_in_list c gs.(hand) && check_legendary_rule gs c && can_cast c current_phase then
    let new_pool := fold_left (fun pool' cost' => snd (remove_mana pool' cost')) pool cost in
    let new_hand := remove_card gs.(hand) c in
    let new_stack := CardItem c :: gs.(stack) in
    let intermediate_gs := mkGameState gs.(battlefield) new_hand gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) new_pool new_stack gs.(passive_abilities) gs.(phase) in
    (* Ajouter les abilities des permanents sur le battlefield au stack *)
    let final_gs := fold_left (fun gs' perm =>
      match perm.(permanent) with
      | Some perm_data => add_abilities_to_stack 1 perm_data gs'
      | None => gs'
      end
    )  gs.(battlefield) intermediate_gs in
   final_gs
  else
    gs.



End game_action.
Export game_action.