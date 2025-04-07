From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Require Import List String.
Require Import Bool.Bool.
Import ListNotations.
Require Import type_definitions.
Import type_definition.
Require Import utility_functions.
Import utility_function.

Local Open Scope string_scope.

Definition Resolve (gs : GameState) (key : nat) (targets : option (list Card)) : GameState :=
  match last_option gs.(stack) with
  | Some (CardItem c) => (* Si c'est une carte *)
      match card_type c with
      | PermanentType => (* Si c'est un permanent *)
        let new_stack : list CardOrPair:= remove_last gs.(stack) in
        let new_battlefield : list Card := c :: gs.(battlefield) in
        mkGameState new_battlefield gs.(hand) gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) gs.(manapool) new_stack gs.(passive_abilities) gs.(phase)
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
      let new_stack := rev rest in
      mkGameState new_gs.(battlefield) new_gs.(hand) new_gs.(library) new_gs.(graveyard) new_gs.(exile) new_gs.(opponent) new_gs.(manapool) new_stack gs.(passive_ability)
  | None => gs (* Si la stack est vide, on ne fait rien *)
  end.