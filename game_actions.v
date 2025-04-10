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
        let gs' : GameState := mkGameState new_battlefield gs.(hand) gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) gs.(manapool) new_stack gs.(passive_abilities) gs.(phase) in
        match check_legendary_rule gs c with
        | false => (* Il y a déjà une instance de cette carte légendaire sur le champ de bataille *)
        sacrifice gs' [c]
        | true => (* Pas de problèmes de carte légendaire *)
          match c.(permanent) with
          | None => gs'
          | Some c_perm =>
            match c_perm.(PassiveAbility) with
            | None => gs'
            | Some p_ability => 
              mkGameState gs'.(battlefield) gs'.(hand) gs'.(library) gs'.(graveyard) gs'.(exile) gs'.(opponent) gs'.(manapool) gs'.(stack) (update_passive_ability_in_dict gs'.(passive_abilities) p_ability true) gs'.(phase)
            end
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
Fixpoint is_pool_modified (original new : list Mana) : bool :=
  match original, new with
  | [], [] => false
  | [], _ => true
  | _, [] => true
  | (mkMana col1 qty1) :: rest1, (mkMana col2 qty2) :: rest2 =>
    if eq_mana_color col1 col2 then
      if Nat.eqb qty1 qty2 then
        is_pool_modified rest1 rest2
      else
        true
    else
      true
  end.



(* Fonction pour lancer une carte *)
Definition Cast (c : Card) (gs : GameState) : GameState :=
  let cost := c.(manacost) in
  match remove_card_costs gs cost with
  | None => gs (* Si les coûts ne peuvent pas être payés, retourne le GameState inchangé *)
  | Some new_gs =>
    if card_in_list c new_gs.(hand) && can_cast c new_gs.(phase) then
      let new_hand := remove_card new_gs.(hand) c in
      let new_stack := CardItem c :: new_gs.(stack) in
      let intermediate_gs := mkGameState
        new_gs.(battlefield)
        new_hand
        new_gs.(library)
        new_gs.(graveyard)
        new_gs.(exile)
        new_gs.(opponent)
        new_gs.(manapool)
        new_stack
        new_gs.(passive_abilities)
        new_gs.(phase) in
      (* Ajouter les abilities des permanents sur le battlefield au stack *)
      let final_gs := fold_left (fun gs' perm =>
        match perm.(permanent) with
        | Some perm_data => add_abilities_to_stack 1 perm_data gs'
        | None => gs'
        end
      ) new_gs.(battlefield) intermediate_gs in
      final_gs
    else
      gs (* Si la carte ne peut pas être lancée, retourne le GameState inchangé *)
  end.




End game_action.
Export game_action.