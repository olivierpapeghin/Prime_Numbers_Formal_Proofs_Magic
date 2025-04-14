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

Local Open Scope string_scope.

Module game_action.



  (* Fonction pour sacrifier des cartes et les déplacer vers le cimetière *)
Definition Resolve (gs : GameState) (key : nat) (targets : option (list Card)) : GameState :=
  let reverse_stack := rev gs.(stack) in  
  match last_option reverse_stack with
  | Some (CardItem c') => (* Si c'est une carte *)
      let c := apply_passive_to_cast (get_active_passives (gs.(passive_abilities))) c' in
      match card_type c with
      | PermanentType => (* Si c'est un permanent *)
        let new_stack : list CardOrPair:= remove_last reverse_stack in
        if is_aura c && negb (is_valid_aura gs c) then (* Si on essaie de resolve une aura invalide *)
          let new_graveyard : list Card :=c :: gs.(graveyard) in
          mkGameState gs.(battlefield) gs.(hand) gs.(library) new_graveyard gs.(exile) gs.(opponent) gs.(manapool) new_stack gs.(passive_abilities) gs.(phase)
        else
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
                let _gs := mkGameState gs'.(battlefield) gs'.(hand) gs'.(library) gs'.(graveyard) gs'.(exile) gs'.(opponent) gs'.(manapool) gs'.(stack) (update_passive_ability_in_dict gs'.(passive_abilities) p_ability (S (find_passive_ability_in_dict gs'.(passive_abilities) p_ability))) gs'.(phase) in
                trigger_passive_effect _gs p_ability
              end
            end
          end
      | InstantType => 
        let new_gs : GameState := activate_spell non_permanent_abilities key targets gs in
        let new_stack : list CardOrPair:= remove_last reverse_stack in
        let new_graveyard : list Card := c :: new_gs.(graveyard) in
        mkGameState new_gs.(battlefield) new_gs.(hand) new_gs.(library) new_graveyard new_gs.(exile) new_gs.(opponent) new_gs.(manapool) new_stack gs.(passive_abilities) gs.(phase)

        | SorceryType => 
        let new_gs : GameState := activate_spell non_permanent_abilities key targets gs in
        let new_stack : list CardOrPair:= remove_last reverse_stack in
        let new_graveyard : list Card := c :: new_gs.(graveyard) in
        mkGameState new_gs.(battlefield) new_gs.(hand) new_gs.(library) new_graveyard new_gs.(exile) new_gs.(opponent) new_gs.(manapool) new_stack gs.(passive_abilities) gs.(phase)

      | UnknownType => gs (* Si on ne reconnait pas le type de la carte on ne fait rien *)
      end
  | Some (PairItem dict_id ability_id) =>
      (* Activer l'ability correspondante *)
      let new_gs := activate_triggered_ability Triggered_Abilities dict_id ability_id targets gs in
      let new_stack : list CardOrPair:= remove_last reverse_stack in
      mkGameState new_gs.(battlefield) new_gs.(hand) new_gs.(library) new_gs.(graveyard) new_gs.(exile) new_gs.(opponent) new_gs.(manapool) new_stack gs.(passive_abilities) gs.(phase)

  | None => gs (* Si la stack est vide, on ne fait rien *)
  end.



(* Fonction pour lancer une carte *)
Definition Cast (c' : Card) (gs : GameState) : GameState :=
  match find_card_in_list c' gs.(hand) with
  | None => gs
  | Some c =>
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
    end
  end.

(* Fonction pour activer une capacité *)
Definition activate_ability
  (index : nat)
  (targets_cost : option (list Card))
  (mana_cost : option (list Mana))
  (targets_ability : option (list Card))
  (card : Card)
  (dico : list(nat * Activated_Ability))
  (gs : GameState) : GameState :=
  match card.(permanent) with
  | None => gs (* La carte n'a pas de permanent *)
  | Some perm =>
    if List_In_nat index perm.(ListActivated) then
      (* Trouver l'Activated_Ability correspondante dans le dictionnaire *)
      match List_assoc beq_nat index dico with
      | Some ability =>
        (* Vérifier si le coût de mana est fourni *)
        match mana_cost with
        | None =>
          (* Pas de coût de mana, activer directement la capacité *)
          let new_gs := ability targets_cost targets_ability None gs in
          mkGameState new_gs.(battlefield) new_gs.(hand) new_gs.(library) new_gs.(graveyard) new_gs.(exile) new_gs.(opponent) new_gs.(manapool) new_gs.(stack) gs.(passive_abilities) gs.(phase)
        | Some mana_list =>
          (* Vérifier si le mana peut être payé *)
          match remove_card_costs gs mana_list with
          | None => gs (* Le coût de mana ne peut pas être payé *)
          | Some new_gs_with_pool =>
            (* Appliquer l'effet de la capacité *)
            let new_gs := ability targets_cost targets_ability (Some mana_list) new_gs_with_pool in
            (* Mettre à jour l'état du jeu *)
            mkGameState new_gs.(battlefield) new_gs.(hand) new_gs.(library) new_gs.(graveyard) new_gs.(exile) new_gs.(opponent) new_gs_with_pool.(manapool) new_gs.(stack) gs.(passive_abilities) gs.(phase)
          end
        end
      | None => gs (* L'index n'est pas dans le dictionnaire *)
      end
    else
      gs (* L'index n'est pas dans la liste des capacités activées *)
  end.
  
Definition Play_land (c : Card) (gs : GameState) : GameState :=
  if card_in_list c gs.(hand) then
    let new_battlefield := c :: gs.(battlefield) in
    let new_hand := remove_card gs.(hand) c in
    let new_gs := mkGameState new_battlefield new_hand gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) gs.(manapool) gs.(stack) (update_passive_ability_in_dict gs.(passive_abilities) LandPlayed (S (find_passive_ability_in_dict gs.(passive_abilities) LandPlayed))) gs.(phase) in
    
    new_gs
  else
    gs.

Definition Initial_GS : GameState := mkGameState [zimone 1; Forest 3; Forest 4; Forest 5] [Forest 2] nil nil nil 20 [mkMana Green 0; mkMana Red 0; mkMana Blue 0 ;mkMana White 0 ; mkMana Black 0 ;mkMana Generic 0] nil DefaultListPassiveAbility MainPhase2.
Definition test := Play_land (Forest 2) Initial_GS.
Compute activate_triggered_ability Triggered_Abilities 2 2 None test.

End game_action.
Export game_action.