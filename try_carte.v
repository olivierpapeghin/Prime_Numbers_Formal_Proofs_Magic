From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
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
Require Import card_instances.
Import card_instance.
Require Import game_actions.
Import game_action.
Module Try_card.

(* Définition d'une capacité qui ajoute un mana noir au manapool *)
Definition add_black_mana (target_cost : option (list Card)) (targets : option (list Card)) (manacost : option (list Mana)) (gs : GameState) : GameState :=
  add_mana gs Black 1.











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


End Try_card.
Export Try_card.


