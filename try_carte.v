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
Module Try_card.


Definition initial_GS : GameState := mkGameState nil nil nil nil nil 0 [] nil.


Definition GameHistory := list GameState.


Definition Save_Game_State (gs : GameState) (history : GameHistory) : GameHistory :=
  history ++ [gs]. (* On ajoute le nouvel état à la fin *)

Definition Get_Current_State (history : GameHistory) : option GameState :=
  match history with
  | [] => None
  | _ => Some (last history initial_GS)
  end.

(* Fonction pour mettre à jour le champ tapped d'un Land dans le battlefield *)
Fixpoint update_tapped_land (target_land : Land) (battlefield : list Card) : list Card :=
  match battlefield with
  | nil => nil
  | c :: rest =>
    match c.(permanent) with
    | None => c :: update_tapped_land target_land rest
    | Some perm =>
      match perm.(land) with
      | None => c :: update_tapped_land target_land rest
      | Some land_in_perm =>
        if eq_land target_land land_in_perm then
          let updated_perm := mkPermanent perm.(ListOnCast) perm.(ListOnDeath) perm.(ListOnPhase) perm.(ListActivated) perm.(creature) perm.(enchantement) (Some land_in_perm) perm.(artifact) true perm.(legendary) true in
          (mkCard (Some updated_perm) c.(instant) c.(sorcery) c.(manacost) c.(name)) :: update_tapped_land target_land rest
        else
          c :: update_tapped_land target_land rest
      end
    end
  end.

(* Fonction pour tap une Land et produire du mana, en mettant à jour l'historique *)
Definition tap_land (target_card : Card) (history : GameHistory) : GameHistory :=
  match Get_Current_State history with
  | None => history (* Si l'historique est vide, retourner l'historique inchangé *)
  | Some current_gs =>
    match target_card.(permanent) with
    | None => history (* Si la carte n'est pas un permanent, ne rien faire *)
    | Some perm =>
      match perm.(land) with
      | None => history (* Si la carte n'est pas un Land, ne rien faire *)
      | Some target_land =>
        if mem_card target_card current_gs.(battlefield) then
          let new_mana := mkMana (land_to_mana_color target_land.(producing)) 1 in
          let new_battlefield := update_tapped_land target_land current_gs.(battlefield) in
          let new_gs := mkGameState new_battlefield current_gs.(hand) current_gs.(library)
                          current_gs.(graveyard) current_gs.(exile) current_gs.(opponent)
                          (new_mana :: current_gs.(manapool)) current_gs.(stack) in
          Save_Game_State new_gs history
        else
          history (* Si la Land n'est pas dans le battlefield, ne rien faire *)
      end
    end
  end.



(* Fonction pour sacrifier des cartes et les déplacer vers le cimetière *)
Definition sacrifice_cards_ability_function (targets : option (list Card)) (gs : GameState) : GameState :=
  match targets with
  | None => gs (* Si aucune cible n'est fournie, retourner l'état du jeu inchangé *)
  | Some target_cards =>
    fold_left
      (fun new_gs target =>
        match target.(permanent) with
        | None => new_gs (* Si la carte n'est pas un permanent, ne rien faire *)
        | Some target_perm =>
          let new_battlefield := remove_card_from_hand new_gs.(battlefield) target in
          let new_graveyard := target :: new_gs.(graveyard) in
          mkGameState new_battlefield new_gs.(hand) new_gs.(library) new_graveyard new_gs.(exile)
                        new_gs.(opponent) new_gs.(manapool) new_gs.(stack)
        end)
      target_cards
      gs
  end.



(* Définition des sous-dictionnaires *)
Definition OnCast : Dict := [(1, sacrifice_cards_ability_function)].
Definition OnPhase : Dict := nil.
Definition OnDeath : Dict := nil.


(* Définition du dictionnaire principal avec des clés de type string *)
Definition Triggered_Abilities : list (nat * Dict) :=
  ( 1 , OnCast) :: (2 , OnPhase) :: (3 , OnDeath) :: nil.

(* Fonction pour trouver un sous-dictionnaire par sa clé *)
Fixpoint find_sub_dict (dicts : list (nat * Dict)) (key1 : nat) : option Dict :=
  match dicts with
  | nil => None
  | (k, sub_dict) :: rest =>
    if Nat.eqb k key1 then Some sub_dict else find_sub_dict rest key1
  end.

(* Fonction pour trouver une capacité par sa clé dans un sous-dictionnaire *)
Fixpoint find_ability_in_sub_dict (sub_dict : Dict) (key2 : nat) : option Ability :=
  match sub_dict with
  | nil => None
  | (k, ability) :: rest =>
    if Nat.eqb k key2 then Some ability else find_ability_in_sub_dict rest key2
  end.

(* Fonction principale pour trouver une capacité dans le dictionnaire principal *)
Definition find_ability_in_triggered_abilities (triggered_abilities : list (nat * Dict)) (pair : nat * nat) : option Ability :=
  let (key1, key2) := pair in
  match find_sub_dict triggered_abilities key1 with
  | None => None
  | Some sub_dict => find_ability_in_sub_dict sub_dict key2
  end.


(* Fonction pour activer les capacités à partir d'une liste de clés avec des cibles *)
Fixpoint activate_abilities_from_list_with_targets (triggered_abilities : list (nat * Dict)) (event_type : nat) (keys : list nat) (targets : option (list Card)) (gs : GameState) : GameState :=
  match keys with
  | [] => gs
  | key :: rest =>
    match find_ability_in_triggered_abilities triggered_abilities (event_type, key) with
    | None => activate_abilities_from_list_with_targets triggered_abilities event_type rest targets gs
    | Some ability =>
      let new_gs := ability targets gs in
      activate_abilities_from_list_with_targets triggered_abilities event_type rest targets new_gs
    end
  end.

(* Fonction générique pour activer une capacité à partir d'une carte avec des cibles *)
Definition activate_ability_from_card_with_targets (triggered_abilities : list (nat * Dict)) (card : Card) (event_type : nat) (targets : option (list Card)) (gs : GameState) : GameState :=
  match card.(permanent) with
  | None => gs (* Si la carte n'est pas un permanent, retourner l'état du jeu inchangé *)
  | Some perm =>
    let ability_keys :=
      match event_type with
      | 1 => perm.(ListOnCast)
      | 2 => perm.(ListOnPhase)
      | 3 => perm.(ListOnDeath)
      | _ => [] (* Par défaut, aucune capacité *)
      end
    in
    activate_abilities_from_list_with_targets triggered_abilities event_type ability_keys targets gs
  end.
Definition forest_land : Land := mkLand Forest.
Definition forest_perm : Permanent := mkPermanent nil nil nil nil None None (Some forest_land) None false false false.
Definition card_forest : Card := mkCard (Some forest_perm) None None [] "Forest".

(* Exemple de création d'une autre carte permanente *)
Definition creature_perm : Permanent := mkPermanent [1] nil nil nil (Some (mkCreature 2 2)) None None None false false false.
Definition card_creature : Card := mkCard (Some creature_perm) None None [] "Creature".

(* État de jeu initial avec des cartes dans le battlefield *)
Definition Test_gs : GameState := mkGameState [card_forest; card_creature] nil nil nil nil 0 [] nil.

(* Liste de cartes cibles à sacrifier *)
Definition target_cards : list Card := [card_forest].



Compute Test_gs.
Compute activate_ability_from_card_with_targets Triggered_Abilities card_creature 1 (Some target_cards) Test_gs.

End Try_card.
Export Try_card.


