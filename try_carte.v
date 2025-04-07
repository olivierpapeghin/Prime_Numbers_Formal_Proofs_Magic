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
Module Try_card.


(* Fonction pour sacrifier des cartes et les déplacer vers le cimetière *)
Definition sacrifice_cards (targets : option (list Card)) (gs : GameState) : GameState :=
  match targets with
  | None => gs (* Si aucune cible n'est fournie, retourner l'état du jeu inchangé *)
  | Some target_cards =>
    fold_left
      (fun new_gs target =>
        match target.(permanent) with
        | None => new_gs (* Si la carte n'est pas un permanent, ne rien faire *)
        | Some target_perm =>
          let new_battlefield := remove_card new_gs.(battlefield) target in
          let new_graveyard := target :: new_gs.(graveyard) in
          mkGameState new_battlefield new_gs.(hand) new_gs.(library) new_graveyard new_gs.(exile)
                        new_gs.(opponent) new_gs.(manapool) new_gs.(stack) gs.(passive_abilities)
        end)
      target_cards
      gs
  end.

(* Définition d'une capacité qui ajoute un mana noir au manapool *)
Definition add_black_mana (targets : option (list Card)) (gs : GameState) : GameState :=
  let new_manapool := (mkMana Black 1) :: gs.(manapool) in
  mkGameState gs.(battlefield) gs.(hand) gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) new_manapool gs.(stack) gs.(passive_abilities).

(* Définition des sous-dictionnaires *)
Definition OnCast : Dict := [(1, sacrifice_cards)].
Definition OnPhase : Dict := nil.
Definition OnDeath : Dict := nil.
Definition OnEnter : Dict := [(1, sacrifice_cards)].


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
 
(* Fonction pour activer une seule capacité à partir d'une clé avec des cibles *)
Definition activate_triggered_ability (triggered_abilities : list (nat * Dict)) (event_type : nat) (key : nat) (targets : option (list Card)) (gs : GameState) : GameState :=
  match find_ability_in_triggered_abilities triggered_abilities (event_type, key) with
  | None => gs (* Aucune capacité trouvée, retourner l'état du jeu inchangé *)
  | Some ability =>
    let new_gs := ability targets gs in
    new_gs (* Retourner l'état du jeu mis à jour après activation de la capacité *)
  end.

Definition add_abilities_to_stack (event_type : nat) (p : Permanent) (gs : GameState) : GameState :=
  fold_left
    (fun gs' pair =>
      match pair with
      | (dict_id, ability_id) =>
        if beq_nat dict_id event_type then
          let new_stack := (PairItem dict_id ability_id) :: gs'.(stack) in
          mkGameState gs'.(battlefield) gs'.(hand) gs'.(library) gs'.(graveyard) gs'.(exile) gs'.(opponent) gs'.(manapool) new_stack gs.(passive_abilities)
        else
          gs'
      end
    )
    p.(Abilities)
    gs.

(* Utilisation de la fonction dans Cast *)
Definition Cast (c:Card) (gs:GameState) : GameState :=
  let cost := c.(manacost) in
  let pool := gs.(manapool) in
  if Can_Pay cost pool && card_in_list c gs.(hand) && check_legendary_rule gs c then
    let new_pool := fold_left remove_mana cost pool in
    let new_hand := remove_card gs.(hand) c in
    let new_stack := CardItem c :: gs.(stack) in
    let intermediate_gs := mkGameState gs.(battlefield) new_hand gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) new_pool new_stack gs.(passive_abilities) in
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



(* Fonction pour résoudre le dernier élément du stack *)
Definition Resolve (targets : option (list Card)) (gs : GameState) : GameState :=
  match gs.(stack) with
  | nil => gs (* Si le stack est vide, retourner l'état du jeu inchangé *)
  | item :: rest =>
    match item with
    | CardItem card =>
      (* Ajouter la carte au battlefield *)
      let new_battlefield := card :: gs.(battlefield) in
      let new_stack := rest in
      mkGameState new_battlefield gs.(hand) gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) gs.(manapool) new_stack gs.(passive_abilities)
    | PairItem dict_id ability_id =>
      (* Activer l'ability correspondante *)
      let new_gs := activate_triggered_ability Triggered_Abilities dict_id ability_id targets gs in
      let new_stack := rev rest in
      mkGameState new_gs.(battlefield) new_gs.(hand) new_gs.(library) new_gs.(graveyard) new_gs.(exile) new_gs.(opponent) new_gs.(manapool) new_stack gs.(passive_abilities)
    end
  end.

Definition Activated_abilities := list (nat * ActivatedAbility). 
Definition Dict_AA := Dict.

(* Definition activate_ability ( AA : Activated_abilities ) (card : Card) ( index : nat ) ( targets_cost : option (list Card)) ( mana_cost : list Mana ) (targets_ability : option (list Card)) (gs : GameState) : GameState := 
  

 *)
Definition Cast_gs : GameState := Cast destructeur Test_gs.
Definition Resol1 : GameState := Resolve (Some [colossal_dreadmaw]) Cast_gs.

Lemma colossal_dreadmaw_in_graveyard :
  card_in_list colossal_dreadmaw (Resol1.(graveyard)) = true.
Proof.
  simpl.
  reflexivity.
Qed.


End Try_card.
Export Try_card.


