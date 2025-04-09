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

Module passive_ability.




Fixpoint update_passive_ability_in_dict (dict : PassiveAbilityDict) (key : PassiveKey) (new_value : bool) : PassiveAbilityDict :=
  match dict with
  | nil => nil
  | (k, activated) :: rest =>
      if eq_passive_key k key 
      then (k, new_value) :: rest  (* Mise à jour de la valeur si la clé correspond *)
      else (k, activated) :: update_passive_ability_in_dict rest key new_value
  end.

Fixpoint Transform_all_creature_in (l : list Card) (new_type : string) : list Card :=
  match l with
  | [] => []
  | c :: rest =>
    match c.(permanent) with
    | None => c :: Transform_all_creature_in rest new_type
    | Some perm =>
      match perm.(creature) with
      | None => c :: Transform_all_creature_in rest new_type
      | Some _ =>
        let new_perm := mkPermanent
          perm.(Abilities)
          perm.(ListActivated)
          perm.(PassiveAbility)
          (new_type :: perm.(subtype))
          perm.(creature)
          perm.(enchantement)
          perm.(land)
          perm.(artifact)
          perm.(token)
          perm.(legendary)
          perm.(tapped)
        in
        let new_card := mkCard
          (Some new_perm)
          c.(instant)
          c.(sorcery)
          c.(manacost)
          c.(name)
          c.(id)
          c.(keywords)
        in
        new_card :: Transform_all_creature_in rest new_type
      end
    end
  end.
  
  
Definition Leyline_of_transformation_passive (gs : GameState) : GameState :=
  let new_battlefield := Transform_all_creature_in gs.(battlefield) "Saproling" in
  let new_hand := Transform_all_creature_in gs.(hand) "Saproling" in
  let new_library := Transform_all_creature_in gs.(library) "Saproling" in
  let new_grave := Transform_all_creature_in gs.(graveyard) "Saproling" in
  let new_exile := Transform_all_creature_in gs.(exile) "Saproling" in
  let new_gs := mkGameState
    new_battlefield
    new_hand
    new_library
    new_grave
    new_exile
    gs.(opponent)
    gs.(manapool)
    gs.(stack)
    gs.(passive_abilities)
    gs.(phase) in
  new_gs
  .
  
Definition trigger_passive_effect (gs : GameState) (key : PassiveKey) : GameState :=
  match key with
  | AllSaprolings => Leyline_of_transformation_passive gs
  | _ => gs
  end.


End passive_ability.
Export passive_ability.

