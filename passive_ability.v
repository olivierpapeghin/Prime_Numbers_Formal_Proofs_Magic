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

Definition get_active_passives (dict : PassiveAbilityDict) : list PassiveKey :=
  fold_right (fun (p : PassiveKey * bool) (acc : list PassiveKey) =>
                let (k, b) := p in if b then k :: acc else acc)
             []
             dict.

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

Fixpoint Add_key_word_to (l : list Card) (new_key_word : string) : list Card :=
  match l with
  | [] => []
  | c :: rest =>
      let new_card := mkCard
        c.(permanent)
        c.(instant)
        c.(sorcery)
        c.(manacost)
        c.(name)
        c.(id)
        (new_key_word :: c.(keywords)) in
      new_card :: Add_key_word_to rest new_key_word
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
  
Definition Leyline_of_anticipation_passive (gs : GameState) : GameState :=
  let new_battlefield := Add_key_word_to gs.(battlefield) "Flash" in
  let new_hand := Add_key_word_to gs.(hand) "Flash" in
  let new_library := Add_key_word_to gs.(library) "Flash" in
  let new_grave := Add_key_word_to gs.(graveyard) "Flash" in
  let new_exile := Add_key_word_to gs.(exile) "Flash" in
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

Definition Life_and_limb_passive (c : Card) : Card :=
  match c.(permanent) with
  | None => c
  | Some perm =>
    match perm.(creature) with
    | Some creature =>
      if existsb (fun s => String.eqb s "Saproling") (subtype perm) then
        let new_perm := mkPermanent
          perm.(Abilities)
          perm.(ListActivated)
          perm.(PassiveAbility)
          perm.(subtype)
          (Some (mkCreature 1 1))
          perm.(enchantement)
          (Some (mkLand (mkMana Green 1)))
          perm.(artifact)
          perm.(token)
          perm.(legendary)
          perm.(tapped) in
        mkCard
          (Some new_perm)
          c.(instant)
          c.(sorcery)
          c.(manacost)
          c.(name)
          c.(id)
          c.(keywords)
      else
        c
    | None =>
      match perm.(land) with
      | None => c
      | Some land =>
        if eq_mana land.(producing) (mkMana Green 1) then
          let new_perm := mkPermanent
            perm.(Abilities)
            perm.(ListActivated)
            perm.(PassiveAbility)
            ("Saproling"%string :: perm.(subtype))
            (Some (mkCreature 1 1))
            perm.(enchantement)
            (Some (mkLand (mkMana Green 1)))
            perm.(artifact)
            perm.(token)
            perm.(legendary)
            perm.(tapped) in
          mkCard
            (Some new_perm)
            c.(instant)
            c.(sorcery)
            c.(manacost)
            c.(name)
            c.(id)
            c.(keywords)
        else
          c
      end
    end
  end.
  
Fixpoint apply_life_and_limb_to (l : list Card) : list Card :=
  match l with
  | [] => []
  | c :: rest =>
      let new_card := Life_and_limb_passive c in
      new_card :: apply_life_and_limb_to rest
  end.

Definition when_life_and_limb_enters (gs : GameState) : GameState :=
  let new_battlefield := apply_life_and_limb_to gs.(battlefield) in
  let new_gs := mkGameState 
    new_battlefield
    gs.(hand)
    gs.(library)
    gs.(graveyard)
    gs.(exile)
    gs.(opponent)
    gs.(manapool)
    gs.(stack)
    gs.(passive_abilities)
    gs.(phase) in
  new_gs.

Definition apply_keypassive (kp : PassiveKey) (c : Card) : Card :=
  match kp with
  | SaprolingsLands => Life_and_limb_passive c
  | _ => c
  end.

Definition apply_passive_to_cast (kps : list PassiveKey) (c : Card) : Card :=
  fold_left (fun acc kp => apply_keypassive kp acc) kps c.

Definition trigger_passive_effect (gs : GameState) (key : PassiveKey) : GameState :=
  match key with
  | AllSaprolings => Leyline_of_transformation_passive gs
  | AllFlash => Leyline_of_anticipation_passive gs
  | SaprolingsLands => when_life_and_limb_enters gs
  | _ => gs
  end.

End passive_ability.
Export passive_ability.

