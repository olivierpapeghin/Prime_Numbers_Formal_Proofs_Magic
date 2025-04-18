From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Require Import List String.
Require Import Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.
Require Import type_definitions.
Import type_definition.
Require Import utility_functions.
Import utility_function.
Require Import card_instances.
Import card_instance.

Local Open Scope string_scope.

Module abilities_effects.

Definition default_card : Card := mkCard None None None nil "Default" 0 [].

(*-----------------------------------------Abilités génériques----------------------------------------------*)

Definition sacrifice (gs : GameState) (targets : list Card) : GameState :=
  (* On retire les cartes sacrifiées du champ de bataille *)
  let new_battlefield := fold_left remove_card targets gs.(battlefield) in
  (* On ajoute les cartes sacrifiées au cimetière *)
  let new_graveyard : list Card := List.app targets gs.(graveyard) in
  (* On prépare un GameState intermédiaire, sans les permanents morts *)
  let intermediate_gs := mkGameState new_battlefield gs.(hand) gs.(library) new_graveyard gs.(exile) gs.(opponent) gs.(manapool) gs.(stack) gs.(passive_abilities) gs.(phase) in
  (* On déclenche les capacités à la mort de chaque permanent sacrifié *)
  let final_gs := fold_left (fun gs' card =>
    match card.(permanent) with
    | Some perm_data => add_abilities_to_stack 3 perm_data gs'
    | None => gs'
    end
  ) targets intermediate_gs in
  final_gs.

Definition tap (c : Card) : Card :=
  match c.(permanent) with
  | Some p =>
  mkCard
  (Some (mkPermanent p.(Abilities) p.(ListActivated) p.(PassiveAbility) p.(subtype) p.(creature) p.(enchantement) p.(land) p.(artifact) p.(token) p.(legendary) true))
  c.(instant) c.(sorcery) c.(manacost) c.(name) c.(id) c.(keywords)
  | None => c
  end.

Definition untap (c : Card) : Card :=
  match c.(permanent) with
  | Some p =>
  mkCard
  (Some (mkPermanent p.(Abilities) p.(ListActivated) p.(PassiveAbility) p.(subtype) p.(creature) p.(enchantement) p.(land) p.(artifact) p.(token) p.(legendary) false))
  c.(instant) c.(sorcery) c.(manacost) c.(name) c.(id) c.(keywords)
  | None => c
  end.


(*-----------------------------------------Effets des Instants/Sorcery----------------------------------------------*)

Definition abuelos_awakening_ability (targets : option (list Card)) (gs : GameState) : GameState :=
  (* On s'assure en premier lieu qu'on a bien une cible *)
  match targets with
  | None => gs (* Pas de cible, on ne fait rien *)
  | Some target_list => 
    (* On doit ensuite vérifier qu'on a qu'une seule cible est qu'elle est un artefact/enchantement non aura *)
    if Nat.eqb (List.length target_list) 1 then 
      let target : Card := hd default_card target_list in (* On prend le premier élément s'il existe *)
      match target.(permanent) with
      | Some p => (* C'est un permanent, on peut vérifier que c'est un enchantement ou un artefact *)
        match permanent_type p with
        | ArtifactType | EnchantmentType => (* C'est un artefact ou un enchantement *) 
          match negb (has_subtype "aura" p.(subtype)) with
            | true =>
            let new_graveyard : list Card := remove_card gs.(graveyard) target in (* On enlève la carte cible du cimetière *)
            let spirit : Card := mkCard(* On crée le token esprit engendré par Abuelo's Awakening *)
            (Some (mkPermanent
              p.(Abilities) (* On copie les abilités du permanent *)
              p.(ListActivated)
              p.(PassiveAbility)
              ("Spirit" :: p.(subtype)) (* On reprend les sous-types et on y ajoute "Spirit" *)
              (Some (mkCreature 1 1)) (* Est une créature 1/1*)
              p.(enchantement)
              p.(land)
              p.(artifact)
              false (* C'est un token *)
              p.(legendary)
              false)) (* Il n'entre pas engagé *)
            None (* Ce n'est pas un instant ou un sorcery *)
            None
            target.(manacost)
            target.(name)
            target.(id) 
            target.(keywords) in 
            let new_battlefield : list Card := spirit :: gs.(battlefield) in
            (mkGameState new_battlefield gs.(hand) gs.(library) new_graveyard gs.(exile) gs.(opponent) gs.(manapool) gs.(stack) gs.(passive_abilities) gs.(phase))
          | false => (* Cible invalide on ne fait rien *)
            gs
          end
        | _ => gs (* Sinon on ne fait rien *)
        end
       | _ => gs
       end
      else
      gs
    end.

Definition narsets_reversal_ability (targets : option (list Card)) (gs : GameState) : GameState :=
  match targets with
  | Some [target] =>  (* exactement une cible *)
      match target.(instant), target.(sorcery) with
      | Some _, _ | _, Some _ =>  (* la cible est un sort *)
          (* Générer un nouvel ID en comptant les occurrences du nom de la carte dans la stack *)
          let get_card_name (item : CardOrPair) : option string :=
            match item with
            | CardItem c => Some c.(name)
            | _ => None
            end in

          let stack_names := map get_card_name gs.(stack) in
          let name_eqb (a b : option string) : bool :=
            match a, b with
            | Some s1, Some s2 => String.eqb s1 s2
            | _, _ => false
            end in

          let id_generated := count_occ (option string) name_eqb stack_names (Some target.(name)) in

          (* Création de la copie *)
          let copied := mkCard
            target.(permanent)
            target.(instant)
            target.(sorcery)
            target.(manacost)
            (target.(name) ++ " (Copy)")
            id_generated
            target.(keywords) in

          (* Supprimer le sort original de la stack *)
          let new_stack :=
            filter (fun item =>
              match item with
              | CardItem c => negb (Nat.eqb c.(id) target.(id))
              | _ => true
              end) gs.(stack) in

          (* Ajouter la copie sur la pile, remettre le sort original en main *)
          let new_stack := CardItem copied :: new_stack in
          let new_hand := target :: gs.(hand) in

          mkGameState gs.(battlefield) new_hand gs.(library) gs.(graveyard)
                      gs.(exile) gs.(opponent) gs.(manapool) new_stack
                      gs.(passive_abilities) gs.(phase)
      | _, _ => gs
      end
  | _ => gs
  end.

Definition molten_duplication_ability (targets : option (list Card)) (gs : GameState) : GameState :=
match targets with
  | Some [target] =>
      match target.(permanent) with
      | Some p =>
          if (isSome p.(creature)) || (isSome p.(artifact)) then
            let count_existing_copies :=
              count_occ (option string) name_eqb
                (map (fun c => Some c.(name)) (List.app gs.(battlefield) gs.(hand)))
                (Some target.(name))
            in
            let base_id := 1 + count_existing_copies in
            let make_token id :=
              mkCard
                (Some (mkPermanent
                        ((2, 1) :: p.(Abilities))
                        p.(ListActivated)
                        p.(PassiveAbility)
                        p.(subtype)
                        p.(creature)
                        p.(enchantement)
                        p.(land)
                        (match p.(artifact) with
                         | Some _ => Some (mkArtifact None)
                         | None => None
                         end)
                        true 
                        p.(legendary)
                        false)) 
                None
                None
                [] 
                target.(name) 
                id
                ["Haste"]
            in
            let new_token1 := make_token base_id in
            let new_token2 := make_token (base_id + 1) in
            if Nat.ltb 0 (find_passive_ability_in_dict gs.(passive_abilities) DoubleToken) then
              let new_battlefield := new_token1 :: new_token2 :: gs.(battlefield) in
              let updated_gs := mkGameState
              new_battlefield gs.(hand) gs.(library) gs.(graveyard)
              gs.(exile) gs.(opponent) gs.(manapool)
              gs.(stack) gs.(passive_abilities) gs.(phase)
            in updated_gs
            else 
              let new_battlefield := new_token1 :: gs.(battlefield) in  
              let updated_gs := mkGameState
              new_battlefield gs.(hand) gs.(library) gs.(graveyard)
              gs.(exile) gs.(opponent) gs.(manapool)
              gs.(stack) gs.(passive_abilities) gs.(phase)
            in updated_gs
          else gs
      | None => gs
      end
  | _ => gs
  end.


Definition non_permanent_abilities : Dict := [(1, abuelos_awakening_ability); (2,narsets_reversal_ability); (3,molten_duplication_ability)].

(*-----------------------------------------Abilités déclenchées----------------------------------------------*)

Definition birgi_ability (targets : option (list Card)) (gs : GameState) : GameState :=
  add_mana gs Red 1.

Definition desecration_elemental_ability (targets : option (list Card)) (gs : GameState) : GameState :=
    match targets with
  | None => gs (* Pas de cible, on ne fait rien *)
  | Some target_list => 
    (* On doit ensuite vérifier qu'on a qu'une seule cible *)
    if Nat.eqb (List.length target_list) 1 then 
    sacrifice gs target_list
    else
    gs
  end.

Definition sacrifice_end_step (targets : option (list Card)) (gs : GameState) : GameState :=
  match targets with
  | Some target_list => sacrifice gs target_list
  | None => gs
  end.

Definition myrkul_ability (targets : option (list Card)) (gs : GameState) : GameState :=
  match targets with
  | None => gs (* Pas de cible, on ne fait rien *)
  | Some target_list =>
      if Nat.eqb (List.length target_list) 1 then
        match hd_error target_list with
        | Some target =>
            match target.(permanent) with
            | Some p =>
                let new_perm := mkPermanent
                  p.(Abilities)
                  p.(ListActivated)
                  p.(PassiveAbility)
                  p.(subtype)
                  None (* On retire le type créature *)
                  (Some (mkEnchantement None)) (* Devient un enchantement *)
                  None
                  None
                  true (* Est un jeton *)
                  p.(legendary)
                  p.(tapped) in

                let new_card := mkCard
                  (Some new_perm)
                  None
                  None
                  target.(manacost)
                  target.(name)
                  target.(id)
                  target.(keywords) in

                let new_graveyard := remove_card gs.(graveyard) target in
                let new_exile := target :: gs.(exile) in
                let new_battlefield := new_card :: gs.(battlefield) in

                mkGameState new_battlefield gs.(hand) gs.(library) new_graveyard
                            new_exile gs.(opponent) gs.(manapool) gs.(stack)
                            gs.(passive_abilities) gs.(phase)
            | None => gs
            end
        | None => gs
        end
      else gs
  end.



Definition isochron_scepter_enter (targets : option (list Card)) (gs : GameState) : GameState :=
match targets with
  | Some [imprinted_card; scepter_card] =>
      match imprinted_card.(instant), scepter_card.(permanent) with
      | Some inst, Some perm =>
          let new_exile := imprinted_card :: gs.(exile) in
          let new_hand := remove_card gs.(hand) imprinted_card in

          let updated_battlefield := map (fun c =>
            if Nat.eqb c.(id) scepter_card.(id) then
              match c.(permanent) with
              | Some p =>
                  let updated_artifact := Some (mkArtifact (Some inst)) in
                  let updated_permanent := mkPermanent
                    p.(Abilities)
                    p.(ListActivated)
                    p.(PassiveAbility)
                    p.(subtype)
                    p.(creature)
                    p.(enchantement)
                    p.(land)
                    updated_artifact
                    p.(token)
                    p.(legendary)
                    p.(tapped) in
                  mkCard
                    (Some updated_permanent)
                    c.(instant)
                    c.(sorcery)
                    c.(manacost)
                    c.(name)
                    c.(id)
                    c.(keywords)
              | None => c
              end
            else c
          ) gs.(battlefield) in

          mkGameState
            updated_battlefield
            new_hand
            gs.(library)
            gs.(graveyard)
            new_exile
            gs.(opponent)
            gs.(manapool)
            gs.(stack)
            gs.(passive_abilities)
            gs.(phase)
      | _, _ => gs
      end
  | _ => gs
  end.
Definition zimone_ability (targets : option (list Card)) (gs : GameState) : GameState := 
  match targets with
  | Some t => gs
  | None => let nb_lands := count_lands gs.(battlefield) in 
            let is_land_played := find_passive_ability_in_dict gs.(passive_abilities) LandPlayed in
            if is_prime nb_lands && Nat.ltb 0 is_land_played then create_token (primo 0) nb_lands gs
            else gs
  end.
  

Definition mirror_room_enter (targets : option (list Card)) (gs : GameState) : GameState :=
  match targets with
  | Some [c'; to_copy'] =>
    match find_card_in_list c' gs.(battlefield) with
    | None => gs
    | Some c =>
      match find_card_in_list to_copy' gs.(battlefield) with
      | None => gs
      | Some to_copy =>
        match to_copy.(permanent) with
        | None => gs
        | Some to_copy_perm =>
          match c.(permanent) with
          | None => gs
          | Some perm =>
            match to_copy_perm.(creature) with
            | None => gs
            | Some crea =>
              let is_mirror_realm_card (n : string) : bool :=
                String.eqb n "Mirror Room // Fractured Realm (full locked)" ||
                String.eqb n "Mirror Room // Fractured Realm (full unlocked)" ||
                String.eqb n "Mirror Room" ||
                String.eqb n "Fractured Realm" in

              let cards : list string :=
                map (fun c => c.(name)) (List.app gs.(battlefield) gs.(hand)) in

              let count_existing_copies : nat :=
                List.length (filter is_mirror_realm_card cards) in
              match get_base_card c (count_existing_copies + 1) with
              | None => gs
              | Some copy =>
                match copy.(permanent) with
                | None => gs
                | Some copy_perm =>
                  let new_subtype := "Reflection" :: copy_perm.(subtype) in
                  let copy1 := mkCard
                          (Some (mkPermanent
                              (copy_perm.(Abilities))
                              (copy_perm.(ListActivated))
                              (copy_perm.(PassiveAbility))
                              (copy_perm.(subtype))
                              (copy_perm.(creature))
                              (copy_perm.(enchantement))
                              (copy_perm.(land))
                              (copy_perm.(artifact))
                              true (* token := true *)
                              (copy_perm.(legendary))
                              false))
                          None
                          None
                          copy.(manacost)
                          copy.(name)
                          copy.(id)
                          copy.(keywords) in
                  let new_battlefield := copy1 :: gs.(battlefield) in
                  
                  let new_gs := mkGameState new_battlefield gs.(hand) gs.(library) gs.(graveyard)
                                    gs.(exile) gs.(opponent) gs.(manapool) gs.(stack)
                                    gs.(passive_abilities) gs.(phase) in
                  add_abilities_to_stack 4 copy_perm new_gs
                end
              end
            end
          end
        end
      end
    end
  | _ => gs
  end. 
  


(* Définition des sous-dictionnaires *)
Definition OnCast : Dict := [(1,birgi_ability);(2, desecration_elemental_ability)].
Definition OnPhase : Dict := [(1,sacrifice_end_step);(2,zimone_ability)].
Definition OnDeath : Dict := [(1,myrkul_ability)].
Definition OnEnter : Dict := [(1,isochron_scepter_enter); (2, mirror_room_enter)].


(* Définition du dictionnaire principal avec des clés de type string *)
Definition Triggered_Abilities : list (nat * Dict) :=
  ( 1 , OnCast) :: (2 , OnPhase) :: (3 , OnDeath) :: (4 , OnEnter) :: nil.

(*-----------------------------------------Abilités activées----------------------------------------------*)

Definition siege_zombie_ability (target_cost : option (list Card)) (targets : option (list Card)) (manacost : option (list Mana)) (gs : GameState) : GameState :=
  (* On vérifie qu'il y a bien trois cibles dans la liste target_cost *)
  match target_cost with
  | Some tc =>
      if Nat.eqb (Coq.Lists.List.length tc) 3 then
    (* Vérifie que chaque carte de la liste a bien un permanent *)
    if forallb (fun c => match c.(permanent) with | Some _ => true | None => false end) tc then
      let tapped_cards := map tap tc in
      let new_battlefield := map (fun c =>
         if existsb (fun target => Nat.eqb target.(id) c.(id)) tc
         then tap c
         else c
      ) gs.(battlefield) in
      mkGameState new_battlefield gs.(hand) gs.(library) gs.(graveyard)
                        gs.(exile) (gs.(opponent)-1) gs.(manapool) gs.(stack)
                        gs.(passive_abilities) gs.(phase)
      else gs (* Une des cartes n'est pas un permanent *)
    else gs (* La liste n'a pas exactement 3 cartes *)
  | None => gs
  end.

Definition clock_of_omens_ability (target_cost : option (list Card)) (targets : option (list Card)) (manacost : option (list Mana)) (gs : GameState) : GameState :=
  match target_cost, targets with (* On regarde si les listes concernées existent *)
  | Some cost_cards, Some target_list =>
      if Nat.eqb (Coq.Lists.List.length cost_cards) 2 then (* On a bien deux cibles uniquements *)
        if forallb is_untapped_artifact cost_cards then
          match target_list with
          | [target] => (* On vérifie qu'il n'y a qu'une seule cible à untap *)
              match target.(permanent) with
              | Some p =>
                  match p.(artifact) with 
                  | Some _ => (* C'est bien un artefact *)
                      (* Tap les cartes utilisées en coût *)
                      let tapped_costs := map tap cost_cards in
                      let battlefield_after_cost :=
                        map (fun c =>
                               if existsb (fun t => eq_card t c) cost_cards
                               then tap c
                               else c
                            ) gs.(battlefield) in
                      (* Untap la carte cible *)
                      let battlefield_final :=
                        map (fun c =>
                               if eq_card target c
                               then untap c
                               else c
                            ) battlefield_after_cost in
                      mkGameState battlefield_final gs.(hand) gs.(library) gs.(graveyard)
                                  gs.(exile) gs.(opponent) gs.(manapool) gs.(stack)
                                  gs.(passive_abilities) gs.(phase)
                  | None => gs
                  end
              | None => gs
              end
          | _ => gs
          end
        else gs
      else gs
  | _, _ => gs
  end.

(* Ici on modifie légèrement l'abilité, on fixe la couleur du mana ajouté à bleue *)
Definition sanctum_weaver_ability (target_cost : option (list Card)) (targets : option (list Card)) (manacost : option (list Mana)) (gs : GameState) : GameState :=
  match target_cost with
  | Some [card] =>
      match card.(permanent) with
      | Some _ =>
          let nb_enchantements := count_enchantments gs.(battlefield) in
          let new_mana :=  (add_mana gs Blue nb_enchantements).(manapool) in
          let new_battlefield := 
          map (fun c =>
             if eq_card c card then tap c else c
          ) gs.(battlefield) in
          mkGameState new_battlefield gs.(hand) gs.(library) gs.(graveyard)
                      gs.(exile) gs.(opponent) new_mana gs.(stack)
                      gs.(passive_abilities) gs.(phase)
      | None => gs
      end
  | _ => gs
  end.

Definition freed_from_the_realm_ability_1 (target_cost : option (list Card)) (targets : option (list Card)) (manacost : option (list Mana)) (gs : GameState) : GameState :=
match remove_card_costs gs [mkMana Blue 1] with
| Some gs' =>
  match targets with
    | Some (c :: _) =>
      match c.(permanent) with
      | Some p =>
        let new_card :=  tap c in
        let new_battlefield := new_card :: remove_card gs.(battlefield) c in
        mkGameState new_battlefield gs'.(hand) gs'.(library) gs'.(graveyard)
                    gs'.(exile) gs'.(opponent) gs'.(manapool) gs'.(stack)
                    gs'.(passive_abilities) gs'.(phase)
      | None => gs
      end
    | _ => gs
    end
| None => gs
end.

Definition freed_from_the_realm_ability_2 (target_cost : option (list Card)) (targets : option (list Card)) (manacost : option (list Mana)) (gs : GameState) : GameState :=
match remove_card_costs gs [mkMana Blue 1] with
| Some gs' =>
  match targets with
    | Some (c :: _) =>
      match c.(permanent) with
      | Some p =>
        let new_card :=  untap c in
        let new_battlefield := new_card :: remove_card gs.(battlefield) c in
        mkGameState new_battlefield gs'.(hand) gs'.(library) gs'.(graveyard)
                    gs'.(exile) gs'.(opponent) gs'.(manapool) gs'.(stack)
                    gs'.(passive_abilities) gs'.(phase)
      | None => gs
      end
    | _ => gs
    end
| None => gs
end.

Definition isochron_scepter_ability (target_cost : option (list Card)) (targets : option (list Card)) (manacost : option (list Mana)) (gs : GameState) : GameState :=
  match manacost with
  | Some cost =>
      match remove_card_costs gs cost with
      | Some gs_after_payment =>
          match target_cost with
          | Some [cost_card] =>
              match targets with
              | Some [target] =>
                  match target.(permanent) with
                  | Some p =>
                      match p.(artifact) with
                      | Some art =>
                          match art.(isochron) with
                          | Some inst =>
                              (* Taper la carte utilisée comme coût *)
                              let battlefield_after_cost :=
                                map (fun c => if eq_card c cost_card then tap c else c)
                                    gs_after_payment.(battlefield) in

                              (* Créer la copie et l’ajouter à la pile *)
                              let copied_card := mkCard None (Some inst) None [] "Isochron ability" 999 [] in
                              let new_stack := CardItem copied_card :: gs_after_payment.(stack) in

                              (* Créer le nouvel état du jeu *)
                              mkGameState
                                battlefield_after_cost
                                gs_after_payment.(hand)
                                gs_after_payment.(library)
                                gs_after_payment.(graveyard)
                                gs_after_payment.(exile)
                                gs_after_payment.(opponent)
                                gs_after_payment.(manapool)
                                new_stack
                                gs_after_payment.(passive_abilities)
                                gs_after_payment.(phase)
                          | None => gs
                          end
                      | None => gs
                      end
                  | None => gs
                  end
              | _ => gs
              end
          | _ => gs
          end
      | None => gs (* Impossible de payer le coût en mana *)
      end
  | None => gs (* Pas de coût en mana fourni *)
  end.

Definition unlock_mirror_room (target_cost : option (list Card)) 
                              (targets : option (list Card)) 
                              (manacost : option (list Mana)) 
                              (gs : GameState) : GameState :=
  match remove_card_costs gs [(mkMana Blue 1); (mkMana Generic 2)] with
  | None => gs
  | Some gs' =>
    match targets with
    | None => gs
    | Some [c'; to_copy'] =>
      match find_card_in_list c' gs.(battlefield) with
      | Some c =>
        match c.(permanent) with
        | None => gs
        | Some perm =>
          let unlocked := mkCard
                            (Some (mkPermanent
                              (perm.(Abilities))
                              [8]
                              (perm.(PassiveAbility))
                              (perm.(subtype))
                              (perm.(creature))
                              (perm.(enchantement))
                              (perm.(land))
                              (perm.(artifact))
                              (perm.(token))
                              (perm.(legendary))
                              false))
                            None
                            None
                            nil
                            "Mirror Room"
                            c.(id)
                            c.(keywords) in
          let gs1 := mirror_room_enter (Some [c; to_copy']) gs in
          let new_battlefield := unlocked :: (remove_card gs1.(battlefield) c) in
          mkGameState new_battlefield gs1.(hand) gs1.(library) gs1.(graveyard)
                    gs1.(exile) gs1.(opponent) gs1.(manapool) gs1.(stack)
                    gs1.(passive_abilities) gs1.(phase)
        end
      | _ => gs
      end
    | _ => gs
    end
  end.
  
Definition unlock_fractured_realm_room (target_cost : option (list Card)) 
                              (targets : option (list Card)) 
                              (manacost : option (list Mana)) 
                              (gs : GameState) : GameState :=
  match remove_card_costs gs [(mkMana Blue 1); (mkMana Generic 2)] with
  | None => gs
  | Some gs' =>
    match targets with
    | None => gs
    | Some [c'] =>
      match find_card_in_list c' gs.(battlefield) with
      | Some c =>
        match c.(permanent) with
        | None => gs
        | Some perm =>
          let unlocked := mkCard
                            (Some (mkPermanent
                              (perm.(Abilities))
                              nil
                              (Some AdditionalTrigger)
                              (perm.(subtype))
                              (perm.(creature))
                              (perm.(enchantement))
                              (perm.(land))
                              (perm.(artifact))
                              (perm.(token))
                              (perm.(legendary))
                              false))
                            None
                            None
                            nil
                            "Mirror Room // Fractured Realm (full unlocked)"
                            c.(id)
                            c.(keywords) in
          let new_battlefield := unlocked :: (remove_card gs.(battlefield) c) in
          mkGameState new_battlefield gs.(hand) gs.(library) gs.(graveyard)
                    gs.(exile) gs.(opponent) gs.(manapool) gs.(stack)
                    (update_passive_ability_in_dict gs.(passive_abilities) AdditionalTrigger (S (find_passive_ability_in_dict gs.(passive_abilities) AdditionalTrigger)))gs.(phase)
        end
      | _ => gs
      end
    | _ => gs
    end
  end.



Definition Dict_AA : list (nat * Activated_Ability) := [
(1, siege_zombie_ability);
(2, clock_of_omens_ability);
(3, sanctum_weaver_ability);
(4, freed_from_the_realm_ability_1);
(5, freed_from_the_realm_ability_2);
(6, isochron_scepter_ability);
(7, unlock_mirror_room);
(8, unlock_fractured_realm_room)].



End abilities_effects.
Export abilities_effects.