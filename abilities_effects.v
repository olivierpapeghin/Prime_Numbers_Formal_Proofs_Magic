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
Require Import passive_ability.
Import passive_ability.

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
            let new_token :=
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
                        true (* token := true *)
                        p.(legendary)
                        false)) (* tapped := false *)
                None
                None
                [] (* Pas de coût de mana, c’est un token *)
                (String.append "Molten Copy of " target.(name))
                998 (* ID fictif temporaire *)
                ["Haste"]
            in
            let new_token1 :=
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
                        true (* token := true *)
                        p.(legendary)
                        false)) (* tapped := false *)
                None
                None
                [] (* Pas de coût de mana, c’est un token *)
                (String.append "Molten Copy of " target.(name))
                999 (* ID fictif temporaire *)
                ["Haste"]
            in
            if Nat.ltb 0 (find_passive_ability_in_dict gs.(passive_abilities) DoubleToken) then
              let new_battlefield := new_token1 :: new_token :: gs.(battlefield) in
              let updated_gs := mkGameState
              new_battlefield gs.(hand) gs.(library) gs.(graveyard)
              gs.(exile) gs.(opponent) gs.(manapool)
              gs.(stack) gs.(passive_abilities) gs.(phase)
            in updated_gs
            else 
              let new_battlefield := new_token :: gs.(battlefield) in  
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

Definition desecration_elemental (targets : option (list Card)) (gs : GameState) : GameState :=
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
  gs.

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
  | Some [c'] =>
    match find_card_in_list c' gs.(battlefield) with
    | None => gs
    | Some c =>
      match c.(permanent) with
      | None => gs
      | Some perm =>
        match perm.(creature) with
        | None => gs
        | Some crea =>
          match get_base_card c 99 with
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
              new_gs
            end
          end
        end
      end
    end
  | _ => gs
  end. 

(* Définition des sous-dictionnaires *)
Definition OnCast : Dict := [(1,birgi_ability)].
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
gs.



Definition Dict_AA : list (nat * Activated_Ability) := [
(1, siege_zombie_ability);
(2, clock_of_omens_ability);
(3, sanctum_weaver_ability);
(4, freed_from_the_realm_ability_1);
(5, freed_from_the_realm_ability_2);
(6, isochron_scepter_ability)].



End abilities_effects.
Export abilities_effects.