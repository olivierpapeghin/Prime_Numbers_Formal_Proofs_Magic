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

Definition tap (gs : GameState) (targets : list Card) : GameState :=
  let new_battlefield := fold_left (fun gs' c =>
      match c.(permanent) with
      | Some perm => gs'
      
      | None => gs'
      end
    ) targets gs.(battlefield) in
  gs.


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

Definition non_permanent_abilities : Dict := [(1, abuelos_awakening_ability)].

(*-----------------------------------------Abilités déclenchées----------------------------------------------*)

Definition birgi_ability (targets : option (list Card)) (gs : GameState) : GameState :=
  add_mana gs Red 1.

(* Définition des sous-dictionnaires *)
Definition OnCast : Dict := [(1,birgi_ability)].
Definition OnPhase : Dict := nil.
Definition OnDeath : Dict := nil.
Definition OnEnter : Dict := nil.


(* Définition du dictionnaire principal avec des clés de type string *)
Definition Triggered_Abilities : list (nat * Dict) :=
  ( 1 , OnCast) :: (2 , OnPhase) :: (3 , OnDeath) :: (4 , OnEnter) :: nil.

(*-----------------------------------------Abilités activées----------------------------------------------*)

Definition siege_zombie_ability (target_cost : option (list Card)) (targets : option (list Card)) (manacost : option (list Mana)) (gs : GameState) : GameState :=
  (* On vérifie qu'il y a bien trois cibles dans la liste target_cost *)
  match target_cost with
  | Some tc =>
    match length tc with
    | 3 => (* Il y a le bon nombre de cibles on peut les tapper et infliger 1 dégât à l'adversaire *)
    let new_battlefield : list Card := fold_left tap target_cost gs.(battlefield) in
    let new_lp : nat := gs.(opponent) - 1 in
    (mkGameState new_battlefield gs.(hand) gs.(library) gs.(graveyard) gs.(exile) new_lp gs.(manapool) gs.(stack) gs.(passive_abilities) gs.(phase))
    | _ => gs (* Il n'y a pas le bon nombre de cibles, on ne fait rien *)
    end
  | None => gs
  end.

Definition Dict_AA : list (nat * Activated_Ability) := [(1, siege_zombie_ability)].

End abilities_effects.
Export abilities_effects.