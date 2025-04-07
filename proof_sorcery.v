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

Definition default_card : Card := mkCard None None None nil "Default" 0 [].

(* On va simuler le cast d'un sorcery : Abuelo's Awakening qui ramène un enchantement non-aura ou un artefact du cimetière sur le champ de bataille *)
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

(* Fonction pour trouver une capacité par sa clé dans un sous-dictionnaire *)
Fixpoint find_ability_in_sub_dict (sub_dict : Dict) (key2 : nat) : option Ability :=
  match sub_dict with
  | nil => None
  | (k, ability) :: rest =>
    if Nat.eqb k key2 then Some ability else find_ability_in_sub_dict rest key2
  end.

(* Fonction pour activer une seule capacité à partir d'une clé avec des cibles *)
Definition activate_spell (spell_abilities : Dict) (key : nat) (targets : option (list Card)) (gs : GameState) : GameState :=
  match find_ability_in_sub_dict spell_abilities key with
  | None => gs (* Aucune capacité trouvée, retourner l'état du jeu inchangé *)
  | Some ability =>
    let new_gs := ability targets gs in
    new_gs (* Retourner l'état du jeu mis à jour après activation de la capacité *)
  end.

Definition abuelos_awakening : Card := mkCard
  None
  None
  (Some (mkSorcery [73]))
  [mkMana White 1; mkMana Generic 2]
  "Abuelo's Awakening"
  1
  [].

Definition mirror_gallery : Card := mkCard
  (Some (mkPermanent (* Est un permanent *)
  nil
  nil
  None
  []
  None
  None
  None
  (Some mkArtifact)
  false
  false
  false))
  None 
  None
  [mkMana Generic 5]
  "Mirror Gallery"
  2
  [].

Definition initial_gamestate : GameState := 
  mkGameState
  nil (* Le champ de bataille est vide *)
  [abuelos_awakening]
  nil (* La bibliothèque est vide *)
  [mirror_gallery] (* Le cimetière est vide *)
  nil (* L'exil est vide *)
  20 (* L'opposant est à 20 PV *)
  [mkMana White 20; mkMana Blue 20; mkMana Black 20; mkMana Red 20; mkMana Green 20] (* On se donne assez de mana pour pouvoir lancer le sort *)
  nil (* La pile est vide *)
  nil  
  MainPhase1.

Compute match mirror_gallery.(permanent) with
| Some p => permanent_type p
| _ => UnknownPermanentType
end.

Compute abuelos_awakening_ability (Some [mirror_gallery]) initial_gamestate. (* On vérifie que l'abilité marche bien comme attendu *)

Definition non_permanent_abilities : Dict := [(73, abuelos_awakening_ability)].

(* Définition des différentes fonctions pour jouer un sort*)
Definition Cast (c:Card) (gs:GameState) : (GameState) :=
  let cost := c.(manacost) in
  let pool := gs.(manapool) in
  if Can_Pay cost pool && card_in_list c gs.(hand) then
    let new_pool := fold_left remove_mana cost pool in
    let new_hand := remove_card gs.(hand) c in
    let new_stack := CardItem c :: gs.(stack) in
    let new_gs := mkGameState gs.(battlefield) new_hand gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) new_pool new_stack gs.(passive_abilities) gs.(phase) in
    (new_gs)
  else
    (gs)
  .

Definition Resolve (gs : GameState) (key : nat) (targets : option (list Card)) : GameState :=
  match last_option gs.(stack) with
  | Some (CardItem c) => (* Si c'est une carte *)
      match card_type c with
      | PermanentType => (* Si c'est un permanent *)
        let new_stack : list CardOrPair:= remove_last gs.(stack) in
        let new_battlefield : list Card := c :: gs.(battlefield) in
        mkGameState new_battlefield gs.(hand) gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) gs.(manapool) new_stack gs.(passive_abilities) gs.(phase)
      | InstantType => gs (* On ne gère pas encore cette éventualité *)
      | SorceryType => 
        let new_gs : GameState := activate_spell non_permanent_abilities key targets gs in
        let new_stack : list CardOrPair:= remove_last gs.(stack) in
        let new_graveyard : list Card := c :: new_gs.(graveyard) in
        mkGameState new_gs.(battlefield) new_gs.(hand) new_gs.(library) new_graveyard new_gs.(exile) new_gs.(opponent) new_gs.(manapool) new_stack gs.(passive_abilities) gs.(phase)
      | UnknownType => gs (* Si on ne reconnait pas le type de la carte on ne fait rien *)
      end
  | Some (PairItem i d) => gs (* Si le dernier élément est une capacité, on ne la traite pas encore *)
  | None => gs (* Si la stack est vide, on ne fait rien *)
  end.

(* Preuve *)
(* On veut prouver que l'abilité de la carte Abuelo's Awakening fonctionne correctement tant que
   la carte passée en paramètre est de type Artefact ou Enchantement et qu'elle n'a pas 
   de sous type Aura, de plus elle doit se trouver dans le cimetière du GameState *)
Lemma abuelos_effect : 
  forall (gs : GameState) (c : Card) (p : Permanent), (* On définit les variables *)
  In c gs.(graveyard) -> (* La carte cible est dans le cimetière du gamestate *)
  c.(permanent) = Some p -> (* Contrainte de la cible *)
  (permanent_type p = ArtifactType \/ permanent_type p = EnchantmentType) ->
  ~ In "aura" p.(subtype) ->
  let new_gs := abuelos_awakening_ability (Some [c]) gs in (* On résaut l'abitlité *)
  In (mkCard (Some (mkPermanent p.(Abilities) p.(ListActivated) p.(PassiveAbility)
                   ("Spirit" :: p.(subtype))
                   (Some (mkCreature 1 1)) p.(enchantement)
                   p.(land) p.(artifact) true p.(legendary) false))
             None None c.(manacost) c.(name) c.(id) c.(keywords))
     new_gs.(battlefield) (* On vérifie qu'on a bien le résultat attendu dans le gamestate *)
  /\ ~ In c new_gs.(graveyard). (* Enfin on vérifie que la cible a quitté le cimetière *)







      