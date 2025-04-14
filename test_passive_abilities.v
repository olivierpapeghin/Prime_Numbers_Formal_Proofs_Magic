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
Require Import abilities_effects.
Import abilities_effects.
Require Import passive_ability.
Import passive_ability.
Require Import game_actions.
Import game_action.
Require Import Land_cards_def.
Import Land_cards.

Definition initial_gamestate : GameState := 
  mkGameState
  [(colossal_dreadmaw 1); (colossal_dreadmaw 2)]
  [(colossal_dreadmaw 3); (leyline_of_transformation 1); (life_and_limb 1)]
  nil (* La bibliothèque est vide *)
  [] (* Le cimetière est vide *)
  nil (* L'exil est vide *)
  20 (* L'opposant est à 20 PV *)
  [mkMana White 20; mkMana Blue 20; mkMana Black 20; mkMana Red 20; mkMana Green 20; mkMana Generic 20] (* On se donne assez de mana pour pouvoir lancer le sort *)
  nil (* La pile est vide *)
  DefaultListPassiveAbility  
  MainPhase1.

Definition gs2 : GameState := Resolve (Cast (leyline_of_transformation 1) initial_gamestate) 0 None.

Definition gs3 : GameState := Resolve (Cast (life_and_limb 1) gs2) 0 None.
Compute Resolve (Cast (colossal_dreadmaw 3) gs3) 0 None.


Definition birgiSaprolings (id : nat) : Card := 
  mkCard 
  (Some (mkPermanent (* Est un permanent *)
    [(1,1)] (* La liste des capacités déclenchées *)
    nil
    None
    ["God"%string; "Saproling"%string]
    (Some (mkCreature 3 3)) (* Est une créature 6/6*)
    None (* N'est pas un enchantement *)
    None (* N'est pas un artifact *)
    None (* N'est pas une land *)
    false (* N'est pas un token *)
    true (* Est légendaire *)
    false)) (* N'est pas tapped *)
  None (* N'est pas un instant *)
  None (* N'est pas un sorcery *)
  [mkMana Red 1; mkMana Generic 2]
  "Birgi, God of Storytelling (and saprolings)"
  id
  nil.
.



