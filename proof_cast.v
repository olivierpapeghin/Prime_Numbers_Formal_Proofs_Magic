From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Program.Equality.
Require Import List String.
From Coq Require Import String.

Import ListNotations.
Open Scope list_scope.
Local Open Scope string_scope.

Require Import type_definitions.
Import type_definition.
Require Import utility_functions.
Import utility_function.

(* Définition des différentes fonctions pour jouer un sort*)
Definition Cast (c:Card) (gs:GameState) : (GameState) :=
  let cost := c.(manacost) in
  let pool := gs.(manapool) in
  if Can_Pay cost pool && card_in_list c gs.(hand) then
    let new_pool := fold_left remove_mana cost pool in
    let new_hand := remove_card gs.(hand) c in
    let new_stack := CardItem c :: gs.(stack) in
    let new_gs := mkGameState gs.(battlefield) new_hand gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) new_pool new_stack in
    (new_gs)
  else
    (gs)
  .

(* On peut déjà vérifer que toutes les étapes marchent bien en testant si un cast est bien fonctionnel *)

(* Instanciation de la carte *)
Definition colossal_dreadmaw : Card := 
  mkCard 
  (Some (mkPermanent (* Est un permanent *)
    nil
    nil
    ["Dinosaur"]
    (Some (mkCreature 6 6)) (* Est une créature 6/6*)
    None (* N'est pas un enchantement *)
    None (* N'est pas un artifact *)
    None (* N'est pas une land *)
    false (* N'est pas un token *)
    false (* N'est pas tapped *)
    false)) (* N'est pas légendaire *)
  None (* N'est pas un instant *)
  None (* N'est pas un sorcery *)
  [mkMana Green 1; mkMana Generic 5] (* Coûte 5 mana générique et 1 mana vert *)
  "Colossal Dreadmaw"
  0 (* Nom de la carte *)
  nil.

(* Instanciation du GameState initial *)
Definition initial_gamestate : GameState := 
  mkGameState
  nil (* Le champ de bataille est vide *)
  [colossal_dreadmaw]
  nil (* La bibliothèque est vide *)
  nil (* Le cimetière est vide *)
  nil (* L'exil est vide *)
  20 (* L'opposant est à 20 PV *)
  [mkMana White 20; mkMana Blue 20; mkMana Black 20; mkMana Red 20; mkMana Green 20] (* On se donne assez de mana pour pouvoir lancer le sort *)
  nil (* La pile est vide *).

Definition gamestate_proof1 : GameState := Cast colossal_dreadmaw initial_gamestate.

Compute gamestate_proof1. (* On peut vérifier à la main que l'effet attendu est bien là *)

Definition list_length := Coq.Lists.List.length.

(* On va vérifier via un théorème qu'on n'a plus de Colossal Dreadmaw en main et un dans la stack*)
Theorem proof1 :
  list_length Card gamestate_proof1.(hand) = 0 /\
  list_length CardOrPair gamestate_proof1.(stack) = 1.
Proof.
  split.  (* Sépare l'objectif en deux sous-objectifs *)
  - (* Première partie : la main est vide *)
    simpl. (* Simplifie l'expression si possible *)
    reflexivity. (* Si l'égalité est triviale, utilise reflexivity *)
  - (* Deuxième partie : la pile contient un élément *)
    simpl.
    reflexivity.
Qed.

(* On va maintenant resolve la pile pour que notre carte arrive sur le champ de bataille *)
Definition Resolve (gs : GameState) : GameState :=
  match last_option gs.(stack) with
  | Some (CardItem c) => (* Si c'est une carte *)
      match card_type c with
      | PermanentType => (* Si c'est un permanent *)
        let new_stack : list CardOrPair:= remove_last gs.(stack) in
        let new_battlefield : list Card := c :: gs.(battlefield) in
        mkGameState new_battlefield gs.(hand) gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) gs.(manapool) new_stack
      | InstantType => gs (* On ne gère pas encore cette éventualité *)
      | SorceryType => gs (* On ne gère pas encore cette éventualité *)
      | UnknownType => gs (* Si on ne reconnait pas le type de la carte on ne fait rien *)
      end
  | Some (PairItem i d) => gs (* Si le dernier élément est une capacité, on ne la traite pas encore *)
  | None => gs (* Si la stack est vide, on ne fait rien *)
  end.

Definition gamestate_proof2 : GameState := Resolve gamestate_proof1.

Compute gamestate_proof2.

(* On va vérifier via un théorème qu'on n'a plus de Colossal Dreadmaw en main et un dans la stack*)
Theorem proof2 :
  list_length CardOrPair gamestate_proof2.(stack) = 0 /\
  list_length Card gamestate_proof2.(battlefield) = 1.
Proof.
  split.  (* Sépare l'objectif en deux sous-objectifs *)
  - (* Première partie : la main est vide *)
    simpl. (* Simplifie l'expression si possible *)
    reflexivity. (* Si l'égalité est triviale, utilise reflexivity *)
  - (* Deuxième partie : la pile contient un élément *)
    simpl.
    reflexivity.
Qed.
