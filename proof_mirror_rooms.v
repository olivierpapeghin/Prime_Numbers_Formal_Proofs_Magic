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
Require Import Land_cards_def.
Import Land_cards.
Require Import game_actions.
Import game_actions.

Local Open Scope string_scope.

Module proof_mirror_room.

Definition initial_gamestate : GameState := 
  mkGameState
  []
  [(abuelos_awakening 1)]
  nil (* La bibliothèque est vide *)
  [(mirror_room_fractured_realm_locked 1)] (* Le cimetière est vide *)
  nil (* L'exil est vide *)
  20 (* L'opposant est à 20 PV *)
  [mkMana White 20; mkMana Blue 100; mkMana Black 20; mkMana Red 20; mkMana Green 200; mkMana Generic 200] (* On se donne assez de mana pour pouvoir lancer le sort *)
  nil (* La pile est vide *)
  DefaultListPassiveAbility  
  MainPhase1.
  
Definition gs1 : GameState := Resolve (Cast (abuelos_awakening 1) initial_gamestate) 1 (Some [mirror_room_fractured_realm_locked 1]).
Definition gs2 : GameState := activate_ability 7 None (Some [mkMana Generic 1])
      (Some [mirror_room_fractured_realm_locked 1; mirror_room_fractured_realm_locked 1])
      (mirror_room_fractured_realm_locked 1) Dict_AA gs1.

Definition mirr_token (id : nat) :=
  mkCard
    (match (mirror_room_fractured_realm_locked 2).(permanent) with
     | None => None
     | Some p =>
         Some (mkPermanent
                 p.(Abilities)
                 p.(ListActivated)
                 p.(PassiveAbility)
                 p.(subtype)
                 p.(creature)
                 p.(enchantement)
                 p.(land)
                 p.(artifact)
                 true (* token := true *)
                 p.(legendary)
                 false) (* tapped := false *)
     end)
    None
    None
    [] (* Pas de coût de mana, c’est un token *)
    (mirror_room_fractured_realm_locked 2).(name)
    id
    [].

Compute gs2.
Compute (mirror_room_fractured_realm_locked 2).

(* activate_ability 7 None (Some [(mkMana Generic 1)]) ( Some [(mirror_room_fractured_realm_locked 1); (mirror_room_fractured_realm_locked 1)]) (mirror_room_fractured_realm_locked 1) Dict_AA gs1.
activate_ability 8 None (Some [(mkMana Generic 1)]) ( Some [(mirror_room 1)]) (mirror_room 1) Dict_AA gs2. *)

Lemma has_fractured_mirror_copy :
  In (mirr_token 2) gs2.(battlefield).
Proof.
  simpl. right. left. reflexivity.
Qed.

Definition count_mirror_room (gs : GameState) : nat :=
  let is_mirror_realm_card (n : string) : bool :=
                String.eqb n "Mirror Room // Fractured Realm (full locked)" ||
                String.eqb n "Mirror Room // Fractured Realm (full unlocked)" ||
                String.eqb n "Mirror Room" ||
                String.eqb n "Fractured Realm" in
  let cards : list string :=
                map (fun c => c.(name)) (List.app gs.(battlefield) gs.(hand)) in

  let count_existing_copies : nat :=
                List.length (filter is_mirror_realm_card cards) in
  count_existing_copies.

(* On définit l'étape qu'on doit répéter indéfiniment *)
Inductive step : GameState -> GameState -> Prop :=
| step_mirror :
    forall gs gs_1 card,
      activate_ability 7 None None
      (Some [card; mirror_room 1])
      (card) Dict_AA gs = gs_1 ->
      step gs gs_1.

(* On peut maintenant définir la boucle infinie *)
CoInductive can_loop_infinitely : GameState -> Prop :=
| loop_step :
    forall gs gs',
      step gs gs' ->
      can_loop_infinitely gs' ->
      can_loop_infinitely gs.

(* On définit une proposition récursive qui va vérifier qu'on peut générer des mirrors_rooms*)
CoFixpoint infinite_loop (gs : GameState) : can_loop_infinitely gs :=
  
  let card := (mirror_room_fractured_realm_locked (count_mirror_room gs))  in
  let gs_1 := activate_ability 7 None None
      (Some [card; mirror_room 1])
      (card) Dict_AA gs in
  loop_step gs gs_1 (step_mirror gs gs_1 card eq_refl) (infinite_loop gs_1).

(* Il ne reste plus qu'à savoir si l'état initial défini plus haut peut boucler à l'infini *)
Theorem infinite_mirror_room_possible :
  can_loop_infinitely gs2.
Proof.
  exact (infinite_loop gs2).
Qed.

End proof_mirror_room.
Export proof_mirror_room.


