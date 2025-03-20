From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Program.Equality.
Require Import List String.

Import ListNotations.

(* Inductive for types in Records *)
Inductive CardTypes := permanent | instant | sorcery .

Inductive PermanentTypes := creature | enchantment | artifact | token | legendary | land.

Inductive PermanentSubTypes := aura | room.

Inductive ManaColor := White | Blue | Black | Red | Green | Generic.

Inductive Events := OnDeath | OnCast | OnPhase.

(* Record for each object *)
Record Mana := {
  color : ManaColor;
  quantity : nat
}.

Record Card := {
  type : CardTypes;
  name : string;
  mana_cost : list Mana;
}.

Definition ManaPool := list Mana.

Record GameState := {
  battlefield : list Card;
  mana_pool : ManaPool;
  opponent : nat;
  hand : list Card;
  library : list Card;
  graveyard : list Card;
  exile : list Card;
  stack : list (Card * nat); (* nat correspond au fait de prendre la carte ou son Ability *)
}.

Record Ability := {
  ability : GameState -> GameState;
  activation_condition : GameState -> bool; (* Condition d'activation *)
}.

Record TriggeredAbility := {
  trigger_ability : Ability;
  trigger_event : Events;
}.

Record Permanent := {
  permanent_card : Card;
  permanent_type : list PermanentTypes;
  permanent_subtype : list PermanentSubTypes;
  tapped_permanent : bool;
  perm_triggered_abilities : list TriggeredAbility; 
}.

Record Instant := {
  instant_card : Card;
  instant_abilities : list Ability
}.

Record Sorcery := {
  sorcery_card : Card;
  sorcery_abilities : list Ability
}.

(* On enregistre tous les permanents joués *)
Definition PermanentRegistry := list Permanent.

Definition GameHistory := list GameState.
