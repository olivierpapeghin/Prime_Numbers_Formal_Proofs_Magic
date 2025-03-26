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

Module type_definition.

(* Définitions essentielles *)
Inductive Lands := Plains | Island | Swamp | Mountain | Forest.
Inductive ManaColor := White | Blue | Black | Red | Green | Generic.

Record Mana := mkMana {
  color : ManaColor;
  quantity : nat
}.

Record Creature := mkCreature {
  power : nat;
  toughness : nat
}.

Record Enchantement := mkEnchantement {
  
}.

Record Artifact := mkArtifact {

}.

Record Land := mkLand {
  producing : Mana;
}.

Record Permanent := mkPermanent {
  ListOnCast : list nat;
  ListOnDeath : list nat;
  ListOnPhase : list nat;
  ListActivated : list nat;
  creature : option Creature;
  enchantement : option Enchantement;
  land : option Land;
  artifact : option Artifact;
  token : bool;
  legendary : bool;
  tapped : bool
}.

Record Sorcery := mkSorcery {
  Spell : list nat;
}.

Record Instant := mkInstant {
  spell : list nat;
}.

Record Card := mkCard {
  permanent : option Permanent;
  instant : option Instant;
  sorcery : option Sorcery;
  manacost : list Mana;
  name : string
}.

(*Définition d'un type spécial stack *)
Inductive CardOrPair :=
| CardItem : Card -> CardOrPair
| PairItem : string -> nat -> CardOrPair.

(* Définition de l'état du jeu *)
Record GameState := mkGameState {
  battlefield : list Card;
  hand : list Card;
  library : list Card;
  graveyard : list Card;
  exile : list Card;
  opponent : nat;
  manapool : list Mana;
  stack : list CardOrPair;
}.

(* Définition générale d'une capacité *)
Definition Ability := option (list Card) -> GameState -> GameState.

(* Définition d'une capacité à activer *)
Record ActivatedAbility := mkActivatedAbility {
  cost_mana : option (list Mana);
  cost_cards : option (list Card);
  effect : option (list Card) -> GameState -> GameState (* Effet de la capacité *)
}.

(* Définition d'une liste de paires clé-valeur pour un dictionnaire *)
Definition Dict := list (nat * Ability).

End type_definition.
Export type_definition.