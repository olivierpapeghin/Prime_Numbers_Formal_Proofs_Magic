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
Inductive ManaColor := White | Blue | Black | Red | Green | Generic.

Record Mana := mkMana {
  color : ManaColor;
  quantity : nat
}.

(* Définition du type de carte *)
Inductive CardType :=
  | PermanentType
  | InstantType
  | SorceryType
  | UnknownType. (* Si aucun type n'est défini *)

Inductive PermanentCardType :=
  | CreatureType
  | ArtifactType
  | EnchantmentType
  | LandType
  | UnknownPermanentType.

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
  Abilities : list (nat * nat);
  ListActivated : list nat;
  subtype : list string;
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
  name : string;
  id : nat
}.

(*Définition d'un type spécial stack *)
Inductive CardOrPair :=
| CardItem : Card -> CardOrPair
| PairItem : nat -> nat -> CardOrPair.

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

Definition Initial_GS : GameState := mkGameState nil nil nil nil nil 20 [mkMana Green 0; mkMana Red 0; mkMana Blue 0 ;mkMana White 0 ; mkMana Black 0] nil. 

End type_definition.
Export type_definition.