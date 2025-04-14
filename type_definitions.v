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

Inductive Phase :=
  | BeginningPhase
  | MainPhase1
  | CombatPhase
  | MainPhase2
  | EndingPhase.

Record Sorcery := mkSorcery {
  Spell : list nat;
}.

Record Instant := mkInstant {
  spell : list nat;
}.

Record Creature := mkCreature {
  power : nat;
  toughness : nat
}.

Record Enchantement := mkEnchantement {
  aura : option (string * nat) (* On retrouve la carte à laquelle est rattachée l'aura via son nom et son id *)
}.

Record Artifact := mkArtifact {
  isochron : option Instant
}.

Record Land := mkLand {
  producing : Mana;
}.

(* Définition des clé pour les différentes abilitées passives *)
Inductive PassiveKey :=
  | AllSaprolings
  | AllFlash
  | DoubleToken
  | AdditionalTrigger
  | NoLegendaryRule
  | SaprolingsLands
  | LandPlayed.

(* Définition du dict pour indiquer si les abilitées passives sont activées *)
Definition PassiveAbilityDict := list (PassiveKey * nat).

(* dict de base pour indiquer si les abilitées passives sont activées *)
Definition DefaultListPassiveAbility : PassiveAbilityDict := [(AllSaprolings, 0); (AllFlash, 0); (DoubleToken, 0); (AdditionalTrigger, 0); (NoLegendaryRule, 0);(SaprolingsLands, 0); (LandPlayed, 0)].

Record Permanent := mkPermanent {
  Abilities : list (nat * nat);
  ListActivated : list nat;
  PassiveAbility : option PassiveKey;
  subtype : list string;
  creature : option Creature;
  enchantement : option Enchantement;
  land : option Land;
  artifact : option Artifact;
  token : bool;
  legendary : bool;
  tapped : bool;
}.

Record Card := mkCard {
  permanent : option Permanent;
  instant : option Instant;
  sorcery : option Sorcery;
  manacost : list Mana;
  name : string;
  id : nat;
  keywords : list string
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
  passive_abilities : PassiveAbilityDict;
  phase : Phase;
}.

(* Définition générale d'une capacité *)
Definition Ability := option (list Card) -> GameState -> GameState.

(* Définition d'une capacité à activer *)
Definition Activated_Ability := option (list Card) -> option (list Card) -> option (list Mana) -> GameState -> GameState.

(* Définition d'une liste de paires clé-valeur pour un dictionnaire *)
Definition Dict := list (nat * Ability).


Definition Initial_GS : GameState := mkGameState nil nil nil nil nil 20 [mkMana Green 0; mkMana Red 0; mkMana Blue 0 ;mkMana White 0 ; mkMana Black 0 ;mkMana Generic 0] nil DefaultListPassiveAbility BeginningPhase. 

End type_definition.
Export type_definition.