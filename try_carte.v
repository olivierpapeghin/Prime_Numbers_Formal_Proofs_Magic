From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Program.Equality.
Require Import List String.

Import ListNotations.

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
  producing : ManaColor
}.


(* Définition d'une carte permanente *)
Record Permanent := mkPermanent {
  ListOnCast : list nat;
  ListOnDeath : list nat;
  ListOnPhase : list nat;
  creature : option Creature;
  enchantement : option Enchantement;
  land : option Land;
  artifact : option Artifact;
  token : bool;
  legendary : bool;
}.

Record Sorcery := mkSorcery {
  Spell : list nat;
}.

(* Définition d'une carte instantanée *)
Record Instant := mkInstant {
  spell : list nat;
}.

(* Définition d'une carte *)
Record Card := mkCard {
  permanent : option Permanent;
  instant : option Instant;
  sorcery : option Sorcery;
  manacost : list Mana;
  name : string
}.

Inductive CardOrPair :=
| CardItem : Card -> CardOrPair
| PairItem : string -> nat -> CardOrPair.


Record GameState := mkGameState {
  battlefield : list Permanent;
  hand : list Card;
  library : list Card;
  graveyard : list Card;
  exile : list Card;
  opponent : nat;
  manapool : list Mana;
  stack : list CardOrPair;
}.

(* Définition d'une capacité *)
Record Ability := mkAbility {
  ability : GameState -> GameState;
  activation_condition : GameState -> bool
}.

(* Définition d'un dictionnaire de capacités *)
Definition AbilityDict := list (nat * Ability).


Definition get_list_on_cast_from_stack (cop : CardOrPair) : option (list nat) :=
  match cop with
  | CardItem card =>
    match card.(permanent) with
    | None => None
    | Some p => Some p.(ListOnCast)
    end
  | PairItem _ _ => None
  end.

(* Fonction pour obtenir le champ token d'une carte *)
Definition get_token (c : Card) : option bool :=
  match c.(permanent) with
  | None => None
  | Some p => Some p.(token)
  end.

(* Fonction pour obtenir une valeur par défaut si l'option est None *)
Definition get_token_default (c : Card) (default : bool) : bool :=
  match get_token c with
  | None => default
  | Some token_value => token_value
  end.

(* Exemple d'utilisation avec if *)
Definition check_token (c : Card) : bool :=
  let token_value := get_token_default c true in
  if token_value then true else false.

(* Fonction pour retrouver une capacité par sa clé *)
Fixpoint find_ability_by_key (dict : AbilityDict) (key : nat) : option Ability :=
  match dict with
  | nil => None
  | (k, ability) :: rest =>
    if Nat.eqb k key then Some ability else find_ability_by_key rest key
  end.

(* Fonction pour parcourir ListOnCast et rechercher toutes les capacités *)
Fixpoint find_abilities_from_list (dict : AbilityDict) (keys : list nat) : list Ability :=
  match keys with
  | nil => nil
  | key :: rest =>
    match find_ability_by_key dict key with
    | None => find_abilities_from_list dict rest
    | Some ability => ability :: find_abilities_from_list dict rest
    end
  end.

Definition exemple_crea : Creature := mkCreature 2 2.

(* Exemple de création d'une carte permanente *)
Definition exemple_perm : Permanent := mkPermanent [1] nil nil (Some exemple_crea) None None None false false.

Definition example_ability : Ability :=
  mkAbility (fun gs => gs) (fun gs => true).

(* Exemple de dictionnaire de capacités *)
Definition example_dict : AbilityDict :=
  (1, example_ability) :: (2, example_ability) :: nil.

(* Exemple de création d'une carte avec une carte permanente *)
Definition exemple_card : Card := mkCard (Some exemple_perm) None None [mkMana White 2] "snoopy" .

Definition ex_cardstack : CardOrPair := CardItem exemple_card.


Definition abilities :=
  match get_list_on_cast_from_stack ex_cardstack with
  | None => nil
  | Some keys => find_abilities_from_list example_dict keys
  end.
Compute abilities.

