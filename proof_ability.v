From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Program.Equality.
Require Import List String.

Import ListNotations.

(* Types énumérés pour les cartes et les couleurs de mana *)
Inductive CardTypes := permanent | instant | sorcery.
Inductive PermanentTypes := creature | enchantment | artifact | token | legendary | land.
Inductive EnchantmentTypes := aura | room.
Inductive ManaColor := White | Blue | Black | Red | Green | Generic.

(* Définition de Mana *)
Record Mana := mkMana {
  color : ManaColor;
  quantity : nat
}.

(* Définition de Card *)
Record Card := mkCard {
  type : CardTypes;
  name : string;
  mana_cost : list Mana
}.

(* Définition de ManaPool *)
Definition ManaPool := list Mana.

(* Définition de GameState *)
Record GameState := mkGameState {
  battlefield : list Card;
  mana_pool : ManaPool;
  opponent : nat;
  hand : list Card;
  library : list Card;
  graveyard : list Card;
  exile : list Card;
  stack : list (Card * nat)
}.

(* Définition d'Ability *)
Record Ability := mkAbility {
  ability : GameState -> GameState;
  activation_condition : GameState -> bool
}.

(* Définition de TriggeredAbility *)
Record TriggeredAbility := make_TA {
  Index : nat;
  TA : Ability
}.

(* Définition de OnCast *)
Definition OnCast := list TriggeredAbility.

(* Fonction pour trouver une TriggeredAbility dans une liste OnCast *)
Fixpoint Find_OCTA (OC : OnCast) (i : nat) : option Ability :=
  match OC with
  | nil => None
  | (make_TA Index TA) :: rest =>
    if Nat.eqb Index i then Some TA else Find_OCTA rest i
  end.

(* Exemple d'une capacité qui ajoute du mana rouge *)
Definition add_red_mana_ability : Ability :=
  mkAbility
    (fun gs =>
      let new_mana_pool := (mkMana Red 1) :: gs.(mana_pool) in
      mkGameState gs.(battlefield) new_mana_pool gs.(opponent) gs.(hand) gs.(library) gs.(graveyard) gs.(exile) gs.(stack)
    )
    (fun gs => true). (* Toujours activable *)

(* Exemple de carte *)
Definition example_card : Card := mkCard permanent "Goblin" [mkMana Red 1].

(* Exemple d'état de jeu initial *)
Definition initial_game_state : GameState := mkGameState
  [] (* battlefield *)
  [] (* mana_pool *)
  0 (* opponent *)
  [example_card] (* hand *)
  [] (* library *)
  [] (* graveyard *)
  [] (* exile *)
  []. (* stack *)
(* Définition d'un dictionnaire de TriggeredAbility *)
Definition TriggeredAbilityDict := list (nat * Ability).

(* Fonction pour trouver une Ability dans le dictionnaire par son index *)
Fixpoint find_ability_by_index (dict : TriggeredAbilityDict) (index : nat) : option Ability :=
  match dict with
  | nil => None
  | (i, ability) :: rest =>
    if Nat.eqb i index then Some ability else find_ability_by_index rest index
  end.

(* Exemple d'utilisation *)
(* Création d'un dictionnaire avec une capacité *)
Definition example_dict : TriggeredAbilityDict :=
  (0, add_red_mana_ability) :: nil.

(* Recherche de la capacité avec l'index 0 *)
Example test_find_ability :
  find_ability_by_index example_dict 0 = Some add_red_mana_ability.
Proof. reflexivity. Qed.


