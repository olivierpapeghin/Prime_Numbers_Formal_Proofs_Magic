From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Program.Equality.
Require Import List String.

Import ListNotations.

Inductive Lands := Plain | Ocean | Swamp | Mountain | Forest.
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
  producing : Lands;
}.

(* Fonction pour mapper un Lands à un ManaColor *)
Definition land_to_mana_color (land : Lands) : ManaColor :=
  match land with
  | Plain => White
  | Ocean => Blue
  | Swamp => Black
  | Mountain => Red
  | Forest => Green
  end.

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
  tapped : bool
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

Definition check_token (c : Card) : bool :=
  let token_value := get_token_default c true in
  if token_value then true else false.

(* Fonction pour retrouver une capacité par sa clef *)
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

Definition ex_land : Land := mkLand Plain.

Definition exemple_crea : Creature := mkCreature 2 2.

(* Exemple de création d'une carte permanente *)
Definition exemple_perm : Permanent := mkPermanent [1] nil nil None None (Some ex_land) None false false false.

Definition example_ability : Ability :=
  mkAbility (fun gs => gs) (fun gs => true).

(* Exemple de dictionnaire de capacités *)
Definition example_dict : AbilityDict :=
  (1, example_ability) :: (2, example_ability) :: nil.

(* Exemple de création d'une carte avec une carte permanente *)
Definition exemple_card : Card := mkCard (Some exemple_perm) None None [mkMana White 2] "snoopy" .

Definition ex_cardstack : CardOrPair := CardItem exemple_card.

Definition initial_GS : GameState := mkGameState [exemple_perm] nil nil nil nil 0 [] nil.


Definition GameHistory := list GameState.


Definition Save_Game_State (gs : GameState) (history : GameHistory) : GameHistory :=
  history ++ [gs]. (* On ajoute le nouvel état à la fin *)

Definition Get_Current_State (history : GameHistory) : option GameState :=
  match history with
  | [] => None
  | _ => Some (last history initial_GS)
  end.

(* Fonction pour comparer deux ManaColor *)
Definition eq_mana_color (c1 c2 : ManaColor) : bool :=
  match c1, c2 with
  | White, White => true
  | Blue, Blue => true
  | Black, Black => true
  | Red, Red => true
  | Green, Green => true
  | Generic, Generic => true
  | _, _ => false
  end.

(* Fonction pour vérifier si un Land est dans le battlefield *)
Fixpoint is_land_in_battlefield (target_land : Land) (battlefield : list Permanent) : bool :=
  match battlefield with
  | nil => false
  | p :: rest =>
    match p.(land) with
    | None => is_land_in_battlefield target_land rest
    | Some land_in_perm =>
      if eq_mana_color (land_to_mana_color target_land.(producing)) (land_to_mana_color land_in_perm.(producing)) then
        true
      else
        is_land_in_battlefield target_land rest
    end
  end.

(* Fonction pour mettre à jour le champ tapped d'un Land dans le battlefield *)
Fixpoint update_tapped_land (target_land : Land) (battlefield : list Permanent) : list Permanent :=
  match battlefield with
  | nil => nil
  | p :: rest =>
    match p.(land) with
    | None => p :: update_tapped_land target_land rest
    | Some land_in_perm =>
      if eq_mana_color (land_to_mana_color target_land.(producing)) (land_to_mana_color land_in_perm.(producing)) then
        mkPermanent p.(ListOnCast) p.(ListOnDeath) p.(ListOnPhase) p.(creature) p.(enchantement) (Some land_in_perm) p.(artifact) true p.(legendary) true :: update_tapped_land target_land rest
      else
        p :: update_tapped_land target_land rest
    end
  end.

(* Fonction pour "tap" un Land et produire du mana, en mettant à jour l'historique *)
Definition tap_land (target_land : Land) (history : GameHistory) : GameHistory :=
  match Get_Current_State history with
  | None => history (* Si l'historique est vide, retourner l'historique inchangé *)
  | Some current_gs =>
    if is_land_in_battlefield target_land current_gs.(battlefield) then
      let new_mana := mkMana (land_to_mana_color target_land.(producing)) 1 in
      let new_battlefield := update_tapped_land target_land current_gs.(battlefield) in
      let new_gs := mkGameState new_battlefield current_gs.(hand) current_gs.(library)
                      current_gs.(graveyard) current_gs.(exile) current_gs.(opponent)
                      (new_mana :: current_gs.(manapool)) current_gs.(stack) in
      Save_Game_State new_gs history
    else
      history (* Si la Land n'est pas dans le battlefield, ne rien faire *)
  end.


Definition abilities :=
  match get_list_on_cast_from_stack ex_cardstack with
  | None => nil
  | Some keys => find_abilities_from_list example_dict keys
  end.

Definition forest_land : Land := mkLand Forest.
Definition forest_perm : Permanent := mkPermanent nil nil nil None None (Some forest_land) None false false false.
Definition card_forest : Card := mkCard (Some forest_perm) None None [] "Forest".
Definition Test_GS : GameState := mkGameState [forest_perm] nil nil nil nil 0 [] nil.

Definition history : GameHistory := [Test_GS].

Compute tap_land forest_land history.




