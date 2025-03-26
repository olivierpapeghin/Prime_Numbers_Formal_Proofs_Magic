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

Module Try_card.

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
  battlefield : list Card;
  hand : list Card;
  library : list Card;
  graveyard : list Card;
  exile : list Card;
  opponent : nat;
  manapool : list Mana;
  stack : list CardOrPair;
}.

Definition Ability := option (list Card) -> GameState -> GameState.

(* Définition d'une liste de paires clé-valeur pour simuler un dictionnaire *)
Definition Dict := list (nat * Ability).

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


Definition initial_GS : GameState := mkGameState nil nil nil nil nil 0 [] nil.


Definition GameHistory := list GameState.


Definition Save_Game_State (gs : GameState) (history : GameHistory) : GameHistory :=
  history ++ [gs]. (* On ajoute le nouvel état à la fin *)

Definition Get_Current_State (history : GameHistory) : option GameState :=
  match history with
  | [] => None
  | _ => Some (last history initial_GS)
  end.
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
Definition eq_mana (m1 m2 : Mana) : bool :=
  eq_mana_color m1.(color) m2.(color) && Nat.eqb m1.(quantity) m2.(quantity).

(* Fonction de comparaison pour les listes de Mana *)
Fixpoint eq_list_mana (l1 l2 : list Mana) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => (eq_mana x y) && eq_list_mana xs ys
  | _, _ => false
  end.

(* Fonction de comparaison pour les options *)
Definition eq_option {A : Type} (eqA : A -> A -> bool) (o1 o2 : option A) : bool :=
  match o1, o2 with
  | None, None => true
  | Some x, Some y => eqA x y
  | _, _ => false
  end.

(* Fonction de comparaison pour Creature *)
Definition eq_creature (c1 c2 : Creature) : bool :=
  (c1.(power) =? c2.(power)) && (c1.(toughness) =? c2.(toughness)).

Definition eq_land (l1 l2 : Land) : bool :=
  let color1 := land_to_mana_color l1.(producing) in
  let color2 := land_to_mana_color l2.(producing) in
  match color1, color2 with
  | White, White => true
  | Blue, Blue => true
  | Black, Black => true
  | Red, Red => true
  | Green, Green => true
  | _, _ => false
  end.
(* Fonction de comparaison pour Permanent *)
Definition eq_permanent (p1 p2 : Permanent) : bool :=
  eq_option eq_creature p1.(creature) p2.(creature) &&
  eq_option eq_land p1.(land) p2.(land) &&
  eq_option (fun _ _ => true) p1.(enchantement) p2.(enchantement) && (* Supposition : tous les enchantements sont identiques *)
  eq_option (fun _ _ => true) p1.(artifact) p2.(artifact) && (* Supposition : tous les artefacts sont identiques *)
  Bool.eqb p1.(token) p2.(token) &&
  Bool.eqb p1.(legendary) p2.(legendary).

(* Fonction qui compare les listes d'entiers *)
Fixpoint eq_list_nat (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => Nat.eqb x y && eq_list_nat xs ys
  | _, _ => false
  end.

(* Fonction de comparaison pour Instant *)
Definition eq_instant (i1 i2 : Instant) : bool :=
  eq_list_nat i1.(spell) i2.(spell).

(* Fonction de comparaison pour Sorcery *)
Definition eq_sorcery (s1 s2 : Sorcery) : bool :=
  eq_list_nat s1.(Spell) s2.(Spell).

(* Fonction principale de comparaison de deux cartes *)
Definition eq_card (c1 c2 : Card) : bool :=
  eq_option eq_permanent c1.(permanent) c2.(permanent) &&
  eq_option eq_instant c1.(instant) c2.(instant) &&
  eq_option eq_sorcery c1.(sorcery) c2.(sorcery) &&
  eq_list_mana c1.(manacost) c2.(manacost) &&
  String.eqb c1.(name) c2.(name).
(* Fonction pour comparer deux ManaColor *)

(* Fonction pour vérifier si un Land est dans le battlefield *)
Fixpoint is_land_in_battlefield (target_land : Land) (battlefield : list Card) : bool :=
  match battlefield with
  | nil => false
  | c :: rest =>
    match c.(permanent) with
    | None => is_land_in_battlefield target_land rest
    | Some perm =>
      match perm.(land) with
      | None => is_land_in_battlefield target_land rest
      | Some land_in_perm =>
        if eq_land target_land land_in_perm then
          true
        else
          is_land_in_battlefield target_land rest
      end
    end
  end.


(* Fonction pour mettre à jour le champ tapped d'un Land dans le battlefield *)
Fixpoint update_tapped_land (target_land : Land) (battlefield : list Card) : list Card :=
  match battlefield with
  | nil => nil
  | c :: rest =>
    match c.(permanent) with
    | None => c :: update_tapped_land target_land rest
    | Some perm =>
      match perm.(land) with
      | None => c :: update_tapped_land target_land rest
      | Some land_in_perm =>
        if eq_land target_land land_in_perm then
          let updated_perm := mkPermanent perm.(ListOnCast) perm.(ListOnDeath) perm.(ListOnPhase) perm.(creature) perm.(enchantement) (Some land_in_perm) perm.(artifact) true perm.(legendary) true in
          (mkCard (Some updated_perm) c.(instant) c.(sorcery) c.(manacost) c.(name)) :: update_tapped_land target_land rest
        else
          c :: update_tapped_land target_land rest
      end
    end
  end.





(* Fonction count_occ qui compte le nombre d'occurrences d'un élément dans une liste *)
Fixpoint count_occ (A : Type) (eqb : A -> A -> bool) (l : list A) (x : A) : nat :=
  match l with
  | [] => 0
  | h :: t => if eqb x h then 1 + count_occ A eqb t x else count_occ A eqb t x
  end.

Fixpoint remove_mana (pool : list Mana) (cost : Mana) : list Mana :=
  match pool with
  | [] => [] (* Si le pool est vide, rien à retirer *)
  | h :: t =>
      if eq_mana_color h.(color) cost.(color) then
        (* Si c'est le même type de mana, on essaie de le consommer *)
        if Nat.leb cost.(quantity) h.(quantity) then
          (* Si la quantité du mana est suffisante pour le coût, on réduit ou on retire *)
          if Nat.eqb cost.(quantity) h.(quantity) then
            t (* On retire le mana si la quantité est exactement la même *)
          else
            {| color := h.(color); quantity := h.(quantity) - cost.(quantity) |} :: t (* On ajuste la quantité restante *)
        else
          (* Si le mana n'est pas suffisant, on le laisse dans le pool *)
          remove_mana t cost
      else
        (* Si ce n'est pas le mana de la bonne couleur, on continue avec le reste du pool *)
        h :: remove_mana t cost
  end.

Fixpoint Can_Pay (cost : list Mana) (pool : list Mana) : bool :=
  match cost with
  | [] => true (* Tout le coût est couvert, on retourne vrai *)
  | c :: cs =>
      if eq_mana_color c.(color) Generic then
        (* Si le coût est générique, on cherche un mana de n'importe quelle couleur dans le pool *)
        match pool with
        | [] => false (* Pas assez de mana dans le pool *)
        | h :: t =>
            (* On consomme n'importe quel mana coloré pour couvrir le coût générique *)
            Can_Pay cs t (* Continue à chercher les autres coûts, après avoir retiré un mana du pool *)
        end
      else
        (* Si c'est un mana coloré spécifique, on cherche un mana correspondant dans le pool *)
        match find (fun m => eq_mana_color m.(color) c.(color)) pool with
        | Some m =>
            (* Si on trouve un mana de la bonne couleur, on le consomme *)
            if Nat.leb c.(quantity) m.(quantity) then
              Can_Pay cs (remove_mana pool c) (* Consommer le mana et vérifier les autres coûts *)
            else
              false (* Pas assez de mana de cette couleur, on échoue *)
        | None => false (* Pas de mana correspondant dans le pool, on échoue *)
        end
  end.

(* Définition d'une fonction pour vérifier la présence d'un élément dans une liste *)
Fixpoint mem_card (c : Card) (l : list Card) : bool :=
  match l with
  | [] => false
  | h :: t => if eq_card c h then true else mem_card c t
  end.

(* Fonction pour "tap" un Land et produire du mana, en mettant à jour l'historique *)
Definition tap_land (target_card : Card) (history : GameHistory) : GameHistory :=
  match Get_Current_State history with
  | None => history (* Si l'historique est vide, retourner l'historique inchangé *)
  | Some current_gs =>
    match target_card.(permanent) with
    | None => history (* Si la carte n'est pas un permanent, ne rien faire *)
    | Some perm =>
      match perm.(land) with
      | None => history (* Si la carte n'est pas un Land, ne rien faire *)
      | Some target_land =>
        if mem_card target_card current_gs.(battlefield) then
          let new_mana := mkMana (land_to_mana_color target_land.(producing)) 1 in
          let new_battlefield := update_tapped_land target_land current_gs.(battlefield) in
          let new_gs := mkGameState new_battlefield current_gs.(hand) current_gs.(library)
                          current_gs.(graveyard) current_gs.(exile) current_gs.(opponent)
                          (new_mana :: current_gs.(manapool)) current_gs.(stack) in
          Save_Game_State new_gs history
        else
          history (* Si la Land n'est pas dans le battlefield, ne rien faire *)
      end
    end
  end.



(* On doit ensuite manipuler les zones dans lesquels les cartes vont passer *)
(* Fonction remove_card qui retire la première occurrence de c dans la liste l *)
Fixpoint remove_card_from_hand (l : list Card) (c : Card) : list Card :=
  match l with
  | [] => [] (* Si la liste est vide, retourne une liste vide *)
  | h :: t => if eq_card h c then t (* Si on trouve la carte, on la retire *)
              else h :: remove_card_from_hand t c (* Sinon, on continue à chercher *)
  end.



Definition forest_land : Land := mkLand Forest.
Definition forest_perm : Permanent := mkPermanent nil nil nil None None (Some forest_land) None false false false.
Definition card_forest : Card := mkCard (Some forest_perm) None None [] "Forest".
Definition Test_GS : GameState := mkGameState nil [card_forest] nil nil nil 0 [] nil.

Definition history : GameHistory := [Test_GS].

(* Fonction pour sacrifier des cartes et les déplacer vers le cimetière *)
Definition sacrifice_cards_ability_function (targets : option (list Card)) (gs : GameState) : GameState :=
  match targets with
  | None => gs (* Si aucune cible n'est fournie, retourner l'état du jeu inchangé *)
  | Some target_cards =>
    fold_left
      (fun new_gs target =>
        match target.(permanent) with
        | None => new_gs (* Si la carte n'est pas un permanent, ne rien faire *)
        | Some target_perm =>
          let new_battlefield := remove_card_from_hand new_gs.(battlefield) target in
          let new_graveyard := target :: new_gs.(graveyard) in
          mkGameState new_battlefield new_gs.(hand) new_gs.(library) new_graveyard new_gs.(exile)
                        new_gs.(opponent) new_gs.(manapool) new_gs.(stack)
        end)
      target_cards
      gs
  end.



(* Définition des sous-dictionnaires *)
Definition OnCast : Dict := [(1, sacrifice_cards_ability_function)].
Definition OnPhase : Dict := nil.
Definition OnDeath : Dict := nil.


(* Définition du dictionnaire principal avec des clés de type string *)
Definition Triggered_Abilities : list (nat * Dict) :=
  ( 1 , OnCast) :: (2 , OnPhase) :: (3 , OnDeath) :: nil.

(* Fonction pour trouver un sous-dictionnaire par sa clé *)
Fixpoint find_sub_dict (dicts : list (nat * Dict)) (key1 : nat) : option Dict :=
  match dicts with
  | nil => None
  | (k, sub_dict) :: rest =>
    if Nat.eqb k key1 then Some sub_dict else find_sub_dict rest key1
  end.

(* Fonction pour trouver une capacité par sa clé dans un sous-dictionnaire *)
Fixpoint find_ability_in_sub_dict (sub_dict : Dict) (key2 : nat) : option Ability :=
  match sub_dict with
  | nil => None
  | (k, ability) :: rest =>
    if Nat.eqb k key2 then Some ability else find_ability_in_sub_dict rest key2
  end.

(* Fonction principale pour trouver une capacité dans le dictionnaire principal *)
Definition find_ability_in_triggered_abilities (triggered_abilities : list (nat * Dict)) (pair : nat * nat) : option Ability :=
  let (key1, key2) := pair in
  match find_sub_dict triggered_abilities key1 with
  | None => None
  | Some sub_dict => find_ability_in_sub_dict sub_dict key2
  end.

(* Exemple de création d'une autre carte permanente *)
Definition creature_perm : Permanent := mkPermanent [1] nil nil (Some (mkCreature 2 2)) None None None false false false.
Definition card_creature : Card := mkCard (Some creature_perm) None None [] "Creature".

(* État de jeu initial avec des cartes dans le battlefield *)
Definition Test_gs : GameState := mkGameState [card_forest; card_creature] nil nil nil nil 0 [] nil.

(* Liste de cartes cibles à sacrifier *)
Definition target_cards : list Card := [card_forest; card_creature].


(* Fonction pour activer les abilities depuis ListOnCast *)
Fixpoint activate_on_cast_abilities (triggered_abilities : list (nat * Dict)) (l : list nat) (gs : GameState) : GameState :=
  match l with
  | [] => gs
  | key :: rest =>
    match find_ability_in_triggered_abilities triggered_abilities (1, key) with
    | None => activate_on_cast_abilities triggered_abilities rest gs
    | Some ability =>
      let new_gs := ability (Some []) gs in
      activate_on_cast_abilities triggered_abilities rest new_gs
    end
  end.

(* Fonction Cast qui active les abilities depuis ListOnCast *)
Definition Cast (c: Card) (gs: GameState) : GameState :=
  let cost := c.(manacost) in
  let pool := gs.(manapool) in
  if Can_Pay cost pool then
    let new_pool := fold_left remove_mana cost pool in
    let new_hand := remove_card_from_hand gs.(hand) c in
    let new_gs := mkGameState gs.(battlefield) new_hand gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) new_pool gs.(stack) in
    (* Activer les abilities depuis ListOnCast *)
    match c.(permanent) with
    | None => new_gs
    | Some perm =>
      activate_on_cast_abilities Triggered_Abilities perm.(ListOnCast) new_gs
    end
  else
    gs.


End Try_card.


