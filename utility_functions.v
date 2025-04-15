From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Program.Equality.
Require Import List String.
Require Import String.
Require Import List.
Require Import Coq.Logic.EqdepFacts.

Import ListNotations.
Open Scope list_scope.
Require Import type_definitions.
Import type_definition.
Module utility_function.


Definition isSome {A : Type} (o : option A) : bool :=
  match o with
  | Some _ => true
  | None => false
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
  let token_value := get_token_default c false in
  if token_value then true else false.

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


Definition next_phase (p : Phase) : Phase :=
  match p with
  | BeginningPhase => MainPhase1
  | MainPhase1 => CombatPhase
  | CombatPhase => MainPhase2
  | MainPhase2 => EndingPhase
  | EndingPhase => BeginningPhase 
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

(* Fonction pour comparer deux Lands en comparant leur production de mana *)
Definition eq_land (l1 l2 : Land) : bool :=
  eq_mana l1.(producing) l2.(producing).

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
  String.eqb c1.(name) c2.(name) &&
  Nat.eqb c1.(id) c2.(id).

Definition phase_eqb (p1 p2 : Phase) : bool :=
  match p1, p2 with
  | BeginningPhase, BeginningPhase => true
  | MainPhase1, MainPhase1 => true
  | CombatPhase, CombatPhase => true
  | MainPhase2, MainPhase2 => true
  | EndingPhase, EndingPhase => true
  | _, _ => false
  end.

(* Fonction principale de comparaison de deux base de cartes *)
Definition eq_card_base (c1 c2 : Card) : bool :=
  eq_option eq_permanent c1.(permanent) c2.(permanent) &&
  eq_option eq_instant c1.(instant) c2.(instant) &&
  eq_option eq_sorcery c1.(sorcery) c2.(sorcery) &&
  eq_list_mana c1.(manacost) c2.(manacost) &&
  String.eqb c1.(name) c2.(name).

Definition eq_passive_key (c1 c2 : PassiveKey) : bool :=
  match c1, c2 with
  | AllSaprolings, AllSaprolings => true
  | AllFlash, AllFlash => true
  | DoubleToken, DoubleToken => true
  | AdditionalTrigger, AdditionalTrigger => true
  | NoLegendaryRule, NoLegendaryRule => true
  | SaprolingsLands, SaprolingsLands => true
  | LandPlayed, LandPlayed => true
  | _, _ => false
  end.

(* Définition d'une fonction pour vérifier la présence d'un élément dans une liste *)
Fixpoint card_in_list (c : Card) (l : list Card) : bool :=
  match l with
  | [] => false
  | h :: t => if eq_card c h then true else card_in_list c t
  end.

(* Fonction qui compte le nombre d'occurrences d'un élément dans une liste *)
Fixpoint count_occ (A : Type) (eqb : A -> A -> bool) (l : list A) (x : A) : nat :=
  match l with
  | [] => 0
  | h :: t => if eqb x h then 1 + count_occ A eqb t x else count_occ A eqb t x
  end.



(* Fonction pour retirer le mana d'une couleur spécifique *)
Fixpoint remove_mana_from_pool (pool : list Mana) (color : ManaColor) (qty : nat) : option (list Mana) :=
  match pool with
  | [] => None
  | mkMana c q :: rest =>
    if eq_mana_color c color then
      if qty <=? q then
        Some ((mkMana c (q - qty)) :: rest)
      else
        None
    else
      match remove_mana_from_pool rest color qty with
      | None => None
      | Some new_rest => Some (mkMana c q :: new_rest)
      end
  end.


(* Fonction pour retirer les coûts d'une carte *)
Fixpoint remove_card_costs (game_state : GameState) (costs : list Mana) : option GameState :=
  match costs with
  | [] => Some game_state (* Tous les coûts ont été retirés avec succès *)
  | cost :: remaining_costs =>
    match remove_mana_from_pool game_state.(manapool) cost.(color) cost.(quantity) with
    | None => None (* Impossible de retirer ce coût, donc échec *)
    | Some new_pool =>
      let new_game_state := mkGameState
        game_state.(battlefield)
        game_state.(hand)
        game_state.(library)
        game_state.(graveyard)
        game_state.(exile)
        game_state.(opponent)
        new_pool
        game_state.(stack)
        game_state.(passive_abilities)
        game_state.(phase) in
      remove_card_costs new_game_state remaining_costs
    end
  end.


(* Définition d'une fonction pour vérifier la présence d'un élément dans une liste *)
Fixpoint find_card_in_list (c : Card) (l : list Card) : option Card :=
  match l with
  | [] => None
  | h :: t => if String.eqb c.(name) h.(name) && Nat.eqb c.(id) h.(id) then (Some h) else find_card_in_list c t
  end.


Fixpoint find_passive_ability_in_dict (dict : PassiveAbilityDict) (key : PassiveKey) : nat :=
  match dict with
  | nil => 0
  | (k, activated) :: rest =>
    if eq_passive_key k key then activated else find_passive_ability_in_dict  rest key
  end.

Fixpoint update_passive_ability_in_dict (dict : PassiveAbilityDict) (key : PassiveKey) (new_value : nat) : PassiveAbilityDict :=
  match dict with
  | nil => nil
  | (k, activated) :: rest =>
      if eq_passive_key k key 
      then (k, new_value) :: rest  (* Mise à jour de la valeur si la clé correspond *)
      else (k, activated) :: update_passive_ability_in_dict rest key new_value
  end.

(* On doit ensuite manipuler les zones dans lesquelles les cartes vont passer *)
(* Fonction remove_card qui retire la première occurrence de c dans la liste l *)
Fixpoint remove_card (l : list Card) (c : Card) : list Card :=
  match l with
  | [] => [] (* Si la liste est vide, retourne une liste vide *)
  | h :: t => if eq_card h c then t (* Si on trouve la carte, on la retire *)
              else h :: remove_card t c (* Sinon, on continue à chercher *)
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
        if eq_mana target_land.(producing) land_in_perm.(producing) then
          let updated_perm := mkPermanent perm.(Abilities) perm.(ListActivated) None perm.(subtype) perm.(creature) perm.(enchantement) (Some land_in_perm) perm.(artifact) true perm.(legendary) true in
          (mkCard (Some updated_perm) c.(instant) c.(sorcery) c.(manacost) c.(name) c.(id) c.(keywords)) :: update_tapped_land target_land rest

        else
          c :: update_tapped_land target_land rest
      end
    end
  end.

Fixpoint is_card_base_in (l : list Card) (c: Card) : bool :=
  match l with
  | [] => true (* Si la liste est vide, retourne une liste vide *)
  | h :: t => if eq_card_base h c then false (* Si on trouve la carte, on la retire *)
              else is_card_base_in t c (* Sinon, on continue à chercher *)
  end.
  


Definition check_legendary_rule (gs: GameState) (c: Card) : bool :=
  match c.(permanent) with
  | None => true
  | Some perm =>
    if (Nat.ltb (find_passive_ability_in_dict (passive_abilities gs) NoLegendaryRule) 1) && perm.(legendary) then
      is_card_base_in gs.(battlefield) c
    else 
      true
  end.

Definition add_mana (gs : GameState) (mc : ManaColor) (q : nat) : GameState :=
  let new_manapool :=
    map (fun m =>
      if eq_mana_color m.(color) mc then
        mkMana mc (m.(quantity) + q)
      else
        m
    ) gs.(manapool)
  in
  mkGameState gs.(battlefield) gs.(hand) gs.(library) gs.(graveyard) gs.(exile) gs.(opponent) new_manapool gs.(stack) gs.(passive_abilities) gs.(phase).

(* Fonction pour tap une Land et produire du mana, en mettant à jour le GameState *)
Definition tap_land (target_card : Card) (gs : GameState) : GameState :=
  match target_card.(permanent) with
  | None => gs (* Si la carte n'est pas un permanent, retourner l'état du jeu inchangé *)
  | Some perm =>
    match perm.(land) with
    | None => gs (* Si la carte n'est pas un Land, ne rien faire *)
    | Some target_land =>
      if card_in_list target_card gs.(battlefield) then
        
        let new_battlefield := update_tapped_land target_land gs.(battlefield) in
          add_mana gs target_land.(producing).(color) target_land.(producing).(quantity)
      else
        gs (* Si la Land n'est pas dans le battlefield, ne rien faire *)
    end
  end.

(* Fonction qui retourne le dernier élément d'une liste *)
Fixpoint last_option {A : Type} (l : list A) : option A :=
  match l with
  | [] => None                 (* Si la liste est vide, retourne None *)
  | [x] => Some x              (* Si un seul élément, retourne Some x *)
  | _ :: xs => last_option xs  (* Sinon, continue sur le reste de la liste *)
  end.

(* Fonction pour enlever le dernier élément d'une liste *)
Fixpoint remove_last {A : Type} (l : list A) : list A :=
  match l with
  | [] => []                  (* Si la liste est vide, on retourne une liste vide *)
  | [x] => []                 (* Si un seul élément, on l'enlève en retournant [] *)
  | x :: xs => x :: remove_last xs (* Sinon, on reconstruit la liste sans le dernier élément *)
  end.

(* Fonction qui détermine le type d'une carte *)
Definition card_type (c : Card) : CardType :=
  match c with
  | mkCard (Some _) None None _ _ _ _ => PermanentType
  | mkCard None (Some _) None _ _ _ _ => InstantType
  | mkCard None None (Some _) _ _ _ _ => SorceryType
  | _ => UnknownType
  end.

Definition permanent_type (c : Permanent) : PermanentCardType :=
  match c with
  | mkPermanent _ _ _ _ (Some _) None None None _ _ _ => CreatureType
  | mkPermanent _ _ _ _ None (Some _) None None _ _ _ => EnchantmentType
  | mkPermanent _ _ _ _ None None (Some _) None _ _ _ => LandType
  | mkPermanent _ _ _ _ None None None (Some _) _ _ _ => ArtifactType
  | _ => UnknownPermanentType
  end.

Definition has_subtype (st : string) (subtypes : list string) : bool :=
  existsb (fun x => String.eqb x st) subtypes.

(* Définition d'une fonction de comparaison booléenne pour nat *)
Fixpoint beq_nat (n m : nat) : bool :=
  match n, m with
  | 0, 0 => true
  | S n', S m' => beq_nat n' m'
  | _, _ => false
  end.


(* Vérifie si un élément est présent dans une liste d'entiers *)
Fixpoint List_In_nat (x : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | y :: l' => if beq_nat x y then true else List_In_nat x l'
  end.

(* Fonction générique pour comparer deux éléments *)
Definition eqb {A : Type} (eq : A -> A -> bool) (x y : A) : bool :=
  eq x y.

(* Cherche une clé dans une liste de paires et retourne la valeur associée *)
Fixpoint List_assoc {A B : Type} (eq : A -> A -> bool) (x : A) (l : list (A * B)) : option B :=
  match l with
  | [] => None
  | (k, v) :: l' => if eqb eq x k then Some v else List_assoc eq x l'
  end.

(* Fonction pour trouver une capacité par sa clé dans un sous-dictionnaire *)
Fixpoint find_ability_in_sub_dict (sub_dict : Dict) (key2 : nat) : option Ability :=
  match sub_dict with
  | nil => None
  | (k, ability) :: rest =>
    if Nat.eqb k key2 then Some ability else find_ability_in_sub_dict rest key2
  end.

(* Fonction pour activer une seule capacité à partir d'une clé avec des cibles *)
Definition activate_spell (spell_abilities : Dict) (key : nat) (targets : option (list Card)) (gs : GameState) : GameState :=
  match find_ability_in_sub_dict spell_abilities key with
  | None => gs (* Aucune capacité trouvée, retourner l'état du jeu inchangé *)
  | Some ability =>
    let new_gs := ability targets gs in
    new_gs (* Retourner l'état du jeu mis à jour après activation de la capacité *)
  end.

(* Fonction pour trouver un sous-dictionnaire par sa clé *)
Fixpoint find_sub_dict (dicts : list (nat * Dict)) (key1 : nat) : option Dict :=
  match dicts with
  | nil => None
  | (k, sub_dict) :: rest =>
    if Nat.eqb k key1 then Some sub_dict else find_sub_dict rest key1
  end.

(* Fonction principale pour trouver une capacité dans le dictionnaire principal *)
Definition find_ability_in_triggered_abilities (triggered_abilities : list (nat * Dict)) (pair : nat * nat) : option Ability :=
  let (key1, key2) := pair in
  match find_sub_dict triggered_abilities key1 with
  | None => None
  | Some sub_dict => find_ability_in_sub_dict sub_dict key2
  end.
 
(* Fonction pour activer une seule capacité à partir d'une clé avec des cibles *)
Definition activate_triggered_ability (triggered_abilities : list (nat * Dict)) (event_type : nat) (key : nat) (targets : option (list Card)) (gs : GameState) : GameState :=
  match find_ability_in_triggered_abilities triggered_abilities (event_type, key) with
  | None => gs (* Aucune capacité trouvée, retourner l'état du jeu inchangé *)
  | Some ability =>
    let new_gs := ability targets gs in
    new_gs (* Retourner l'état du jeu mis à jour après activation de la capacité *)
  end.


Definition add_abilities_to_stack (event_type : nat) (p : Permanent) (gs : GameState) : GameState :=
  fold_left
    (fun gs' pair =>
      match pair with
      | (dict_id, ability_id) =>
        if beq_nat dict_id event_type then
          let n := find_passive_ability_in_dict gs.(passive_abilities) AdditionalTrigger in
          let repeated_items := repeat (PairItem dict_id ability_id) n in
          let new_stack := repeated_items ++ gs'.(stack) in
          mkGameState gs'.(battlefield) gs'.(hand) gs'.(library) gs'.(graveyard) gs'.(exile) gs'.(opponent) gs'.(manapool) new_stack gs.(passive_abilities) gs.(phase)
        else
          gs'
      end
    )
    p.(Abilities)
    gs.

(* Vérifie si une carte possède un mot-clé spécifique *)
Definition has_keyword (kw : string) (c : Card) : bool :=
  existsb (String.eqb kw) (keywords c).

Definition can_cast (c : Card) (p : Phase) : bool :=
  match c with
  | mkCard _ _ (Some _) _ _ _ _ => (* It's a Sorcery *)
      if has_keyword "Flash" c then true
      else if (phase_eqb p MainPhase1) || (phase_eqb p MainPhase2) then true
      else false
  | mkCard _ (Some _) _ _ _ _ _ => true (* An Instant can be played anytime *)
  | mkCard (Some _) _ _ _ _ _ _ => (* A Permanent *)
      if has_keyword "Flash" c then true
      else if (phase_eqb p MainPhase1) || (phase_eqb p MainPhase2) then true
      else false
  | _ => false
  end.

Definition is_untapped_artifact (c : Card) : bool :=
  match c.(permanent) with
  | Some p =>
      match p.(artifact) with
      | Some _ => negb p.(tapped) (* C'est un artefact non tappé *)
      | None => false
      end
  | None => false
  end.

Definition advance_phase (gs : GameState) : GameState :=
  let new_phase := next_phase gs.(phase) in
  let intermediate_gs := mkGameState gs.(battlefield) gs.(hand) gs.(library) gs.(graveyard)
              gs.(exile) gs.(opponent) gs.(manapool) gs.(stack) gs.(passive_abilities) new_phase in
  if phase_eqb new_phase EndingPhase then  
  fold_left (fun gs' card =>
  match card.(permanent) with
    | Some perm_data => add_abilities_to_stack 2 perm_data gs'
    | None => gs'
    end
  ) gs.(battlefield) intermediate_gs
  else
  intermediate_gs.

Definition count_enchantments (cards : list Card) : nat :=
  fold_left (fun acc c =>
    match c.(permanent) with
    | Some p =>
        match p.(enchantement) with
        | Some _ => acc + 1
        | None => acc
        end
    | None => acc
    end) cards 0.

Definition is_aura (c : Card) : bool :=
  match c.(permanent) with
  | Some p =>
      match p.(enchantement) with
      | Some e =>
          match e.(aura) with
          | Some _ => true
          | None => false
          end
      | None => false
      end
  | None => false
  end.

Definition is_valid_aura (gs : GameState) (c : Card) : bool :=
  match c.(permanent) with
  | Some p =>
    match p.(enchantement) with
    | Some e =>
      match e.(aura) with
      | Some (aura_name, aura_id) =>
        (* Chercher une créature avec ce nom et cet id sur le champ de bataille *)
        existsb
          (fun c =>
            match c.(permanent) with
            | Some perm =>
                match perm.(creature) with
                | Some _ => String.eqb c.(name) aura_name && Nat.eqb c.(id) aura_id
                | None => false
                end
            | None => false
            end
          )
          gs.(battlefield)
      | None => false (* Pas de cible d’aura indiquée *)
      end
    | None => false (* Ce permanent n’est pas un enchantement *)
    end
  | None => false
  end.

Definition divides (n d : nat) : bool := Nat.eqb (n mod d) 0.

Fixpoint check_divisors (n d : nat) : bool :=
  match d with
  | 0 => false
  | 1 => true  (* Si on a testé jusqu'à 1 sans trouver de diviseur, c'est premier *)
  | S d' =>
      if n mod d =? 0 then false (* Si n est divisible par d, alors ce n'est pas premier *)
      else check_divisors n d'
  end.

Definition is_prime (n : nat) : bool :=
  match n with
  | 0 | 1 => false (* 0 et 1 ne sont pas premiers *)
  | 2 => true (* 2 est premier *)
  | _ => check_divisors n (n - 1) (* Vérifie les diviseurs de n jusqu'à n-1 *)
  end.

Definition is_land (p : Permanent) : bool :=
  match p.(land) with
  | Some _ => true
  | None => false
  end.

Fixpoint count_lands (cards : list Card) : nat :=
  match cards with
  | nil => 0
  | card :: rest =>
    match card.(permanent) with
    | Some p => if is_land p then 1 + count_lands rest else count_lands rest
    | None => count_lands rest
    end
  end.

Fixpoint count_tokens (cards : list Card) : nat :=
  match cards with
  | nil => 0
  | card :: rest =>
    match card.(permanent) with
    | Some p => if check_token card then 1 + count_tokens rest else count_tokens rest
    | None => count_tokens rest
    end
  end.

Definition create_token (c : Card) (gs : GameState) : GameState :=
  match c.(permanent) with
  |Some p => if check_token c then 
          let nb_token := count_tokens gs.(battlefield) +1 in
          let new_token :=
              mkCard
                (Some (mkPermanent
                        nil
                        p.(ListActivated)
                        p.(PassiveAbility)
                        p.(subtype)
                        p.(creature)
                        p.(enchantement)
                        p.(land)
                        p.(artifact)
                        true (* token := true *)
                        p.(legendary)
                        false)) (* tapped := false *)
                None
                None
                [] (* Pas de coût de mana, c’est un token *)
                c.(name)
                nb_token
                []
            in
            let new_battlefield := new_token :: gs.(battlefield) in
            let updated_gs := mkGameState
              new_battlefield gs.(hand) gs.(library) gs.(graveyard)
              gs.(exile) gs.(opponent) gs.(manapool)
              gs.(stack) gs.(passive_abilities) gs.(phase)
            in updated_gs
  else gs
  |None => gs
  end. 

End utility_function.
Export utility_function.
