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
Require Import type_definitions.
Import type_definition.
Module utility_function.

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
  String.eqb c1.(name) c2.(name).

(* Définition d'une fonction pour vérifier la présence d'un élément dans une liste *)
Fixpoint mem_card (c : Card) (l : list Card) : bool :=
  match l with
  | [] => false
  | h :: t => if eq_card c h then true else mem_card c t
  end.

(* Fonction qui compte le nombre d'occurrences d'un élément dans une liste *)
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
          let updated_perm := mkPermanent perm.(ListOnCast) perm.(ListOnDeath) perm.(ListOnPhase) perm.(ListActivated) perm.(subtype) perm.(creature) perm.(enchantement) (Some land_in_perm) perm.(artifact) true perm.(legendary) true in
          (mkCard (Some updated_perm) c.(instant) c.(sorcery) c.(manacost) c.(name)) :: update_tapped_land target_land rest
        else
          c :: update_tapped_land target_land rest
      end
    end
  end.


(* Fonction pour tap une Land et produire du mana, en mettant à jour le GameState *)
Definition tap_land (target_card : Card) (gs : GameState) : GameState :=
  match target_card.(permanent) with
  | None => gs (* Si la carte n'est pas un permanent, retourner l'état du jeu inchangé *)
  | Some perm =>
    match perm.(land) with
    | None => gs (* Si la carte n'est pas un Land, ne rien faire *)
    | Some target_land =>
      if mem_card target_card gs.(battlefield) then
        let new_mana := target_land.(producing) in
        let new_battlefield := update_tapped_land target_land gs.(battlefield) in
        mkGameState new_battlefield gs.(hand) gs.(library)
                    gs.(graveyard) gs.(exile) gs.(opponent)
                    (new_mana :: gs.(manapool)) gs.(stack)
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
  | mkCard (Some _) None None _ _ => PermanentType
  | mkCard None (Some _) None _ _ => InstantType
  | mkCard None None (Some _) _ _ => SorceryType
  | _ => UnknownType
  end.

Definition permanent_type (c : Permanent) : PermanentCardType :=
  match c with
  | mkPermanent _ _ _ _ _ (Some _) None None None _ _ _ => CreatureType
  | mkPermanent _ _ _ _ _ None (Some _) None None _ _ _ => EnchantmentType
  | mkPermanent _ _ _ _ _ None None (Some _) None _ _ _ => ArtifactType
  | mkPermanent _ _ _ _ _ None None None (Some _) _ _ _ => LandType
  | _ => UnknownPermanentType
  end.

Definition has_subtype (st : string) (subtypes : list string) : bool :=
  existsb (fun x => String.eqb x st) subtypes.

End utility_function.
Export utility_function.
