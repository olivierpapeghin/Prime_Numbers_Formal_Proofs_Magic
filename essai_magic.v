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

Inductive EnchantmentTypes := aura | room.

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

(* Not used for now, but could be after *)
Record Land := {
  produce_mana : ManaColor;
  tapped : bool
}.


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
  tapped_permanent : bool;
  permanent_abilities : list Ability;
  perm_triggered_abilities : list TriggeredAbility; 
}.
(* On enregistre tous les permanents joués *)
Definition PermanentRegistry := list Permanent.

(* Fonction eqb_card qui compare deux cartes *)
Definition eqb_card (x y : Card) : bool :=
  if string_dec x.(name) y.(name) then
    match x.(type), y.(type) with
    | permanent, permanent => true
    | instant, instant => true
    | sorcery, sorcery => true
    | _, _ => false
    end
  else
    false.

(* Fonction qui recherche un permanent dans le champ de bataille *)
Fixpoint Find_permanent (card : Card) (battlefield : list Permanent) : option Permanent :=
  match battlefield with
  | [] => None
  | p :: ps =>
      if eqb_card p.(permanent_card) card then Some p
      else Find_permanent card ps
  end.

Definition Save_Permanent (p : Permanent) (registry : PermanentRegistry) : PermanentRegistry :=
  p :: registry.


Record Instant := {
  instant_card : Card;
  instant_abilities : list Ability;
  instant_triggered_abilities : list TriggeredAbility; 
}.

Definition GameHistory := list GameState.

Definition Save_Game_State (gs : GameState) (history : GameHistory) : GameHistory :=
  history ++ [gs]. (* On ajoute le nouvel état à la fin *)

(* Default GameState *)
Definition GameState_0 := {|
  battlefield := [];
  mana_pool := [];
  opponent := 20;
  hand := [];
  library := [];
  graveyard := [];
  exile := [];
  stack := [];
|}.

(* To get the last version of the GameState *)
Definition Get_Current_State (history : GameHistory) : option GameState :=
  match history with
  | [] => None
  | _ => Some (last history GameState_0)
  end.

Definition tap (P : Permanent) : Permanent := {|
  permanent_card := P.(permanent_card);
  permanent_type := P.(permanent_type);
  tapped_permanent := true;
  permanent_abilities := P.(permanent_abilities);
  perm_triggered_abilities := P.(perm_triggered_abilities); (* Conserver les triggered abilities *)
|}.

Definition untap (P : Permanent) : Permanent := {|
  permanent_card := P.(permanent_card);
  permanent_type := P.(permanent_type);
  tapped_permanent := false;
  permanent_abilities := P.(permanent_abilities);
  perm_triggered_abilities := P.(perm_triggered_abilities); (* Conserver les triggered abilities *)
|}.

Definition ManaColor_eq (mc1 mc2 : ManaColor) : bool :=
  match mc1, mc2 with
  | Generic, _ => true
  | _, Generic => true
  | White, White => true
  | Blue, Blue => true
  | Black, Black => true
  | Red, Red => true
  | Green, Green => true
  | _, _ => false
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
      if ManaColor_eq h.(color) cost.(color) then
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
      if ManaColor_eq c.(color) Generic then
        (* Si le coût est générique, on cherche un mana de n'importe quelle couleur dans le pool *)
        match pool with
        | [] => false (* Pas assez de mana dans le pool *)
        | h :: t =>
            (* On consomme n'importe quel mana coloré pour couvrir le coût générique *)
            Can_Pay cs t (* Continue à chercher les autres coûts, après avoir retiré un mana du pool *)
        end
      else
        (* Si c'est un mana coloré spécifique, on cherche un mana correspondant dans le pool *)
        match find (fun m => ManaColor_eq m.(color) c.(color)) pool with
        | Some m =>
            (* Si on trouve un mana de la bonne couleur, on le consomme *)
            if Nat.leb c.(quantity) m.(quantity) then
              Can_Pay cs (remove_mana pool c) (* Consommer le mana et vérifier les autres coûts *)
            else
              false (* Pas assez de mana de cette couleur, on échoue *)
        | None => false (* Pas de mana correspondant dans le pool, on échoue *)
        end
  end.

Definition Activate_Ability (ab : Ability) (gs : GameState) : GameState :=
  (* Vérifier si la condition d'activation est remplie *)
  if ab.(activation_condition) gs then
    (* Si la condition d'activation est vraie, appliquer l'ability *)
    ab.(ability) gs
  else
    (* Si la condition d'activation n'est pas remplie, retourner l'état du jeu inchangé *)
    gs.

(* Fonction remove_card qui retire la première occurrence de c dans la liste l *)
Fixpoint remove_card (l : list Card) (c : Card) : list Card :=
  match l with
  | [] => [] (* Si la liste est vide, retourne une liste vide *)
  | h :: t => if eqb_card h c then t (* Si on trouve la carte, on la retire *)
              else h :: remove_card t c (* Sinon, on continue à chercher *)
  end.


Definition eqb_event : Events -> Events -> bool :=
  (* Fonction pour comparer les événements *)
  fun e1 e2 => match e1, e2 with
    | OnDeath, OnDeath => true
    | OnCast, OnCast => true
    | OnPhase, OnPhase => true
    | _, _ => false
    end.

(* Fonction qui vérifie si une carte est sur le battlefield *)
Fixpoint is_on_battlefield (bf : list Card) (c : Card) : bool :=
  match bf with
  | [] => false
  | h :: t => if eqb_card h c then true else is_on_battlefield t c
  end.

(* Fonction pour récupérer toutes les triggered abilities des permanents sur le champ de bataille *)
Fixpoint Get_Triggered_Abilities (permanents : list Permanent) : list TriggeredAbility :=
  match permanents with
  | [] => []
  | p :: ps => p.(perm_triggered_abilities) ++ Get_Triggered_Abilities ps
  end.

Fixpoint Check_Triggered_Abilities (event : Events) (registry : PermanentRegistry) (gs : GameState) : GameState :=
  let triggered_abilities :=
    fold_left (fun acc card =>
      match Find_permanent card registry with
      | Some p =>
          fold_left (fun acc_ab ta =>
            if eqb_event ta.(trigger_event) event then
              ta.(trigger_ability) :: acc_ab
            else
              acc_ab
          ) acc p.(perm_triggered_abilities)
      | None => acc
      end
    ) [] gs.(battlefield) in
  fold_left (fun acc_gs ab =>
    if ab.(activation_condition) acc_gs then
      ab.(ability) acc_gs
    else
      acc_gs
  ) gs triggered_abilities.






Definition Cast_Permanent (p : Permanent) (history : GameHistory) (registry : PermanentRegistry) : (GameHistory * PermanentRegistry) :=
  match Get_Current_State history with
  | None => (history, registry) (* Si l'historique est vide, on ne fait rien. *)
  | Some gs =>
      let cost := p.(permanent_card).(mana_cost) in
      let pool := gs.(mana_pool) in
      if Can_Pay cost pool then
        let new_pool := fold_left remove_mana cost pool in
        let new_battlefield := p.(permanent_card) :: gs.(battlefield) in
        let new_hand := remove_card gs.(hand) p.(permanent_card) in
        let new_gs := {| 
          battlefield := new_battlefield;
          mana_pool := new_pool;
          opponent := gs.(opponent);
          hand := new_hand;
          library := gs.(library);
          graveyard := gs.(graveyard);
          exile := gs.(exile);
          stack := gs.(stack);
        |} in
        (* Sauvegarde du permanent dans le registre *)
        let updated_registry := Save_Permanent p registry in
        (* Lister les triggered abilities des permanents sur le battlefield *)
        let triggered_abilities := Get_Triggered_Abilities gs.(battlefield) in
        (* Activer les triggered abilities en vérifiant si elles réagissent à OnCast *)
        let filtered_abilities := filter (fun ab => eqb_event ab.(trigger_event) OnCast) triggered_abilities in
        let final_gs := Check_Triggered_Abilities filtered_abilities new_gs in
        (Save_Game_State final_gs history, updated_registry)
      else
        (history, registry) (* Si le coût ne peut pas être payé, l'historique reste inchangé. *)
  end.






Definition Cast_Instant (i : Instant) (history : GameHistory) : GameHistory :=
  match Get_Current_State history with
  | None => history (* Si l'historique est vide, on ne fait rien. *)
  | Some gs =>
      let cost := i.(instant_card).(mana_cost) in
      let pool := gs.(mana_pool) in
      if Can_Pay cost pool then
        let new_pool := fold_left remove_mana cost pool in
        (* Appliquer les abilities *)
        let gs_after_ability := fold_left (fun acc_gs ability =>
          Activate_Ability ability acc_gs
        ) i.(instant_abilities) gs in
        (* Ajouter les cartes activées sur le champ de bataille *)
        let new_battlefield := gs_after_ability.(battlefield) in
        let new_hand := remove_card gs_after_ability.(hand) i.(instant_card) in
        let new_graveyard := i.(instant_card) :: gs_after_ability.(graveyard) in
        let new_gs := {|
          battlefield := new_battlefield;
          mana_pool := new_pool;
          opponent := gs_after_ability.(opponent);
          hand := new_hand;
          library := gs_after_ability.(library);
          graveyard := new_graveyard;
          exile := gs_after_ability.(exile);
          stack := gs_after_ability.(stack);
          
        |} in
        let triggered_abilities := Check_Triggered_Abilities new_gs [i] in
        (* Ici, vous pouvez ajouter un traitement pour les triggered abilities si nécessaire *)
        Save_Game_State new_gs history
      else
        history (* Si le coût ne peut pas être payé, l'historique reste inchangé. *)
  end.


(* Exemples d'utilisation *)
Definition Zimone : Permanent := {|
  permanent_card := {|
    type := permanent;
    name := "Zimone, All-questionning";
    mana_cost := [{| color := White; quantity := 2 |};{| color := Blue; quantity := 1 |}];
  |};
  tapped_permanent := false;
  permanent_type := [creature; legendary];
  permanent_abilities := [];
  triggered_abilities := [] (* Ajout des triggered abilities *)
|}.

Definition Snoopy : Permanent := {|
  permanent_card := {|
    type := permanent;
    name := "Snoopy le merveilleux";
    mana_cost := [{| color := White; quantity := 3 |};{| color := Black; quantity := 2 |}];
  |};
  tapped_permanent := false;
  permanent_type := [creature; token];
  permanent_abilities := [];
  triggered_abilities := [] (* Ajout des triggered abilities *)
|}.

Definition Create_Snoopy : Ability := {|
  ability := fun gs =>
    let new_battlefield := Snoopy.(permanent_card) :: gs.(battlefield) in
    {| battlefield := new_battlefield;
       mana_pool := gs.(mana_pool);
       opponent := gs.(opponent);
       hand := gs.(hand);
       library := gs.(library);
       graveyard := gs.(graveyard);
       exile := gs.(exile);
       stack := gs.(stack);
       events := gs.(events) (* Conserver les événements *)
    |};
  activation_condition := fun gs => true (* Condition d'activation *)
|}.

Definition Invasion_doggesque : Instant := {|
  instant_card := {|
    type := instant;
    name := "Envahir la populace";
    mana_cost := [{| color := White; quantity := 3 |};{| color := Black; quantity := 2 |}; {| color := Generic; quantity := 2 |}];
  |};
  instant_abilities := [Create_Snoopy];
  triggered_abilities := [] (* Ajout des triggered abilities *)
|}.

Definition My_mana : ManaPool := [
{| color := Red; quantity := 20 |};
{| color := Black; quantity := 20 |};
{| color := White; quantity := 20 |};
{| color := Blue; quantity := 20 |}].

(* Un état de jeu minimal pour tester la fonction Cast_Card *)
Definition initial_game_state : GameState := {|
  battlefield := [];
  mana_pool := My_mana;
  opponent := 20;
  hand := [Zimone.(permanent_card); Invasion_doggesque.(instant_card)];
  library := [];
  graveyard := [];
  exile := [];
  stack := [];
  events := [] (* Initialisation de la liste des événements *)
|}.

Definition initial_history : GameHistory := [initial_game_state].
Definition test_hist := Cast_Instant Invasion_doggesque initial_history.

Compute test_hist.
