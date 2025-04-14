Require Import Nat.
Require Import Arith.
Require Import ZArith.

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


Compute is_prime 881.