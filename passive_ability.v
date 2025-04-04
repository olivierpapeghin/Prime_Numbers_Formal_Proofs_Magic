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
Require Import utility_functions.
Import utility_function.

Module Passive_Cards.



Compute find_passive_ability_in_dict ListPassiveAbility DoubleToken.

Compute update_passive_ability_in_dict ListPassiveAbility AllFlash true.
Compute ListPassiveAbility.

End Passive_Cards.
Export Passive_Cards.

