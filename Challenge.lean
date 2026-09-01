/-
Copyright (c) 2024 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/

import Mathlib

/-!

# Challenge file for Palomar's Comparator check

The purpose of this file is to give a self-contained formulation
of the *statement* of this repository's version of Arrow's theorem,
`BooleanFun.BV.dictator_of_condorcet_and_unanimous` that only
depends on Mathlib.

The theorem is not proved here but intentionally left as `sorry`.
The proof is contained in `BooleanFun.Arrow`.

## Main result

This file states a version of Arrow's theorem [arrow1950] for 3-candidate elections,
see `dictator_of_condorcet_and_unanimous`.
We follow O'Donnell [odonnell2014], Sec. 2.5,
which follows Kalai's approach [kalai2002] via Fourier analysis of Boolean valued functions.

## References
* [R. O'Donnell, *Analysis of Boolean functions*, Cambridge University Press, 2014][odonnell2014]
* [G. Kalai, *A Fourier-theoretic perspective on the Condorcet paradox and Arrow's
  theorem*, Advances in Applied Mathematics 29(3) (October 2002), pp. 412-426][kalai2002]
* [K. Arrow, *A difficulty in the concept of social welfare*,
  Journal of Political Economy 58(4) (August 1950), pp. 328-346][arrow1950]

-/

namespace BooleanFun

noncomputable section

/-- A Boolean function maps an `n`-tuple of bits (of type `Fin n → Fin 2`) to a real number. -/
abbrev BooleanFunc (n : ℕ) : Type := (Fin n → Fin 2) → ℝ

variable {n : ℕ} {α : Type*} {f g : BooleanFunc n} {x : Fin n → Fin 2}

/-- Definition of Walsh character -/
abbrev walshCharacter (S : Finset (Fin n)) : BooleanFunc n := fun x ↦ ∏ i ∈ S, (-1) ^ (x i).val

/-- Walsh character -/
scoped notation "χ" => walshCharacter

/-- `BooleanValued f` bundles a proof that `f` takes values `±1`. -/
structure BooleanValued (f : BooleanFunc n) : Prop where
  one_or_neg_one : ∀ x, f x = 1 ∨ f x = -1

namespace BV

/-- Encodes votes of `n` voters in a 2-candidate election. -/
abbrev Votes n := Fin n → Fin 2

/-- A dictator is a Walsh character of a singleton set. -/
abbrev dictator {n : ℕ} (i : Fin n) : BooleanFunc n := χ {i}

/-- Not-all-equal predicate on three values. -/
abbrev NAE3 (x y z : α) : Prop := ¬ (x = y ∧ y = z)

/-- Voter preferences in an election among 3 candidates A, B, C are represented by three
vote ensembles `x y z` representing votes in the three 2-candidate elections among the candidates:
`x` contains the votes for the election A vs. B, `y` for B vs. C and `z` for C vs. A.
Three vote ensembles `x y z` are consistent if they encode a ranking of the
three candidates A, B, C for each voter. This is expressed by the not-all-equal predicate.
See [odonnell2014], Sec. 2.5. -/
def VoteConsistent (x y z : Votes n) : Prop :=
    ∀ i, NAE3 (x i) (y i) (z i)


/-- A voting rule is Condorcet, if in every 3-candidate election conducted
  using it there is a Condercet winner. -/
def IsCondorcet (f : BooleanFunc n) : Prop :=
    ∀ x y z, VoteConsistent x y z → NAE3 (f x) (f y) (f z)

/-- A voting rule admits a dictator if it is equal to `dictator i` for some `i`. -/
def HasDictator (f : BooleanFunc n) : Prop :=
    ∃ i, f = dictator i

/-- A voting rule is unanimous if it selects candidate `i` if everyone votes for `i`.  -/
def IsUnanimous (f : BooleanFunc n) : Prop := f 0 = 1 ∧ f 1 = -1

/-- **Arrow's theorem**
As formulated in [odonnell2014], Sec. 2.5: Every unanimous voting rule that always admits a Condorcet winner is a dictatorship.
Here a voting rule is represented by a Boolean valued function on the Hamming cube. -/
theorem dictator_of_condorcet_and_unanimous (hbv : BooleanValued f)
    (hf : IsUnanimous f) (hf' : IsCondorcet f) : HasDictator f := by
  sorry

end BV

end

end BooleanFun
