/-
Copyright (c) 2024 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Real.Irrational

-- set_option profiler true

/-!
General lemmas not specific to analysis of Boolean functions.
These should gradually be removed or converted to `ToMathlib` where appropriate
-/

namespace BooleanFun

open Finset Pi

variable {α:Type*} {β:Type*}
variable {s : Finset α}

variable {ι:Type*} [Fintype ι]
variable {κ:Type*}

variable {R : Type*} {M : Type*}
variable [Ring R] [AddCommGroup M] [Module R M]

section Singleton

lemma card_eq_one {S : Finset α} : S.card = 1 ↔ ∃ i:α, S = {i} := by {
    have := (Multiset.card_eq_one (α := α) (s := S.val))
    simp only [card_val, val_eq_singleton_iff] at this
    assumption
}

-- not to be confused with `Finset.sum_singleton`
lemma sum_singletons [AddCommMonoid α] {F : Finset ι → α} {G:ι → α} (h:∀ i, F {i} = G i):
    ∑ S ∈ {S|S.card = 1}, F S = ∑ i, G i := by {
  symm
  apply sum_of_injOn (e := fun i ↦ {i})
  -- injective
  · intro j _ l _ h
    dsimp at h
    apply eq_of_mem_singleton
    rw [← h]
    exact mem_singleton_self j
-- maps into correct set
  · intro j _
    simp
-- ets : surjective
  · intro S hS hS'
    simp at hS
    obtain ⟨i, hi⟩ := card_eq_one.mp hS
    simp at hS'
    tauto
-- summands equal
  · intro i _
    symm
    exact h i
}

lemma sum_singletons' [AddCommMonoid α] {F : Finset ι → α}:
    ∑ S ∈ {S|S.card = 1}, F S = ∑ i, F {i} := by apply sum_singletons; intro i; rfl

end Singleton

section Ite
-- Basic lemmas for rewriting `ite` expressions -- there must be a better way to do this

variable {α:Sort*} {P : Prop} [Decidable P] {a b c:α}

lemma ite_ite_same (a b c:α):
    ite P (ite P a b) c = ite P a c := by split_ifs <;> rfl

lemma rw_ite_left (h : P → a = c):
    ite P a b = ite P c b := by split_ifs; rw [h]; assumption; rfl

lemma rw_ite_right (h:¬P → a = c):
    ite P b a = ite P b c := by split_ifs; rfl; rw [h]; assumption

lemma ite_add_ite {α:Type*} [AddCommMonoid α] (a₁ b₁ a₂ b₂:α):
    ite P a₁ b₁ + ite P a₂ b₂ = ite P (a₁ + a₂) (b₁ + b₂) := by split_ifs <;> simp

lemma ite_ite_not (P : Prop) [Decidable P] (a b c:α):
    ite P (ite (¬P) a b) c = ite P b c := by split_ifs <;> rfl

lemma ite_ite_not'(P : Prop) [Decidable P] (a b c:α):
    ite (¬P) (ite P a b) c = ite (¬P) b c := by split_ifs <;> rfl

end Ite

noncomputable section OneOn

variable {p q : Prop}

open Classical

/-- Real-valued `0-1` indicator testing a proposition. We prefer this over using `Set.indicator` and we don't call it
indicator to avoid ambiguities with Mathlib definitions. -/
abbrev oneOn (p : Prop) : ℝ := ite (h := propDecidable p)  p 1 0

lemma oneOn_true (h : p) : oneOn p = 1 := by simpa

lemma oneOn_false (h:¬p) : oneOn p = 0 := by simpa

lemma oneOn_and : oneOn (p∧q) = (oneOn p) * (oneOn q) := by
  unfold oneOn; split_ifs <;> {simp; try tauto}

lemma oneOn_not : oneOn (¬p) = 1 - oneOn p := by
  unfold oneOn; split_ifs <;> simp

lemma oneOn_prod {p:ι → Prop} : ∏ i, oneOn (p i) = oneOn (∀ i, p i) := by
  unfold oneOn
  split_ifs with h
  · simp [h]
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    rw [← Finset.prod_erase_mul (a := i) (s := Finset.univ) (h := Finset.mem_univ i)]
    simp [hi]

end OneOn

section PowStuff

/-- natural number version of `zpow_sub₀` -/
lemma npow_sub₀ {G : Type*} [GroupWithZero G] {a : G} {m n:ℕ} (ha : a ≠ 0) (h : n≤m):
    a^(m-n) = a^m / a^n := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, Nat.cast_sub h, zpow_sub₀ ha]

/-- Solutions of the equation `ρᵏ = ρ` in real numbers. -/
lemma pow_eq_self_imp {ρ:ℝ} {k:ℕ}:
    ρ^k = ρ → (k = 1 ∨ ρ = 0 ∨ ρ = 1 ∨ ρ = -1) := by
  intro h
  cases k with
  | zero => right; right; left; symm; rwa [pow_zero] at h
  | succ k =>
    by_cases hρ : ρ = 0
    · right; left; assumption
    · rw [pow_succ] at h
      nth_rewrite 3 [← one_mul ρ] at h
      have h := mul_right_cancel₀ hρ h
      obtain h'|h'|⟨h', _⟩ := pow_eq_one_iff_cases.mp h
      · left; rwa [add_left_eq_self]
      · right; right; left; assumption
      · right; right; right; assumption

end PowStuff

end BooleanFun

--#lint
