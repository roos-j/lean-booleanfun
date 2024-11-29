import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Finset

variable {ι N α:Type*}

section ToAlgebraOrderBigOperatorsGroupFinset

section OrderedCommMonoid

variable [OrderedCommMonoid N]

variable {s : Finset ι} {f : ι → N}

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
lemma all_one_of_le_one_le_of_prod_eq_one:
    (∀ x ∈ s, 1 ≤ f x) → ∏ x ∈ s, f x = 1 → ∀ x ∈ s, f x = 1 := by
  convert Multiset.all_one_of_le_one_le_of_prod_eq_one (s:=s.1.map f) <;> simp

end OrderedCommMonoid

end ToAlgebraOrderBigOperatorsGroupFinset

section ToDataFintypeBasic

variable [Fintype α] [DecidableEq α]

@[simp]
lemma filter_univ_not_mem (s : Finset α) : univ.filter (· ∉ s) = sᶜ := by
  ext; simp only [mem_filter, mem_univ, true_and, mem_compl]

end ToDataFintypeBasic

end Finset
