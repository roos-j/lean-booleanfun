import Mathlib.Algebra.Order.BigOperators.Group.Finset

variable {ι N:Type*}

namespace Finset

section OrderedCommMonoid

variable [OrderedCommMonoid N]

variable {s : Finset ι} {f : ι → N}

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
lemma all_one_of_le_one_le_of_prod_eq_one:
    (∀ x ∈ s, 1 ≤ f x) → ∏ x ∈ s, f x = 1 → ∀ x ∈ s, f x = 1 := by
  convert Multiset.all_one_of_le_one_le_of_prod_eq_one (s:=s.1.map f) <;> simp

end OrderedCommMonoid

end Finset
