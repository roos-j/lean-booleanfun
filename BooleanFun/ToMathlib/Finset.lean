import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Finset

variable {ι N α:Type*}

section ToAlgebraOrderBigOperatorsGroupFinset

section OrderedCommMonoid

variable [OrderedCommMonoid N]

variable {s : Finset ι} {f : ι → N}

-- already exists; this proof is shorter but takes slightly longer
-- @[to_additive sum_eq_zero_iff_of_nonneg]
-- theorem prod_eq_one_iff_of_one_le' :
--     (∀ i ∈ s, 1 ≤ f i) → ((∏ i ∈ s, f i) = 1 ↔ ∀ i ∈ s, f i = 1) :=
--   fun h ↦ ⟨by
--     convert Multiset.all_one_of_le_one_le_of_prod_eq_one (s:=s.1.map f) (by convert h; simp only [Multiset.mem_map,
--       mem_val, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂])
--     simp only [Multiset.mem_map, mem_val, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂],
--     prod_eq_one⟩

end OrderedCommMonoid

end ToAlgebraOrderBigOperatorsGroupFinset

section ToDataFintypeBasic

variable [Fintype α] [DecidableEq α]

@[simp]
lemma filter_univ_not_mem (s : Finset α) : univ.filter (· ∉ s) = sᶜ := by
  ext; simp only [mem_filter, mem_univ, true_and, mem_compl]

end ToDataFintypeBasic

end Finset
