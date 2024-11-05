/-
Copyright (c) 2024 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import BooleanFun.Basic

--set_option profiler true

/-!
# Boolean valued functions

This file introduces a typeclass `BooleanValued` for Boolean functions only taking values `±1`
and proves some basic properties specific to Boolean-valued functions.

## Main results

* `eq_character_of_fourier_weight_one_eq_one`, used in the proof of Arrow's theorem
* `almost_character` -- a theorem on BLR linearity testing
-/

noncomputable section

namespace BooleanFun

open BooleanFun Finset Function Fin

variable {n:ℕ} {f g:BooleanFunc n} {x:Fin n→Fin 2}

/-- `BooleanValued f` bundles a proof that `f` takes values `±1`. -/
class BooleanValued (f: BooleanFunc n): Prop where
  one_or_neg_one: ∀ x, f x = 1 ∨ f x = -1

namespace BV

variable [hbv: BooleanValued f] [hbvg: BooleanValued g]

lemma eq_one_or_eq_neg_one: ∀ x, f x = 1 ∨ f x = -1 := hbv.one_or_neg_one

lemma norm_sq_eq_one:
    ‖f‖^2 = 1 := by
  unfold norm instNormBooleanFunc InnerProductSpace.Core.toNorm
  dsimp
  rw [inner_eq_inner_product]
  unfold inner_product
  conv in f * f =>
    ext x
    dsimp
    tactic =>
      have : f x * f x = 1 := by
        cases hbv.one_or_neg_one x with | _ => simp [*]
    rw [this]
  have : (λ_:Fin n→Fin 2↦(1:ℝ)) = (1:BooleanFunc n) := by ext; simp
  simp [this]

lemma fourier_eq_one:
    ∑ S, |𝓕 f S|^2 = 1 := by
  rw [←walsh_plancherel]
  exact norm_sq_eq_one

lemma eq_neg_one_of_ne_one (h':f x≠1) : f x = -1 :=
  or_iff_not_imp_left.mp (hbv.one_or_neg_one x) h'

lemma eq_one_of_ne_neg_one (h':f x≠-1) : f x = 1 :=
  or_iff_not_imp_right.mp (hbv.one_or_neg_one x) h'

instance neg_boolean_valued [hbv: BooleanValued f]: BooleanValued (-f) where
  one_or_neg_one := by intro x; rw [Pi.neg_apply, neg_inj, neg_eq_iff_eq_neg, or_comm]; exact hbv.one_or_neg_one _

/-- Walsh characters are Boolean valued -/
instance (S:Finset (Fin n)): BooleanValued (χ S) where
    one_or_neg_one := by simp_rw [walsh_eq_neg_one_pow_sum, neg_one_pow_eq_or _, implies_true]

section DegreeOne

/-- A Boolean valued function that is a linear combination of degree one characters must be constant
times a degree one character.
Most involved step towards `eq_character_of_fourier_weight_one_eq_one`. -/
-- Unfortunately a bit lengthy
lemma eq_character_of_eq_sum_degree_one (hn:n>0) (hf:∀ x, f x = ∑ i, 𝓕 f {i}*(-1)^(x i).val):
    ∃ S∈{S|S.card = 1}, ∃ c:ℝ, f = c•χ S := by
  wlog hf1: f 0 = 1 with h1
  { -- replace f by -f
    -- have h': IsBooleanValued (-f) := neg_is_boolean_valued (h:=h)
    have hf' : ∀ x, (-f) x = ∑ i, 𝓕 (-f) {i}*(-1)^(x i).val := by intro x; simp; exact hf x
    have : (-f) 0 = 1 := by
      rw [Pi.neg_apply, neg_eq_iff_eq_neg]; exact eq_neg_one_of_ne_one hf1
    specialize h1 hn hf' this
    obtain ⟨S, hS0, hS1⟩ := h1
    obtain ⟨c, hc⟩ := hS1
    use S
    constructor
    · assumption
    · use -c
      rw [neg_smul, ←hc, neg_neg]
  }

  cases n with
  | zero => contradiction
  | succ n =>
    induction n with
    | zero => -- only one coordinate
      use {0}
      simp
      use 1
      simp
      ext x
      rw [hf] at hf1
      simp at hf1
      rw [hf]
      simpa
    | succ n hi => -- will reduce one coordinate
      have hf0eq : f 0 = ∑ i, 𝓕 f {i} := by
        rw [hf]
        apply sum_congr (by rfl)
        intro i _
        simp
      have hf0feq : ∀ i₀, f (flipAt i₀ 0) = ∑ i∈univ.erase i₀, 𝓕 f {i} + -𝓕 f {i₀}:= by
        intro i₀
        rw [hf]
        rw [←sum_erase_add (a:=i₀)]
        congr 1
        · apply sum_congr (by rfl)
          intro i hi
          rw [flipAt_unflipped (h:=ne_of_mem_erase hi)]
          rw [Pi.zero_apply, Fin.val_zero, pow_zero, mul_one]
        · rw [flipAt_flipped]
          rw [Pi.zero_apply, sub_zero, Fin.val_one, pow_one, mul_neg, mul_one]
        · exact mem_univ i₀
      -- key step:
      have: ∃ i₀, f (flipAt i₀ 0) = 1 := by
        by_contra hc -- suppose not
        have hfm1: ∀i, f (flipAt i 0) = -1 := by
          intro i; exact eq_neg_one_of_ne_one ((not_exists.mp hc) i)
        have : ∀ i, 𝓕 f {i} = 1 := by
          intro i; symm
          calc
            1 = (1 - (-1))/2              := by norm_num
            _ = (f 0 - f (flipAt i 0))/2 := by rw [hf1, hfm1]
            _ = (∑ i', 𝓕 f {i'} - ∑ i'∈univ.erase i, 𝓕 f {i'} + 𝓕 f {i})/2 := by rw [hf0eq, hf0feq]; ring
            _ = _                         := by rw [←sum_erase_add (a:=i)]; ring; exact mem_univ i
        have : f 0 = n+2 := by
          rw [hf0eq]
          conv => enter [1,2,i]; rw [this]
          simp; ring
        have : (1:ℝ) ≥ 2 := by
          calc 1 = f 0   := by symm; exact hf1
               _ = n + 2 := by exact this
               _ ≥ 0 + 2 := by gcongr; exact Nat.cast_nonneg n
               _ = 2     := by simp
        have : ¬(1:ℝ)≥2  := by simp
        exact this (by assumption)
      obtain ⟨i₀,hi₀⟩ := this -- this coordinate must have zero coefficient
      have hFi0zero : 𝓕 f {i₀} = 0 := by
        symm
        calc 0 = (1 - 1)/2                  := by ring
             _ = (f 0 - f (flipAt i₀ 0))/2 := by rw [hf1, hi₀]
             _ = ((∑ i, 𝓕 f {i} - ∑ i∈univ.erase i₀, 𝓕 f {i}) + 𝓕 f {i₀})/2 :=
              by rw [hf0eq, hf0feq]; ring
             _ = 𝓕 f {i₀} :=
              by rw [←sum_erase_add (a:=i₀) (h:=mem_univ i₀)]; ring
      -- apply inductive hypothesis to the fiber with i₀ coordinate fixed
      let g : BooleanFunc (n+1) := λ x => f (Fin.insertNth i₀ 0 x)
      have hgeq: g = ∑ i, 𝓕 f {i₀.succAbove i}•χ {i} := by
        ext x
        simp
        unfold g
        nth_rewrite 1 [hf]
        rw [←sum_erase_add (a:=i₀), hFi0zero, zero_mul, add_zero]
        symm
        apply sum_of_injOn (e:=λ i=>i₀.succAbove i)
        · intro i _ j _
          dsimp
          exact succAbove_right_inj.mp
        · unfold Set.MapsTo
          intro i _
          simp
          apply succAbove_ne i₀
        · intro i hi0 hi1
          simp at hi1
          simp at hi0
          contradiction
        · intro i _
          simp
        · exact mem_univ i₀
      have : ∀ i, 𝓕 g {i} = 𝓕 f {i₀.succAbove i} := by
        intro i
        calc _ = ⟨χ {i}, g⟩       := by rfl
             _ = ⟨χ {i}, ∑ i, 𝓕 f {i₀.succAbove i}•χ {i}⟩ := by rw [hgeq]
             _ = ∑ i', 𝓕 f {i₀.succAbove i'}*⟨χ {i}, χ {i'}⟩ := by
                  rw [inner_sum]; conv => enter[1,2,i']; rw [inner_smul_right]
             _ = 𝓕 f {i₀.succAbove i}                     := by
                  conv => enter [1,2,i']; rw [walsh_inner_eq]
                  simp
      have hgeq': ∀ x, g x = ∑ i, 𝓕 g {i}*(-1)^(x i).val := by
        intro x; nth_rewrite 1 [hgeq]; rw [sum_apply]; apply sum_congr (by rfl); intro i _; simp [this]
      have : g 0 = 1 := by unfold g; simp; exact hf1
      have : BooleanValued g := BooleanValued.mk
        (by intro x; exact hbv.one_or_neg_one (Fin.insertNth i₀ 0 x))
      have := hi (f:=g) (Nat.succ_pos n) (by assumption) (by assumption)
      obtain ⟨S,hS1,hS2⟩ := this
      obtain ⟨c,hc⟩ := hS2
      simp at hS1
      obtain ⟨i₁,hi₁⟩ := card_eq_one.mp hS1
      use {Fin.succAbove i₀ i₁}
      constructor
      · simp
      · use c
        funext x
        simp
        -- f is independent of i₀-coordinate
        have hfxi: f x = f (update x i₀ 0) := by
          calc f x = ∑ i, 𝓕 f {i}*(-1)^(x i).val :=
                  by rw [hf]
                _  = ∑ i∈univ.erase i₀, 𝓕 f {i}*(-1)^(x i).val + 𝓕 f {i₀}*(-1)^(x i₀).val :=
                  by rw [sum_erase_add (h:=mem_univ i₀)]
                _  = ∑ i∈univ.erase i₀, 𝓕 f {i}*(-1)^(x i).val +   0*(-1)^(update x i₀ 0 i₀).val :=
                  by rw [hFi0zero]; simp
                _  = ∑ i∈univ.erase i₀, 𝓕 f {i}*(-1)^(update x i₀ 0 i).val +   0*(-1)^(update x i₀ 0 i₀).val :=
                  by {congr 1; apply sum_congr (by rfl);
                        intro i hi; apply ne_of_mem_erase at hi; rw [update_noteq hi]}
                _ = _ :=
                  by rw [←hFi0zero, sum_erase_add (h:=mem_univ i₀), ←hf]
        calc _ = f (Fin.insertNth i₀ 0 (Fin.removeNth i₀ x))  := by rw [hfxi, Fin.insertNth_removeNth]
              _ = g (Fin.removeNth i₀ x)                      := by rfl
              _ = (c•χ {i₁}) (Fin.removeNth i₀ x)             := by rw [hc, hi₁]
              _ = _                                           := by simp; left; rfl

/-- A Boolean valued function with degree one Fourier weight equal to one
must be `±1` times a degree one character. -/
lemma eq_character_of_fourier_weight_one_eq_one' (hn:n>0) (hf:fourierWeight 1 f=1):
    ∃ S∈{S|S.card=1}, ∃ c:ℝ, f = c•χ S := by
  have hf' : ∀ x, f x = ∑ i, 𝓕 f {i}*(-1)^(x i).val := by
    apply eq_sum_degree_one_of_fourier_weight_one
    rw [hf, norm_sq_eq_one]
  exact eq_character_of_eq_sum_degree_one hn hf'

/-- A Boolean valued function with degree one Fourier weight equal to one
must be `±1` times a degree one character.
This is [odonnell2014], Exercise 1.19(a). -/
lemma eq_character_of_fourier_weight_one_eq_one (hn:n>0) (hf:fourierWeight 1 f=1):
    ∃ i, ∃ c:ℝ, f = c•χ {i} := by
  obtain ⟨S, hS, hS'⟩ := eq_character_of_fourier_weight_one_eq_one' hn hf
  obtain ⟨i, hi⟩ := card_eq_one.mp hS
  use i
  rwa [hi] at hS'

end DegreeOne

section Distance

/-- The Hamming distance of two Boolean-valued functions is equal to
the proportion of inputs where they are not equal. The definition does not
require `f g` be Boolean-valued, but it will only be used in this context. -/
abbrev distance (f g:BooleanFunc n): ℝ :=
  𝐄 (λ x↦oneOn (f x≠g x))

lemma oneOn_eq_of_one_or_neg_one {x y:ℝ} (hx:x=1 ∨ x=-1) (hy:y=1 ∨ y=-1):
    oneOn (x=y) = (1/2)*(1+x*y) := by
  obtain ⟨hx|hx, hy|hy⟩ := And.intro hx hy <;> { rw [hx, hy]; norm_num }

lemma oneOn_ne_of_one_or_neg_one {x y:ℝ} (hx:x=1 ∨ x=-1) (hy:y=1 ∨ y=-1):
    oneOn (x≠y) = (1/2)*(1-x*y) := by
  obtain ⟨hx|hx, hy|hy⟩ := And.intro hx hy <;> { rw [hx, hy]; norm_num }

lemma distance_eq: distance f g = 𝐄 (λ x↦(1/2)*(1-(f x)*(g x))) := by
  unfold distance
  simp_rw [oneOn_ne_of_one_or_neg_one (hbv.one_or_neg_one _) (hbvg.one_or_neg_one _)]

lemma inner_eq_distance: ⟨f,g⟩ = 1-2*distance f g := by
  rw [distance_eq]
  unfold expectation
  dsimp
  rw [←mul_sum, sum_sub_distrib]
  ring_nf
  simp
  rw [mul_comm, ←inv_pow, ←one_div]
  rfl

end Distance

section BLR
/-!
  We introduce the BLR "linearity" test [Blum, Luby, Rubinfeld][blr1990]
  following O'Donnell [odonnell2014], Sec. 1.6.
-/

/-- The BLR test accepts `f` on independently and uniformly chosen `x y` if `(f x)*(f y)=f (x+y)`.
The acceptance probability is the proportion of inputs `x y` on which the test accepts. -/
abbrev acceptanceProbabilityBLR (f:BooleanFunc n): ℝ :=
  𝐄 $ λ x ↦ 𝐄 $ λ y ↦ oneOn $ (f x)*(f y)=f (x+y)

lemma acceptanceProbabilityBLR_eq: acceptanceProbabilityBLR f =
    (𝐄 $ λ x ↦ 𝐄 $ λ y ↦ (1/2)*(1+(f x)*(f y)*(f (x+y)))) := by
  have hl: ∀ x y, (f x)*(f y) = 1 ∨ (f x)*(f y) = -1 := by
    intro x y
    obtain ⟨hx|hx,hy|hy⟩ := And.intro (hbv.one_or_neg_one x) (hbv.one_or_neg_one y)
      <;> { rw [hx, hy]; simp }
  unfold acceptanceProbabilityBLR
  simp_rw [oneOn_eq_of_one_or_neg_one (hl _ _) (hbv.one_or_neg_one _)]

omit hbv in
-- A "trivial" step in the proof of `almost_character`
-- would be nice if this could be done with very few tactics
private lemma _aux_lemma: (𝐄 $ λ x ↦ 𝐄 $ λ y ↦ (1/2)*(1+(f x)*(f y)*(f (x+y))))
      = (1/2)*(1+(𝐄 $ λ x ↦ (f x)*(𝐄 $ λ y ↦ (f y)*(f (x+y))))) := by
    unfold expectation
    dsimp
    conv => enter [1,2,2,x]; rw [←mul_sum, sum_add_distrib, mul_add, mul_add]
            simp; arg 2; rw [←mul_assoc, mul_comm _ 2⁻¹, mul_assoc]
            enter [2,2,2,y]; rw [mul_assoc]
    conv => enter [1,2,2,x,2]; rw [←mul_sum]
            rw [←mul_assoc, ←mul_assoc, mul_comm _ (f x), ←mul_assoc, mul_comm (f x) _]
            rw [mul_assoc, mul_assoc]
    rw [sum_add_distrib, Finset.sum_const]
    simp
    rw [←mul_sum, ←mul_add, ←mul_assoc, mul_comm _ 2⁻¹, mul_assoc]
    rw [mul_add, inv_mul_cancel₀ (by simp)]

/-- The BLR test can detect that a Boolean valued function is close to being a character.
See [odonnell2014], Theorem 1.30. -/
theorem almost_character {ε:ℝ} (h:acceptanceProbabilityBLR f≥1-ε):
    ∃ S, distance f (χ S) ≤ ε := by
  have : 1-ε ≤ (1/2)*(1+∑ S, (𝓕 f S)*(𝓕 f S)^2) := by
    calc
      _ ≤ acceptanceProbabilityBLR f                                := h
      _ = (𝐄 $ λ x ↦ 𝐄 $ λ y ↦ (1/2)*(1+(f x)*(f y)*(f (x+y))))   := acceptanceProbabilityBLR_eq
      _ = (1/2)*(1+(𝐄 $ λ x ↦ (f x)*(𝐄 $ λ y ↦ (f y)*(f (x+y))))) := _aux_lemma
      _ = (1/2)*(1+(𝐄 $ λ x ↦ (f x)*(f⋆f) x))                      := by rfl
      _ = (1/2)*(1+𝐄 (f*(f⋆f)))                                     := by rw [expectation_mul_apply]
      _ = (1/2)*(1+∑ S, (𝓕 f S)*(𝓕 (f⋆f) S))                        :=
        by rw [←inner_eq_expectation, inner_eq_sum_fourier]
      _ = _ := by rw [fourier_convolution]; simp_rw [Pi.mul_apply, pow_two]
  have: ∃ S₀, ∀ S, 𝓕 f S ≤ 𝓕 f S₀ := Finite.exists_max (𝓕 f ·)
  obtain ⟨S₀, hS₀⟩ := this
  have : 1-2*ε ≤ 1-2*distance f (χ S₀) := by
    calc
      _ ≤ ∑ S, (𝓕 f S)*(𝓕 f S)^2  := by linarith
      _ ≤ ∑ S, (𝓕 f S₀)*(𝓕 f S)^2 := by gcongr; exact hS₀ _
      _ ≤ (𝓕 f S₀)*∑ S, |𝓕 f S|^2 := by simp_rw [sq_abs]; rw [mul_sum]
      _ = 𝓕 f S₀                  := by rw [fourier_eq_one, mul_one]
      _ = ⟨f, χ S₀⟩                := by rw [fourier_eq_inner, inner_comm]
      _ = _                        := inner_eq_distance
  use S₀
  linarith


end BLR

end BV

end BooleanFun

--#lint
