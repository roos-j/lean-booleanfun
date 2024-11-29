/-
Copyright (c) 2024 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import BooleanFun.AuxLemmas
import BooleanFun.ToMathlib.Finset

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi

--set_option profiler true

/-!
# Analysis on Boolean functions

This file contains some basic definitions and theorems for analysis
of real-valued Boolean functions mainly following Ryan O'Donnell's book [odonnell2014].
The Hamming cube is represented by the function type `Fin n→Fin 2`, so that
a `BooleanFunc n` is a `(Fin n→Fin 2)→ℝ`.

Thanks to Mathlib, it is relatively straightforward to get started with Fourier analysis:
* Typeclass inference automatically equips `BooleanFunc n` with the appropriate ℝ-vector space structure.
* We define inner product space structure via `InnerProductSpace.Core` and show that
the `walshCharacter`s form an orthonormal basis.
* Then Plancherel's theorem follows from Mathlib's `OrthogonalFamily.inner_sum`.

Even if there was a general framework for Fourier transforms on LCA groups in Mathlib,
it may be preferrable to use this ad-hoc definition due to slightly different notational conventions
in the context of Boolean functions, and the simplicity of working with finite sums.

## Main results

* `walsh_fourier` expresses a Boolean function in terms of its Walsh-Fourier transform
* `variance_le_totalInfluence` is a version of the classical L² Poincaré inequality
* `fourier_convolution` is the convolution theorem for the Walsh-Fourier transform

## Notation

* `𝐄` denotes expectation with respect to uniform probability measure
* `χ S` denotes the Walsh character associated with an `S:Finset (Fin n)`
* `𝓕` denotes the Walsh-Fourier transform `fourierTransform`
* `⟨⬝,⬝⟩` denotes the inner product defined as expectation of product
* `‖⬝‖` denotes the (normalized) L² norm
* `⋆` denotes convolution

## ToDo
* Generalize to `RCLike`-valued
* Fill in some more basic facts

-/

namespace BooleanFun

noncomputable section

open Real BigOperators Function Finset Pi

/-- A Boolean function maps an `n`-tuple of bits (of type `Fin n→Fin 2`) to a real number. -/
abbrev BooleanFunc (n:ℕ) : Type := (Fin n → Fin 2) → ℝ

variable {α:Type*}

variable {n:ℕ} {f g:BooleanFunc n} {x y:Fin n→Fin 2} {i:Fin n}
variable {S S':Finset (Fin n)} {v:Fin 2}

lemma two_eq_zero: (2:Fin n→Fin 2) = 0 := by
  obtain hn|hn := isEmpty_or_nonempty (Fin n)
  · simp only [Unique.eq_default]
  · exact CharTwo.two_eq_zero

/-- Translation invariance -/
lemma sum_translate (a:Fin n→Fin 2): ∑ x, f x = ∑ x, f (x+a) := by
  apply sum_bijective (λ x↦x+a)
  · constructor
    · intro x y; simp
    · intro y; use y+a; abel_nf; simp [two_eq_zero]
  · simp
  · intro i _; abel_nf; simp [two_eq_zero]

/-- The expectation of a Boolean function is its average value with respect to the uniform
probability measure on `Fin n→Fin 2`. -/
def expectation: BooleanFunc n→ₗ[ℝ] ℝ := {
  toFun := λ f => (1/2)^n * ∑ i, f i
  map_add' := by
    intro f g
    simp only [one_div, inv_pow, Pi.add_apply]
    rw [sum_add_distrib]
    ring
  map_smul' := by
    intro c f
    simp
    rw [←mul_sum]
    ring
}

/-- Expectation of a Boolean function -/
notation "𝐄" => expectation

lemma expectation_mul_apply: 𝐄 (λ x↦(f x)*(g x)) = 𝐄 (f*g) := by rfl

/-- Definition of Walsh character -/
abbrev walshCharacter (S:Finset (Fin n)): BooleanFunc n := λ x => ∏ i∈S, (-1)^(x i).val

/-- Walsh character -/
notation "χ" => walshCharacter

lemma walsh_def: χ S x = ∏ i∈S, (-1)^(x i).val := by rfl

lemma walsh_ne_zero: χ S x ≠ 0 := by
  apply prod_ne_zero_iff.mpr; intro i _; simp

lemma walsh_eq_neg_one_pow_sum: χ S x = (-1)^∑ i∈S, (x i).val := prod_pow_eq_pow_sum _ _ _
-- or use Finset.cons_induction

/-- Walsh characters are characters. -/
lemma walsh_add: χ S (x+y) = (χ S x)*(χ S y) := by
  rw [←prod_mul_distrib, prod_congr (by rfl)]
  have: ∀ v:Fin 2, v = 0 ∨ v = 1 := by decreasing_trivial
  intro i _
  dsimp
  obtain ⟨hx|hx,hy|hy⟩ := And.intro (this (x i)) (this (y i))
    <;> { rw [hx, hy]; simp }

/-- Dual space of Boolean functions as the type of real-valued functions on `Finset (Fin n)`. -/
abbrev BooleanFunc' n := Finset (Fin n)→ℝ

/-- The Walsh-Fourier transform of a Boolean function `f` is defined on sets of coordinates
`S:Finset (Fin n)` as expectation of the Walsh character `χ S` times `f`. -/
def fourierTransform: BooleanFunc n→ₗ[ℝ] BooleanFunc' n := {
  toFun := λ f => λ S => 𝐄 (χ S * f)
  map_add' := by
    intro f g
    funext S
    simp
    ring_nf
    simp
  map_smul' := by
    intro c f
    funext S
    simp
}

/-- Walsh-Fourier transform on Boolean functions -/
notation "𝓕" => fourierTransform

theorem expectation_eq_fourier: 𝐄 f = 𝓕 f ∅ := by
  unfold fourierTransform
  unfold walshCharacter
  unfold expectation
  simp only [one_div, inv_pow, LinearMap.coe_mk,
      AddHom.coe_mk, Pi.mul_apply, prod_empty, one_mul]

/-- The inner product of two Boolean functions is the expectation of their pointwise product. -/
--use bilinear map API?
abbrev inner_product {n : ℕ} (f g : BooleanFunc n): ℝ := 𝐄 (f*g)

@[simp]
theorem inner_prod_self_nn: inner_product f f ≥ 0 := by
  apply mul_nonneg
  norm_num
  apply sum_nonneg
  intros x _
  apply mul_self_nonneg

/-- Boolean functions form an inner product space. -/
instance instInnerProductSpaceCoreBooleanFunc : InnerProductSpace.Core ℝ (BooleanFunc n) := {
  inner := inner_product
  conj_symm := by
    intros f g
    simp only [conj_trivial]
    unfold inner_product
    rw [mul_comm]
  nonneg_re := by
    intro f
    simp only [RCLike.re_to_real, inner_prod_self_nn]
  add_left := by
    unfold inner_product
    simp only [add_mul, map_add, implies_true]
  smul_left := by
    unfold inner_product
    simp only [Algebra.smul_mul_assoc, map_smul, smul_eq_mul, conj_trivial, implies_true]
  definite := by
    intro f
    dsimp
    unfold inner_product expectation
    simp only [one_div, inv_pow, LinearMap.coe_mk, AddHom.coe_mk, Pi.mul_apply, mul_eq_zero,
      inv_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, false_or]
    intro hf
    ext x
    rw [Pi.zero_apply]
    have hff : 0 ≤ f*f := by
      intro x
      simp only [Pi.zero_apply, Pi.mul_apply]
      exact mul_self_nonneg _
    have := (Fintype.sum_eq_zero_iff_of_nonneg hff).1 hf
    have := congr_fun this x
    exact mul_self_eq_zero.1 this
}

instance instNormedAddCommGroupBooleanFunc: NormedAddCommGroup (BooleanFunc n) :=
  instInnerProductSpaceCoreBooleanFunc.toNormedAddCommGroup

instance: SeminormedAddCommGroup (BooleanFunc n) :=
  instNormedAddCommGroupBooleanFunc.toSeminormedAddCommGroup

instance instInnerProductSpaceBooleanFunc: InnerProductSpace ℝ (BooleanFunc n) :=
  InnerProductSpace.ofCore instInnerProductSpaceCoreBooleanFunc

/-- Inner product of Boolean functions -/
notation "⟨" f ", " g "⟩" => inner (𝕜:=ℝ) f g


@[local simp]
lemma inner_eq_inner_product: ⟨f,g⟩ = inner_product f g := by rfl

instance: Norm (BooleanFunc n) := InnerProductSpace.Core.toNorm (𝕜:=ℝ) (F:=BooleanFunc n)

lemma inner_comm: ⟨f,g⟩ = ⟨g,f⟩ := by simp; unfold inner_product; simp_rw [mul_comm]

/-- Cauchy-Schwarz inequality on Boolean functions -/
theorem cauchy_schwarz: |⟨f,g⟩| ≤ ‖f‖*‖g‖ := by
  have h := InnerProductSpace.Core.norm_inner_le_norm (𝕜:=ℝ) (F:=BooleanFunc n) f g
  simp at h
  exact h

lemma walsh_sq_eq_one: (χ S)^2 = 1 := by
  funext x
  unfold walshCharacter
  simp only [Pi.pow_apply, Pi.one_apply]
  rw [←prod_pow]
  ring_nf
  simp

@[simp]
lemma expectation_one: @expectation n 1 = 1 := by
  unfold expectation
  simp only [one_div, inv_pow, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, sum_const, card_univ,
    Fintype.card_pi, Fintype.card_fin, prod_const, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
    mul_one, isUnit_iff_ne_zero, ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and,
    not_false_eq_true, IsUnit.inv_mul_cancel]

lemma norm_sq_eq_inner: ‖f‖^2 = ⟨f,f⟩ := by
  rw [←RCLike.re_to_real (x:=⟨f,f⟩), ←InnerProductSpace.norm_sq_eq_inner]

/-- Walsh characters are L² normalized. -/
@[local simp]
theorem walsh_norm_one (S:Finset (Fin n)): ‖χ S‖ = 1 := by
  rw [norm_eq_sqrt_inner (𝕜:=ℝ)]
  simp only [sqrt_eq_one, inner_eq_inner_product, inner_product]
  rw [←pow_two, walsh_sq_eq_one]
  simp

@[local simp]
theorem walsh_inner_self_eq_one: ⟨χ S, χ S⟩ = 1 := by
  rw [←norm_sq_eq_inner, walsh_norm_one, one_pow]

theorem walsh_mul_eq: χ S * χ S' = χ (symmDiff S S') := by
  funext x
  unfold walshCharacter
  simp
  rw (config:={occs:=.pos [1]}) [←sdiff_union_inter S S']
  rw (config:={occs:=.pos [3]}) [←sdiff_union_inter S' S]
  repeat rw [prod_union (disjoint_sdiff_inter _ _)]
  rw [inter_comm S]
  ring_nf
  have haux : (∏ i ∈ S' ∩ S, ((-1:ℝ)^(x i).val)) ^ 2 = 1 := by
    rw [←prod_pow]; ring_nf; simp
  rw [haux, mul_one]
  rw [←prod_union]
  rfl
  rw [disjoint_iff_ne]
  simp
  intro a ha _ b hb hb2
  intro h
  rw [h] at ha
  contradiction

lemma inner_eq_expectation: ⟨f,g⟩ = 𝐄 (f*g) := by rfl

lemma fourier_eq_inner: 𝓕 f S = ⟨χ S, f⟩ := by rfl

/-- Flip the `i₀`th bit of `x`. -/
def flipAt (i₀:Fin n) (x:Fin n→Fin 2): Fin n→ Fin 2 := λ i => if i=i₀ then 1-x i else x i

/-- The `i₀`th bit of `x` is flipped. -/
lemma flipAt_flipped {i₀:Fin n} {x:Fin n→Fin 2}: flipAt i₀ x i₀ = 1- x i₀ := by
  unfold flipAt
  split_ifs <;> tauto

/-- Bits that are not the `i₀`th bits remain unchanged. -/
lemma flipAt_unflipped {i i₀:Fin n} {h:i≠i₀} {x:Fin n→Fin 2}: flipAt i₀ x i = x i := by
  unfold flipAt
  split_ifs <;> tauto

/-- Flipping a bit twice results in no change. -/
lemma flipAt_flipAt_eq {i₀:Fin n} {x:Fin n→Fin 2}: flipAt i₀ (flipAt i₀ x) = x := by
  unfold flipAt
  funext i
  split_ifs with h
  rw [sub_sub_cancel]
  rfl

/-- Flipping a bit is an involution on `Fin n→Fin 2`. -/
theorem flipAt_involutive {i₀:Fin n}: Function.Involutive (flipAt i₀) := by
  intro x
  rw [flipAt_flipAt_eq]

/-- Flipping a bit is a bijection on `Fin n→Fin 2`. -/
theorem flipAt_bijective {i₀:Fin n}: Function.Bijective (flipAt i₀) :=
    Function.Involutive.bijective (flipAt_involutive)

theorem expectation_walsh_eq_zero (hS:S.Nonempty): 𝐄 (χ S) = 0 := by
  unfold expectation
  simp
  unfold walshCharacter
  obtain ⟨i₀, hi₀⟩ := hS
  conv =>
    enter [1,2,x]
    rw [←mul_prod_erase (s:=S) (a:=i₀) (h:=(by assumption))]
  rw [←sum_filter_add_sum_filter_not (p:=λ x=>x i₀ = 0)]
  repeat rw [sum_filter]
  conv =>
    enter [1, 1, 2, x]
    tactic =>
      have h: (if x i₀ = 0 then (-1)^(x i₀).val*∏ x_1 ∈ S.erase i₀, (-1:ℝ) ^ (x x_1).val else 0:ℝ) =
      (if x i₀ = 0 then ∏ x_1 ∈ S.erase i₀, (-1:ℝ) ^ (x x_1).val else 0:ℝ) := by
        split_ifs with h
        rw [h]
        simp
        rfl
    rw [h]
  conv =>
    enter [1, 2, 2, x]
    tactic =>
      have h: (if ¬x i₀ = 0 then (-1)^(x i₀).val*∏ x_1 ∈ S.erase i₀, (-1:ℝ) ^ (x x_1).val else 0:ℝ) = (if ¬x i₀ = 0 then -∏ x_1 ∈ S.erase i₀, (-1:ℝ) ^ (x x_1).val else 0:ℝ) := by
        split_ifs with h
        rfl
        rw [Fin.eq_one_of_neq_zero _ h]
        simp
    rw [h]
  rw [add_eq_zero_iff_eq_neg]
  rw [←sum_neg_distrib]
  symm
  -- Apply flipAt i₀ and use congruence
  rw [←Function.Bijective.sum_comp (flipAt_bijective (i₀:=i₀))]
  apply sum_congr (by rfl)
  intro x _
  simp only [flipAt_flipped, ite_not]
  split_ifs with h1 h2 h3
  rw [h2, sub_zero] at h1
  contradiction
  rw [neg_zero]
  rw [neg_neg]
  apply prod_congr (by rfl)
  intro i hi
  rw [flipAt_unflipped (h:=ne_of_mem_erase hi)]
  rw [Fin.eq_one_of_neq_zero _ h3] at h1
  contradiction

theorem walsh_orthogonal (S S':Finset (Fin n)) (h:S≠S'): ⟨χ S, χ S'⟩ = 0 := by
  simp
  unfold inner_product
  simp [walsh_mul_eq]
  apply expectation_walsh_eq_zero
  by_contra h1
  simp at h1
  contradiction

@[local simp]
theorem walsh_inner_eq: ⟨χ S,χ S'⟩ = oneOn (S=S') := by
  unfold oneOn
  split_ifs with h
  rw [←h]
  exacts [walsh_inner_self_eq_one, walsh_orthogonal S S' h]

theorem walsh_orthonormal : Orthonormal (ι:=Finset (Fin n)) ℝ χ := ⟨walsh_norm_one, walsh_orthogonal⟩

/-- Basis of Walsh characters on `BooleanFunc n`. -/
abbrev walsh_basis : Basis (ι:=Finset (Fin n)) ℝ (BooleanFunc n) :=
  basisOfOrthonormalOfCardEqFinrank (v:=χ) walsh_orthonormal (by simp)

/-- Orthonormal basis of Walsh characters on `BooleanFunc n`. -/
abbrev walsh_orthonormal_basis : OrthonormalBasis (ι:=Finset (Fin n)) ℝ (BooleanFunc n) :=
  Basis.toOrthonormalBasis (basisOfOrthonormalOfCardEqFinrank (v:=χ) walsh_orthonormal (by simp))
    (by simp [walsh_orthonormal])

-- Q: Why does this not work:
-- def walsh_orthonormal_basis' : OrthonormalBasis (ι:=Finset (Fin n)) ℝ (BooleanFunc n) :=
--     Basis.toOrthonormalBasis walsh_basis walsh_orthonormal
/-- Walsh-Fourier expansion: Every Boolean function is equal to a linear combination of Walsh characters. -/
theorem walsh_fourier (f:BooleanFunc n): f = ∑ S:Finset (Fin n), (𝓕 f S)•χ S := by
  have h := OrthonormalBasis.sum_repr' walsh_orthonormal_basis f
  nth_rewrite 1 [←h]
  apply sum_congr (by rfl)
  intro x _
  unfold fourierTransform
  simp

lemma fourier_walsh: 𝓕 (χ S) S' = oneOn (S'=S) := by
  calc _ = ⟨χ S', χ S⟩   := by rfl
       _ = oneOn (S'=S) := walsh_inner_eq

/-- Plancherel/Parseval theorem for Boolean functions. -/
theorem inner_eq_sum_fourier: ⟨f,g⟩ = ∑ S:Finset (Fin n), (𝓕 f S)*(𝓕 g S) := by
  nth_rewrite 1 [walsh_fourier f]
  nth_rewrite 1 [walsh_fourier g]
  exact OrthogonalFamily.inner_sum (Orthonormal.orthogonalFamily walsh_orthonormal) _ _ _

/-- Plancherel/Parseval theorem for Boolean functions. -/
theorem walsh_plancherel: ‖f‖^2 = ∑ S:Finset (Fin n), |𝓕 f S|^2 := by
  simp_rw [norm_sq_eq_inner, inner_eq_sum_fourier (f:=f) (g:=f), sq_abs, pow_two]

/-- Set the `i₀`th bit of `x` to `v`.
TODO: possibly use Mathlib's `Function.update` -/
abbrev setAt (i₀:Fin n) (v:Fin 2) (x:Fin n→Fin 2) : Fin n→Fin 2 :=
  λ i => if i=i₀ then v else x i

/-- The `i₀`th bit of `setAt i₀ v x` has value `v`. -/
lemma setAt_it (i₀:Fin n) (v:Fin 2) (x:Fin n→Fin 2): setAt i₀ v x i₀ = v := by
  unfold setAt
  split_ifs <;> tauto

/-- Bits other than the `i₀`th bit are unaffected by `setAt`. -/
lemma setAt_other (i₀:Fin n) (v:Fin 2) (x:Fin n→Fin 2) (i:Fin n) (h:i₀≠i): setAt i₀ v x i = x i := by
  unfold setAt
  split_ifs <;> tauto

/-- Discrete partial "derivative" of a Boolean function with respect to the `i`th coordinate.
See Def. 2.16 in [odonnell2014]. -/
def dderiv (i:Fin n) : BooleanFunc n→ₗ[ℝ] BooleanFunc n := {
  toFun := λ f => λ x => (f (setAt i 0 x) - f (setAt i 1 x))/2
  map_add' := by
    intro f g
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' := by
    intro c f
    funext x
    simp
    ring
}

lemma walsh_setAt_eq_ite: χ S (setAt i v x) = ite (i∈S) ((-1)^v.val*χ (S \ {i}) x) (χ S x) := by
  unfold walshCharacter
  split_ifs with h
  rw [←mul_prod_erase S _ h]
  rw [setAt_it]
  simp
  rw [erase_eq]
  apply prod_congr (by rfl)
  intro j hj
  rw [setAt_other]
  simp at hj
  symm
  exact hj.right
  apply prod_congr (by rfl)
  intro j hj
  have : i≠j := by
    by_contra hc
    rw [hc] at h
    contradiction
  rwa [setAt_other]

theorem dderiv_walsh (i:Fin n) (S:Finset (Fin n)): dderiv i (χ S) = ite (i∈S) (χ (S \ {i})) 0 := by
  funext x
  unfold dderiv
  simp
  repeat rw [walsh_setAt_eq_ite]
  split_ifs with h <;> simp

theorem dderiv_eq_sum_fourier (i:Fin n) (f:BooleanFunc n): dderiv i f = ∑ S∈{S | i∈S}, 𝓕 f S•χ (S \ {i}) := by
  rw (config:={occs:=.pos [1]}) [walsh_fourier f]
  rw [map_sum, sum_filter, sum_congr (by rfl)]
  intro S _
  rw [map_smul, dderiv_walsh]
  simp

/-- The `i`th coordinate Laplacian operator as in Def. 2.25 [odonnell2014].  -/
def laplace (i:Fin n) : BooleanFunc n→ₗ[ℝ] BooleanFunc n := {
  toFun := λ f => λ x => (f (x) - f (flipAt i x))/2
  map_add' := by
    intro f g
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' := by
    intro c f
    funext x
    simp
    ring
}

lemma setAt_eq_id (h:x i = v): setAt i v x = x := by
  funext j
  unfold setAt
  split_ifs with hj
  · rw [hj]; symm; assumption
  · rfl

lemma setAt_eq_flipAt (h:x i≠v): setAt i v x = flipAt i x := by
  funext j
  unfold setAt flipAt
  split_ifs with hj
  · rw [hj]; decreasing_trivial
  · rfl

lemma laplace_eq_dderiv (i:Fin n) (f:BooleanFunc n) (x:Fin n→Fin 2):
    laplace i f x = (-1)^(x i).val*(dderiv i f x) := by
  unfold laplace
  unfold dderiv
  dsimp
  have : x i = 0 ∨ x i ≠ 0 := by tauto
  cases this with
  | inl hx =>
    simp [hx]
    rw [setAt_eq_id hx]
    rw [setAt_eq_flipAt]
    · rw [hx]
      tauto
  | inr hx =>
    have hx1 := Fin.eq_one_of_neq_zero (x i) hx
    rw [setAt_eq_id hx1]
    rw [setAt_eq_flipAt hx]
    simp [hx1]
    ring

theorem laplace_walsh (i:Fin n) (S:Finset (Fin n)): laplace i (χ S) = ite (i∈S) (χ S) 0 := by
  funext x
  rw [laplace_eq_dderiv]
  rw [dderiv_walsh]
  split_ifs with h
  · unfold walshCharacter
    rw [←erase_eq]
    rw [mul_prod_erase (s:=S) (a:=i) (f:=λ i => (-1:ℝ)^(x i).val) h]
  · simp only [Pi.zero_apply, mul_zero]

theorem laplace_eq_sum_fourier (i:Fin n) (f:BooleanFunc n): laplace i f = ∑ S∈{S | i∈S}, 𝓕 f S•χ (S) := by
  rw (config:={occs:=.pos [1]}) [walsh_fourier f]
  rw [map_sum, sum_filter, sum_congr (by rfl)]
  intro S _
  rw [map_smul, laplace_walsh]
  simp

/-- The `i`th influence of a Boolean function is defined as the expectation of the `i`th Laplacian squared. -/
abbrev influence (f:BooleanFunc n) (i:Fin n): ℝ := 𝐄 ((laplace i f)^2)

theorem influence_eq_sum_fourier (f:BooleanFunc n) (i:Fin n):
    influence f i = ∑ S∈{S | i∈S}, (𝓕 f S)^2 := by
  unfold influence
  nth_rewrite 1 [laplace_eq_sum_fourier]
  -- it would be nice to have a tactic that does the following kind of calculation
  rw [pow_two, sum_mul_sum]
  rw [map_sum]
  rw [sum_filter]
  conv =>
    enter [1, 2, S]
    conv =>
      arg 2
      rw [map_sum]
      enter [2, S']
      -- it would be nice if there was a tactic that does the following automatically
      rw [mul_smul_comm, map_smul, smul_mul_assoc, map_smul]
      rw [←inner_eq_expectation, walsh_inner_eq]
    simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_filter,
      mem_univ, true_and, ite_ite_same]
  rw [←sum_filter]
  rw [sum_congr (by rfl)]
  intro S _
  rw [←pow_two]

/-- The total influence of a Boolean function is defined as the sum of the `i`th influences. -/
abbrev totalInfluence (f:BooleanFunc n): ℝ := ∑ i, influence f i

theorem totalInfluence_eq_sum_fourier (f:BooleanFunc n): totalInfluence f = ∑ S, S.card*(𝓕 f S)^2 := by
  unfold totalInfluence
  conv =>
    enter [1, 2, i]
    rw [influence_eq_sum_fourier f i]
    rw [sum_filter]
  rw [sum_comm]
  simp

/-- Covariance of two Boolean functions -/
abbrev covariance (f g:BooleanFunc n) : ℝ := 𝐄 (f*g)-𝐄 f*𝐄 g

/-- Variance of a Boolean function defined via covariance -/
abbrev variance (f:BooleanFunc n) : ℝ := covariance f f

theorem covariance_eq_sum_fourier (f g:BooleanFunc n) : covariance f g = ∑ S∈{S:Finset (Fin n) | S.Nonempty}, 𝓕 f S*𝓕 g S := by
  unfold covariance
  nth_rewrite 1 [walsh_fourier f, walsh_fourier g]
  rw [sum_mul_sum, map_sum]
  conv =>
    enter [1,1,2,S]
    rw [map_sum]
    enter [2, S']
    rw [mul_smul_comm, map_smul, smul_mul_assoc, map_smul]
    rw [←inner_eq_expectation, walsh_inner_eq]
    simp
  simp
  rw [←sum_erase_add (a:={})]
  rw [expectation_eq_fourier, expectation_eq_fourier]
  rw [add_sub_assoc]
  conv =>
    enter [1, 2]
    ring_nf
  rw [add_zero]
  rw [sum_congr]
  { -- there should be a lemma in `Finset` for this?
    ext S
    constructor
    · intro h
      simp at *
      exact nonempty_iff_ne_empty.mpr h
    · intro h
      simp at *
      exact nonempty_iff_ne_empty.mp h
  }
  · intro S _
    rw [mul_comm]
  · exact mem_univ ∅

theorem variance_eq_sum_fourier (f:BooleanFunc n) : variance f = ∑ S∈{S:Finset (Fin n) | S.Nonempty}, (𝓕 f S)^2 := by
  have := covariance_eq_sum_fourier f f
  conv =>
    enter [2,2,S]
    rw [pow_two]
  assumption

/-- L² Poincaré inequality: variance of a Boolean function is ≤ total Influence.
See [odonnell2014], Sec. 2.3. -/
theorem variance_le_totalInfluence (f:BooleanFunc n): variance f ≤ totalInfluence f := by
  rw [variance_eq_sum_fourier, totalInfluence_eq_sum_fourier]
  rw [sum_filter]
  gcongr with S
  split_ifs with h
  · nth_rewrite 1 [←one_mul ((𝓕 f S)^2)]
    gcongr
    simp only [Nat.one_le_cast, one_le_card, h]
  · rw [←zero_mul 0]
    gcongr
    simp only [Nat.cast_nonneg]
    exact sq_nonneg (𝓕 f S)


section FourierWeight
-- some redundancy in this section

/-- The `k`th Fourier weight is the sum of squares of degree `k` Fourier coefficients -/
abbrev fourierWeight (k:ℕ) (f:BooleanFunc n) : ℝ := ∑ S∈{S | S.card = k}, |𝓕 f S|^2

/-- Alternative expression for degree one Fourier weight in terms in terms of sum over coordinates -/
abbrev fourierWeightOne (f:BooleanFunc n) : ℝ := ∑ i, |𝓕 f {i}|^2

lemma fourier_weight_one {f:BooleanFunc n} : fourierWeight 1 f = fourierWeightOne f := by
  apply sum_singletons; intro i; rfl

lemma fourier_eq_zero_iff_fourier_weight_eq {k:ℕ} {f:BooleanFunc n}:
    (∀ S, S.card ≠ k → 𝓕 f S = 0) ↔ fourierWeight k f=‖f‖^2 := by
  constructor
  · intro h
    have h: ∀ S, S.card ≠ k → |𝓕 f S|^2 = 0 := by
      intro S hS; simp; exact h S hS
    symm
    rw [walsh_plancherel]
    calc
      _ = fourierWeight k f + ∑ S∈{S | S.card ≠ k}, |𝓕 f S|^2 :=
        by rw [sum_filter_add_sum_filter_not]
      _ = fourierWeight k f + ∑ S, if S.card ≠ k then |𝓕 f S|^2 else 0 :=
        by rw [sum_filter]
      _ = fourierWeight k f :=
        by conv => {enter [1,2,2,S]; rw [rw_ite_left (h S), ite_self]}; simp
  · intro h S hS
    have : ∑ S ∈ {S | S.card≠k}, |𝓕 f S|^2 = 0 := by
      symm
      calc 0 = ‖f‖^2 - ‖f‖^2                              := by ring
          _ = ∑ S, |𝓕 f S|^2 - fourierWeight k f          := by rw [h, walsh_plancherel]
          _ = ∑ S∈{S | S.card = k}, |𝓕 f S|^2 + ∑ S∈{S | S.card ≠ k}, |𝓕 f S|^2
                - fourierWeight k f                       := by rw [sum_filter_add_sum_filter_not]
          _ = ∑ S∈{S | S.card ≠ k}, |𝓕 f S|^2             := by rw [add_comm, add_sub_assoc, sub_self, add_zero]
    have := (sum_eq_zero_iff_of_nonneg <| by intro S _; apply pow_two_nonneg).mp this
    specialize this S (by simp [hS])
    rw [sq_abs, pow_eq_zero_iff (by trivial)] at this
    assumption

lemma eq_sum_fourier_of_fourier_weight {k:ℕ} {f:BooleanFunc n} (h:fourierWeight k f=‖f‖^2):
    f = ∑ S∈{S|S.card = k}, 𝓕 f S • χ S := by
  have hf : ∑ S ∈ {S | S.card≠k}, 𝓕 f S•χ S = 0 := by
    rw [sum_eq_zero]
    intro S hS
    rw [smul_eq_zero]
    left
    simp at hS
    exact fourier_eq_zero_iff_fourier_weight_eq.mpr h S hS
  calc
    f = ∑ S, 𝓕 f S•χ S                     := walsh_fourier f
    _ = ∑ S ∈ {S | S.card=k}, 𝓕 f S•χ S +
      ∑ S ∈ {S | S.card≠k}, 𝓕 f S•χ S     := by rw [sum_filter_add_sum_filter_not]
    _ = ∑ S ∈ {S | S.card=k}, 𝓕 f S•χ S    := by rw [hf, add_zero]

lemma eq_sum_degree_one_of_fourier_weight_one {f:BooleanFunc n} (h:fourierWeight 1 f=‖f‖^2) :
    ∀ x, f x = ∑ i, 𝓕 f {i} * (-1)^(x i).val := by
  intro x
  nth_rewrite 1 [eq_sum_fourier_of_fourier_weight h, sum_apply]
  apply sum_singletons
  intro i
  simp only [Pi.smul_apply, prod_singleton, smul_eq_mul]

lemma eq_sum_degree_one_of_fourier_eq_zero {f:BooleanFunc n} (h:∀ S, S.card ≠ 1 → 𝓕 f S = 0):
    ∀ x, f x = ∑ i, 𝓕 f {i} * (-1)^(x i).val :=
  eq_sum_degree_one_of_fourier_weight_one (fourier_eq_zero_iff_fourier_weight_eq.mp h)

end FourierWeight

section Multiplier

/-- Walsh-Fourier multiplier as an ℝ-linear operator on Boolean functions -/
def multiplier (m:ℕ→ℝ): BooleanFunc n→ₗ[ℝ] BooleanFunc n := {
  toFun := λ f => ∑ S:Finset (Fin n), (m S.card)•𝓕 f S•χ S
  map_add' := by
    intro f g
    ext x
    dsimp
    repeat rw [sum_apply]
    rw [←sum_add_distrib, sum_congr (by rfl)]
    intro S _
    simp only [map_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' := by
    intro c f
    ext x
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, sum_apply, RingHom.id_apply]
    rw [mul_sum, sum_congr (by rfl)]
    intro S _
    ring
}

/-- Walsh characters are eigenfunctions of multipliers. -/
lemma multiplier_walsh {m:ℕ→ℝ} {S:Finset (Fin n)}: multiplier m (χ S) = (m S.card)•χ S := by
  unfold multiplier
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  conv => enter [1,2,S']; rw [fourier_walsh]
  simp

/-- The noise operator defined via Fourier expansion. See Prop. 2.47 in [odonnell2014]. -/
abbrev noise_operator (ρ:ℝ): BooleanFunc n→ₗ[ℝ] BooleanFunc n := multiplier (ρ^·)

/-- Noise stability  -/
abbrev noise_stability (ρ:ℝ) (f:BooleanFunc n) := ⟨f, noise_operator ρ f⟩

lemma noise_stability_eq_sum_fourier {ρ:ℝ}: noise_stability ρ f = ∑ S, ρ^(S.card)*|𝓕 f S|^2 := by
  unfold noise_stability
  nth_rewrite 1 [walsh_fourier f]
  unfold noise_operator multiplier
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rewrite [sum_inner]
  conv => enter [1, 2, S]; rw [inner_smul_left, inner_sum];
          enter [2,2,S']; rw [inner_smul_right]; rw [inner_smul_right];
          rw [walsh_inner_eq]
  simp
  apply sum_congr (by rfl)
  intro S _
  ring

end Multiplier

section Convolution

/-- Discrete convolution of Boolean functions -/
abbrev convolution (f g:BooleanFunc n): BooleanFunc n := λ x↦𝐄 (λ y↦(f y)*(g (x+y)))

/-- Discrete convolution of Boolean functions -/
infixl:67 "⋆" => convolution

-- lemma convolution_comm: f⋆g = g⋆f := by
--   sorry

-- lemma convolution_assoc: f⋆g⋆h = f⋆(g⋆h) := by
--   sorry

/-- Convolution theorem: the Walsh-Fourier transform turns convolution into pointwise product. -/
lemma fourier_convolution: 𝓕 (f⋆g) = (𝓕 f)*(𝓕 g) := by
  -- (1/2)^n*∑ x, (χ S x)*( (1/2)^n*∑ y, (f y)*(g (x+y))   )
  funext S
  unfold fourierTransform convolution expectation
  dsimp
  -- = ∑ y, ∑ x, (1/2)^n*(1/2)^n*(χ S x)*(f y)*(g (x+y))
  simp_rw [mul_sum]; rw [sum_comm]
  -- chg var. x ↦ x+y using 2*y = 0
  conv => enter [1,2,y]; rw [sum_translate y]
  -- use character add. property
  -- (1/2)^n*∑ y, (1/2)^n*∑ x, (χ S x)*(χ S y)*(f y)*(g x)
  simp_rw [walsh_add]
  rw [sum_comm]
  -- reorder -- there should be short tactics for these things
  simp_rw [sum_mul]
  apply sum_congr (by rfl)
  intro y _
  apply sum_congr (by rfl)
  intro x _
  ring_nf
  rw [two_eq_zero, mul_zero, add_zero]

end Convolution

end

--#lint
--#min_imports
