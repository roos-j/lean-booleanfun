/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/

import BooleanFun.Basic

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-!

# Bobkov's isoperimetric inequality

## Main definitions

* Gaussian isoperimetric profile `gaussianI`

## Main theorems

* Differential equation for the Gaussian isoperimetric profile `gaussianI_mul_deriv_deriv_eq`
* Bobkov's two-point inequality `bobkov_two_point`

-/

namespace BooleanFun

noncomputable section

open Real intervalIntegral ProbabilityTheory Function Set Filter
open scoped Topology

/-- The standard Gaussian density function -/
def ϕ := gaussianPDFReal 0 1

/-- The standard Gaussian CDF.
**Note:** We prefer to avoid Mathlib's CDF implementation.
 -/
def Φ (t : ℝ) := ∫ s in Iio t, ϕ s

namespace Lemm

lemma ϕ_pos
  : (t : ℝ) → 0 < ϕ t
  := by
  intro t
  unfold ϕ
  apply gaussianPDFReal_pos 0 1 t
  norm_num

lemma integrable_ϕ
  : MeasureTheory.Integrable ϕ
  := by
  unfold ϕ
  exact integrable_gaussianPDFReal 0 1

lemma support_ϕ
  : support ϕ = univ
  := by
  refine support_eq_univ ?_
  intro i
  exact ne_of_gt (ϕ_pos i)

lemma integral_Iio_ϕ_pos
  : (w : ℝ) → 0 < ∫ s in Iio w, ϕ s
  := by
  intro w
  refine (MeasureTheory.integral_pos_iff_support_of_nonneg ?_ ?_).mpr ?_
  .
    change (r : ℝ) → 0 ≤ ϕ r
    exact λ r ↦ le_of_lt (ϕ_pos r)
  .
    apply MeasureTheory.Integrable.restrict
    exact integrable_ϕ
  .
    rw [support_ϕ]
    rw [MeasureTheory.Measure.restrict_apply_univ]
    simp only [volume_Iio, ENNReal.zero_lt_top]

lemma integral_Ici_ϕ_pos
  : (w : ℝ) → 0 < ∫ s in Ici w, ϕ s
  := by
  intro w
  refine (MeasureTheory.integral_pos_iff_support_of_nonneg ?_ ?_).mpr ?_
  .
    change (r : ℝ) → 0 ≤ ϕ r
    exact λ r ↦ le_of_lt (ϕ_pos r)
  .
    apply MeasureTheory.Integrable.restrict
    exact integrable_ϕ
  .
    rw [support_ϕ]
    rw [MeasureTheory.Measure.restrict_apply_univ]
    simp only [volume_Ici, ENNReal.zero_lt_top]

lemma integral_ϕ_eq_one
  : ∫ s : ℝ, ϕ s = 1
  := by
  unfold ϕ
  refine integral_gaussianPDFReal_eq_one 0 ?_
  norm_num

lemma continuous_Φ
  : Continuous Φ
  := by
  refine continuous_iff_continuousAt.mpr ?_
  intro t
  have l_intgϕ
    : MeasureTheory.IntegrableOn ϕ (Iio (t + 1))
    := by
    exact integrable_ϕ.integrableOn
  have l_contΦ
    : ContinuousOn Φ (Iic (t + 1))
    := by
    unfold Φ
    exact MeasureTheory.IntegrableOn.continuousOn_Iic_primitive_Iio l_intgϕ
  apply l_contΦ.continuousAt
  refine Iic_mem_nhds ?_
  exact lt_add_one t

lemma tendsto_Φ_atBot
  : Tendsto Φ atBot (𝓝 0)
  := by
  unfold Φ
  exact MeasureTheory.tendsto_integral_Iio_zero fun ⦃U⦄ a ↦ a

lemma tendsto_Φ_atTop
  : Tendsto Φ atTop (𝓝 1)
  := by
  have l_complement
    : Φ = λ t : ℝ => 1 - ∫ s in Ici t, ϕ s
    := by
    funext t
    apply (eq_sub_iff_add_eq).mpr
    unfold Φ
    rw [← integral_ϕ_eq_one]
    exact integral_Iio_add_Ici integrable_ϕ.integrableOn integrable_ϕ.integrableOn
  have l_tail
    : Tendsto (λ t : ℝ => ∫ s in Ici t, ϕ s) atTop (𝓝 0)
    := by exact MeasureTheory.tendsto_integral_Ici_zero fun ⦃U⦄ a ↦ a
  rw [l_complement]
  have l_sub := l_tail.const_sub 1
  rw [sub_zero] at l_sub
  exact l_sub

end Lemm

/-- The range of the Gaussian CDF is the open interval `(0, 1)`. -/
theorem Φ_range
  : range Φ = Ioo 0 1
  := by
  apply Set.ext
  intro x
  change (∃ i : ℝ, Φ i = x) ↔ (0 < x ∧ x < 1)
  apply Iff.intro
  .
    intro hy
    cases hy with
    | intro w h =>
      rw [← h]
      apply And.intro
      .
        exact Lemm.integral_Iio_ϕ_pos w
      .
        unfold Φ
        have l_intg_split
          : (∫ (s : ℝ) in Iio w, ϕ s) + (∫ (s : ℝ) in Ici w, ϕ s) =
              (∫ (s : ℝ), ϕ s)
          := by
          exact integral_Iio_add_Ici
            Lemm.integrable_ϕ.integrableOn
            Lemm.integrable_ϕ.integrableOn
        rw [Lemm.integral_ϕ_eq_one] at l_intg_split
        rw [← l_intg_split]
        exact lt_add_of_pos_right
          (∫ (s : ℝ) in Iio w, ϕ s)
          (Lemm.integral_Ici_ϕ_pos w)
  .
    intro hy
    cases hy with
    | intro g0 l1 =>
      change x ∈ range Φ
      refine mem_range_of_exists_le_of_exists_ge ?_ ?_ ?_
      .
        exact Lemm.continuous_Φ
      .
        obtain ⟨w, hw⟩ :=
          (Lemm.tendsto_Φ_atBot.eventually_lt_const g0).exists
        apply Exists.intro w
        exact le_of_lt hw
      .
        -- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Order/OrderClosed.html#Filter.Tendsto.eventually_const_lt (leansearch.net)
        obtain ⟨w, hw⟩ :=
          (Lemm.tendsto_Φ_atTop.eventually_const_lt l1).exists
        apply Exists.intro w
        exact le_of_lt hw

namespace Lemm

lemma ϕ_eq
  : (t : ℝ) → ϕ t = (1 / √(2 * π)) * exp (-(t ^ 2) / 2)
  := by
  intro t
  unfold ϕ
  rw [ProbabilityTheory.gaussianPDFReal_def] -- leansearch.net
  simp [mul_one, sub_zero, one_div]

lemma hasDerivAt_ϕ
  : (t : ℝ) → HasDerivAt ϕ (-t * ϕ t) t
  := by
  intro t
  have l_sq
    : HasDerivAt (λ u : ℝ => u ^ 2) (2 * t) t
    := by
    simpa only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      using (hasDerivAt_id t).fun_pow 2
  have l_expo
    : HasDerivAt (λ u : ℝ => -(u ^ 2) / 2) (-t) t
    := by
    have l_quot := l_sq.neg.div_const 2
    have l_quot_val
      : -(2 * t) / 2 = -t
      := by
      ring
    rw [l_quot_val] at l_quot
    exact l_quot
  have l_exp
    : HasDerivAt
        (λ u : ℝ => exp (-(u ^ 2) / 2))
        (exp (-(t ^ 2) / 2) * (-t))
        t
    := by
    exact l_expo.exp
  have l_prod := l_exp.const_mul (1 / √(2 * π))
  have l_lam
    : ϕ = λ u : ℝ => (1 / √(2 * π)) * exp (-(u ^ 2) / 2)
    := by
    funext u
    exact ϕ_eq u
  rw [← l_lam] at l_prod
  have l_product_value
    : (1 / √(2 * π)) * (exp (-(t ^ 2) / 2) * (-t)) = -t * ϕ t
    := by
    rw [ϕ_eq]
    ring
  rw [l_product_value] at l_prod
  exact l_prod

lemma continuous_ϕ
  : Continuous ϕ
  := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (hasDerivAt_ϕ t).continuousAt

lemma hasDerivAt_Φ
  : (t : ℝ) → HasDerivAt Φ (ϕ t) t
  := by
  intro t
  have l_primitive
    : Φ = λ u : ℝ => (∫ s in 0..u, ϕ s) + Φ 0
    := by
    funext u
    apply (sub_eq_iff_eq_add).mp
    unfold Φ
    rw [
      ← MeasureTheory.integral_Iic_eq_integral_Iio,
      ← MeasureTheory.integral_Iic_eq_integral_Iio
    ]
    exact integral_Iic_sub_Iic integrable_ϕ.integrableOn integrable_ϕ.integrableOn
  have l_deriv
    : HasDerivAt (λ u : ℝ => ∫ s in 0..u, ϕ s) (ϕ t) t
    := by
    apply integral_hasDerivAt_right
    .
      exact integrable_ϕ.intervalIntegrable
    .
      exact continuous_ϕ.stronglyMeasurable.stronglyMeasurableAtFilter
    .
      exact continuous_ϕ.continuousAt

  rw [l_primitive]
  exact HasDerivAt.add_const (Φ 0) l_deriv

lemma strictMono_Φ
  : StrictMono Φ
  := by
  apply strictMono_of_hasDerivAt_pos hasDerivAt_Φ -- leansearch
  intro t
  exact ϕ_pos t

lemma Φ_mem_Ioo
  : (t : ℝ) → Φ t ∈ Ioo 0 1
  := by
  intro t
  rw [← Φ_range]
  exact mem_range_self t

lemma Φ_invFun_id
  : {x : ℝ} → x ∈ Ioo 0 1 → Φ (invFun Φ x) = x
  := by
  intro x hx
  apply invFun_eq
  change x ∈ range Φ
  rw [Φ_range]
  exact hx

lemma continuousAt_invFun_Φ
  : {x : ℝ} → x ∈ Ioo 0 1 → ContinuousAt (invFun Φ) x
  := by
  intro x hx
  apply tendsto_order.mpr
  apply And.intro
  .
    intro a ha
    have l_ax
      : Φ a < x
      := by
      rw [← Φ_invFun_id hx]
      exact strictMono_Φ ha
    have l_in
      : ∀ᶠ y in 𝓝 x, y ∈ Ioo 0 1
      := Ioo_mem_nhds hx.1 hx.2
    have l_above
      : ∀ᶠ y in 𝓝 x, Φ a < y
      := eventually_gt_nhds l_ax
    filter_upwards [l_in, l_above]
    intro y hy hay
    apply strictMono_Φ.lt_iff_lt.mp
    rw [Φ_invFun_id hy]
    exact hay
  .
    intro b hb
    have l_xb
      : x < Φ b
      := by
      rw [← Φ_invFun_id hx]
      exact strictMono_Φ hb
    have l_in
      : ∀ᶠ y in 𝓝 x, y ∈ Ioo 0 1
      := Ioo_mem_nhds hx.1 hx.2
    have l_below
      : ∀ᶠ y in 𝓝 x, y < Φ b
      := eventually_lt_nhds l_xb
    filter_upwards [l_in, l_below] with y hy hyb
    apply strictMono_Φ.lt_iff_lt.mp
    rw [Φ_invFun_id hy]
    exact hyb

lemma hasDerivAt_invFun_Φ
  : {x : ℝ} → x ∈ Ioo 0 1 →
      HasDerivAt (invFun Φ) (ϕ (invFun Φ x))⁻¹ x
  := by
  intro x hx
  apply HasDerivAt.of_local_left_inverse
  .
    exact continuousAt_invFun_Φ hx
  .
    exact hasDerivAt_Φ (invFun Φ x)
  .
    exact ne_of_gt (ϕ_pos (invFun Φ x))
  .
    have l_in
      : ∀ᶠ y in 𝓝 x, y ∈ Ioo 0 1
      := Ioo_mem_nhds hx.1 hx.2
    filter_upwards [l_in] with y hy
    exact Φ_invFun_id hy

end Lemm

/-- The Gaussian isoperimetric profile `I = ϕ ∘ Φ⁻¹`

**Implementation note:** Mathematically, the domain of this function is `[0, 1]`, but
we extend it to the whole real line by the junk value `0`.
Careful: In Lean `Φ⁻¹` is the pointwise reciprocal, but we need the inverse function.
 -/
def gaussianI (x : ℝ) := if x ∈ Ioo 0 1 then (ϕ ∘ invFun Φ) x else 0

@[inherit_doc]
scoped notation "𝓘" => gaussianI

@[simp]
theorem gaussianI_zero
  : 𝓘 0 = 0
  := by
  simp [gaussianI]
  -- 0 is out of range (def)

@[simp]
theorem gaussianI_one
  : 𝓘 1 = 0
  := by
  simp [gaussianI]
  -- 1 is out of range (def)

namespace Lemm

lemma gaussianI_eq
  : {x : ℝ} → x ∈ Ioo 0 1 → 𝓘 x = ϕ (invFun Φ x)
  := by
  intro x hx
  unfold gaussianI
  rw [ite_eq_left hx]
  rfl

end Lemm

-- In this section we compute derivatives of `I` on `(0, 1)`.
section gaussianI_derivatives

/-- The Gaussian isoperimetric profile is differentiable on `(0, 1)` -/
-- original: theorem hasDerivAt_gaussianI (hx : x ∈ Ioo 0 1) : HasDerivAt 𝓘 (-invFun Φ x) x
theorem hasDerivAt_gaussianI
  : {x : ℝ} → x ∈ Ioo 0 1 → HasDerivAt 𝓘 (-invFun Φ x) x
  := by
  intro x hx
  have l_comp
    : HasDerivAt
        (ϕ ∘ invFun Φ)
        ((-invFun Φ x * ϕ (invFun Φ x)) * (ϕ (invFun Φ x))⁻¹)
        x
    := by
    exact (Lemm.hasDerivAt_ϕ (invFun Φ x)).comp x (Lemm.hasDerivAt_invFun_Φ hx) -- leansearch.net
  have l_nonzero
    : ϕ (invFun Φ x) ≠ 0
    := ne_of_gt (Lemm.ϕ_pos (invFun Φ x))
  rw [mul_assoc, mul_inv_cancel₀ l_nonzero, mul_one] at l_comp -- ChatGPT help: mul_inv_cancel₀ (leansearch.net gave all useless results (that looked good))
  -- cant do rw ite_left because gaussianI is λ bound
  apply l_comp.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx]
  intro y hy
  unfold gaussianI
  rw [ite_eq_left hy]

/-- The Gaussian isoperimetric profile's derivative.  -/
-- original: theorem deriv_gaussianI (hx : x ∈ Ioo 0 1) : deriv 𝓘 x = -invFun Φ x
theorem deriv_gaussianI
  : {x : ℝ} → x ∈ Ioo 0 1 → deriv 𝓘 x = -invFun Φ x
  := by
  intro x hx
  exact (hasDerivAt_gaussianI hx).deriv

/-- The Gaussian isoperimetric profile is positive on `(0, 1)`. -/
-- original : theorem gaussianI_pos (hx : x ∈ Ioo 0 1) : 0 < 𝓘 x
theorem gaussianI_pos
  : {x : ℝ} -> (hx : x ∈ Ioo 0 1) -> 0 < 𝓘 x
  := by
  intro x hx
  rw [Lemm.gaussianI_eq hx]
  exact Lemm.ϕ_pos (invFun Φ x)

/-- The derivative of the Gaussian isoperimetric profile is also differentiable on `(0, 1)`. -/
-- original: theorem hasDerivAt_deriv_gaussianI (hx : x ∈ Ioo 0 1) : HasDerivAt (deriv 𝓘) (-(𝓘 x)⁻¹) x
theorem hasDerivAt_deriv_gaussianI
  : {x : ℝ} → x ∈ Ioo 0 1 →
      HasDerivAt (deriv 𝓘) (-(𝓘 x)⁻¹) x
  := by
  intro x hx
  have l_neg
    : HasDerivAt
        (λ y => -invFun Φ y)
        (-(ϕ (invFun Φ x))⁻¹)
        x
    := by
    exact (Lemm.hasDerivAt_invFun_Φ hx).neg
  rw [← Lemm.gaussianI_eq hx] at l_neg
  apply l_neg.congr_of_eventuallyEq
  have l_in
    : ∀ᶠ y in 𝓝 x, y ∈ Ioo 0 1
    := Ioo_mem_nhds hx.1 hx.2
  filter_upwards [l_in] with y hy
  exact deriv_gaussianI hy

/-- The second derivative of the Gaussian isoperimetric profile -/
-- original: theorem deriv_deriv_gaussianI (hx : x ∈ Ioo 0 1) : deriv (deriv 𝓘) x = -(𝓘 x)⁻¹
theorem deriv_deriv_gaussianI
  : {x : ℝ} → x ∈ Ioo 0 1 → deriv (deriv 𝓘) x = -(𝓘 x)⁻¹
  := by
  intro x hx
  exact (hasDerivAt_deriv_gaussianI hx).deriv

/-- The second derivative of the Gaussian isoperimetric profile is negative on `(0, 1)`. -/
-- original: theorem deriv_deriv_gaussianI_neg (hx : x ∈ Ioo 0 1) : deriv (deriv 𝓘) x < 0
theorem deriv_deriv_gaussianI_neg
  : {x : ℝ} → x ∈ Ioo 0 1 → deriv (deriv 𝓘) x < 0
  := by
  intro x hx
  rw [deriv_deriv_gaussianI hx]
  apply neg_lt_zero.mpr
  apply inv_pos.mpr
  exact gaussianI_pos hx

namespace Lemm

lemma tendsto_invFun_Φ_zero
  : Tendsto (invFun Φ) (𝓝[>] 0) atBot
  := by
  apply tendsto_atBot.mpr -- leansearch
  -- idea: Φ is mono -> Φ (invFun Φ a) ≤ Φ b; a ∈ ioo 0 1 -> Φ (invFun Φ a) = a; so a ≤ Φ b
  intro b
  have l_in
    : ∀ᶠ x : ℝ in 𝓝[>] 0, x ∈ Ioo 0 1
    := Ioo_mem_nhdsGT zero_lt_one -- leansearch
  have l_below
    : ∀ᶠ x : ℝ in 𝓝[>] 0, x < Φ b
    := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    exact eventually_lt_nhds (Φ_mem_Ioo b).1
  filter_upwards [l_in, l_below]
  intro x hx hxb
  apply strictMono_Φ.le_iff_le.mp
  rw [Φ_invFun_id hx]
  exact le_of_lt hxb

lemma tendsto_invFun_Φ_one
  : Tendsto (invFun Φ) (𝓝[<] 1) atTop
  := by
  -- same ideea
  apply tendsto_atTop.mpr
  intro b
  have l_in
    : ∀ᶠ x : ℝ in 𝓝[<] 1, x ∈ Ioo 0 1
    := Ioo_mem_nhdsLT zero_lt_one
  have l_above
    : ∀ᶠ x : ℝ in 𝓝[<] 1, Φ b < x
    := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    exact eventually_gt_nhds (Φ_mem_Ioo b).2
  filter_upwards [l_in, l_above] with x hx hbx
  apply strictMono_Φ.le_iff_le.mp
  rw [Φ_invFun_id hx]
  exact le_of_lt hbx

lemma tendsto_ϕ_atBot
  : Tendsto ϕ atBot (𝓝 0)
  := by
  have l_sq_atTop
    : Tendsto (λ t : ℝ => t ^ 2) atTop atTop
    := by
    exact tendsto_pow_atTop (by norm_num)

  have l_sq
    : Tendsto (λ t : ℝ => t ^ 2) atBot atTop
    := by
    simpa only [Function.comp_def, neg_sq]
      using l_sq_atTop.comp tendsto_neg_atBot_atTop

  have l_expo
    : Tendsto (λ t : ℝ => -(t ^ 2) / 2) atBot atBot
    := by
    exact (tendsto_neg_atTop_atBot.comp l_sq).atBot_div_const
      (by norm_num)

  have l_exp
    : Tendsto (λ t : ℝ => exp (-(t ^ 2) / 2)) atBot (𝓝 0)
    := by
    exact Real.tendsto_exp_atBot.comp l_expo

  have l_form
    : ϕ = λ t : ℝ => (1 / √(2 * π)) * exp (-(t ^ 2) / 2)
    := by
    funext t
    exact ϕ_eq t

  rw [l_form]
  simpa only [mul_zero]
    using l_exp.const_mul (1 / √(2 * π))

lemma tendsto_ϕ_atTop
  : Tendsto ϕ atTop (𝓝 0)
  := by
  have l_sq
    : Tendsto (λ t : ℝ => t ^ 2) atTop atTop
    := by
    exact tendsto_pow_atTop (by norm_num)

  have l_expo
    : Tendsto (λ t : ℝ => -(t ^ 2) / 2) atTop atBot
    := by
    exact (tendsto_neg_atTop_atBot.comp l_sq).atBot_div_const
      (by norm_num)

  have l_exp
    : Tendsto (λ t : ℝ => exp (-(t ^ 2) / 2)) atTop (𝓝 0)
    := by
    exact Real.tendsto_exp_atBot.comp l_expo

  have l_form
    : ϕ = λ t : ℝ => (1 / √(2 * π)) * exp (-(t ^ 2) / 2)
    := by
    funext t
    exact ϕ_eq t

  rw [l_form]
  simpa only [mul_zero]
    using l_exp.const_mul (1 / √(2 * π))

lemma tendsto_gaussianI_zero
  : Tendsto 𝓘 (𝓝[>] 0) (𝓝 0)
  := by
  have l_comp
    : Tendsto (ϕ ∘ invFun Φ) (𝓝[>] 0) (𝓝 0)
    := by
    exact tendsto_ϕ_atBot.comp tendsto_invFun_Φ_zero

  apply l_comp.congr'

  have l_in
    : ∀ᶠ x : ℝ in 𝓝[>] 0, x ∈ Ioo 0 1
    := Ioo_mem_nhdsGT zero_lt_one

  filter_upwards [l_in] with x hx
  exact (gaussianI_eq hx).symm


lemma tendsto_gaussianI_one
  : Tendsto 𝓘 (𝓝[<] 1) (𝓝 0)
  := by
  have l_comp
    : Tendsto (ϕ ∘ invFun Φ) (𝓝[<] 1) (𝓝 0)
    := by
    exact tendsto_ϕ_atTop.comp tendsto_invFun_Φ_one

  apply l_comp.congr'

  have l_in
    : ∀ᶠ x : ℝ in 𝓝[<] 1, x ∈ Ioo 0 1
    := Ioo_mem_nhdsLT zero_lt_one

  filter_upwards [l_in] with x hx
  exact (gaussianI_eq hx).symm

lemma continuousOn_gaussianI
  : ContinuousOn 𝓘 (Icc 0 1)
  := by
  intro x hx

  by_cases hx0 : x = 0
  .
    subst x
    have l_cont
      : ContinuousWithinAt 𝓘 (Ioi 0) 0
      := by
      change Tendsto 𝓘 (𝓝[>] 0) (𝓝 (𝓘 0))
      rw [gaussianI_zero]
      exact tendsto_gaussianI_zero

    apply l_cont.insert.mono
    intro y hy
    change y = 0 ∨ 0 < y
    rcases eq_or_lt_of_le hy.1 with hy0 | hy0
    . exact Or.inl hy0.symm
    . exact Or.inr hy0

  by_cases hx1 : x = 1
  .
    subst x
    have l_cont
      : ContinuousWithinAt 𝓘 (Iio 1) 1
      := by
      change Tendsto 𝓘 (𝓝[<] 1) (𝓝 (𝓘 1))
      rw [gaussianI_one]
      exact tendsto_gaussianI_one

    apply l_cont.insert.mono
    intro y hy
    change y = 1 ∨ y < 1
    exact eq_or_lt_of_le hy.2

  have l_in
    : x ∈ Ioo 0 1
    := by
    constructor
    . exact lt_of_le_of_ne hx.1 (Ne.symm hx0)
    . exact lt_of_le_of_ne hx.2 hx1

  exact (hasDerivAt_gaussianI l_in).continuousAt.continuousWithinAt

end Lemm

/-- The Gaussian isoperimetric profile is strictly concave on `[0, 1]`. -/
theorem strictConcaveOn_gaussianI
  : StrictConcaveOn ℝ (Icc 0 1) 𝓘
  := by
  apply strictConcaveOn_of_deriv2_neg
  . exact convex_Icc 0 1
  . exact Lemm.continuousOn_gaussianI
  .
    intro x hx
    rw [interior_Icc] at hx
    change deriv (deriv 𝓘) x < 0
    exact deriv_deriv_gaussianI_neg hx

/-- Differential equation satisfied by the Gaussian isoperimetric profile. -/
-- original: theorem gaussianI_mul_deriv_deriv_eq (hx : x ∈ Ioo 0 1) : 𝓘 x * deriv (deriv 𝓘) x = -1
theorem gaussianI_mul_deriv_deriv_eq
  : {x : ℝ} → x ∈ Ioo 0 1 → 𝓘 x * deriv (deriv 𝓘) x = -1
  := by
  intro x hx
  rw [deriv_deriv_gaussianI hx]
  rw [mul_neg, mul_inv_cancel₀ (ne_of_gt (gaussianI_pos hx))]

/-- The limit of `I' x` tends to `∞` as `x → 0+`. -/
theorem tendsto_deriv_gaussianI_zero
  : Tendsto (deriv 𝓘) (𝓝[>] 0) atTop
  := by
  have l_neg
    : Tendsto (λ x => -invFun Φ x) (𝓝[>] 0) atTop
    := by
    exact tendsto_neg_atBot_atTop.comp Lemm.tendsto_invFun_Φ_zero
  apply l_neg.congr'
  have l_in
    : ∀ᶠ x : ℝ in 𝓝[>] 0, x ∈ Ioo 0 1
    := Ioo_mem_nhdsGT zero_lt_one
  filter_upwards [l_in] with x hx
  exact (deriv_gaussianI hx).symm

/-- The limit of `I' x` tends to `-∞` as `x → 1-`. -/
theorem tendsto_deriv_gaussianI_one
  : Tendsto (deriv 𝓘) (𝓝[<] 1) atBot
  := by
  -- same
  have l_neg
    : Tendsto (λ x => -invFun Φ x) (𝓝[<] 1) atBot
    := by
    exact tendsto_neg_atTop_atBot.comp Lemm.tendsto_invFun_Φ_one
  apply l_neg.congr'
  have l_in
    : ∀ᶠ x : ℝ in 𝓝[<] 1, x ∈ Ioo 0 1
    := Ioo_mem_nhdsLT zero_lt_one
  filter_upwards [l_in] with x hx
  exact (deriv_gaussianI hx).symm

end gaussianI_derivatives

-- In this section we prove Bobkov's two-point inequality.
section twopoint_inequality

-- Todo: formulate this correctly (for any given interval, open?)
-- /-- If a function `I` solves `I · I'' = -c` on an interval for some `0 < c`, then it is concave.
-- **Note:** In Bobkov's formulation `c = 1`.
--  -/
-- theorem concave_of_mul_deriv_deriv_eq_neg {I : ℝ → ℝ}

-- /-- If a function `I` solves `I · I'' = -c` on an interval for some `0 < c`, then `(I') ^ 2` is convex. -/
-- theorem convex_deriv_pow_two_of_mul_deriv_deriv_eq_neg

-- /-- Bobkov's classical two-point inequality for a non-negative function `I` satisfying `I · I'' = -1` on an interval. -/
-- theorem bobkov_two_point_of_mul_deriv_deriv_eq_neg

/-- Bobkov's classical two-point inequality for the Gaussian isoperimetric profile. -/
theorem bobkov_two_point
  {a b : ℝ}
  (ha : a ∈ Icc 0 1)
  (hb : b ∈ Icc 0 1)
  : 2 * 𝓘 ((a + b) / 2) ≤
      √((𝓘 a) ^ 2 + ((a - b) / 2) ^ 2) +
      √((𝓘 b) ^ 2 + ((a - b) / 2) ^ 2)
  := by
  sorry

end twopoint_inequality

-- ToDo: add Bobkov's isoperimetric inequality
-- The idea is that the two point inequality is the 1D case and then one can run induction on dimension

end

end BooleanFun
