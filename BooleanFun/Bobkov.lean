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
import Mathlib.Analysis.Calculus.MeanValue
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
  : {x : ℝ} → x ∈ Ioo 0 1
    → HasDerivAt (invFun Φ) (ϕ (invFun Φ x))⁻¹ x
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
  : {x : ℝ} → x ∈ Ioo 0 1
    → HasDerivAt (deriv 𝓘) (-(𝓘 x)⁻¹) x
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
-- bobkov lemma 2.b
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

namespace Lemm

lemma hasDerivAt_deriv_gaussianI_pow_two
  : {x : ℝ} → x ∈ Ioo 0 1
    → HasDerivAt
        (λ y : ℝ => (deriv 𝓘 y) ^ 2)
        (-2 * deriv 𝓘 x / 𝓘 x)
        x
  := by
  intro x hx

  have l_sq
    : HasDerivAt
        (λ y : ℝ => (deriv 𝓘 y) ^ 2)
        (2 * deriv 𝓘 x * (-(𝓘 x)⁻¹))
        x
    := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
      using (hasDerivAt_deriv_gaussianI hx).fun_pow 2

  have l_value
    : 2 * deriv 𝓘 x * (-(𝓘 x)⁻¹) =
        -2 * deriv 𝓘 x / 𝓘 x
    := by
    rw [div_eq_mul_inv]
    ring

  rw [l_value] at l_sq
  exact l_sq

lemma hasDerivAt_deriv_deriv_gaussianI_pow_two
  : {x : ℝ} → x ∈ Ioo 0 1
    → HasDerivAt
        (deriv (λ y : ℝ => (deriv 𝓘 y) ^ 2))
        (2 * (1 + (deriv 𝓘 x) ^ 2) / (𝓘 x) ^ 2)
        x
  := by
  intro x hx

  have l_nonzero
    : 𝓘 x ≠ 0
    := ne_of_gt (gaussianI_pos hx)

  have l_first
    : HasDerivAt 𝓘 (deriv 𝓘 x) x
    := by
    rw [deriv_gaussianI hx]
    exact hasDerivAt_gaussianI hx

  have l_quot :=
    ((hasDerivAt_deriv_gaussianI hx).const_mul (-2)).div
      l_first l_nonzero

  have l_value
    : ((-2 * (-(𝓘 x)⁻¹)) * 𝓘 x -
        (-2 * deriv 𝓘 x) * deriv 𝓘 x) / (𝓘 x) ^ 2 =
        2 * (1 + (deriv 𝓘 x) ^ 2) / (𝓘 x) ^ 2
    := by
    field_simp [l_nonzero] ; ring

  rw [l_value] at l_quot

  apply l_quot.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact (hasDerivAt_deriv_gaussianI_pow_two hy).deriv

lemma convexOn_deriv_gaussianI_pow_two
  : ConvexOn ℝ (Ioo 0 1) (λ x : ℝ => (deriv 𝓘 x) ^ 2)
  := by
  apply convexOn_of_deriv2_nonneg'
  . exact convex_Ioo 0 1
  .
    intro x hx
    exact (hasDerivAt_deriv_gaussianI_pow_two hx).differentiableAt.differentiableWithinAt
  .
    intro x hx
    exact (hasDerivAt_deriv_deriv_gaussianI_pow_two hx).differentiableAt.differentiableWithinAt
  .
    intro x hx
    change 0 ≤ deriv (deriv (λ y : ℝ => (deriv 𝓘 y) ^ 2)) x
    rw [(hasDerivAt_deriv_deriv_gaussianI_pow_two hx).deriv]
    positivity

lemma ϕ_neg
  : (t : ℝ) → ϕ (-t) = ϕ t
  := by
  intro t
  simp only [ϕ_eq, neg_sq]

lemma Φ_neg
  : (t : ℝ) → Φ (-t) = 1 - Φ t
  := by
  intro t
  have l_deriv
    : (u : ℝ)
    →   HasDerivAt (λ v : ℝ => Φ (-v) + Φ v) 0 u
    := by
    intro u
    have l_neg
      : HasDerivAt
          (λ v : ℝ => Φ (-v))
          (ϕ (-u) * (-1))
          u
      := by
      exact (hasDerivAt_Φ (-u)).comp u (hasDerivAt_id u).neg
    simpa only [ϕ_neg, mul_neg_one, neg_add_cancel]
      using l_neg.fun_add (hasDerivAt_Φ u)

  have l_const
    : (u : ℝ) → Φ (-u) + Φ u = Φ (-t) + Φ t
    := by
    intro u
    exact is_const_of_deriv_eq_zero
      (λ v => (l_deriv v).differentiableAt)
      (λ v => (l_deriv v).deriv)
      u t

  have l_reflected
    : Tendsto (λ u : ℝ => Φ (-u)) atTop (𝓝 0)
    := by
    exact tendsto_Φ_atBot.comp tendsto_neg_atTop_atBot

  have l_limit
    : Tendsto (λ u : ℝ => Φ (-u) + Φ u) atTop (𝓝 1)
    := by
    simpa only [zero_add]
      using l_reflected.add tendsto_Φ_atTop

  have l_limit_const
    : Tendsto (λ _ : ℝ => Φ (-t) + Φ t) atTop (𝓝 1)
    := by
    apply l_limit.congr'
    exact Filter.Eventually.of_forall l_const

  have l_sum
    : Φ (-t) + Φ t = 1
    := by
    exact tendsto_nhds_unique tendsto_const_nhds l_limit_const

  exact (eq_sub_iff_add_eq).mpr l_sum

lemma invFun_Φ_one_sub
  : {x : ℝ} → x ∈ Ioo 0 1
    → invFun Φ (1 - x) = -invFun Φ x
  := by
  intro x hx
  have l_in
    : 1 - x ∈ Ioo 0 1
    := by
    constructor
    . linarith [hx.2]
    . linarith [hx.1]
  apply strictMono_Φ.injective
  rw [Φ_invFun_id l_in, Φ_neg, Φ_invFun_id hx]

lemma gaussianI_one_sub
  : (x : ℝ) → 𝓘 (1 - x) = 𝓘 x
  := by
  intro x
  by_cases hx : x ∈ Ioo 0 1
  .
    have l_in
      : 1 - x ∈ Ioo 0 1
      := by
      constructor
      . linarith [hx.2]
      . linarith [hx.1]
    rw [gaussianI_eq l_in, gaussianI_eq hx,
      invFun_Φ_one_sub hx, ϕ_neg]
  .
    have l_out
      : 1 - x ∉ Ioo 0 1
      := by
      intro hy
      apply hx
      constructor
      . linarith [hy.2]
      . linarith [hy.1]
    simp only [gaussianI, ite_eq_right l_out, ite_eq_right hx]

lemma deriv_gaussianI_one_sub
  : {x : ℝ} → x ∈ Ioo 0 1
    → deriv 𝓘 (1 - x) = -deriv 𝓘 x
  := by
  intro x hx
  have l_in
    : 1 - x ∈ Ioo 0 1
    := by
    constructor
    . linarith [hx.2]
    . linarith [hx.1]
  rw [deriv_gaussianI l_in, deriv_gaussianI hx,
    invFun_Φ_one_sub hx]

lemma deriv_gaussianI_pow_two_one_sub
  : {x : ℝ} → x ∈ Ioo 0 1
    → (deriv 𝓘 (1 - x)) ^ 2 = (deriv 𝓘 x) ^ 2
  := by
  intro x hx
  rw [deriv_gaussianI_one_sub hx, neg_sq]

lemma deriv_gaussianI_pow_two_le_of_mem_Icc
  : {a b : ℝ} → a ∈ Ioo 0 1 → b ∈ Icc a (1 - a)
    → (deriv 𝓘 b) ^ 2 ≤ (deriv 𝓘 a) ^ 2
  := by
  intro a b ha hb
  have l_reflected
    : 1 - a ∈ Ioo 0 1
    := by
    constructor
    . linarith [ha.2]
    . linarith [ha.1]
  have l_bound
    : (deriv 𝓘 b) ^ 2 ≤
        max ((deriv 𝓘 a) ^ 2) ((deriv 𝓘 (1 - a)) ^ 2)
    := by
    exact convexOn_deriv_gaussianI_pow_two.le_on_segment
      ha l_reflected (Icc_subset_segment hb)
  rw [deriv_gaussianI_pow_two_one_sub ha, max_self] at l_bound
  exact l_bound

lemma gaussianI_le_of_mem_Icc
  : {a b : ℝ} → a ∈ Icc 0 1 → b ∈ Icc a (1 - a)
    → 𝓘 a ≤ 𝓘 b
  := by
  intro a b ha hb
  have l_reflected
    : 1 - a ∈ Icc 0 1
    := by
    constructor
    . linarith [ha.2]
    . linarith [ha.1]
  have l_bound
    : min (𝓘 a) (𝓘 (1 - a)) ≤ 𝓘 b
    := by
    exact strictConcaveOn_gaussianI.concaveOn.ge_on_segment
      ha l_reflected (Icc_subset_segment hb)
  rw [gaussianI_one_sub, min_self] at l_bound
  exact l_bound

lemma hasDerivAt_gaussianI_pow_two
  : {x : ℝ} → x ∈ Ioo 0 1
    → HasDerivAt
        (λ y : ℝ => (𝓘 y) ^ 2)
        (2 * 𝓘 x * deriv 𝓘 x)
        x
  := by
  intro x hx
  have l_first
    : HasDerivAt 𝓘 (deriv 𝓘 x) x
    := by
    rw [deriv_gaussianI hx]
    exact hasDerivAt_gaussianI hx
  simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    using l_first.fun_pow 2

lemma hasDerivAt_deriv_of_gaussianI_pow_two
  : {x : ℝ} → x ∈ Ioo 0 1
    → HasDerivAt
        (deriv (λ y : ℝ => (𝓘 y) ^ 2))
        (2 * ((deriv 𝓘 x) ^ 2 - 1))
        x
  := by
  intro x hx
  have l_nonzero
    : 𝓘 x ≠ 0
    := ne_of_gt (gaussianI_pos hx)
  have l_first
    : HasDerivAt 𝓘 (deriv 𝓘 x) x
    := by
    rw [deriv_gaussianI hx]
    exact hasDerivAt_gaussianI hx
  have l_prod
    : HasDerivAt
        (λ y : ℝ => 2 * 𝓘 y * deriv 𝓘 y)
        ((2 * deriv 𝓘 x) * deriv 𝓘 x +
          (2 * 𝓘 x) * (-(𝓘 x)⁻¹))
        x
    := by
    exact (l_first.const_mul 2).fun_mul
      (hasDerivAt_deriv_gaussianI hx)
  have l_value
    : (2 * deriv 𝓘 x) * deriv 𝓘 x +
        (2 * 𝓘 x) * (-(𝓘 x)⁻¹) =
        2 * ((deriv 𝓘 x) ^ 2 - 1)
    := by
    field_simp [l_nonzero] ; ring
  rw [l_value] at l_prod
  apply l_prod.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact (hasDerivAt_gaussianI_pow_two hy).deriv

-- bobkov p. 212
def bobkovG (c x : ℝ) := (𝓘 (c + x)) ^ 2 + x ^ 2

lemma hasDerivAt_bobkovG
  : {c x : ℝ} → c + x ∈ Ioo 0 1
    → HasDerivAt
        (bobkovG c)
        (2 * 𝓘 (c + x) * deriv 𝓘 (c + x) + 2 * x)
        x
  := by
  intro c x hx
  have l_shift
    : HasDerivAt (λ y : ℝ => c + y) 1 x
    := by
    exact (hasDerivAt_id x).const_add c
  have l_comp
    : HasDerivAt
        (λ y : ℝ => (𝓘 (c + y)) ^ 2)
        (2 * 𝓘 (c + x) * deriv 𝓘 (c + x))
        x
    := by
    simpa only [Function.comp_def, mul_one]
      using (hasDerivAt_gaussianI_pow_two hx).comp x l_shift
  have l_sq
    : HasDerivAt (λ y : ℝ => y ^ 2) (2 * x) x
    := by
    simpa only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      using (hasDerivAt_id x).fun_pow 2
  unfold bobkovG
  exact l_comp.fun_add l_sq

lemma hasDerivAt_deriv_bobkovG
  : {c x : ℝ} → c + x ∈ Ioo 0 1
    → HasDerivAt
        (deriv (bobkovG c))
        (2 * (deriv 𝓘 (c + x)) ^ 2)
        x
  := by
  intro c x hx
  have l_shift
    : HasDerivAt (λ y : ℝ => c + y) 1 x
    := by
    exact (hasDerivAt_id x).const_add c
  have l_comp
    : HasDerivAt
        (λ y : ℝ => deriv (λ z : ℝ => (𝓘 z) ^ 2) (c + y))
        (2 * ((deriv 𝓘 (c + x)) ^ 2 - 1))
        x
    := by
    simpa only [Function.comp_def, mul_one]
      using (hasDerivAt_deriv_of_gaussianI_pow_two hx).comp x l_shift
  have l_linear
    : HasDerivAt (λ y : ℝ => 2 * y) 2 x
    := by
    simpa only [id_eq, mul_one]
      using (hasDerivAt_id x).const_mul 2
  have l_sum := l_comp.fun_add l_linear
  have l_value
    : 2 * ((deriv 𝓘 (c + x)) ^ 2 - 1) + 2 =
        2 * (deriv 𝓘 (c + x)) ^ 2
    := by
    ring
  rw [l_value] at l_sum
  apply l_sum.congr_of_eventuallyEq
  filter_upwards
    [l_shift.continuousAt.eventually (Ioo_mem_nhds hx.1 hx.2)]
    with y hy
  rw [(hasDerivAt_bobkovG hy).deriv,
    (hasDerivAt_gaussianI_pow_two hy).deriv]

def bobkovR (c x : ℝ) :=
  bobkovG c x + bobkovG c (-x) - 2 * bobkovG c 0 -
    2 * (deriv 𝓘 c) ^ 2 * x ^ 2

lemma hasDerivAt_bobkovR
  : {c x : ℝ} → c + x ∈ Ioo 0 1 → c - x ∈ Ioo 0 1
    → HasDerivAt
        (bobkovR c)
        (deriv (bobkovG c) x - deriv (bobkovG c) (-x) -
          4 * (deriv 𝓘 c) ^ 2 * x)
        x
  := by
  intro c x hp hm
  have l_minus_in
    : c + (-x) ∈ Ioo 0 1
    := by
    simpa only [sub_eq_add_neg] using hm
  have l_plus
    : HasDerivAt (bobkovG c) (deriv (bobkovG c) x) x
    := by
    rw [(hasDerivAt_bobkovG hp).deriv]
    exact hasDerivAt_bobkovG hp
  have l_minus_at
    : HasDerivAt (bobkovG c) (deriv (bobkovG c) (-x)) (-x)
    := by
    rw [(hasDerivAt_bobkovG l_minus_in).deriv]
    exact hasDerivAt_bobkovG l_minus_in
  have l_minus
    : HasDerivAt
        (λ y : ℝ => bobkovG c (-y))
        (-deriv (bobkovG c) (-x))
        x
    := by
    simpa only [Function.comp_def, mul_neg_one]
      using l_minus_at.comp x (hasDerivAt_id x).neg
  have l_sq
    : HasDerivAt (λ y : ℝ => y ^ 2) (2 * x) x
    := by
    simpa only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      using (hasDerivAt_id x).fun_pow 2
  have l_base :=
    ((l_plus.fun_add l_minus).sub_const (2 * bobkovG c 0)).fun_sub
      (l_sq.const_mul (2 * (deriv 𝓘 c) ^ 2))
  have l_value
    : deriv (bobkovG c) x + -deriv (bobkovG c) (-x) -
        (2 * (deriv 𝓘 c) ^ 2) * (2 * x) =
        deriv (bobkovG c) x - deriv (bobkovG c) (-x) -
          4 * (deriv 𝓘 c) ^ 2 * x
    := by
    ring
  rw [l_value] at l_base
  unfold bobkovR
  exact l_base

lemma hasDerivAt_deriv_bobkovR
  : {c x : ℝ} → c + x ∈ Ioo 0 1 → c - x ∈ Ioo 0 1
    → HasDerivAt
        (deriv (bobkovR c))
        (2 * ((deriv 𝓘 (c + x)) ^ 2 +
          (deriv 𝓘 (c - x)) ^ 2 - 2 * (deriv 𝓘 c) ^ 2))
        x
  := by
  intro c x hp hm
  have l_minus_in
    : c + (-x) ∈ Ioo 0 1
    := by
    simpa only [sub_eq_add_neg] using hm
  have l_plus
    : HasDerivAt
        (deriv (bobkovG c))
        (2 * (deriv 𝓘 (c + x)) ^ 2)
        x
    := hasDerivAt_deriv_bobkovG hp
  have l_minus
    : HasDerivAt
        (λ y : ℝ => deriv (bobkovG c) (-y))
        (-(2 * (deriv 𝓘 (c - x)) ^ 2))
        x
    := by
    simpa only [Function.comp_def, mul_neg_one, ← sub_eq_add_neg]
      using (hasDerivAt_deriv_bobkovG l_minus_in).comp x
        (hasDerivAt_id x).neg
  have l_linear
    : HasDerivAt
        (λ y : ℝ => 4 * (deriv 𝓘 c) ^ 2 * y)
        (4 * (deriv 𝓘 c) ^ 2)
        x
    := by
    simpa only [id_eq, mul_one]
      using (hasDerivAt_id x).const_mul (4 * (deriv 𝓘 c) ^ 2)
  have l_base := (l_plus.fun_sub l_minus).fun_sub l_linear
  have l_value
    : 2 * (deriv 𝓘 (c + x)) ^ 2 -
        (-(2 * (deriv 𝓘 (c - x)) ^ 2)) -
        4 * (deriv 𝓘 c) ^ 2 =
        2 * ((deriv 𝓘 (c + x)) ^ 2 +
          (deriv 𝓘 (c - x)) ^ 2 - 2 * (deriv 𝓘 c) ^ 2)
    := by
    ring
  rw [l_value] at l_base
  apply l_base.congr_of_eventuallyEq
  have l_shift_plus
    : HasDerivAt (λ y : ℝ => c + y) 1 x
    := by
    exact (hasDerivAt_id x).const_add c
  have l_shift_minus
    : HasDerivAt (λ y : ℝ => c - y) (-1) x
    := by
    simpa only [id_eq] using (hasDerivAt_id x).const_sub c
  filter_upwards
    [l_shift_plus.continuousAt.eventually (Ioo_mem_nhds hp.1 hp.2),
      l_shift_minus.continuousAt.eventually (Ioo_mem_nhds hm.1 hm.2)]
    with y hyp hym
  exact (hasDerivAt_bobkovR hyp hym).deriv

lemma convexOn_bobkovR
  : {c t : ℝ} → c + t ∈ Ioo 0 1 → c - t ∈ Ioo 0 1
    → ConvexOn ℝ (Icc (-t) t) (bobkovR c)
  := by
  intro c t hp hm
  have l_in
    : {y : ℝ} → y ∈ Icc (-t) t
    →   c + y ∈ Ioo 0 1 ∧ c - y ∈ Ioo 0 1
    := by
    intro y hy
    constructor
    .
      constructor
      . linarith [hm.1, hy.1]
      . linarith [hp.2, hy.2]
    .
      constructor
      . linarith [hm.1, hy.2]
      . linarith [hp.2, hy.1]
  apply convexOn_of_deriv2_nonneg'
  . exact convex_Icc (-t) t
  .
    intro y hy
    have h := l_in hy
    exact (hasDerivAt_bobkovR h.1 h.2).differentiableAt.differentiableWithinAt
  .
    intro y hy
    have h := l_in hy
    exact (hasDerivAt_deriv_bobkovR h.1 h.2).differentiableAt.differentiableWithinAt
  .
    intro y hy
    have h := l_in hy
    change 0 ≤ deriv (deriv (bobkovR c)) y
    rw [(hasDerivAt_deriv_bobkovR h.1 h.2).deriv]
    have l_mid := convexOn_deriv_gaussianI_pow_two.2 h.1 h.2
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    simp only [smul_eq_mul] at l_mid
    have l_center
      : ((1 : ℝ) / 2) * (c + y) +
          ((1 : ℝ) / 2) * (c - y) = c
      := by
      ring
    rw [l_center] at l_mid
    linarith

lemma bobkovG_sum_lower_bound
  : {c x : ℝ} → 0 ≤ x
    → c + x ∈ Ioo 0 1 → c - x ∈ Ioo 0 1
    → 2 * (deriv 𝓘 c) ^ 2 * x ^ 2 ≤
        bobkovG c x + bobkovG c (-x) - 2 * bobkovG c 0
  := by
  intro c x hx hp hm
  have l_even
    : bobkovR c (-x) = bobkovR c x
    := by
    unfold bobkovR
    simp only [neg_neg, neg_sq]
    ring
  have l_zero
    : bobkovR c 0 = 0
    := by
    unfold bobkovR
    simp only [neg_zero]
    ring
  have l_left
    : -x ∈ Icc (-x) x
    := by
    constructor
    . exact le_rfl
    . linarith
  have l_right
    : x ∈ Icc (-x) x
    := by
    constructor
    . linarith
    . exact le_rfl
  have l_center
    : (0 : ℝ) ∈ segment ℝ (-x) x
    := by
    exact Icc_subset_segment ⟨by linarith, hx⟩
  have l_bound
    : bobkovR c 0 ≤ max (bobkovR c (-x)) (bobkovR c x)
    := by
    exact (convexOn_bobkovR hp hm).le_on_segment
      l_left l_right l_center
  rw [l_zero, l_even, max_self] at l_bound
  unfold bobkovR at l_bound
  linarith

-- idk how to "Fix c ∈ (0, 1)"
def bobkovU (c x : ℝ) := bobkovG c x - bobkovG c (-x)

lemma hasDerivAt_bobkovU
  : {c x : ℝ} → c + x ∈ Ioo 0 1 → c - x ∈ Ioo 0 1
    → HasDerivAt
        (bobkovU c)
        (deriv (bobkovG c) x + deriv (bobkovG c) (-x))
        x
  := by
  intro c x hp hm
  have l_minus_in
    : c + (-x) ∈ Ioo 0 1
    := by
    simpa only [sub_eq_add_neg] using hm
  have l_plus
    : HasDerivAt (bobkovG c) (deriv (bobkovG c) x) x
    := by
    rw [(hasDerivAt_bobkovG hp).deriv]
    exact hasDerivAt_bobkovG hp
  have l_minus_at
    : HasDerivAt (bobkovG c) (deriv (bobkovG c) (-x)) (-x)
    := by
    rw [(hasDerivAt_bobkovG l_minus_in).deriv]
    exact hasDerivAt_bobkovG l_minus_in
  have l_minus
    : HasDerivAt
        (λ y : ℝ => bobkovG c (-y))
        (-deriv (bobkovG c) (-x))
        x
    := by
    simpa only [Function.comp_def, mul_neg_one]
      using l_minus_at.comp x (hasDerivAt_id x).neg
  unfold bobkovU
  simpa only [sub_neg_eq_add]
    using l_plus.fun_sub l_minus

lemma hasDerivAt_deriv_bobkovU
  : {c x : ℝ} → c + x ∈ Ioo 0 1 → c - x ∈ Ioo 0 1
    → HasDerivAt
        (deriv (bobkovU c))
        (2 * ((deriv 𝓘 (c + x)) ^ 2 -
          (deriv 𝓘 (c - x)) ^ 2))
        x
  := by
  intro c x hp hm
  have l_minus_in
    : c + (-x) ∈ Ioo 0 1
    := by
    simpa only [sub_eq_add_neg] using hm
  have l_plus
    : HasDerivAt
        (deriv (bobkovG c))
        (2 * (deriv 𝓘 (c + x)) ^ 2)
        x
    := hasDerivAt_deriv_bobkovG hp
  have l_minus
    : HasDerivAt
        (λ y : ℝ => deriv (bobkovG c) (-y))
        (-(2 * (deriv 𝓘 (c - x)) ^ 2))
        x
    := by
    simpa only [Function.comp_def, mul_neg_one, ← sub_eq_add_neg]
      using (hasDerivAt_deriv_bobkovG l_minus_in).comp x
        (hasDerivAt_id x).neg
  have l_base := l_plus.fun_add l_minus
  have l_value
    : 2 * (deriv 𝓘 (c + x)) ^ 2 +
        (-(2 * (deriv 𝓘 (c - x)) ^ 2)) =
        2 * ((deriv 𝓘 (c + x)) ^ 2 -
          (deriv 𝓘 (c - x)) ^ 2)
    := by
    ring
  rw [l_value] at l_base
  apply l_base.congr_of_eventuallyEq
  have l_shift_plus
    : HasDerivAt (λ y : ℝ => c + y) 1 x
    := by
    exact (hasDerivAt_id x).const_add c
  have l_shift_minus
    : HasDerivAt (λ y : ℝ => c - y) (-1) x
    := by
    simpa only [id_eq] using (hasDerivAt_id x).const_sub c
  filter_upwards
    [l_shift_plus.continuousAt.eventually (Ioo_mem_nhds hp.1 hp.2),
      l_shift_minus.continuousAt.eventually (Ioo_mem_nhds hm.1 hm.2)]
    with y hyp hym
  exact (hasDerivAt_bobkovU hyp hym).deriv

lemma concaveOn_bobkovU
  : {c t : ℝ} → c ≤ 1 / 2
    → c + t ∈ Ioo 0 1 → c - t ∈ Ioo 0 1
    → ConcaveOn ℝ (Icc 0 t) (bobkovU c)
  := by
  intro c t hc hp hm
  have l_in
    : {y : ℝ} → y ∈ Icc 0 t
    →   c + y ∈ Ioo 0 1 ∧ c - y ∈ Ioo 0 1
    := by
    intro y hy
    constructor
    .
      constructor
      . linarith [hm.1, hy.1, hy.2]
      . linarith [hp.2, hy.2]
    .
      constructor
      . linarith [hm.1, hy.2]
      . linarith [hp.2, hy.1, hy.2]
  apply concaveOn_of_deriv2_nonpos'
  . exact convex_Icc 0 t
  .
    intro y hy
    have h := l_in hy
    exact (hasDerivAt_bobkovU h.1 h.2).differentiableAt.differentiableWithinAt
  .
    intro y hy
    have h := l_in hy
    exact (hasDerivAt_deriv_bobkovU h.1 h.2).differentiableAt.differentiableWithinAt
  .
    intro y hy
    have h := l_in hy
    change deriv (deriv (bobkovU c)) y ≤ 0
    rw [(hasDerivAt_deriv_bobkovU h.1 h.2).deriv]
    have l_segment
      : c + y ∈ Icc (c - y) (1 - (c - y))
      := by
      constructor
      . linarith [hy.1]
      . linarith [hc]
    have l_compare :=
      deriv_gaussianI_pow_two_le_of_mem_Icc h.2 l_segment
    linarith

-- Bobkov 22
lemma bobkovU_upper_bound
  : {c x : ℝ} → 0 ≤ x → c ≤ 1 / 2
    → c + x ∈ Ioo 0 1 → c - x ∈ Ioo 0 1
    → bobkovU c x ≤ 4 * 𝓘 c * deriv 𝓘 c * x
  := by
  intro c x hx hc hp hm
  by_cases hx0 : x = 0
  .
    subst x
    simp [bobkovU]

  have l_positive : 0 < x
    := lt_of_le_of_ne hx (Ne.symm hx0)

  have l_center : c ∈ Ioo 0 1 := by
    constructor
    . linarith [hm.1]
    . linarith [hp.2]

  have l_plus_zero : c + 0 ∈ Ioo 0 1 := by
    simpa only [add_zero] using l_center

  have l_minus_zero : c - 0 ∈ Ioo 0 1 := by
    simpa only [sub_zero] using l_center

  have l_G_deriv
    : deriv (bobkovG c) 0 = 2 * 𝓘 c * deriv 𝓘 c := by
    simpa only [add_zero, mul_zero]
      using (hasDerivAt_bobkovG l_plus_zero).deriv

  have l_U_deriv
    : HasDerivAt (bobkovU c) (4 * 𝓘 c * deriv 𝓘 c) 0 := by
    have l_base := hasDerivAt_bobkovU l_plus_zero l_minus_zero
    simp only [neg_zero, l_G_deriv] at l_base
    have l_value
      : 2 * 𝓘 c * deriv 𝓘 c + 2 * 𝓘 c * deriv 𝓘 c =
          4 * 𝓘 c * deriv 𝓘 c := by
      ring
    rw [l_value] at l_base
    exact l_base

  have l_zero : bobkovU c 0 = 0 := by
    simp [bobkovU]

  have l_left : (0 : ℝ) ∈ Icc 0 x := by
    exact ⟨le_rfl, hx⟩

  have l_right : x ∈ Icc 0 x := by
    exact ⟨hx, le_rfl⟩

  have l_slope
    : slope (bobkovU c) 0 x ≤ 4 * 𝓘 c * deriv 𝓘 c := by
    exact (concaveOn_bobkovU hc hp hm).slope_le_of_hasDerivAt
      l_left l_right l_positive l_U_deriv

  simp only [slope_def_field, l_zero, sub_zero] at l_slope
  exact (div_le_iff₀ l_positive).mp l_slope

lemma bobkovU_nonneg
  : {c x : ℝ} → 0 ≤ x → c ≤ 1 / 2
    → c + x ∈ Ioo 0 1 → c - x ∈ Ioo 0 1
    → 0 ≤ bobkovU c x
  := by
  intro c x hx hc hp hm

  have l_left : c - x ∈ Icc 0 1 := by
    exact ⟨le_of_lt hm.1, le_of_lt hm.2⟩

  have l_segment
    : c + x ∈ Icc (c - x) (1 - (c - x)) := by
    constructor
    . linarith [hx]
    . linarith [hc]

  have l_compare : 𝓘 (c - x) ≤ 𝓘 (c + x) := by
    exact gaussianI_le_of_mem_Icc l_left l_segment

  have l_sum : 0 ≤ 𝓘 (c + x) + 𝓘 (c - x) := by
    exact add_nonneg
      (le_of_lt (gaussianI_pos hp))
      (le_of_lt (gaussianI_pos hm))

  have l_product
    : 0 ≤
        (𝓘 (c + x) - 𝓘 (c - x)) *
        (𝓘 (c + x) + 𝓘 (c - x)) := by
    exact mul_nonneg (sub_nonneg.mpr l_compare) l_sum

  unfold bobkovU bobkovG
  simp only [neg_sq, ← sub_eq_add_neg]
  nlinarith [l_product]

-- bobkov 20
lemma bobkovU_sq_le
  : {c x : ℝ} → 0 ≤ x → c ≤ 1 / 2
    → c + x ∈ Ioo 0 1 → c - x ∈ Ioo 0 1
    → (bobkovU c x) ^ 2 ≤
        8 * (𝓘 c) ^ 2 * (bobkovG c x + bobkovG c (-x) - 2 * bobkovG c 0)
  := by
  intro c x hx hc hp hm

  have l_nonneg : 0 ≤ bobkovU c x := by
    exact bobkovU_nonneg hx hc hp hm

  have l_upper
    : bobkovU c x ≤ 4 * 𝓘 c * deriv 𝓘 c * x := by
    exact bobkovU_upper_bound hx hc hp hm

  have l_upper_nonneg
    : 0 ≤ 4 * 𝓘 c * deriv 𝓘 c * x := by
    exact le_trans l_nonneg l_upper

  have l_product
    : 0 ≤
        (4 * 𝓘 c * deriv 𝓘 c * x - bobkovU c x) *
        (4 * 𝓘 c * deriv 𝓘 c * x + bobkovU c x) := by
    exact mul_nonneg
      (sub_nonneg.mpr l_upper)
      (add_nonneg l_upper_nonneg l_nonneg)

  have l_square
    : (bobkovU c x) ^ 2 ≤
        (4 * 𝓘 c * deriv 𝓘 c * x) ^ 2 := by
    nlinarith [l_product]

  have l_sum
    : 2 * (deriv 𝓘 c) ^ 2 * x ^ 2 ≤
        bobkovG c x + bobkovG c (-x) - 2 * bobkovG c 0 := by
    exact bobkovG_sum_lower_bound hx hp hm

  calc
    (bobkovU c x) ^ 2
        ≤ (4 * 𝓘 c * deriv 𝓘 c * x) ^ 2 := l_square
    _ = 8 * (𝓘 c) ^ 2 *
          (2 * (deriv 𝓘 c) ^ 2 * x ^ 2) := by
      ring
    _ ≤ 8 * (𝓘 c) ^ 2 *
          (bobkovG c x + bobkovG c (-x) - 2 * bobkovG c 0) := by
      exact mul_le_mul_of_nonneg_left l_sum (by positivity)

lemma bobkov_sqrt_bound
  : {p A B : ℝ} → 0 ≤ p → 0 ≤ A → 0 ≤ B
    → (A - B) ^ 2 ≤ 8 * p ^ 2 * (A + B - 2 * p ^ 2)
    → 2 * p ≤ √A + √B
  := by
  intro p A B hp hA hB h_bound

  have l_sqrtA_nonneg : 0 ≤ √A := sqrt_nonneg A
  have l_sqrtB_nonneg : 0 ≤ √B := sqrt_nonneg B
  have l_sqrtA_sq : (√A) ^ 2 = A := sq_sqrt hA
  have l_sqrtB_sq : (√B) ^ 2 = B := sq_sqrt hB

  by_contra h_not
  have l_lt : √A + √B < 2 * p := by
    exact lt_of_not_ge h_not

  have l_sum_pos : 0 < 2 * p + (√A + √B) := by
    linarith

  have l_first_product
    : 0 <
        (2 * p - (√A + √B)) *
        (2 * p + (√A + √B)) := by
    exact mul_pos (sub_pos.mpr l_lt) l_sum_pos

  have l_cross
    : 2 * √A * √B < 4 * p ^ 2 - (A + B) := by
    nlinarith only [l_first_product, l_sqrtA_sq, l_sqrtB_sq]

  have l_cross_nonneg : 0 ≤ 2 * √A * √B := by
    positivity

  have l_left_pos
    : 0 < 4 * p ^ 2 - (A + B) - 2 * √A * √B := by
    linarith only [l_cross]

  have l_right_pos
    : 0 < 4 * p ^ 2 - (A + B) + 2 * √A * √B := by
    linarith only [l_cross, l_cross_nonneg]

  have l_final_product
    : 0 <
        (4 * p ^ 2 - (A + B) - 2 * √A * √B) *
        (4 * p ^ 2 - (A + B) + 2 * √A * √B) := by
    exact mul_pos l_left_pos l_right_pos

  have l_sqrt_product_sq : (√A * √B) ^ 2 = A * B := by
    rw [mul_pow, sq_sqrt hA, sq_sqrt hB]

  nlinarith only [h_bound, l_final_product, l_sqrt_product_sq]

-- bobkov 17
lemma bobkov_two_point_centered
  : {c x : ℝ} → 0 ≤ x → c ≤ 1 / 2
    → c + x ∈ Ioo 0 1 → c - x ∈ Ioo 0 1
    → 2 * 𝓘 c ≤
        √((𝓘 (c + x)) ^ 2 + x ^ 2) +
        √((𝓘 (c - x)) ^ 2 + x ^ 2)
  := by
  intro c x hx hc hp hm

  have l_center : c ∈ Ioo 0 1 := by
    constructor
    . linarith [hm.1]
    . linarith [hp.2]

  have l_nonneg : 0 ≤ 𝓘 c := by
    exact le_of_lt (gaussianI_pos l_center)

  have l_plus_nonneg : 0 ≤ bobkovG c x := by
    unfold bobkovG
    positivity

  have l_minus_nonneg : 0 ≤ bobkovG c (-x) := by
    unfold bobkovG
    positivity

  have l_zero : bobkovG c 0 = (𝓘 c) ^ 2 := by
    simp [bobkovG]

  have l_bound
    : (bobkovG c x - bobkovG c (-x)) ^ 2 ≤
        8 * (𝓘 c) ^ 2 *
          (bobkovG c x + bobkovG c (-x) - 2 * (𝓘 c) ^ 2) := by
    have l_sq := bobkovU_sq_le hx hc hp hm
    unfold bobkovU at l_sq
    rw [l_zero] at l_sq
    exact l_sq

  have l_result
    : 2 * 𝓘 c ≤ √(bobkovG c x) + √(bobkovG c (-x)) := by
    exact bobkov_sqrt_bound
      l_nonneg l_plus_nonneg l_minus_nonneg l_bound

  simpa only [bobkovG, neg_sq, ← sub_eq_add_neg] using l_result

lemma bobkov_two_point_interior
  : {a b : ℝ} → a ∈ Ioo 0 1 → b ∈ Ioo 0 1
    → 2 * 𝓘 ((a + b) / 2) ≤
        √((𝓘 a) ^ 2 + ((a - b) / 2) ^ 2) +
        √((𝓘 b) ^ 2 + ((a - b) / 2) ^ 2)
  := by
  intro a b ha hb

  have l_ordered
    : {u v : ℝ} → u ∈ Ioo 0 1 → v ∈ Ioo 0 1 → u ≤ v
      → 2 * 𝓘 ((u + v) / 2) ≤
        √((𝓘 u) ^ 2 + ((u - v) / 2) ^ 2) +
        √((𝓘 v) ^ 2 + ((u - v) / 2) ^ 2)
    := by
    intro u v hu hv huv
    let c : ℝ := (u + v) / 2
    let x : ℝ := (v - u) / 2

    have l_x : 0 ≤ x := by
      dsimp [x]
      linarith

    have l_plus : c + x = v := by
      dsimp [c, x]
      ring

    have l_minus : c - x = u := by
      dsimp [c, x]
      ring

    have l_square : x ^ 2 = ((u - v) / 2) ^ 2 := by
      dsimp [x]
      ring

    have l_bound
      : 2 * 𝓘 c ≤
          √((𝓘 (c + x)) ^ 2 + x ^ 2) +
          √((𝓘 (c - x)) ^ 2 + x ^ 2) := by
      by_cases hc : c ≤ 1 / 2
      .
        apply bobkov_two_point_centered l_x hc
        . rw [l_plus]
          exact hv
        . rw [l_minus]
          exact hu
      .
        have l_half : 1 - c ≤ 1 / 2 := by
          linarith

        have l_reflected_plus : 1 - c + x = 1 - u := by
          linarith only [l_minus]

        have l_reflected_minus : 1 - c - x = 1 - v := by
          linarith only [l_plus]

        have l_reflected_plus_in : 1 - c + x ∈ Ioo 0 1 := by
          rw [l_reflected_plus]
          constructor
          . linarith [hu.2]
          . linarith [hu.1]

        have l_reflected_minus_in : 1 - c - x ∈ Ioo 0 1 := by
          rw [l_reflected_minus]
          constructor
          . linarith [hv.2]
          . linarith [hv.1]

        have l_reflected_bound :=
          bobkov_two_point_centered
            l_x l_half l_reflected_plus_in l_reflected_minus_in

        simp only
          [l_reflected_plus, l_reflected_minus, gaussianI_one_sub]
          at l_reflected_bound
        rw [l_plus, l_minus]
        linarith only [l_reflected_bound]

    simp only [l_plus, l_minus, l_square] at l_bound
    dsimp [c] at l_bound
    linarith only [l_bound]

  rcases le_total a b with hab | hba
  . exact l_ordered ha hb hab
  .
    have l_swapped := l_ordered hb ha hba

    have l_center : (b + a) / 2 = (a + b) / 2 := by
      ring

    have l_square : ((b - a) / 2) ^ 2 = ((a - b) / 2) ^ 2 := by
      ring

    simp only [l_center, l_square] at l_swapped
    linarith only [l_swapped]

end Lemm

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
