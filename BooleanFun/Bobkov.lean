/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/

import BooleanFun.Basic

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

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

/-- The range of the Gaussian CDF is the open interval `(0, 1)`. -/
theorem Φ_range : range Φ = Ioo 0 1 := by
  sorry

/-- The Gaussian isoperimetric profile `I = ϕ ∘ Φ⁻¹`

**Implementation note:** Mathematically, the domain of this function is `[0, 1]`, but
we extend it to the whole real line by the junk value `0`.
Careful: In Lean `Φ⁻¹` is the pointwise reciprocal, but we need the inverse function.
 -/
def gaussianI (x : ℝ) := if x ∈ Ioo 0 1 then (ϕ ∘ invFun Φ) x else 0

@[inherit_doc]
scoped notation "𝓘" => gaussianI

@[simp]
theorem gaussianI_zero : 𝓘 0 = 0 := by
  sorry

@[simp]
theorem gaussianI_one : 𝓘 1 = 0 := by
  sorry

-- In this section we compute derivatives of `I` on `(0, 1)`.
section gaussianI_derivatives

variable {x : ℝ}

/-- The Gaussian isoperimetric profile is differentiable on `(0, 1)` -/
theorem hasDerivAt_gaussianI (hx : x ∈ Ioo 0 1) : HasDerivAt 𝓘 (-invFun Φ x) x := by
  sorry

/-- The Gaussian isoperimetric profile's derivative.  -/
theorem deriv_gaussianI (hx : x ∈ Ioo 0 1) : deriv 𝓘 x = -invFun Φ x := by
  sorry

/-- The Gaussian isoperimetric profile is positive on `(0, 1)`. -/
theorem gaussianI_pos (hx : x ∈ Ioo 0 1) : 0 < 𝓘 x := by
  sorry

/-- The derivative of the Gaussian isoperimetric profile is also differentiable on `(0, 1)`. -/
theorem hasDerivAt_deriv_gaussianI (hx : x ∈ Ioo 0 1) : HasDerivAt (deriv 𝓘) (-(𝓘 x)⁻¹) x := by
  sorry

/-- The second derivative of the Gaussian isoperimetric profile -/
theorem deriv_deriv_gaussianI (hx : x ∈ Ioo 0 1) : deriv (deriv 𝓘) x = -(𝓘 x)⁻¹ := by
  sorry

/-- The second derivative of the Gaussian isoperimetric profile is negative on `(0, 1)`. -/
theorem deriv_deriv_gaussianI_neg (hx : x ∈ Ioo 0 1) : deriv (deriv 𝓘) x < 0 := by
  sorry

/-- The Gaussian isoperimetric profile is strictly concave on `[0, 1]`. -/
theorem strictConcaveOn_gaussianI : StrictConcaveOn ℝ (Icc 0 1) 𝓘 := by
  sorry

/-- Differential equation satisfied by the Gaussian isoperimetric profile. -/
theorem gaussianI_mul_deriv_deriv_eq (hx : x ∈ Ioo 0 1) :
    𝓘 x * deriv (deriv 𝓘) x = -1 := by
  sorry

/-- The limit of `I' x` tends to `∞` as `x → 0+`. -/
theorem tendsto_deriv_gaussianI_zero : Tendsto (deriv 𝓘) (𝓝[>] 0) atTop := by
  sorry

/-- The limit of `I' x` tends to `-∞` as `x → 1-`. -/
theorem tendsto_deriv_gaussianI_one : Tendsto (deriv 𝓘) (𝓝[<] 1) atBot := by
  sorry

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
theorem bobkov_two_point {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    2 * 𝓘 ((a + b) / 2) ≤ √((𝓘 a) ^ 2 + ((a - b) / 2) ^ 2) + √((𝓘 b) ^ 2 + ((a - b) / 2) ^ 2) := by
  sorry

end twopoint_inequality

-- ToDo: add Bobkov's isoperimetric inequality
-- The idea is that the two point inequality is the 1D case and then one can run induction on dimension

end

end BooleanFun
