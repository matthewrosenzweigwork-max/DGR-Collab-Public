import Mathlib

/-!
# The entropy (1): the regularized entropy `G_δ`

`G_δ(r) = r arsinh(r/δ) - √(r² + δ²)` is smooth on `ℝ` with `G_δ'' = 1/√(r² + δ²) ∈ (0, 1/δ]`.
Up to an affine function of `r` (harmless under conservation of mass), `G_δ(r) → r log r` as
`δ → 0`.
-/

open Real Filter Topology

namespace SharpLSI

/-- `G_δ(r) = r arsinh(r/δ) - √(r² + δ²)`: `G_δ'' = 1/√(r² + δ²)`. -/
noncomputable def entG (δ r : ℝ) : ℝ := r * arsinh (r / δ) - Real.sqrt (r ^ 2 + δ ^ 2)
noncomputable def entGp (δ r : ℝ) : ℝ := arsinh (r / δ)
noncomputable def entGpp (δ r : ℝ) : ℝ := (Real.sqrt (r ^ 2 + δ ^ 2))⁻¹

theorem sqrt_sq_add_pos {δ : ℝ} (hδ : 0 < δ) (r : ℝ) : 0 < Real.sqrt (r ^ 2 + δ ^ 2) :=
  Real.sqrt_pos.2 (by positivity)

theorem delta_mul_sqrt {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    δ * Real.sqrt (1 + (r / δ) ^ 2) = Real.sqrt (r ^ 2 + δ ^ 2) := by
  have : r ^ 2 + δ ^ 2 = δ ^ 2 * (1 + (r / δ) ^ 2) := by field_simp; ring
  rw [this, Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ.le]

theorem hasDerivAt_entGp {δ : ℝ} (hδ : 0 < δ) (r : ℝ) : HasDerivAt (entGp δ) (entGpp δ r) r := by
  have hc := HasDerivAt.comp r (hasStrictDerivAt_arsinh (r / δ)).hasDerivAt
    ((hasDerivAt_id r).div_const δ)
  have h : HasDerivAt (fun x => arsinh (x / δ)) ((Real.sqrt (1 + (r / δ) ^ 2))⁻¹ * (1 / δ)) r := by
    simpa only [Function.comp_def, id] using hc
  unfold entGp entGpp
  convert h using 1
  rw [← delta_mul_sqrt hδ r]; field_simp

theorem hasDerivAt_entG {δ : ℝ} (hδ : 0 < δ) (r : ℝ) : HasDerivAt (entG δ) (entGp δ r) r := by
  have hc := HasDerivAt.comp r (hasStrictDerivAt_arsinh (r / δ)).hasDerivAt
    ((hasDerivAt_id r).div_const δ)
  have h0 : HasDerivAt (fun x => arsinh (x / δ)) ((Real.sqrt (1 + (r / δ) ^ 2))⁻¹ * (1 / δ)) r := by
    simpa only [Function.comp_def, id] using hc
  have h1 := (hasDerivAt_id' r).mul h0
  have h2 := ((hasDerivAt_pow 2 r).add_const (δ ^ 2)).sqrt (by positivity)
  unfold entG entGp
  convert h1.sub h2 using 1
  have hs := sqrt_sq_add_pos hδ r
  rw [← delta_mul_sqrt hδ r] at hs ⊢
  field_simp
  ring

theorem continuous_entGpp {δ : ℝ} (hδ : 0 < δ) : Continuous (entGpp δ) :=
  (by fun_prop : Continuous fun r : ℝ => Real.sqrt (r ^ 2 + δ ^ 2)).inv₀
    fun r => (sqrt_sq_add_pos hδ r).ne'

theorem entGpp_pos {δ : ℝ} (hδ : 0 < δ) (r : ℝ) : 0 < entGpp δ r :=
  inv_pos.2 (sqrt_sq_add_pos hδ r)

theorem entGpp_le {δ : ℝ} (hδ : 0 < δ) (r : ℝ) : entGpp δ r ≤ δ⁻¹ := by
  unfold entGpp
  refine inv_anti₀ hδ ?_
  rw [Real.le_sqrt hδ.le (by positivity)]; nlinarith [sq_nonneg r]

end SharpLSI
