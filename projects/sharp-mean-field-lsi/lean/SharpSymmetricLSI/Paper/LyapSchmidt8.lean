import SharpSymmetricLSI.Paper.LyapSchmidt7

/-!
# Section 4.2 (lane s42; R14): the reduced energy and its gradient

`PsiC h = ∫ (1+h) log(1+h) dμ + ½ ∫ h T h dμ` is `G(μ(1+h))` (manuscript, the reduced energy
`φ(x) = F(μ(1 + x + y(x))) - F_*`, via (4.15)). It is differentiable on `posSet` with
`DΨ(h) k = ∫ k (log(1+h) + 1) dμ + ½ (∫ k T h + ∫ h T k) dμ`. For mean-zero `h, k` and
`log(1+h) + T h = c + ∑ bᵢ φᵢ` this is `∑ bᵢ ⟨k, φᵢ⟩`: on the graph of (4.5) the gradient of the
reduced energy is the coefficient vector `b` (manuscript: `∇φ(x) = g(x + y(x)) ∈ E`).
-/

noncomputable section
open MeasureTheory Filter Real Topology Metric
open scoped ContDiff

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section reduced
variable (hyp : Hyp V W KV KW) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]

/-- The reduced energy on `C(𝕋^d)`. -/
def PsiC (h : CT d) : ℝ := meanC μ ((1 + h) * logC h) + 1 / 2 * meanC μ (h * TC hyp μ h)

/-- Its derivative. -/
def DPsiC (h : CT d) : CT d →L[ℝ] ℝ :=
  pairC μ (logC h + 1) + (1 / 2 : ℝ) • (pairC μ (TC hyp μ h) + (pairC μ h).comp (TC hyp μ))

theorem DPsiC_apply (h k : CT d) : DPsiC hyp μ h k =
    ∫ x, k x * (logC h x + 1) ∂μ +
      (∫ x, k x * TC hyp μ h x ∂μ + ∫ x, TC hyp μ k x * h x ∂μ) / 2 := by
  simp only [DPsiC, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, pairC_apply, ContinuousMap.add_apply, ContinuousMap.one_apply,
    smul_eq_mul]
  ring

theorem logCDeriv_mul_apply {h : CT d} (hh : h ∈ posSet) (k : CT d) (x : Torus d) :
    ((1 + h) * logCDeriv h k) x = k x := by
  have hu := isUnit_one_add hh
  have hx : (1 + h x) ≠ 0 := (hh x).ne'
  simp only [logCDeriv, ContinuousLinearMap.mul_apply', ContinuousMap.mul_apply,
    ringInverse_apply hu, ContinuousMap.add_apply, ContinuousMap.one_apply]
  field_simp

theorem hasFDerivAt_PsiC {h : CT d} (hh : h ∈ posSet) :
    HasFDerivAt (PsiC hyp μ) (DPsiC hyp μ h) h := by
  have h1 := ((hasFDerivAt_id h).const_add 1).mul' (hasFDerivAt_logC hh)
  have h2 := (hasFDerivAt_id h).mul' (TC hyp μ).hasFDerivAt
  have h3 := ((meanC μ).hasFDerivAt.comp h h1).add
    (((meanC μ).hasFDerivAt.comp h h2).const_mul (1 / 2 : ℝ))
  have h4 : HasFDerivAt (PsiC hyp μ) _ h := h3
  refine h4.congr_fderiv ?_
  ext k
  rw [DPsiC_apply]
  simp [meanC_apply]
  have e1 : ∫ x, (1 + h x) * (logCDeriv h k) x ∂μ = ∫ x, k x ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have := logCDeriv_mul_apply hh k x
    simpa [ContinuousMap.mul_apply] using this
  have i1 : Integrable (fun x => logC h x * k x) μ :=
    integrable_of_continuous ((logC h).continuous.mul k.continuous)
  have i2 : Integrable (fun x => k x) μ := integrable_of_continuous k.continuous
  have e2 : ∫ x, k x * (logC h x + 1) ∂μ = ∫ x, logC h x * k x ∂μ + ∫ x, k x ∂μ := by
    rw [← integral_add i1 i2]; congr 1; funext x; ring
  have e3 : ∫ x, h x * TC hyp μ k x ∂μ = ∫ x, TC hyp μ k x * h x ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have e4 : ∫ x, TC hyp μ h x * k x ∂μ = ∫ x, k x * TC hyp μ h x ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [e1, e2, e3, e4]
  ring

end reduced

end SharpLSI
