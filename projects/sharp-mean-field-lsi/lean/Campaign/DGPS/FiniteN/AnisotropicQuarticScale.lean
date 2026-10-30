import DGPS.FiniteN.Tools.GroundState

/-!
# Analytic support for the anisotropic quartic scale

The square completion in `anisotropic_remote_quartic_saddle.md`, §6.1, gives a genuine
harmonic-oscillator estimate. Its directional weighted version is the flat-coordinate input
for FIN069. This module does not assert the final T13 scale row: transport through the
FIN068 Morse chart, global mean-corrected IMS, and the particle rare-box cone remain separate.
-/

open MeasureTheory Real
open scoped ContDiff

namespace DGPS.FiniteN

/-- Square completion for one linear coordinate and its dual direction. All terms are
integrable because the test is smooth and compactly supported; no undefined-integral case
is used. The coordinate need not have unit norm, but `l v = 1` is required. -/
theorem quartic_harmonic_oscillator {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    (l : E →L[ℝ] ℝ) (v : E) (hlv : l v = 1) (a : ℝ)
    (G : E → ℝ) (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) :
    a * ∫ x, G x ^ 2 ∂μ ≤
      ∫ x, (fderiv ℝ G x v) ^ 2 + a ^ 2 * (l x) ^ 2 * G x ^ 2 ∂μ := by
  let dG : E → ℝ := fun x => fderiv ℝ G x v
  have hdG : Continuous dG :=
    (hG.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdGc : HasCompactSupport dG := hGc.fderiv_apply ℝ v
  have hG2c : HasCompactSupport (fun x => G x ^ 2) := by
    simp_rw [pow_two]
    exact hGc.mul_right
  have hdG2c : HasCompactSupport (fun x => dG x ^ 2) := by
    simp_rw [pow_two]
    exact hdGc.mul_right
  have hG2i : Integrable (fun x => G x ^ 2) μ :=
    (hG.continuous.pow 2).integrable_of_hasCompactSupport hG2c
  have hdG2i : Integrable (fun x => dG x ^ 2) μ :=
    (hdG.pow 2).integrable_of_hasCompactSupport hdG2c
  have hcrossc : HasCompactSupport (fun x => l x * G x * dG x) := by
    exact hGc.mul_left.mul_right
  have hcrossi : Integrable (fun x => l x * G x * dG x) μ :=
    ((l.continuous.mul hG.continuous).mul hdG).integrable_of_hasCompactSupport hcrossc
  have hpotc : HasCompactSupport (fun x => a ^ 2 * l x ^ 2 * G x ^ 2) :=
    hG2c.mul_left
  have hpoti : Integrable (fun x => a ^ 2 * l x ^ 2 * G x ^ 2) μ :=
    (continuous_const.mul (l.continuous.pow 2) |>.mul (hG.continuous.pow 2)).integrable_of_hasCompactSupport hpotc
  let H : E → ℝ := fun x => G x * G x * l x
  have hHs : ContDiff ℝ ∞ H := (hG.mul hG).mul l.contDiff
  have hHc : HasCompactSupport H := hGc.mul_right.mul_right
  have hDHi : Integrable (fun x => fderiv ℝ H x v) μ :=
    ((hHs.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hHc.fderiv_apply ℝ v)
  have hDH0 : ∫ x, fderiv ℝ H x v ∂μ = 0 := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ) (f := H)
      (g := fun _ : E => (1 : ℝ)) (v := v) (by simpa using hDHi) (by simp)
      (by simpa using hHs.continuous.integrable_of_hasCompactSupport hHc)
      (fun x _ => (hHs.differentiable (by simp)) x) (fun x _ => differentiableAt_const _)
    simpa using h
  have hDH : (fun x => fderiv ℝ H x v) =
      fun x => G x ^ 2 + 2 * (l x * G x * dG x) := by
    funext x
    have hx := ((((hG.differentiable (by simp)) x).hasFDerivAt.fun_mul
      ((hG.differentiable (by simp)) x).hasFDerivAt).fun_mul l.hasFDerivAt)
    rw [hx.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hlv]
    dsimp [dG]
    ring
  rw [hDH, integral_add hG2i (hcrossi.const_mul 2), integral_const_mul] at hDH0
  have hsq : 0 ≤ ∫ x, (dG x + a * l x * G x) ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  have heq : (fun x => (dG x + a * l x * G x) ^ 2) =
      fun x => (dG x ^ 2 + a ^ 2 * l x ^ 2 * G x ^ 2) +
        (2 * a) * (l x * G x * dG x) := by
    funext x
    ring
  have henergyi : Integrable (fun x => dG x ^ 2 + a ^ 2 * l x ^ 2 * G x ^ 2) μ :=
    hdG2i.add hpoti
  rw [heq, integral_add henergyi (hcrossi.const_mul (2 * a)), integral_const_mul] at hsq
  change a * ∫ x, G x ^ 2 ∂μ ≤ ∫ x, dG x ^ 2 + a ^ 2 * l x ^ 2 * G x ^ 2 ∂μ
  have hscaled := congrArg (fun z : ℝ => a * z) hDH0
  nlinarith [hscaled]


/-- The flat-coordinate local estimate behind FIN069. The second derivative hypothesis is
pointwise curvature information, not a spectral-gap assumption. The square-root coefficient
is derived from the ground-state identity and `quartic_harmonic_oscillator`. -/
theorem quartic_directional_local_dirichlet {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (l : E →L[ℝ] ℝ) (v : E) (hlv : l v = 1)
    (U : Set E) (c : ℝ) (hc : 0 ≤ c)
    (hneg : ∀ x ∈ U, fderiv ℝ (fun y => fderiv ℝ ψ y v) x v ≤ -c * (l x) ^ 2)
    (N : ℝ) (hN : 0 ≤ N)
    (F : E → ℝ) (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F) (hFU : tsupport F ⊆ U) :
    Real.sqrt (c * N / 2) * (∫ x, F x ^ 2 * exp (-(N * ψ x)) ∂μ) ≤
      ∫ x, (fderiv ℝ F x v) ^ 2 * exp (-(N * ψ x)) ∂μ := by
  let G : E → ℝ := fun x => F x * exp (-(N * ψ x) / 2)
  have hGs : ContDiff ℝ ∞ G :=
    hF.mul (contDiff_exp.comp ((contDiff_const.mul hψ).neg.div_const 2))
  have hGc : HasCompactSupport G := hFc.mul_right
  have hroot : Real.sqrt (c * N / 2) ^ 2 = c * N / 2 :=
    Real.sq_sqrt (by positivity)
  obtain ⟨hLi, hRi, hEq⟩ := groundState_direction_aux (μ := μ) N ψ F hψ hF hFc v
  have hG2c : HasCompactSupport (fun x => G x ^ 2) := by
    simp_rw [pow_two]
    exact hGc.mul_right
  have hDG2c : HasCompactSupport (fun x => (fderiv ℝ G x v) ^ 2) := by
    simp_rw [pow_two]
    exact (hGc.fderiv_apply ℝ v).mul_right
  have hDGi : Integrable (fun x => (fderiv ℝ G x v) ^ 2) μ :=
    (((hGs.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2).integrable_of_hasCompactSupport hDG2c
  have hpotc : HasCompactSupport (fun x => Real.sqrt (c * N / 2) ^ 2 * l x ^ 2 * G x ^ 2) :=
    hG2c.mul_left
  have hpoti : Integrable (fun x => Real.sqrt (c * N / 2) ^ 2 * l x ^ 2 * G x ^ 2) μ :=
    ((continuous_const.mul (l.continuous.pow 2)).mul (hGs.continuous.pow 2)).integrable_of_hasCompactSupport hpotc
  have hOi : Integrable (fun x => (fderiv ℝ G x v) ^ 2 +
      Real.sqrt (c * N / 2) ^ 2 * l x ^ 2 * G x ^ 2) μ := hDGi.add hpoti
  have hcomp : (∫ x, (fderiv ℝ G x v) ^ 2 +
      Real.sqrt (c * N / 2) ^ 2 * l x ^ 2 * G x ^ 2 ∂μ) ≤
      ∫ x, (fderiv ℝ G x v) ^ 2 +
        (N ^ 2 * (fderiv ℝ ψ x v) ^ 2 / 4 -
          N * fderiv ℝ (fun y => fderiv ℝ ψ y v) x v / 2) * G x ^ 2 ∂μ := by
    refine integral_mono hOi hRi fun x => ?_
    by_cases hx : F x = 0
    · simp [G, hx]
    · have hcurv := hneg x (hFU (subset_tsupport F hx))
      have hpot : (c * N / 2) * l x ^ 2 ≤
          N ^ 2 * (fderiv ℝ ψ x v) ^ 2 / 4 -
            N * fderiv ℝ (fun y => fderiv ℝ ψ y v) x v / 2 := by
        have hsq : 0 ≤ N ^ 2 * (fderiv ℝ ψ x v) ^ 2 / 4 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hcurv hN]
      rw [hroot]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hpot (sq_nonneg (G x)))
  have hmass : (∫ x, G x ^ 2 ∂μ) = ∫ x, F x ^ 2 * exp (-(N * ψ x)) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp [G]
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hosc := quartic_harmonic_oscillator (μ := μ) l v hlv (Real.sqrt (c * N / 2)) G hGs hGc
  rw [hmass] at hosc
  exact hosc.trans (hcomp.trans_eq hEq.symm)

/-- The exact flat Morse potential has transverse Hessian equal to the reduced second
ordinary derivative. In particular the stable quadratic coordinate does not supply the
unstable local gap. -/
theorem quartic_flat_transverse_hessian (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (q : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ =>
      fderiv ℝ (fun z : ℝ × ℝ => z.1 ^ 2 / 2 + φ z.2) p (0, 1)) q (0, 1) =
      deriv (deriv φ) q.2 := by
  have hφ1 : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφ2 : Differentiable ℝ (deriv φ) :=
    (contDiff_infty_iff_deriv.1 hφ).2.differentiable (by simp)
  have hfirst : (fun p : ℝ × ℝ =>
      fderiv ℝ (fun z : ℝ × ℝ => z.1 ^ 2 / 2 + φ z.2) p (0, 1)) =
      fun p => deriv φ p.2 := by
    funext p
    have hfst : HasFDerivAt (fun z : ℝ × ℝ => z.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
      hasFDerivAt_fst
    have hsnd : HasFDerivAt (fun z : ℝ × ℝ => z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
      hasFDerivAt_snd
    have hleft : HasFDerivAt (fun z : ℝ × ℝ => z.1 ^ 2 / 2)
        (p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
      convert (hfst.pow 2).const_mul (1 / 2 : ℝ) using 1
      · funext z
        ring
      · ext z <;> simp <;> ring
    have hright := hφ1.differentiableAt.hasDerivAt.comp_hasFDerivAt p hsnd
    change (fderiv ℝ ((fun z : ℝ × ℝ => z.1 ^ 2 / 2) +
      (φ ∘ fun z : ℝ × ℝ => z.2)) p) (0, 1) = _
    rw [(hleft.add hright).fderiv]
    simp
  rw [hfirst]
  have hsnd : HasFDerivAt (fun z : ℝ × ℝ => z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) q :=
    hasFDerivAt_snd
  have h := hφ2.differentiableAt.hasDerivAt.comp_hasFDerivAt q hsnd
  change (fderiv ℝ (deriv φ ∘ fun z : ℝ × ℝ => z.2) q) (0, 1) = _
  rw [h.fderiv]
  simp

/-- The negative reduced curvature in the FIN068 chart gives the local square-root estimate
for the flat product potential, for every compactly supported smooth test in its transverse
window. This statement requires a smooth reduced potential on the whole line; local smooth
extension/zero-extension transport is still required for the actual selected chart. -/
theorem quartic_flat_local_dirichlet (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (I : Set ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hneg : ∀ y ∈ I, deriv (deriv φ) y ≤ -c * y ^ 2)
    (N : ℝ) (hN : 0 ≤ N) (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) (hFI : ∀ q ∈ tsupport F, q.2 ∈ I) :
    Real.sqrt (c * N / 2) *
        (∫ q : ℝ × ℝ, F q ^ 2 * exp (-(N * (q.1 ^ 2 / 2 + φ q.2)))) ≤
      ∫ q : ℝ × ℝ, (fderiv ℝ F q (0, 1)) ^ 2 *
        exp (-(N * (q.1 ^ 2 / 2 + φ q.2))) := by
  apply quartic_directional_local_dirichlet (μ := volume)
    (fun q : ℝ × ℝ => q.1 ^ 2 / 2 + φ q.2) (by fun_prop)
    (ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 1) (by simp)
    {q | q.2 ∈ I} c hc ?_ N hN F hF hFc hFI
  intro q hq
  rw [quartic_flat_transverse_hessian φ hφ q]
  exact hneg q.2 hq

/-- For the exact polynomial flat saddle, the coefficient is `sqrt(6*b*N)`: the second
transverse derivative is computed as `-12*b*y^2`. The genuine reduced potential in FIN068
also has higher-order terms and is handled by its proved local curvature bound instead. -/
theorem quartic_polynomial_local_dirichlet (b : ℝ) (hb : 0 ≤ b)
    (N : ℝ) (hN : 0 ≤ N) (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) :
    Real.sqrt (6 * b * N) *
        (∫ q : ℝ × ℝ, F q ^ 2 * exp (-(N * (q.1 ^ 2 / 2 - b * q.2 ^ 4)))) ≤
      ∫ q : ℝ × ℝ, (fderiv ℝ F q (0, 1)) ^ 2 *
        exp (-(N * (q.1 ^ 2 / 2 - b * q.2 ^ 4))) := by
  have hd : deriv (fun y : ℝ => -b * y ^ 4) = fun y => -4 * b * y ^ 3 := by
    funext y
    convert ((hasDerivAt_pow 4 y).const_mul (-b)).deriv using 1 <;> ring
  have hdd : ∀ y : ℝ, deriv (deriv (fun z : ℝ => -b * z ^ 4)) y = -12 * b * y ^ 2 := by
    intro y
    rw [hd]
    convert ((hasDerivAt_pow 3 y).const_mul (-4 * b)).deriv using 1 <;> ring
  have h := quartic_flat_local_dirichlet (fun y => -b * y ^ 4) (by fun_prop)
    Set.univ (12 * b) (by positivity) (fun y _ => by rw [hdd]; exact le_of_eq (by ring))
    N hN F hF hFc (fun _ _ => Set.mem_univ _)
  have he : 12 * b * N / 2 = 6 * b * N := by ring
  simpa only [he, sub_eq_add_neg, neg_mul] using h

end DGPS.FiniteN
