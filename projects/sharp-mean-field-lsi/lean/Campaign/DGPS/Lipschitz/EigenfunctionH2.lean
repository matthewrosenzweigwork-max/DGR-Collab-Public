import DGPS.Lipschitz.WeightedGenerator

/-!
# LIP010a: weighted eigenfunctions lie in `H²`

First piece of the R8 split of LIP010.  Let `w` be a weight with `WData d w b c C` (so only
`b ∈ L∞` is assumed) and let `e ∈ L²(w m)` be a weak eigenfunction of the weighted Dirichlet form,
`∫ ⟨∇e, ∇f⟩ w = λ ⟨e, f⟩_w` for every `f ∈ H¹`.  Then

* `∫ ‖∇e‖² ≤ (2M² + 3)(1 + λ) ∫ e²` (H¹ bound, `M ≥ ‖b‖_∞`);
* `e ∈ H²` and `‖e‖_{H²} ≤ (4M² + 6)(1 + λ) ‖e‖_{L²(m)}`.

The constants depend only on `M`.  Route: `Δe = -(λ e + b·∇e)` weakly
(`converse_laplacian`), the Fourier energy inequality `‖∇e‖² ≤ (s‖e‖² + ‖Δe‖²/s)/2`, absorption of
the drift term, and `periodic_laplacian_h2_regularity`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace DGPS.Lipschitz

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent DGPS.Lipschitz.WeightedGenerator

variable {d : ℕ}

/-- Fourier energy inequality: `‖∇u‖² ≤ (s‖u‖² + ‖Δu‖²/s)/2` for `u ∈ H¹` with weak Laplacian `g`. -/
private lemma lip010a_energy_le {u g : Torus d → ℝ} {G : Torus d → Tangent d}
    (hG : IsWeakGradient u G) (hg : IsWeakLaplacian u g) {s : ℝ} (hs : 0 < s) :
    ∫ x, ‖G x‖ ^ 2 ∂haar d ≤
      (s * ∫ x, u x ^ 2 ∂haar d + (∫ x, g x ^ 2 ∂haar d) / s) / 2 := by
  have hA := hasSum_gradWeight_weakGradient hG
  have hB := hasSum_sq_fourierCoeff hg.memLp
  have hC := hasSum_sq_fourierCoeff hg.memLp_lap
  have hD := (hB.mul_left (s / 2)).add (hC.mul_left (1 / (2 * s)))
  have hle := hasSum_le (fun k => ?_) hA hD
  · calc ∫ x, ‖G x‖ ^ 2 ∂haar d ≤ s / 2 * ∫ x, u x ^ 2 ∂haar d +
          1 / (2 * s) * ∫ x, g x ^ 2 ∂haar d := hle
      _ = _ := by field_simp
  · have hk := hg.fourierCoeff_eq k
    have hn : ‖fourierCoeff g k‖ = gradWeight k * ‖fourierCoeff u k‖ := by
      rw [hk, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by unfold gradWeight; positivity)]
    show gradWeight k * ‖fourierCoeff u k‖ ^ 2 ≤
      s / 2 * ‖fourierCoeff u k‖ ^ 2 + 1 / (2 * s) * ‖fourierCoeff g k‖ ^ 2
    rw [hn]
    have hx := sq_nonneg ‖fourierCoeff u k‖
    have key : s / 2 * ‖fourierCoeff u k‖ ^ 2 +
        1 / (2 * s) * (gradWeight k * ‖fourierCoeff u k‖) ^ 2 - gradWeight k * ‖fourierCoeff u k‖ ^ 2
        = (s - gradWeight k) ^ 2 / (2 * s) * ‖fourierCoeff u k‖ ^ 2 := by
      field_simp
      ring
    have : 0 ≤ (s - gradWeight k) ^ 2 / (2 * s) * ‖fourierCoeff u k‖ ^ 2 := by positivity
    linarith

/-- The weighted eigenfunction bounds, in the form consumed downstream.

`e ∈ L²(w m)` with weak gradient `G` satisfies the weak eigen-equation
`∫ ⟨G, Y⟩ w = λ ⟨e, f⟩_w` for all `f ∈ H¹` with weak gradient `Y`; `M` bounds `‖b‖_∞`.
Then `e ∈ H²` (with the given `G` as gradient), `∫ ‖G‖² ≤ (2M²+3)(1+λ) ∫ e²` and
`‖e‖_{H²} ≤ (4M²+6)(1+λ) ‖e‖_{L²(m)}`. -/
theorem eigenfunction_h2_bound {w : Torus d → ℝ} {b : Torus d → Tangent d} {c C M lam : ℝ}
    (hwd : WData d w b c C) (hM : ∀ᵐ x ∂haar d, ‖b x‖ ≤ M) (hlam : 0 ≤ lam)
    (e : Hw d w) (G : Torus d → Tangent d) (hG : IsWeakGradient (e : Torus d → ℝ) G)
    (heig : ∀ (f : Hw d w) (Y : Torus d → Tangent d), IsWeakGradient (f : Torus d → ℝ) Y →
      weightedForm w G Y = lam * ⟪e, f⟫_ℝ) :
    ∃ H : Fin d → Fin d → Torus d → ℝ, IsWeakHessian (e : Torus d → ℝ) G H ∧
      ∫ x, ‖G x‖ ^ 2 ∂haar d ≤ (2 * M ^ 2 + 3) * (1 + lam) * ∫ x, (e : Torus d → ℝ) x ^ 2 ∂haar d ∧
      Real.sqrt (h2NormSq (e : Torus d → ℝ) G H) ≤
        (4 * M ^ 2 + 6) * (1 + lam) * Real.sqrt (∫ x, (e : Torus d → ℝ) x ^ 2 ∂haar d) := by
  have hc := hwd.pos
  have hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C := Eventually.of_forall hwd.bound
  set u : Torus d → ℝ := (e : Torus d → ℝ) with hu
  have hg : MemLp (fun x => lam * u x) 2 (haar d) := hG.memLp.const_mul lam
  have hid : ∀ (y : Torus d → ℝ) (Y : Torus d → Tangent d), IsWeakGradient y Y →
      ∫ z, ⟪G z, Y z⟫_ℝ * w z ∂haar d = ∫ z, (lam * u z) * y z * w z ∂haar d := by
    intro y Y hy
    have hyw : MemLp y 2 (wMeasure d w) := (memLp_wMeasure_iff hc hwb).mpr hy.memLp
    set f : Hw d w := hyw.toLp y with hf
    have hfy : ((f : Hw d w) : Torus d → ℝ) =ᵐ[wMeasure d w] y := MemLp.coeFn_toLp hyw
    have hfy' := ae_eq_haar hc hwb hfy
    have hfg : IsWeakGradient ((f : Hw d w) : Torus d → ℝ) Y :=
      hy.congr_ae hfy'.symm (Filter.EventuallyEq.refl _ _)
    have h := heig f Y hfg
    rw [inner_Lp_wMeasure hwd.meas hc hwb] at h
    unfold weightedForm at h
    rw [h, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hfy'] with z hz
    simp only [RCLike.inner_apply, conj_trivial]
    rw [hz]
    ring
  have hlap := converse_laplacian hwd hG hg hid
  -- pointwise bound for the Laplacian
  set Y0 := ∫ x, ‖G x‖ ^ 2 ∂haar d with hY0
  set U := ∫ x, u x ^ 2 ∂haar d with hU
  have hUnn : 0 ≤ U := integral_nonneg fun x => sq_nonneg _
  have hYnn : 0 ≤ Y0 := integral_nonneg fun x => sq_nonneg _
  have hGi : Integrable (fun x => ‖G x‖ ^ 2) (haar d) := hG.memLp_grad.norm.integrable_sq
  have hui : Integrable (fun x => u x ^ 2) (haar d) := hG.memLp.integrable_sq
  have hgi : Integrable (fun x => (-(lam * u x + ⟪b x, G x⟫_ℝ)) ^ 2) (haar d) :=
    hlap.memLp_lap.integrable_sq
  have hGg : ∫ x, (-(lam * u x + ⟪b x, G x⟫_ℝ)) ^ 2 ∂haar d ≤ 2 * lam ^ 2 * U + 2 * M ^ 2 * Y0 := by
    have hmono : ∫ x, (-(lam * u x + ⟪b x, G x⟫_ℝ)) ^ 2 ∂haar d ≤
        ∫ x, (2 * lam ^ 2 * u x ^ 2 + 2 * M ^ 2 * ‖G x‖ ^ 2) ∂haar d := by
      refine integral_mono_ae hgi ((hui.const_mul _).add (hGi.const_mul _)) ?_
      filter_upwards [hM] with x hx
      have h1 : |⟪b x, G x⟫_ℝ| ≤ M * ‖G x‖ :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
      have h2 : ⟪b x, G x⟫_ℝ ^ 2 ≤ (M * ‖G x‖) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      nlinarith [sq_nonneg (lam * u x - ⟪b x, G x⟫_ℝ)]
    refine hmono.trans (le_of_eq ?_)
    rw [integral_add (hui.const_mul _) (hGi.const_mul _), integral_const_mul, integral_const_mul]
  have hGgnn : 0 ≤ ∫ x, (-(lam * u x + ⟪b x, G x⟫_ℝ)) ^ 2 ∂haar d :=
    integral_nonneg fun x => sq_nonneg _
  set Gg := ∫ x, (-(lam * u x + ⟪b x, G x⟫_ℝ)) ^ 2 ∂haar d with hGgdef
  -- absorb the drift
  have hm : 0 ≤ M ^ 2 := sq_nonneg M
  have ha : 1 ≤ 1 + lam := by linarith
  have hY : Y0 ≤ (2 * M ^ 2 + 3) * (1 + lam) * U := by
    set s : ℝ := 2 * (M ^ 2 + (1 + lam)) with hsdef
    have hs : 0 < s := by positivity
    have h1 := lip010a_energy_le hG hlap hs
    have h2 : 2 * s * Y0 ≤ s ^ 2 * U + Gg := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * s)
      calc 2 * s * Y0 ≤ 2 * s * ((s * U + Gg / s) / 2) := this
        _ = s ^ 2 * U + Gg := by field_simp
    have h3 : (2 * s - 2 * M ^ 2) * Y0 ≤ (s ^ 2 + 2 * lam ^ 2) * U := by nlinarith
    have h4 : 0 < 2 * s - 2 * M ^ 2 := by rw [hsdef]; nlinarith
    have h5 : (2 * s - 2 * M ^ 2) * Y0 ≤ (2 * s - 2 * M ^ 2) * ((2 * M ^ 2 + 3) * (1 + lam) * U) := by
      refine h3.trans ?_
      have key : s ^ 2 + 2 * lam ^ 2 ≤ (2 * s - 2 * M ^ 2) * ((2 * M ^ 2 + 3) * (1 + lam)) := by
        rw [hsdef]
        nlinarith [mul_nonneg hm (sub_nonneg.mpr ha), mul_nonneg hm hlam,
          mul_nonneg hlam hlam, mul_nonneg (mul_nonneg hm hm) hlam]
      calc (s ^ 2 + 2 * lam ^ 2) * U ≤ ((2 * s - 2 * M ^ 2) * ((2 * M ^ 2 + 3) * (1 + lam))) * U :=
            mul_le_mul_of_nonneg_right key hUnn
        _ = _ := by ring
    exact le_of_mul_le_mul_left h5 h4
  have hGg2 : Gg ≤ (2 * M ^ 2 + 2) ^ 2 * (1 + lam) ^ 2 * U := by
    have : Gg ≤ 2 * lam ^ 2 * U + 2 * M ^ 2 * ((2 * M ^ 2 + 3) * (1 + lam) * U) := by
      nlinarith
    refine this.trans ?_
    have e1 : (2 * M ^ 2 + 2) ^ 2 * (1 + lam) ^ 2 * U -
        (2 * lam ^ 2 * U + 2 * M ^ 2 * ((2 * M ^ 2 + 3) * (1 + lam) * U)) =
        U * (((2 * M ^ 2 + 2) ^ 2 - 2) * lam ^ 2 + (2 * (2 * M ^ 2 + 2) ^ 2 - 2 * M ^ 2 * (2 * M ^ 2 + 3)) * lam
          + ((2 * M ^ 2 + 2) ^ 2 - 2 * M ^ 2 * (2 * M ^ 2 + 3))) := by ring
    have e2 : 0 ≤ U * (((2 * M ^ 2 + 2) ^ 2 - 2) * lam ^ 2 +
        (2 * (2 * M ^ 2 + 2) ^ 2 - 2 * M ^ 2 * (2 * M ^ 2 + 3)) * lam
          + ((2 * M ^ 2 + 2) ^ 2 - 2 * M ^ 2 * (2 * M ^ 2 + 3))) := by
      refine mul_nonneg hUnn ?_
      have a1 : 0 ≤ (2 * M ^ 2 + 2) ^ 2 - 2 := by nlinarith
      have a2 : 0 ≤ 2 * (2 * M ^ 2 + 2) ^ 2 - 2 * M ^ 2 * (2 * M ^ 2 + 3) := by nlinarith
      have a3 : 0 ≤ (2 * M ^ 2 + 2) ^ 2 - 2 * M ^ 2 * (2 * M ^ 2 + 3) := by nlinarith
      positivity
    linarith
  -- H² regularity
  obtain ⟨G', H, hH', hb⟩ := h2_bound_of_weakLaplacian ⟨G, hG⟩ hlap
  have hGae : G =ᵐ[haar d] G' := hG.ae_eq hH'.grad
  have hH : IsWeakHessian u G H :=
    { grad := hG
      memLp_hess := hH'.memLp_hess
      ibp := fun i j φ hφ => by
        rw [← hH'.ibp i j φ hφ]
        refine integral_congr_ae ?_
        filter_upwards [hGae] with x hx
        rw [hx] }
  have hh2 : h2NormSq u G H = h2NormSq u G' H := by
    unfold h2NormSq
    congr 2
    refine integral_congr_ae ?_
    filter_upwards [hGae] with x hx
    rw [hx]
  have hsq : Real.sqrt Gg ≤ (2 * M ^ 2 + 2) * (1 + lam) * Real.sqrt U := by
    calc Real.sqrt Gg ≤ Real.sqrt (((2 * M ^ 2 + 2) * (1 + lam)) ^ 2 * U) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = _ := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  refine ⟨H, hH, hY, ?_⟩
  rw [hh2]
  have hsU := Real.sqrt_nonneg U
  calc Real.sqrt (h2NormSq u G' H) ≤ 2 * (Real.sqrt U + Real.sqrt Gg) := hb
    _ ≤ 2 * (Real.sqrt U + (2 * M ^ 2 + 2) * (1 + lam) * Real.sqrt U) := by linarith
    _ ≤ (4 * M ^ 2 + 6) * (1 + lam) * Real.sqrt U := by
        nlinarith [mul_nonneg hsU hlam]

end DGPS.Lipschitz
