import DGPS.FiniteN.ScalarFoldFIN057
import DGPS.FiniteN.Tools.QuadraticLaplace

/-!
# FIN061: fold latent rare box mass

Let `ψ = scalarPsi κ h_c` (`κ > 2`), `t_* = -s_*`, `d_N = N^{-1/3}` and let
`η_N ∝ e^{-Nψ} dt` be the normalized latent (auxiliary) law on `ℝ`.  With `t₊` the positive
nondegenerate global minimizer and `Δ = ψ(t_*) - ψ(t₊) > 0` (FIN056), we show that for every
fixed `K > 0` the mass `η_N(|t - t_*| ≤ K d_N)` is two-sided comparable to `N^{1/6} e^{-NΔ}`
for all large `N`.  Since `K > 0` is arbitrary, the same holds for every fixed nontrivial smaller
centered box.

Proof: the global normalizer is `≍ N^{-1/2} e^{-Nψ(t₊)}` (FIN019 on `E = ℝ`, with the quadratic
growth coming from `log I₀ ≤ |t|`); on the box the exact cubic coordinate (FIN057) gives
`|N(ψ(t) - ψ(t_*))| ≤ M³K³/3`, so the box integral is `≍ N^{-1/3} e^{-Nψ(t_*)}`.

The main theorem is `DGPS.FiniteN.fold_latent_rare_box_mass`.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace DGPS.FiniteN

/-- The normalized latent law `η_N ∝ e^{-Nψ} dt` on `ℝ`. -/
noncomputable def foldLatentEtaFIN061 (ψ : ℝ → ℝ) (N : ℝ) : Measure ℝ :=
  (∫⁻ t, ENNReal.ofReal (Real.exp (-(N * ψ t))))⁻¹ •
    (volume : Measure ℝ).withDensity (fun t => ENNReal.ofReal (Real.exp (-(N * ψ t))))

end DGPS.FiniteN

namespace DGPS.FiniteN.ScalarFoldFIN061

open DGPS.Models DGPS.Circle.BesselMoments DGPS.Circle.AngularNormalization DGPS.FiniteN

/-- Mass of a measurable set under the latent law, as a ratio of Laplace integrals. -/
theorem eta_real_FIN061 (ψ : ℝ → ℝ) (N : ℝ) (hZ : 0 < ∫ t, Real.exp (-(N * ψ t)))
    (S : Set ℝ) (hS : MeasurableSet S) :
    (foldLatentEtaFIN061 ψ N S).toReal =
      (∫ t in S, Real.exp (-(N * ψ t))) / ∫ t, Real.exp (-(N * ψ t)) := by
  have hint : Integrable (fun t => Real.exp (-(N * ψ t))) := by
    by_contra h
    rw [integral_undef h] at hZ
    exact lt_irrefl _ hZ
  have hnn : 0 ≤ᵐ[volume] fun t => Real.exp (-(N * ψ t)) :=
    Filter.Eventually.of_forall fun t => (Real.exp_pos _).le
  have hZe : (∫⁻ t, ENNReal.ofReal (Real.exp (-(N * ψ t)))) =
      ENNReal.ofReal (∫ t, Real.exp (-(N * ψ t))) :=
    (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
  have hSe : (∫⁻ t in S, ENNReal.ofReal (Real.exp (-(N * ψ t)))) =
      ENNReal.ofReal (∫ t in S, Real.exp (-(N * ψ t))) :=
    (ofReal_integral_eq_lintegral_ofReal hint.integrableOn
      (ae_restrict_of_ae hnn)).symm
  unfold foldLatentEtaFIN061
  rw [Measure.smul_apply, withDensity_apply _ hS, smul_eq_mul, hZe, hSe, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le,
    ENNReal.toReal_ofReal (setIntegral_nonneg hS fun t _ => (Real.exp_pos _).le)]
  ring

theorem besselI_zero_le_FIN061 (t : ℝ) : besselI 0 t ≤ Real.exp |t| := by
  have h0 : besselI 0 t = ∫ θ, Real.exp (t * angCos θ) * 1 ∂angHaar := by
    simp [besselI, angMode_zero]
  rw [h0]
  have hI := integrable_exp_mul t (fun _ => 1) continuous_const (fun _ => by simp)
  calc ∫ θ, Real.exp (t * angCos θ) * 1 ∂angHaar ≤ ∫ _θ, Real.exp |t| ∂angHaar :=
        integral_mono hI (integrable_const _) fun θ => by
          rw [mul_one]; exact Real.exp_le_exp.2 (mul_angCos_le t θ)
    _ = Real.exp |t| := by simp

theorem log_besselI_zero_le_FIN061 (t : ℝ) : Real.log (besselI 0 t) ≤ |t| :=
  (Real.log_le_iff_le_exp (besselI_zero_pos t)).2 (besselI_zero_le_FIN061 t)

/-- Quadratic growth of `scalarPsi` around any point. -/
theorem quadratic_growth_FIN061 {κ : ℝ} (hκ : 0 < κ) (h p : ℝ) :
    ∃ b > 0, ∃ C : ℝ, ∀ w : ℝ, b * dist w p ^ 2 - C ≤ scalarPsi κ h w - scalarPsi κ h p := by
  refine ⟨1 / (8 * κ), by positivity,
    (h - p) ^ 2 / (2 * κ) + 2 * κ + |p| + scalarPsi κ h p, fun w => ?_⟩
  have hlog := log_besselI_zero_le_FIN061 w
  have hd : dist w p = |w - p| := Real.dist_eq w p
  rw [hd, sq_abs]
  unfold scalarPsi
  have hx : |w - p| ≤ (w - p) ^ 2 / (8 * κ) + 2 * κ := by
    have h8 : 0 < 8 * κ := by positivity
    rw [← sub_nonneg]
    have : (w - p) ^ 2 / (8 * κ) + 2 * κ - |w - p| = (|w - p| - 4 * κ) ^ 2 / (8 * κ) := by
      have hsa : |w - p| ^ 2 = (w - p) ^ 2 := sq_abs _
      field_simp
      nlinarith [hsa]
    rw [this]; positivity
  have hwp : |w| ≤ |w - p| + |p| := by
    calc |w| = |(w - p) + p| := by ring_nf
      _ ≤ |w - p| + |p| := abs_add_le _ _
  have hsq : (w - p) ^ 2 / (4 * κ) - (h - p) ^ 2 / (2 * κ) ≤ (w - h) ^ 2 / (2 * κ) := by
    have h4 : 0 < 4 * κ := by positivity
    rw [div_sub_div _ _ h4.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ (w - p - 2 * (w - h)) ^ 2 := sq_nonneg _
    nlinarith [mul_pos hκ hκ, sq_nonneg (w - p - 2 * (w - h)), mul_nonneg hκ.le (sq_nonneg (w - p - 2 * (w - h))),
      mul_nonneg (mul_pos hκ hκ).le (sq_nonneg (w - p - 2 * (w - h)))]
  have e1 : (w - p) ^ 2 / (8 * κ) = (w - p) ^ 2 / (4 * κ) - (w - p) ^ 2 / (8 * κ) := by
    field_simp; ring
  have e2 : 1 / (8 * κ) * (w - p) ^ 2 = (w - p) ^ 2 / (8 * κ) := by ring
  have e3 : (p - h) ^ 2 = (h - p) ^ 2 := by ring
  rw [e2, e3]
  linarith


/-- The second Fréchet derivative of a function on `ℝ` is `ψ'' · v · v`. -/
theorem fderiv_fderiv_apply_FIN061 {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (x v : ℝ) :
    fderiv ℝ (fderiv ℝ ψ) x v v = deriv (deriv ψ) x * (v * v) := by
  have h1 : fderiv ℝ ψ = fun y => (deriv ψ y) • (1 : ℝ →L[ℝ] ℝ) := by
    funext y
    ext
    simp [fderiv_eq_smul_deriv]
  have hd : DifferentiableAt ℝ (deriv ψ) x := by
    have : ContDiff ℝ 1 (deriv ψ) := hψ.iterate_deriv' 1 1
    exact (this.differentiable (by simp)) x
  rw [h1]
  have := fderiv_smul_const (c := deriv ψ) hd (1 : ℝ →L[ℝ] ℝ)
  rw [show (fun y => deriv ψ y • (1 : ℝ →L[ℝ] ℝ)) = fun y => (deriv ψ) y • (1 : ℝ →L[ℝ] ℝ) from rfl, this]
  simp [fderiv_eq_smul_deriv]
  ring


/-- FIN019 on `E = ℝ`: two-sided Laplace bound for the global normalizer. -/
theorem laplace_normalizer_FIN061 {ψ : ℝ → ℝ} {tp : ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hmin : ∀ t, t ≠ tp → ψ tp < ψ t) (hH : 0 < deriv (deriv ψ) tp)
    (hgrow : ∃ b > 0, ∃ C : ℝ, ∀ w : ℝ, b * dist w tp ^ 2 - C ≤ ψ w - ψ tp) :
    ∃ L > 0, ∃ A > 0, ∃ N0 : ℝ, 1 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N →
      L * N ^ (-(1 / 2 : ℝ)) * Real.exp (-(N * ψ tp)) ≤ ∫ t, Real.exp (-(N * ψ t)) ∧
      ∫ t, Real.exp (-(N * ψ t)) ≤ A * N ^ (-(1 / 2 : ℝ)) * Real.exp (-(N * ψ tp)) := by
  have h := quadratic_minimum_laplace_bounds_and_gap_tails (E := ℝ) hψ
    (fun w => by
      by_cases hw : w = tp
      · rw [hw]
      · exact (hmin w hw).le)
    (fun w hw => by
      by_contra hne
      have := hmin w hne
      linarith)
    ⟨deriv (deriv ψ) tp, hH, fun v => by
      rw [fderiv_fderiv_apply_FIN061 hψ]
      have : ‖v‖ ^ 2 = v * v := by rw [Real.norm_eq_abs, sq_abs]; ring
      rw [this]⟩
    hgrow
  obtain ⟨⟨L, hL, A, hA, N0, hN0, hb⟩, -⟩ := h
  refine ⟨L, hL, A, hA, N0, hN0, fun N hN => ?_⟩
  have := hb N hN
  simpa [Module.finrank_self] using this


/-- Cubic-coordinate bound: `|ψ(t) - ψ(t_*)| ≤ M³ |t - t_*|³ / 3` on the coordinate interval. -/
theorem cubic_bound_FIN061 {ψ v : ℝ → ℝ} {α β tStar M : ℝ}
    (hα : α < tStar) (hβ : tStar < β)
    (hv : ContDiffOn ℝ ∞ v (Set.Ioo α β)) (hv0 : v tStar = 0)
    (hcube : ∀ t ∈ Set.Ioo α β, v t ^ 3 = 3 * (ψ tStar - ψ t))
    (hbd : ∀ t ∈ Set.Ioo α β, deriv v t ≤ M ∧ 0 ≤ deriv v t) {t : ℝ} (ht : t ∈ Set.Ioo α β) :
    |ψ t - ψ tStar| ≤ M ^ 3 * |t - tStar| ^ 3 / 3 := by
  have hts : tStar ∈ Set.Ioo α β := ⟨hα, hβ⟩
  have hdiff : ∀ x ∈ Set.Ioo α β, DifferentiableAt ℝ v x := fun x hx =>
    ((hv.differentiableOn (by simp)) x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (f := v) (C := M) hdiff
    (fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbd x hx).2]
      exact (hbd x hx).1) (convex_Ioo α β) hts ht
  rw [hv0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have h3 : ψ t - ψ tStar = -(v t ^ 3) / 3 := by
    have := hcube t ht
    linarith
  rw [h3, abs_div, abs_neg, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have : |v t| ^ 3 ≤ (M * |t - tStar|) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hmvt 3
  rw [mul_pow] at this
  linarith

/-- Two-sided bound for the Laplace integral over a centered box where `|N(ψ - ψ_*)| ≤ B`. -/
theorem box_integral_FIN061 {ψ : ℝ → ℝ} (hψ : Continuous ψ) (N tStar r B : ℝ) (hr : 0 < r)
    (hB : ∀ t ∈ Set.Icc (tStar - r) (tStar + r), |N * (ψ t - ψ tStar)| ≤ B) :
    Real.exp (-B) * Real.exp (-(N * ψ tStar)) * (2 * r) ≤
        ∫ t in Set.Icc (tStar - r) (tStar + r), Real.exp (-(N * ψ t)) ∧
      ∫ t in Set.Icc (tStar - r) (tStar + r), Real.exp (-(N * ψ t)) ≤
        Real.exp B * Real.exp (-(N * ψ tStar)) * (2 * r) := by
  have hcont : Continuous fun t => Real.exp (-(N * ψ t)) :=
    Real.continuous_exp.comp (continuous_const.mul hψ).neg
  have hint : IntegrableOn (fun t => Real.exp (-(N * ψ t))) (Set.Icc (tStar - r) (tStar + r)) :=
    hcont.continuousOn.integrableOn_Icc
  have hvol : (volume : Measure ℝ).real (Set.Icc (tStar - r) (tStar + r)) = 2 * r := by
    rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  have hpt : ∀ t ∈ Set.Icc (tStar - r) (tStar + r),
      Real.exp (-B) * Real.exp (-(N * ψ tStar)) ≤ Real.exp (-(N * ψ t)) ∧
      Real.exp (-(N * ψ t)) ≤ Real.exp B * Real.exp (-(N * ψ tStar)) := by
    intro t ht
    have h := abs_le.1 (hB t ht)
    rw [← Real.exp_add, ← Real.exp_add]
    constructor <;> apply Real.exp_le_exp.2 <;> nlinarith [h.1, h.2]
  constructor
  · have := setIntegral_mono_on (integrableOn_const (by simp)) hint measurableSet_Icc
      (fun t ht => (hpt t ht).1)
    rw [setIntegral_const, hvol, smul_eq_mul] at this
    linarith
  · have := setIntegral_mono_on hint (integrableOn_const (by simp)) measurableSet_Icc
      (fun t ht => (hpt t ht).2)
    rw [setIntegral_const, hvol, smul_eq_mul] at this
    linarith

end DGPS.FiniteN.ScalarFoldFIN061

namespace DGPS.FiniteN

open DGPS.Models DGPS.FiniteN.ScalarFoldFIN061

/-- **FIN061.** Fold latent rare box mass.  For `κ > 2` let `ψ = scalarPsi κ h_c`,
`t_* = -s_*`, `d_N = N^{-1/3}`, and let `η_N ∝ e^{-Nψ} dt` be the latent law.  There are a positive
nondegenerate global minimizer `t₊ > 0` of `ψ` and `Δ = ψ(t_*) - ψ(t₊) > 0` such that for every
fixed `K > 0` the box mass `η_N(|t - t_*| ≤ K d_N)` lies between `c N^{1/6} e^{-NΔ}` and
`C N^{1/6} e^{-NΔ}` for all large `N` (`c, C > 0` depending on `κ` and `K`).  As `K > 0` is
arbitrary, this includes every fixed nontrivial smaller centered box. -/
theorem fold_latent_rare_box_mass (κ : ℝ) (hκ : 2 < κ) :
    let hc := scalarFoldField κ
    let ψ := scalarPsi κ hc
    let tStar := -scalarFoldPoint κ
    ∃ tPlus Δ : ℝ, 0 < tPlus ∧ (∀ t : ℝ, t ≠ tPlus → ψ tPlus < ψ t) ∧
      Δ = ψ tStar - ψ tPlus ∧ 0 < Δ ∧
      ∀ K : ℝ, 0 < K → ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℝ, 1 ≤ N0 ∧
        ∀ N : ℝ, N0 ≤ N →
          c * N ^ (1 / 6 : ℝ) * Real.exp (-(N * Δ)) ≤
              (foldLatentEtaFIN061 ψ N
                (Set.Icc (tStar - K * N ^ (-(1 / 3) : ℝ)) (tStar + K * N ^ (-(1 / 3) : ℝ)))).toReal ∧
            (foldLatentEtaFIN061 ψ N
                (Set.Icc (tStar - K * N ^ (-(1 / 3) : ℝ)) (tStar + K * N ^ (-(1 / 3) : ℝ)))).toReal ≤
              C * N ^ (1 / 6 : ℝ) * Real.exp (-(N * Δ)) := by
  intro hc ψ tStar
  have hκ0 : 0 < κ := by linarith
  have hψinf : ContDiff ℝ ∞ ψ := ScalarFoldFIN057.scalarPsi_contDiff_FIN057 κ hc
  have hψ2 : ContDiff ℝ 2 ψ := hψinf.of_le (WithTop.coe_le_coe.2 le_top)
  have hψc : Continuous ψ := hψinf.continuous
  obtain ⟨-, -, tp, htp0, -, -, -, -, -, -, -, hH, hmin, -, hΔ⟩ := fold_auxiliary_cubic_geometry κ hκ
  obtain ⟨α, β, v, T, m, M, hα, hβ, hm, hmM, hv, hv0, hcube, hbd, -, -, -, -, -, -⟩ :=
    exact_fold_cubic_coordinate κ hκ
  refine ⟨tp, ψ tStar - ψ tp, htp0, hmin, rfl, hΔ, fun K hK => ?_⟩
  -- Laplace bound for the global normalizer
  obtain ⟨b, hb, Cg, hgrow⟩ := quadratic_growth_FIN061 hκ0 hc tp
  obtain ⟨L, hL, A, hA, N1, hN1, hlap⟩ :=
    laplace_normalizer_FIN061 hψ2 hmin hH ⟨b, hb, Cg, hgrow⟩
  -- the box lies in the coordinate interval for large N
  set ρ : ℝ := min (tStar - α) (β - tStar) with hρ
  have hρ0 : 0 < ρ := lt_min (by linarith) (by linarith)
  set B : ℝ := M ^ 3 * K ^ 3 / 3 with hBdef
  refine ⟨2 * K * Real.exp (-B) / A, by positivity, 2 * K * Real.exp B / L, by positivity,
    max N1 (K ^ 3 / ρ ^ 3 + 1), le_trans hN1 (le_max_left _ _), fun N hN => ?_⟩
  have hN1' : N1 ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : K ^ 3 / ρ ^ 3 + 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < N := by linarith
  have hlapN := hlap N hN1'
  -- scalings
  set d : ℝ := N ^ (-(1 / 3) : ℝ) with hd
  set e : ℝ := N ^ (-(1 / 2) : ℝ) with he
  set s : ℝ := N ^ (1 / 6 : ℝ) with hs
  have hdpos : 0 < d := Real.rpow_pos_of_pos hNpos _
  have hepos : 0 < e := Real.rpow_pos_of_pos hNpos _
  have hspos : 0 < s := Real.rpow_pos_of_pos hNpos _
  have hd_eq : d = s * e := by
    rw [hd, hs, he, ← Real.rpow_add hNpos]; norm_num
  have hd3 : N * d ^ 3 = 1 := by
    have : d ^ 3 = N ^ (-1 : ℝ) := by
      rw [hd, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num
    rw [this, Real.rpow_neg_one]; field_simp
  -- the box is inside the coordinate interval
  have hKd : K * d < ρ := by
    have h1 : (K * d) ^ 3 < ρ ^ 3 := by
      have : (K * d) ^ 3 = K ^ 3 / N := by
        rw [mul_pow]; field_simp; nlinarith [hd3]
      rw [this, div_lt_iff₀ hNpos]
      have h2 : K ^ 3 / ρ ^ 3 < N := by linarith
      rw [div_lt_iff₀ (by positivity)] at h2
      linarith
    exact lt_of_pow_lt_pow_left₀ 3 hρ0.le h1
  have hmem : ∀ t ∈ Set.Icc (tStar - K * d) (tStar + K * d), t ∈ Set.Ioo α β := by
    intro t ht
    have h1 : tStar - K * d ≤ t := ht.1
    have h2 : t ≤ tStar + K * d := ht.2
    have h3 : ρ ≤ tStar - α := min_le_left _ _
    have h4 : ρ ≤ β - tStar := min_le_right _ _
    constructor <;> linarith
  -- bound N |ψ t - ψ t_*| ≤ B on the box
  have hBbox : ∀ t ∈ Set.Icc (tStar - K * d) (tStar + K * d), |N * (ψ t - ψ tStar)| ≤ B := by
    intro t ht
    have hc3 := cubic_bound_FIN061 (ψ := ψ) (v := v) (tStar := tStar) (M := M) hα hβ hv hv0 hcube
      (fun x hx => ⟨(hbd x hx).2, by linarith [(hbd x hx).1]⟩) (hmem t ht)
    have habs : |t - tStar| ≤ K * d := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have hM0 : 0 ≤ M := by linarith
    rw [abs_mul, abs_of_pos hNpos]
    calc N * |ψ t - ψ tStar| ≤ N * (M ^ 3 * |t - tStar| ^ 3 / 3) :=
          mul_le_mul_of_nonneg_left hc3 hNpos.le
      _ ≤ N * (M ^ 3 * (K * d) ^ 3 / 3) := by
          gcongr
      _ = B := by
          have : N * (M ^ 3 * (K * d) ^ 3 / 3) = M ^ 3 * K ^ 3 / 3 * (N * d ^ 3) := by ring
          rw [this, hd3, mul_one]
  obtain ⟨hbl, hbu⟩ := box_integral_FIN061 hψc N tStar (K * d) B (by positivity) hBbox
  -- assemble
  have hZl := hlapN.1
  have hZu := hlapN.2
  set Q : ℝ := Real.exp (-(N * ψ tp)) with hQ
  set P : ℝ := Real.exp (-(N * ψ tStar)) with hP
  set E : ℝ := Real.exp (-(N * (ψ tStar - ψ tp))) with hE
  have hQpos : 0 < Q := Real.exp_pos _
  have hPQ : P = Q * E := by
    rw [hP, hQ, hE, ← Real.exp_add]; congr 1; ring
  have hZpos : 0 < ∫ t, Real.exp (-(N * ψ t)) := lt_of_lt_of_le (by positivity) hZl
  rw [eta_real_FIN061 ψ N hZpos _ measurableSet_Icc]
  have hexpB : 0 < Real.exp B := Real.exp_pos _
  have hexpmB : 0 < Real.exp (-B) := Real.exp_pos _
  have hEpos : 0 < E := Real.exp_pos _
  set Z : ℝ := ∫ t, Real.exp (-(N * ψ t)) with hZ
  set Nu : ℝ := ∫ t in Set.Icc (tStar - K * d) (tStar + K * d), Real.exp (-(N * ψ t)) with hNu
  have hscale : 2 * (K * d) = 2 * K * (s * e) := by rw [hd_eq]; ring
  constructor
  · rw [le_div_iff₀ hZpos]
    calc 2 * K * Real.exp (-B) / A * s * E * Z
        ≤ 2 * K * Real.exp (-B) / A * s * E * (A * e * Q) := by gcongr
      _ = Real.exp (-B) * P * (2 * (K * d)) := by
          rw [hPQ, hscale]; field_simp
      _ ≤ Nu := by
          rw [hscale] at hbl ⊢
          exact hbl
  · rw [div_le_iff₀ hZpos]
    calc Nu ≤ Real.exp B * P * (2 * (K * d)) := hbu
      _ = 2 * K * Real.exp B / L * s * E * (L * e * Q) := by
          rw [hPQ, hscale]; field_simp
      _ ≤ 2 * K * Real.exp B / L * s * E * Z := by gcongr

end DGPS.FiniteN
