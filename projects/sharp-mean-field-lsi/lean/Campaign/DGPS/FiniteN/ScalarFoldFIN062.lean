import DGPS.FiniteN.ScalarFoldFIN061
import DGPS.FiniteN.ScalarFoldFIN060F
import DGPS.FiniteN.Tools.Hubbard
import DGPS.FiniteN.Tools.GaussianCoupling

/-!
# FIN062: fold empirical support upper bound by the posterior

For the scalar cosine Hubbard model at the fold field `h_c`, let `z_N` be the posterior center
of the empirical field, `t_* = -s_*`, `d_N = N^{-1/3}` and `S_N = {|z_N - t_*| ≤ 2 d_N}`.
The exact posterior coupling (FIN011) writes the latent variable as `t = z_N + N^{-1/2} √κ ξ`
with `ξ` standard Gaussian and independent of the particles.  On the event `|ξ| < r_N`, where
`r_N` is chosen so that `N^{-1/2} √κ r_N ≤ d_N`, the latent point lies in `|t - t_*| ≤ 3 d_N`.
Since the Gaussian event `|ξ| < r_N` has probability at least `1/2` once `r_N² ≥ 2`, we get
`P_N(S_N) ≤ 2 η_N(|t - t_*| ≤ 3 d_N)`, and the FIN061 box bound closes the estimate.

The main theorem is `DGPS.FiniteN.fold_empirical_support_upper_by_posterior`.
Helper names carry the suffix `FIN062`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DGPS.FiniteN.ScalarFoldFIN062

open DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.GaussianCoupling

theorem coord_bound_FIN062 {c t q x r d : ℝ} (hc : |c - t| ≤ 2 * d) (hx : |x| < r)
    (hqr : |q| * r ≤ d) : |c + q * x - t| ≤ 3 * d := by
  have h1 : |q * x| ≤ d := by
    rw [abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_left hx.le (abs_nonneg q)) hqr
  have h2 : c + q * x - t = (c - t) + q * x := by ring
  rw [h2]
  have h3 := abs_add_le (c - t) (q * x)
  linarith

theorem affine_coord_FIN062 (D : Matrix (Fin 1) (Fin 1) ℝ) (N : ℕ+) (c ξ : Fin 1 → ℝ) :
    affineMap D N c ξ 0 = c 0 + (Real.sqrt (N : ℝ))⁻¹ * sqrtD D 0 0 * ξ 0 := by
  simp only [affineMap, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Fin.sum_univ_one]
  ring

theorem sqrtD_sq_FIN062 (D : Matrix (Fin 1) (Fin 1) ℝ) (hD : D.PosDef) :
    sqrtD D 0 0 * sqrtD D 0 0 = D 0 0 := by
  have h := congrFun (congrFun (sqrtD_mul_self hD) 0) 0
  simpa [Matrix.mul_apply, Fin.sum_univ_one] using h

theorem d_facts_FIN062 {κ N : ℝ} (hN : 8 * κ ^ 3 ≤ N) (hN1 : 1 ≤ N) :
    0 < N ^ (-(1 / 3) : ℝ) ∧ 2 * κ ≤ (N ^ (-(1 / 3) : ℝ)) ^ 2 * N := by
  have hN0 : 0 < N := by linarith
  have hd0 : 0 < N ^ (-(1 / 3) : ℝ) := Real.rpow_pos_of_pos hN0 _
  have hdinv : (N ^ (-(1 / 3) : ℝ)) ^ 3 = N⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num [Real.rpow_neg_one]
  have hd3 : (N ^ (-(1 / 3) : ℝ)) ^ 3 * N = 1 := by
    rw [hdinv, inv_mul_cancel₀ hN0.ne']
  have h8 : 8 * κ ^ 3 * (N ^ (-(1 / 3) : ℝ)) ^ 3 ≤ 1 := by
    rw [hdinv, ← div_eq_mul_inv, div_le_one hN0]
    exact hN
  have h2 : 2 * κ * N ^ (-(1 / 3) : ℝ) ≤ 1 := by
    by_contra hcon
    have hcon' : 1 < 2 * κ * N ^ (-(1 / 3) : ℝ) := not_le.mp hcon
    have h1 : 1 < (2 * κ * N ^ (-(1 / 3) : ℝ)) ^ 3 := one_lt_pow₀ hcon' (by norm_num)
    have h3 : (2 * κ * N ^ (-(1 / 3) : ℝ)) ^ 3 = 8 * κ ^ 3 * (N ^ (-(1 / 3) : ℝ)) ^ 3 := by
      ring
    linarith
  refine ⟨hd0, le_of_mul_le_mul_right ?_ hd0⟩
  calc 2 * κ * N ^ (-(1 / 3) : ℝ) ≤ 1 := h2
    _ = (N ^ (-(1 / 3) : ℝ)) ^ 2 * N * N ^ (-(1 / 3) : ℝ) := by
      have e : (N ^ (-(1 / 3) : ℝ)) ^ 2 * N * N ^ (-(1 / 3) : ℝ) =
          (N ^ (-(1 / 3) : ℝ)) ^ 3 * N := by ring
      rw [e, hd3]

theorem radius_FIN062 {κ N d a : ℝ} (hκ : 0 < κ) (hN : 0 < N) (ha : a * a = κ) (hd : 0 < d)
    (hdN : 2 * κ ≤ d ^ 2 * N) :
    ∃ r : ℝ, 0 < r ∧ |(Real.sqrt N)⁻¹ * a| * r ≤ d ∧ 2 ≤ r ^ 2 := by
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at ha
    norm_num at ha
    linarith
  have hs0 : (Real.sqrt N)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_ne_zero'.2 hN)
  have hq0 : 0 < |(Real.sqrt N)⁻¹ * a| := abs_pos.2 (mul_ne_zero hs0 ha0)
  have ha2 : a ^ 2 = κ := by rw [sq]; exact ha
  have hq2 : ((Real.sqrt N)⁻¹ * a) ^ 2 = κ / N := by
    rw [mul_pow, inv_pow, Real.sq_sqrt hN.le, ha2]
    ring
  refine ⟨d / |(Real.sqrt N)⁻¹ * a|, div_pos hd hq0, le_of_eq ?_, ?_⟩
  · field_simp
  · rw [div_pow, sq_abs, hq2, div_div_eq_mul_div, le_div_iff₀ hκ]
    exact hdN

theorem gauss_good_FIN062 {r : ℝ} (hr : 0 < r) (hr2 : 2 ≤ r ^ 2) :
    2⁻¹ ≤ stdGaussianPi 1 ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' {y : ℝ | r ≤ |y|})ᶜ := by
  have hY : MeasurableSet {y : ℝ | r ≤ |y|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hpre : MeasurableSet ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' {y : ℝ | r ≤ |y|}) :=
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurable hY
  have hmp : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ)
      (stdGaussianPi 1) (gaussianReal 0 1) :=
    measurePreserving_funUnique (gaussianReal 0 1) (Fin 1)
  have : IsProbabilityMeasure (stdGaussianPi 1) := by
    unfold stdGaussianPi
    infer_instance
  have hmem : MemLp id 2 (gaussianReal 0 1) := memLp_id_gaussianReal' 2 (by simp)
  have hint : ∫ x, id x ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal
  have hvar : variance id (gaussianReal 0 1) = 1 := variance_id_gaussianReal
  have hC := ProbabilityTheory.meas_ge_le_variance_div_sq hmem hr
  rw [hint, hvar] at hC
  simp only [id_eq, sub_zero] at hC
  have hbad : stdGaussianPi 1 ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' {y : ℝ | r ≤ |y|}) ≤
      2⁻¹ := by
    rw [hmp.measure_preimage hY.nullMeasurableSet]
    calc gaussianReal 0 1 {y : ℝ | r ≤ |y|} ≤ ENNReal.ofReal (1 / r ^ 2) := hC
      _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le two_pos hr2)
      _ = 2⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  have hsum : stdGaussianPi 1 ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' {y : ℝ | r ≤ |y|}) +
      stdGaussianPi 1 ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' {y : ℝ | r ≤ |y|})ᶜ = 1 :=
    prob_add_prob_compl hpre
  have key : (2⁻¹ : ℝ≥0∞) + 2⁻¹ ≤ 2⁻¹ + stdGaussianPi 1
      ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' {y : ℝ | r ≤ |y|})ᶜ := by
    rw [ENNReal.inv_two_add_inv_two, ← hsum]
    gcongr
  exact ENNReal.le_of_add_le_add_left (ENNReal.inv_ne_top.2 two_ne_zero) key

theorem auxLaw_box_FIN062 {κ : ℝ} (hκ : 0 < κ) (h : ℝ) (N : ℕ+) (B : Set ℝ)
    (hB : MeasurableSet B) :
    auxLaw (ScalarFoldFIN060.dSFIN060 κ) (ScalarFoldFIN060.hSFIN060 h)
        ScalarFoldFIN060.uSFIN060 ScalarFoldFIN060.phiSFIN060 (DGPS.haar 1) N
        ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' B) =
      DGPS.FiniteN.foldLatentEtaFIN061 (DGPS.Models.scalarPsi κ h) (N : ℝ) B := by
  have hT : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ) volume volume :=
    volume_preserving_funUnique (Fin 1) ℝ
  have hemb := (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding
  have hZ : ∫⁻ w : Fin 1 → ℝ, ENNReal.ofReal (Real.exp (-((N : ℝ) *
        DGPS.Models.scalarPsi κ h (w 0)))) =
      ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (-((N : ℝ) * DGPS.Models.scalarPsi κ h t))) :=
    hT.lintegral_comp_emb hemb (fun t : ℝ => ENNReal.ofReal (Real.exp (-((N : ℝ) *
      DGPS.Models.scalarPsi κ h t))))
  have hS : ∫⁻ w in (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' B,
        ENNReal.ofReal (Real.exp (-((N : ℝ) * DGPS.Models.scalarPsi κ h (w 0)))) =
      ∫⁻ t in B, ENNReal.ofReal (Real.exp (-((N : ℝ) * DGPS.Models.scalarPsi κ h t))) :=
    hT.setLIntegral_comp_preimage_emb hemb (fun t : ℝ => ENNReal.ofReal (Real.exp (-((N : ℝ) *
      DGPS.Models.scalarPsi κ h t)))) B
  have hpre : MeasurableSet ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' B) :=
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurable hB
  unfold auxLaw DGPS.FiniteN.foldLatentEtaFIN061 auxMass
  simp only [ScalarFoldFIN060.auxPotential_FIN060 hκ, neg_mul]
  rw [Measure.smul_apply, Measure.smul_apply, withDensity_apply _ hpre, withDensity_apply _ hB,
    smul_eq_mul, smul_eq_mul, hZ, hS]

theorem particle_support_le_FIN062 {M : Type*} [MeasurableSpace M] {m : Measure M}
    [IsFiniteMeasure m] {U : M → ℝ} {φ : M → Fin 1 → ℝ} (hyp : HubbardHyp m U φ)
    {D : Matrix (Fin 1) (Fin 1) ℝ} (hD : D.PosDef) (h : Fin 1 → ℝ) (N : ℕ+) (t d r : ℝ)
    (hqr : |(Real.sqrt (N : ℝ))⁻¹ * sqrtD D 0 0| * r ≤ d) (hr : 0 < r) (hr2 : 2 ≤ r ^ 2) :
    hubbardParticleLaw D h U φ m N {x : Fin (N : ℕ) → M | |posteriorCenter D h φ N x 0 - t| ≤
        2 * d} ≤
      2 * auxLaw D h U φ m N ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹'
        Icc (t - 3 * d) (t + 3 * d)) := by
  have hC : Measurable (couplingMap D h φ N) := by
    refine Measurable.prodMk ?_ measurable_fst
    have h1 : Measurable fun p : (Fin (N : ℕ) → M) × (Fin 1 → ℝ) =>
        posteriorCenter D h φ N p.1 := (measurable_posteriorCenter hyp D h N).comp measurable_fst
    have hcont : Continuous fun ξ : Fin 1 → ℝ => (Real.sqrt (N : ℝ))⁻¹ • Matrix.mulVec (sqrtD D) ξ := by
      unfold Matrix.mulVec dotProduct
      fun_prop
    have h2 : Measurable fun p : (Fin (N : ℕ) → M) × (Fin 1 → ℝ) =>
        (Real.sqrt (N : ℝ))⁻¹ • Matrix.mulVec (sqrtD D) p.2 := hcont.measurable.comp measurable_snd
    exact h1.add h2
  have hA3 : MeasurableSet ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Icc (t - 3 * d) (t + 3 * d)) :=
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurable measurableSet_Icc
  have hpreY : MeasurableSet ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' {y : ℝ | r ≤ |y|}) :=
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurable
      (measurableSet_le measurable_const continuous_abs.measurable)
  have : IsProbabilityMeasure (stdGaussianPi 1) := by
    unfold stdGaussianPi
    infer_instance
  have hsub : {x : Fin (N : ℕ) → M | |posteriorCenter D h φ N x 0 - t| ≤ 2 * d} ×ˢ
        ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' {y : ℝ | r ≤ |y|})ᶜ ⊆
      (couplingMap D h φ N) ⁻¹' (Prod.fst ⁻¹' ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹'
        Icc (t - 3 * d) (t + 3 * d))) := by
    rintro ⟨x, ξ⟩ ⟨hx, hξ⟩
    have hξ' : |ξ 0| < r := by
      by_contra hcon
      exact hξ (show r ≤ |ξ 0| from not_lt.mp hcon)
    have key : |affineMap D N (posteriorCenter D h φ N x) ξ 0 - t| ≤ 3 * d := by
      rw [affine_coord_FIN062]
      exact coord_bound_FIN062 hx hξ' hqr
    have hab := abs_le.mp key
    show (MeasurableEquiv.funUnique (Fin 1) ℝ) (affineMap D N (posteriorCenter D h φ N x) ξ) ∈
      Icc (t - 3 * d) (t + 3 * d)
    show affineMap D N (posteriorCenter D h φ N x) ξ 0 ∈ Icc (t - 3 * d) (t + 3 * d)
    exact ⟨by linarith [hab.1], by linarith [hab.2]⟩
  have hmain : hubbardParticleLaw D h U φ m N {x : Fin (N : ℕ) → M | |posteriorCenter D h φ N x 0 - t| ≤
        2 * d} * stdGaussianPi 1 ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' {y : ℝ | r ≤ |y|})ᶜ ≤
      auxLaw D h U φ m N ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹'
        Icc (t - 3 * d) (t + 3 * d)) := by
    calc hubbardParticleLaw D h U φ m N {x : Fin (N : ℕ) → M | |posteriorCenter D h φ N x 0 - t| ≤
            2 * d} * stdGaussianPi 1 ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' {y : ℝ | r ≤ |y|})ᶜ
        = ((hubbardParticleLaw D h U φ m N).prod (stdGaussianPi 1))
            ({x : Fin (N : ℕ) → M | |posteriorCenter D h φ N x 0 - t| ≤ 2 * d} ×ˢ
              ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' {y : ℝ | r ≤ |y|})ᶜ) :=
          (Measure.prod_prod _ _).symm
      _ ≤ ((hubbardParticleLaw D h U φ m N).prod (stdGaussianPi 1))
            ((couplingMap D h φ N) ⁻¹' (Prod.fst ⁻¹' ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹'
              Icc (t - 3 * d) (t + 3 * d)))) := measure_mono hsub
      _ = (((hubbardParticleLaw D h U φ m N).prod (stdGaussianPi 1)).map (couplingMap D h φ N))
            (Prod.fst ⁻¹' ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹'
              Icc (t - 3 * d) (t + 3 * d))) :=
          (Measure.map_apply hC (measurable_fst hA3)).symm
      _ = hubbardJoint D h U φ m N (Prod.fst ⁻¹' ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹'
              Icc (t - 3 * d) (t + 3 * d))) := by
          rw [coupling_eq hyp hD h N]
      _ = (hubbardJoint D h U φ m N).map Prod.fst ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹'
              Icc (t - 3 * d) (t + 3 * d)) := (Measure.map_apply measurable_fst hA3).symm
      _ = auxLaw D h U φ m N ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹'
              Icc (t - 3 * d) (t + 3 * d)) := by
          rw [hubbardJoint_map_fst hyp hD h N]
  have hhalf := gauss_good_FIN062 hr hr2
  have h1 : hubbardParticleLaw D h U φ m N {x : Fin (N : ℕ) → M | |posteriorCenter D h φ N x 0 - t| ≤
        2 * d} * 2⁻¹ ≤ auxLaw D h U φ m N ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹'
          Icc (t - 3 * d) (t + 3 * d)) :=
    le_trans (mul_le_mul_of_nonneg_left hhalf (by positivity)) hmain
  have h22 : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel two_ne_zero (by norm_num)
  calc hubbardParticleLaw D h U φ m N {x : Fin (N : ℕ) → M | |posteriorCenter D h φ N x 0 - t| ≤
        2 * d}
      = hubbardParticleLaw D h U φ m N {x : Fin (N : ℕ) → M | |posteriorCenter D h φ N x 0 - t| ≤
          2 * d} * (2 * 2⁻¹) := by rw [h22, mul_one]
    _ = 2 * (hubbardParticleLaw D h U φ m N {x : Fin (N : ℕ) → M |
          |posteriorCenter D h φ N x 0 - t| ≤ 2 * d} * 2⁻¹) := by ring
    _ ≤ 2 * auxLaw D h U φ m N ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹'
          Icc (t - 3 * d) (t + 3 * d)) := mul_le_mul_of_nonneg_left h1 (by positivity)

end DGPS.FiniteN.ScalarFoldFIN062

namespace DGPS.FiniteN

open MeasureTheory ProbabilityTheory Set
open DGPS.FiniteN.ScalarFoldFIN062
open DGPS.Models DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.GaussianCoupling

theorem fold_empirical_support_upper_by_posterior (κ : ℝ) (hκ : 2 < κ) :
    ∃ tPlus Δ : ℝ, 0 < tPlus ∧
      (∀ t : ℝ, t ≠ tPlus →
        DGPS.Models.scalarPsi κ (DGPS.Models.scalarFoldField κ) tPlus <
          DGPS.Models.scalarPsi κ (DGPS.Models.scalarFoldField κ) t) ∧
      Δ = DGPS.Models.scalarPsi κ (DGPS.Models.scalarFoldField κ) (-DGPS.Models.scalarFoldPoint κ) -
          DGPS.Models.scalarPsi κ (DGPS.Models.scalarFoldField κ) tPlus ∧
      0 < Δ ∧
      ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℝ, 1 ≤ N0 ∧ ∀ N : ℕ+, N0 ≤ (N : ℝ) →
        hubbardParticleLaw (ScalarFoldFIN060.dSFIN060 κ)
            (ScalarFoldFIN060.hSFIN060 (DGPS.Models.scalarFoldField κ)) ScalarFoldFIN060.uSFIN060
            ScalarFoldFIN060.phiSFIN060 (DGPS.haar 1) N
            {x : Fin (N : ℕ) → DGPS.Torus 1 |
              |posteriorCenter (ScalarFoldFIN060.dSFIN060 κ)
                  (ScalarFoldFIN060.hSFIN060 (DGPS.Models.scalarFoldField κ)) ScalarFoldFIN060.phiSFIN060 N x 0
                - (-DGPS.Models.scalarFoldPoint κ)| ≤ 2 * (N : ℝ) ^ (-(1 / 3) : ℝ)} ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (1 / 6 : ℝ) * Real.exp (-((N : ℝ) * Δ))) := by
  have hκ0 : 0 < κ := by linarith
  obtain ⟨tp, Δ, htp0, hmin, hΔeq, hΔ, hbox⟩ := DGPS.FiniteN.fold_latent_rare_box_mass κ hκ
  refine ⟨tp, Δ, htp0, hmin, hΔeq, hΔ, ?_⟩
  obtain ⟨c0, hc0, C0, hC0, N0, -, hbox3⟩ := hbox 3 (by norm_num)
  refine ⟨2 * C0, by linarith, max (max N0 (8 * κ ^ 3)) 1, le_max_right _ _, ?_⟩
  intro N hN
  have hNr : 1 ≤ (N : ℝ) := le_trans (le_max_right _ _) hN
  have hN8 : 8 * κ ^ 3 ≤ (N : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNN0 : N0 ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNpos : 0 < (N : ℝ) := by linarith
  obtain ⟨hd0, hdN⟩ := d_facts_FIN062 hN8 hNr
  have ha : sqrtD (ScalarFoldFIN060.dSFIN060 κ) 0 0 * sqrtD (ScalarFoldFIN060.dSFIN060 κ) 0 0 = κ := by
    rw [sqrtD_sq_FIN062 _ (ScalarFoldFIN060.dSFIN060_posDef hκ0)]
    simp [ScalarFoldFIN060.dSFIN060]
  obtain ⟨r, hr, hqr, hr2⟩ := radius_FIN062 hκ0 hNpos ha hd0 hdN
  have key := particle_support_le_FIN062 ScalarFoldFIN060.hubbardHyp_FIN060
    (ScalarFoldFIN060.dSFIN060_posDef hκ0) (ScalarFoldFIN060.hSFIN060 (DGPS.Models.scalarFoldField κ)) N
    (-DGPS.Models.scalarFoldPoint κ) ((N : ℝ) ^ (-(1 / 3) : ℝ)) r hqr hr hr2
  rw [auxLaw_box_FIN062 hκ0 (DGPS.Models.scalarFoldField κ) N _ measurableSet_Icc] at key
  obtain ⟨hlow, hup⟩ := hbox3 (N : ℝ) hNN0
  have hpos : 0 < c0 * (N : ℝ) ^ (1 / 6 : ℝ) * Real.exp (-((N : ℝ) * Δ)) :=
    mul_pos (mul_pos hc0 (Real.rpow_pos_of_pos hNpos _)) (Real.exp_pos _)
  have hne : DGPS.FiniteN.foldLatentEtaFIN061 (DGPS.Models.scalarPsi κ (DGPS.Models.scalarFoldField κ))
      (N : ℝ) (Icc (-DGPS.Models.scalarFoldPoint κ - 3 * (N : ℝ) ^ (-(1 / 3) : ℝ))
        (-DGPS.Models.scalarFoldPoint κ + 3 * (N : ℝ) ^ (-(1 / 3) : ℝ))) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hlow
    linarith
  have hb0 : 0 ≤ C0 * (N : ℝ) ^ (1 / 6 : ℝ) * Real.exp (-((N : ℝ) * Δ)) :=
    mul_nonneg (mul_nonneg hC0.le (Real.rpow_nonneg hNpos.le _)) (Real.exp_pos _).le
  have hup' := (ENNReal.le_ofReal_iff_toReal_le hne hb0).2 hup
  refine le_trans key ?_
  calc 2 * DGPS.FiniteN.foldLatentEtaFIN061 (DGPS.Models.scalarPsi κ (DGPS.Models.scalarFoldField κ))
        (N : ℝ) (Icc (-DGPS.Models.scalarFoldPoint κ - 3 * (N : ℝ) ^ (-(1 / 3) : ℝ))
          (-DGPS.Models.scalarFoldPoint κ + 3 * (N : ℝ) ^ (-(1 / 3) : ℝ)))
      ≤ 2 * ENNReal.ofReal (C0 * (N : ℝ) ^ (1 / 6 : ℝ) * Real.exp (-((N : ℝ) * Δ))) :=
        mul_le_mul_of_nonneg_left hup' (by positivity)
    _ = ENNReal.ofReal (2 * (C0 * (N : ℝ) ^ (1 / 6 : ℝ) * Real.exp (-((N : ℝ) * Δ)))) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    _ = ENNReal.ofReal (2 * C0 * (N : ℝ) ^ (1 / 6 : ℝ) * Real.exp (-((N : ℝ) * Δ))) := by
        congr 1
        ring

end DGPS.FiniteN
