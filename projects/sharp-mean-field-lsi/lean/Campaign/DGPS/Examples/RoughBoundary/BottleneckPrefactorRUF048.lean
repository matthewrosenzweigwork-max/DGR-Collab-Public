import DGPS.Examples.RoughBoundary.RareSupportRUF047
import DGPS.Examples.RoughBoundary.SmoothSymmetricTestRUF046
import DGPS.Particle.Rates

set_option maxHeartbeats 2000000

/-!
# RUF048: exact bottleneck upper bound prefactor

For the fixed model and the fixed smooth cutoff data of the RUF043 bottleneck feature, the
symmetric particle rate satisfies `r_N^sym ≤ C N^{-2} e^{-cN}` for all large `N`, with
`c = b/2` and `C = 8 C_grad J_S / (c_A Δ)`. Here `C_grad = CX² CΦ² + 1` (the smooth-cutoff and
smooth-feature gradient bounds, shifted to be positive), `J_S` is the net count of the compact
annulus, `c_A = (2 C_Z)⁻¹` is the rare-support constant, and `Δ` is the remote level.

Proof. The test `F_N = χ(Y_N)` with `Y_N = N⁻¹ Σ Φ(x_i)` is a smooth symmetric test (RUF046).
Its energy is at most `(CX² CΦ² / N) · J_S e^{-N(Δ + b/2)}`, the `N^{-1}` coming from the
empirical-average gradient. Its homogeneous entropy is at least `c_A (Δ/4) N e^{-NΔ}` (the
rare-support bound of RUF047), the second `N` coming from the logarithm `log(1/P_N(B_N))`. Dividing
`2E` by the entropy cancels `e^{-NΔ}` and leaves `N^{-2} e^{-(b/2) N}`.

All RUF043 witnesses come from one obtain. The RUF046 and RUF047 helpers are reused in their
witness-as-hypothesis form, and the entropy step is a generic core lemma.
-/

open MeasureTheory
open scoped ENNReal ContDiff

namespace DGPS.Examples.RoughBoundary.Bottleneck

open DGPS.Examples.RoughBoundary.Feature
open DGPS.Examples.RoughBoundary.FreeEnergy
open DGPS.Examples.RoughBoundary.Model
open DGPS.Examples.RoughBoundary.Particle
open DGPS.Examples.RoughBoundary.Semicontinuity
open DGPS.Examples.RoughBoundary.Landscape

/-- Generic rare-support entropy bound (the core of RUF047, with the witnesses as hypotheses).
If `F ∈ [0,1]` is `1` on `A`, vanishes off `B` with `A ⊆ B`, and the two basin probabilities
satisfy `(2 C_Z)⁻¹ e^{-NΔ} ≤ μ(A)` and `μ(B) ≤ J_B e^{-NΔ/2}` with `4 log J_B ≤ NΔ`, then
`Ent_μ(F²) ≥ (2 C_Z)⁻¹ (Δ/4) N e^{-NΔ}`. -/
lemma rare_support_core_RUF048 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A B : Set Ω} (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hAB : A ⊆ B) {F : Ω → ℝ} (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    (hFA : ∀ x ∈ A, F x = 1) (hFB : ∀ x, x ∉ B → F x = 0)
    {Cz Δ JB N : ℝ} (hCz : 0 < Cz) (hΔ : 0 < Δ) (hJB : 0 < JB) (hN : 0 ≤ N)
    (hAr : (2 * Cz)⁻¹ * Real.exp (-(N * Δ)) ≤ μ.real A)
    (hBr : μ.real B ≤ JB * Real.exp (-N * Δ / 2))
    (hlog : 4 * Real.log JB ≤ N * Δ) :
    ENNReal.ofReal ((2 * Cz)⁻¹ * Δ / 4 * N * Real.exp (-(N * Δ))) ≤
      homogeneousEntropy μ (fun x => F x ^ 2) := by
  have hApos : 0 < μ.real A :=
    lt_of_lt_of_le (mul_pos (inv_pos.mpr (by linarith)) (Real.exp_pos _)) hAr
  have hBpos : 0 < μ.real B := lt_of_lt_of_le hApos (measureReal_mono hAB)
  have hlogB : Real.log (μ.real B) ≤ Real.log JB + (-N * Δ / 2) := by
    have h := Real.log_le_log hBpos hBr
    rwa [Real.log_mul hJB.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  have hL1 : N * Δ / 4 ≤ Real.log (1 / μ.real B) := by
    rw [one_div, Real.log_inv]
    linarith
  have ha_pos : 0 < ∫ x, F x ^ 2 ∂μ :=
    lt_of_lt_of_le hApos (integral_sq_ge_RUF047 hAm hFm hF0 hF1 hFA)
  have hvm : Measurable (fun x => F x ^ 2) := hFm.pow_const 2
  have hvB : ∀ x, x ∉ B → F x ^ 2 = 0 := fun x hx => by
    rw [hFB x hx]
    norm_num
  have hEnt := entropy_lower_by_support_RUF047 hBm hvm (fun x => sq_nonneg (F x))
    (fun x => pow_le_one₀ (hF0 x) (hF1 x)) hvB _ rfl ha_pos hBpos
  have hkey : (2 * Cz)⁻¹ * Δ / 4 * N * Real.exp (-(N * Δ)) ≤
      (∫ x, F x ^ 2 ∂μ) * Real.log (1 / μ.real B) := by
    have hK : (2 * Cz)⁻¹ * Real.exp (-(N * Δ)) ≤ ∫ x, F x ^ 2 ∂μ :=
      hAr.trans (integral_sq_ge_RUF047 hAm hFm hF0 hF1 hFA)
    have hNn : (0 : ℝ) ≤ N * Δ / 4 := div_nonneg (mul_nonneg hN hΔ.le) (by norm_num)
    have hmul := mul_le_mul hK hL1 hNn ha_pos.le
    calc (2 * Cz)⁻¹ * Δ / 4 * N * Real.exp (-(N * Δ))
        = (2 * Cz)⁻¹ * Real.exp (-(N * Δ)) * (N * Δ / 4) := by ring
      _ ≤ _ := hmul
  exact (ENNReal.ofReal_le_ofReal hkey).trans hEnt

/-- RUF048: the exact bottleneck upper bound prefactor. There are positive constants
`C_grad`, `J_S`, `c_A`, `b` such that, with `c = b/2` and `C = 8 C_grad J_S / (c_A Δ)`,
`r_N^sym ≤ C N^{-2} e^{-cN}` for all `N ≥ N₀`. -/
theorem exact_bottleneck_upper_bound_prefactor {L : ℝ} (hL : 0 < L)
    (hcert : RoughLandscapeCertificate (Ufeat L (1 / L)))
    (tstar : EuclideanSpace ℝ (Fin 2)) (r₀ lam : ℝ) (hr₀ : 0 < r₀) (hlam : 0 < lam)
    (hcrit : fderiv ℝ (featurePotential kappa0 (Ufeat L (1 / L))) tstar = 0)
    (h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∉ Metric.closedBall tstar r₀)
    (hH : ∀ x ∈ Metric.closedBall tstar r₀, ∀ v : EuclideanSpace ℝ (Fin 2),
      lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (featurePotential kappa0 (Ufeat L (1 / L)))) x v v) :
    ∃ CG : ℝ, 0 < CG ∧ ∃ JS : ℕ, 0 < JS ∧ ∃ cA : ℝ, 0 < cA ∧ ∃ b : ℝ, 0 < b ∧
      ∃ N₀ : ℕ, ∀ N : ℕ+, N₀ ≤ (N : ℕ) →
        DGPS.particleRateSym (modelData hL (1 / L)) N ≤
          ENNReal.ofReal (8 * CG * JS / (cA * remoteLevel_RUF043 L (1 / L) tstar) *
            ((N : ℝ) ^ 2)⁻¹ * Real.exp (-((N : ℝ) * (b / 2)))) := by
  obtain ⟨R, hR, hΔpos, -, -, -, η, -, hηr, Φ, hΦcd, hΦapp, χ, hχcd, hχ01, -, hχ0, hsupp,
    hχball, -, hBinc, hSinc, hKB, b, hb, hKS, zmin, hzmin, -⟩ :=
    fixed_smooth_bottleneck_feature_and_compatible_neighborhoods hL (1 / L) hcert tstar r₀ lam
      hr₀ hlam hcrit h0 hH
  set zs : EuclideanSpace ℝ (Fin 2) := remoteCentre_RUF043 tstar
  set Δ : ℝ := remoteLevel_RUF043 L (1 / L) tstar
  have hR4 : 0 ≤ R / 4 := by linarith
  have hκ : 0 < kappa := kappa_pos
  have hδSpos : 0 < Real.sqrt (b / kappa) := Real.sqrt_pos.2 (div_pos hb hκ)
  have hδS2 : kappa * Real.sqrt (b / kappa) ^ 2 / 2 = b / 2 := by
    rw [Real.sq_sqrt (div_pos hb hκ).le]
    field_simp
  obtain ⟨CX, hCX0, hCX⟩ := fderiv_bound_RUF046 hχcd hR4 hsupp
  obtain ⟨CΦ, hCΦ0, hCΦ⟩ := partial_bound_RUF046 hΦcd
  obtain ⟨JS, hJS, cS, hcS, hcovS⟩ :=
    exists_finite_net_RUF044 (compactAnnulus_RUF044 zs (R / 4)) ⟨zmin, hzmin⟩ hδSpos
  obtain ⟨Cz, hCz, -, NA, hA⟩ :=
    remote_basin_lower_fixed_RUF047 hL hcert tstar hcrit R η hR hηr Φ hΦcd hΦapp
  obtain ⟨JB, hJB, hB⟩ := basin_upper_fixed_RUF047 hL tstar R hR hΔpos Φ hBinc hKB
  have hJBpos : (0 : ℝ) < JB := Nat.cast_pos.mpr hJB
  have hCzne : Cz ≠ 0 := hCz.ne'
  have hcA : 0 < (2 * Cz)⁻¹ := inv_pos.mpr (by linarith)
  refine ⟨CX ^ 2 * CΦ ^ 2 + 1, by positivity, JS, hJS, (2 * Cz)⁻¹, hcA, b, hb,
    max NA ⌈4 * Real.log JB / Δ⌉₊, ?_⟩
  intro N hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hNA : NA ≤ (N : ℕ) := le_trans (le_max_left _ _) hN
  have hNJ : ⌈4 * Real.log JB / Δ⌉₊ ≤ (N : ℕ) := le_trans (le_max_right _ _) hN
  have hNΔ : 4 * Real.log JB ≤ (N : ℝ) * Δ :=
    (div_le_iff₀ hΔpos).1 ((Nat.le_ceil _).trans (Nat.cast_le.mpr hNJ))
  -- energy estimate for the smooth symmetric test (RUF046 with the witnesses as hypotheses)
  have hsmooth := isSmoothPeriodicParticle_RUF046 (N := N) Φ hΦcd χ hχcd
  have hYm := measurable_smoothMean_RUF046 (N := N) Φ hΦcd
  have hTc : IsClosed (transitionAnnulus_RUF043 zs (R / 4)) := by
    have h1 : IsClosed {y : EuclideanSpace ℝ (Fin 2) | R / 4 ≤ ‖y - zs‖} :=
      isClosed_le continuous_const (by fun_prop)
    have h2 : IsClosed {y : EuclideanSpace ℝ (Fin 2) | ‖y - zs‖ ≤ 2 * (R / 4)} :=
      isClosed_le (by fun_prop) continuous_const
    exact h1.inter h2
  have hS : MeasurableSet {x : DGPS.ParticleSpace 1 N |
      smoothMean_RUF043 Φ N x ∈ transitionAnnulus_RUF043 zs (R / 4)} :=
    hTc.measurableSet.preimage hYm
  have hsubS : {x : DGPS.ParticleSpace 1 N | smoothMean_RUF043 Φ N x ∈
      transitionAnnulus_RUF043 zs (R / 4)} ⊆
      {x : DGPS.ParticleSpace 1 N | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈
        compactAnnulus_RUF043 zs (R / 4)} := by
    intro x hx
    have hx' : smoothMean_RUF043 Φ N x ∈ transitionAnnulus_RUF043 zs (R / 4) := hx
    exact hSinc N x hx'
  have hBound := finite_cover_any_L_RUF044 hL (compactAnnulus_RUF043 zs (R / 4))
    (compactAnnulus_RUF044 zs (R / 4)) (Δ + b) (fun z hz => hKS z hz)
    (Real.sqrt (b / kappa)) hδSpos JS cS hcS hcovS N
  have hexp : -(N : ℝ) * (Δ + b - kappa * Real.sqrt (b / kappa) ^ 2 / 2) =
      -(N : ℝ) * (Δ + b / 2) := by
    rw [hδS2]
    ring
  rw [hexp] at hBound
  have hprob := (measure_mono hsubS).trans hBound
  have hpt := pointwise_RUF046 (N := N) Φ hΦcd χ hχcd hsupp hCX0 hCX hCΦ0 hCΦ
  obtain ⟨f, hfF, hE⟩ := energy_le_RUF046 (A := modelData hL (1 / L)) (N := N)
    (fun x : DGPS.ParticleSpace 1 N => χ (smoothMean_RUF043 Φ N x)) hsmooth _ hS
    (c := CX ^ 2 * CΦ ^ 2 / (N : ℝ)) (p := (JS : ℝ) * Real.exp (-(N : ℝ) * (Δ + b / 2)))
    (by positivity) (by positivity) hpt hprob
  -- the test is symmetric
  have hsym : DGPS.IsSymmetricParticleFun (modelData hL (1 / L)) N
      (fun x : DGPS.ParticleSpace 1 N => χ (smoothMean_RUF043 Φ N x)) := by
    intro σ
    refine Filter.Eventually.of_forall fun x => ?_
    have hsum : ∑ i, Φ (x (σ i)) = ∑ i, Φ (x i) :=
      Equiv.sum_comp σ (fun k => Φ (x k))
    show χ (smoothMean_RUF043 Φ N (DGPS.permuteParticles σ x)) =
      χ (smoothMean_RUF043 Φ N x)
    unfold smoothMean_RUF043 DGPS.permuteParticles
    rw [hsum]
  have hfs : DGPS.IsSymmetricParticleTest f := by
    unfold DGPS.IsSymmetricParticleTest
    rw [hfF]
    exact hsym
  -- rare-support entropy bound
  have hPμ : IsProbabilityMeasure (DGPS.particleLaw (modelData hL (1 / L)) N) := inferInstance
  set μ := DGPS.particleLaw (modelData hL (1 / L)) N
  have hFm : Measurable (fun x : DGPS.ParticleSpace 1 N => χ (smoothMean_RUF043 Φ N x)) :=
    hχcd.continuous.measurable.comp hYm
  have hF01 : ∀ x : DGPS.ParticleSpace 1 N,
      0 ≤ χ (smoothMean_RUF043 Φ N x) ∧ χ (smoothMean_RUF043 Φ N x) ≤ 1 :=
    fun x => hχ01 _
  have hAm : MeasurableSet {x : DGPS.ParticleSpace 1 N | smoothMean_RUF043 Φ N x ∈
      Metric.ball zs ((R / 4) / 2)} :=
    Metric.isOpen_ball.measurableSet.preimage hYm
  have hBm : MeasurableSet {x : DGPS.ParticleSpace 1 N | smoothMean_RUF043 Φ N x ∈
      Metric.ball zs (2 * (R / 4))} :=
    Metric.isOpen_ball.measurableSet.preimage hYm
  have hAB : {x : DGPS.ParticleSpace 1 N | smoothMean_RUF043 Φ N x ∈
      Metric.ball zs ((R / 4) / 2)} ⊆
      {x : DGPS.ParticleSpace 1 N | smoothMean_RUF043 Φ N x ∈
        Metric.ball zs (2 * (R / 4))} :=
    fun x hx => Metric.ball_subset_ball (by linarith) hx
  have hFA : ∀ x ∈ {x : DGPS.ParticleSpace 1 N | smoothMean_RUF043 Φ N x ∈
      Metric.ball zs ((R / 4) / 2)}, χ (smoothMean_RUF043 Φ N x) = 1 := by
    intro x hx
    rw [Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm] at hx
    exact (hχball _ hx).1
  have hFB : ∀ x, x ∉ {x : DGPS.ParticleSpace 1 N | smoothMean_RUF043 Φ N x ∈
      Metric.ball zs (2 * (R / 4))} → χ (smoothMean_RUF043 Φ N x) = 0 := by
    intro x hx
    rw [Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm, not_lt] at hx
    exact hχ0 _ hx
  have hAr : (2 * Cz)⁻¹ * Real.exp (-((N : ℝ) * Δ)) ≤ μ.real {x : DGPS.ParticleSpace 1 N |
      smoothMean_RUF043 Φ N x ∈ Metric.ball zs ((R / 4) / 2)} :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 (hA N hNA)
  have hBr : μ.real {x : DGPS.ParticleSpace 1 N | smoothMean_RUF043 Φ N x ∈
      Metric.ball zs (2 * (R / 4))} ≤ (JB : ℝ) * Real.exp (-(N : ℝ) * Δ / 2) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hB N)
    rw [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)] at h
    exact h
  have hEnt : ENNReal.ofReal ((2 * Cz)⁻¹ * Δ / 4 * (N : ℝ) * Real.exp (-((N : ℝ) * Δ))) ≤
      DGPS.particleEntropy (modelData hL (1 / L)) N f := by
    unfold DGPS.particleEntropy
    rw [hfF]
    exact rare_support_core_RUF048 hAm hBm hAB hFm (fun x => (hF01 x).1)
      (fun x => (hF01 x).2) hFA hFB hCz hΔpos hJBpos hN0.le hAr hBr hNΔ
  -- the quotient bound: 2E / Ent ≤ C N^{-2} e^{-(b/2) N}
  have hYpos : 0 < (2 * Cz)⁻¹ * Δ / 4 * (N : ℝ) * Real.exp (-((N : ℝ) * Δ)) :=
    mul_pos (mul_pos (div_pos (mul_pos hcA hΔpos) (by norm_num)) hN0) (Real.exp_pos _)
  have hEntPos : 0 < DGPS.particleEntropy (modelData hL (1 / L)) N f :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.2 hYpos) hEnt
  have hsplit : Real.exp (-(N : ℝ) * (Δ + b / 2)) =
      Real.exp (-((N : ℝ) * Δ)) * Real.exp (-((N : ℝ) * (b / 2))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hZ : 0 ≤ (JS : ℝ) * (Real.exp (-((N : ℝ) * Δ)) * Real.exp (-((N : ℝ) * (b / 2)))) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  have hcoef : CX ^ 2 * CΦ ^ 2 / (N : ℝ) ≤ (CX ^ 2 * CΦ ^ 2 + 1) * (N : ℝ)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hN0.le)
  have hE2 : 2 * DGPS.particleEnergy (modelData hL (1 / L)) N f ≤
      2 * ((CX ^ 2 * CΦ ^ 2 + 1) * (N : ℝ)⁻¹ * ((JS : ℝ) *
        (Real.exp (-((N : ℝ) * Δ)) * Real.exp (-((N : ℝ) * (b / 2)))))) := by
    have h1 : DGPS.particleEnergy (modelData hL (1 / L)) N f ≤
        (CX ^ 2 * CΦ ^ 2 + 1) * (N : ℝ)⁻¹ * ((JS : ℝ) *
          (Real.exp (-((N : ℝ) * Δ)) * Real.exp (-((N : ℝ) * (b / 2))))) := by
      refine hE.trans ?_
      rw [hsplit]
      exact mul_le_mul_of_nonneg_right hcoef hZ
    linarith
  have hE0ne : Real.exp (-((N : ℝ) * Δ)) ≠ 0 := (Real.exp_pos _).ne'
  have hNne : (N : ℝ) ≠ 0 := hN0.ne'
  have hΔne : Δ ≠ 0 := hΔpos.ne'
  have h2Cz : 2 * Cz ≠ 0 := mul_ne_zero two_ne_zero hCzne
  have hXY : 2 * ((CX ^ 2 * CΦ ^ 2 + 1) * (N : ℝ)⁻¹ * ((JS : ℝ) *
        (Real.exp (-((N : ℝ) * Δ)) * Real.exp (-((N : ℝ) * (b / 2)))))) /
      ((2 * Cz)⁻¹ * Δ / 4 * (N : ℝ) * Real.exp (-((N : ℝ) * Δ))) =
      8 * (CX ^ 2 * CΦ ^ 2 + 1) * (JS : ℝ) / ((2 * Cz)⁻¹ * Δ) * ((N : ℝ) ^ 2)⁻¹ *
        Real.exp (-((N : ℝ) * (b / 2))) := by
    field_simp
    ring
  refine (DGPS.particleRateSym_le_quotient (modelData hL (1 / L)) N f hfs hEntPos).trans ?_
  unfold DGPS.particleQuotient
  refine (ENNReal.div_le_div (ENNReal.ofReal_le_ofReal hE2) hEnt).trans ?_
  rw [← ENNReal.ofReal_div_of_pos hYpos]
  exact ENNReal.ofReal_le_ofReal (le_of_eq hXY)

end DGPS.Examples.RoughBoundary.Bottleneck
