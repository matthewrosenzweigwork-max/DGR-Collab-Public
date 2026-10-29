import DGPS.Examples.RoughBoundary.BasinSupportRUF044
import DGPS.Examples.RoughBoundary.RemoteBasinRUF045

/-!
# RUF047: rare support entropy lower bound

For the particle law `P_N` of the remote-basin model, a measurable test function `F` with
`F = 1` on the basin set `A_N` (radius `R/8` around `z_*`) and `F = 0` outside the support set
`B_N` (radius `2 (R/4)`) has homogeneous entropy `Ent_{P_N}(F²)` bounded below by
`a_N log(1/p_N)`, where `a_N = ∫ F² dP_N ≥ P_N(A_N)` and `p_N = P_N(B_N)`.
Combining the RUF044 upper bound on `p_N` and the RUF045 lower bound on `P_N(A_N)`, all with
one shared RUF043 witness `(R, η, Φ)`, gives `Ent_{P_N}(F²) ≥ (c_A Δ / 4) N e^{-NΔ}`.
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
open Metric

/-- Pointwise identity behind the tangent bound: for `t ≥ 0`, `a, s > 0`, the defect of the
affine minorant `t log(s/a) + a - s` is exactly the entropy integrand at level `s`. -/
lemma entropyIntegrand_sub_affine_RUF047 {a s t : ℝ} (ha : 0 < a) (hs : 0 < s) (ht : 0 ≤ t) :
    entropyIntegrand a t - (t * Real.log (s / a) + a - s) = entropyIntegrand s t := by
  rcases eq_or_lt_of_le ht with h0 | hpos
  · subst h0
    simp [entropyIntegrand]
  · have hlog : Real.log (t / a) = Real.log (t / s) + Real.log (s / a) := by
      rw [← Real.log_mul (div_pos hpos hs).ne' (div_pos hs ha).ne']
      congr 1
      field_simp
    unfold entropyIntegrand
    rw [hlog]
    ring

/-- The homogeneous entropy integrand of a `[0,1]`-valued function is integrable: on `[0,1]`
it agrees with the continuous function `t log t - t log a - t + a`. -/
lemma integrable_entropyIntegrand_RUF047 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {a : ℝ} (ha : 0 < a) {v : Ω → ℝ} (hvm : Measurable v)
    (hv0 : ∀ x, 0 ≤ v x) (hv1 : ∀ x, v x ≤ 1) :
    Integrable (fun x => entropyIntegrand a (v x)) μ := by
  have hψc : Continuous (fun t : ℝ => t * Real.log t - t * Real.log a - t + a) := by
    have h1 : Continuous fun t : ℝ => t * Real.log t := Real.continuous_mul_log
    have h2 : Continuous fun t : ℝ => t * Real.log a := continuous_id.mul continuous_const
    exact ((h1.sub h2).sub continuous_id).add continuous_const
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hψc.continuousOn
  have hEq : (fun x => entropyIntegrand a (v x)) =
      fun x => v x * Real.log (v x) - v x * Real.log a - v x + a := by
    funext x
    unfold entropyIntegrand
    rcases eq_or_lt_of_le (hv0 x) with h0 | hpos
    · rw [← h0]
      simp
    · rw [Real.log_div hpos.ne' ha.ne']
      ring
  rw [hEq]
  refine Integrable.mono' (integrable_const C) ?_ ?_
  · exact (hψc.measurable.comp hvm).aestronglyMeasurable
  · refine ae_of_all _ fun x => ?_
    exact hC (v x) ⟨hv0 x, hv1 x⟩

/-- Entropy lower bound from a support constraint (the conditioning/convexity step of RUF047).
For a probability measure `μ`, a `[0,1]`-valued measurable `v` vanishing off `B`, with
`a = ∫ v dμ > 0` and `p = μ(B) > 0`: `Ent_μ(v) ≥ a log(1/p)`.

Proof: with `s = a/p`, the tangent bound `entropyIntegrand a t ≥ t log(s/a) + a - s 1_B` holds
pointwise (on `B` it is `entropyIntegrand s t ≥ 0`; off `B` both sides equal `a`). Integrating,
the right side is `a log(s/a) + a - s p = a log(1/p)`. -/
lemma entropy_lower_by_support_RUF047 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : Set Ω} (hBm : MeasurableSet B)
    {v : Ω → ℝ} (hvm : Measurable v) (hv0 : ∀ x, 0 ≤ v x) (hv1 : ∀ x, v x ≤ 1)
    (hvB : ∀ x, x ∉ B → v x = 0) (a : ℝ) (ha_def : ∫ x, v x ∂μ = a) (ha : 0 < a)
    (hp : 0 < μ.real B) :
    ENNReal.ofReal (a * Real.log (1 / μ.real B)) ≤ homogeneousEntropy μ v := by
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = a / μ.real B := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hs_def]; exact div_pos ha hp
  have hsp : s * μ.real B = a := by rw [hs_def]; field_simp
  have hsa : s / a = 1 / μ.real B := by rw [hs_def]; field_simp
  have hI := integrable_entropyIntegrand_RUF047 (μ := μ) ha hvm hv0 hv1
  have hnn : 0 ≤ᵐ[μ] fun x => entropyIntegrand a (v x) :=
    ae_of_all _ fun x => entropyIntegrand_nonneg ha (hv0 x)
  have hvI : Integrable v μ :=
    (integrable_const (1 : ℝ)).mono' hvm.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_of_nonneg (hv0 x)]; exact hv1 x)
  have hind : Integrable (fun x => B.indicator (fun _ => (1 : ℝ)) x) μ :=
    (integrable_const (1 : ℝ)).indicator hBm
  have hgI : Integrable (fun x => v x * Real.log (s / a) +
      (a - s * B.indicator (fun _ => (1 : ℝ)) x)) μ :=
    (hvI.mul_const _).add ((integrable_const a).sub (hind.const_mul s))
  have hpt : ∀ x, v x * Real.log (s / a) + (a - s * B.indicator (fun _ => (1 : ℝ)) x) ≤
      entropyIntegrand a (v x) := by
    intro x
    by_cases hx : x ∈ B
    · have hid := entropyIntegrand_sub_affine_RUF047 ha hs (hv0 x)
      have hnn' := entropyIntegrand_nonneg hs (hv0 x)
      simp only [Set.indicator_of_mem hx]
      linarith
    · have h0 := hvB x hx
      simp [hx, h0, entropyIntegrand]
  have hint_le : ∫ x, (v x * Real.log (s / a) + (a - s * B.indicator (fun _ => (1 : ℝ)) x)) ∂μ
      ≤ ∫ x, entropyIntegrand a (v x) ∂μ :=
    integral_mono hgI hI hpt
  have hcomp : ∫ x, (v x * Real.log (s / a) + (a - s * B.indicator (fun _ => (1 : ℝ)) x)) ∂μ
      = a * Real.log (1 / μ.real B) := by
    have hi1 : Integrable (fun x => v x * Real.log (s / a)) μ := hvI.mul_const _
    have hi2 : Integrable (fun x => a - s * B.indicator (fun _ => (1 : ℝ)) x) μ :=
      (integrable_const a).sub (hind.const_mul s)
    rw [integral_add hi1 hi2, integral_sub (integrable_const a) (hind.const_mul s),
      integral_mul_const, ha_def, integral_const, integral_const_mul,
      integral_indicator_const _ hBm]
    simp only [smul_eq_mul, mul_one, probReal_univ]
    rw [hsa]
    linarith [hsp]
  rw [homogeneousEntropy_of_integral_ne_zero (by rw [ha_def]; exact ha.ne'), ha_def]
  calc ENNReal.ofReal (a * Real.log (1 / μ.real B))
      = ENNReal.ofReal (∫ x, (v x * Real.log (s / a) + (a - s * B.indicator (fun _ => (1 : ℝ)) x)) ∂μ) := by
        rw [hcomp]
    _ ≤ ENNReal.ofReal (∫ x, entropyIntegrand a (v x) ∂μ) := ENNReal.ofReal_le_ofReal hint_le
    _ = ∫⁻ x, ENNReal.ofReal (entropyIntegrand a (v x)) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hI hnn

/-- Upper bound for the basin set `B_N = {smoothMean ∈ ball(z_*, 2(R/4))}`, for the given
RUF043 smooth feature `Φ`: `P_N(B_N) ≤ J_B e^{-NΔ/2}` with `J_B` independent of `N`. -/
lemma basin_upper_fixed_RUF047 {L : ℝ} (hL : 0 < L) (tstar : E2) (R : ℝ) (hR : 0 < R)
    (hΔpos : 0 < remoteLevel_RUF043 L (1 / L) tstar) (Φ : Torus 1 → E2)
    (hBinc : ∀ N : ℕ+, ∀ x : ParticleSpace 1 N,
      ‖smoothMean_RUF043 Φ N x - remoteCentre_RUF043 tstar‖ < 2 * (R / 4) →
        roughMean_RUF043 L (1 / L) N x ∈ compactBall_RUF043 (remoteCentre_RUF043 tstar) (R / 4))
    (hKB : ∀ z ∈ compactBall_RUF043 (remoteCentre_RUF043 tstar) (R / 4),
      remoteLevel_RUF043 L (1 / L) tstar ≤ remotePotential_RUF043 L (1 / L) z) :
    ∃ JB : ℕ, 0 < JB ∧ ∀ N : ℕ+,
      particleLaw (modelData hL (1 / L)) N
          {x | smoothMean_RUF043 Φ N x ∈
            Metric.ball (remoteCentre_RUF043 tstar) (2 * (R / 4))} ≤
        ENNReal.ofReal (JB * Real.exp (-(N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar / 2)) := by
  set zs : E2 := remoteCentre_RUF043 tstar with hzs
  set Δ : ℝ := remoteLevel_RUF043 L (1 / L) tstar with hΔ
  have hκ : 0 < kappa := kappa_pos
  have hKBc : IsCompact (compactBall_RUF043 zs (R / 4)) := compactBall_RUF044 zs (R / 4)
  have hKBne : (compactBall_RUF043 zs (R / 4)).Nonempty := by
    refine ⟨zs, ?_⟩
    show ‖zs - zs‖ ≤ 9 * (R / 4) / 4
    rw [sub_self, norm_zero]
    positivity
  have hδBpos : 0 < Real.sqrt (Δ / kappa) := Real.sqrt_pos.2 (div_pos hΔpos hκ)
  have hδB2 : kappa * Real.sqrt (Δ / kappa) ^ 2 / 2 = Δ / 2 := by
    rw [Real.sq_sqrt (div_pos hΔpos hκ).le]
    field_simp
  obtain ⟨JB, hJB, cB, hcB, hcovB⟩ :=
    exists_finite_net_RUF044 hKBc hKBne hδBpos
  refine ⟨JB, hJB, fun N => ?_⟩
  have hsubB : {x : ParticleSpace 1 N | smoothMean_RUF043 Φ N x ∈
      Metric.ball zs (2 * (R / 4))} ⊆
      {x : ParticleSpace 1 N | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈
        compactBall_RUF043 zs (R / 4)} := by
    intro x hx
    have hx' : smoothMean_RUF043 Φ N x ∈ Metric.ball zs (2 * (R / 4)) := hx
    exact hBinc N x (mem_ball_iff_norm.1 hx')
  have hBound := finite_cover_any_L_RUF044 hL (compactBall_RUF043 zs (R / 4)) hKBc Δ
    (fun z hz => hKB z hz) (Real.sqrt (Δ / kappa)) hδBpos JB cB hcB hcovB N
  have hexp : -(N : ℝ) * (Δ - kappa * Real.sqrt (Δ / kappa) ^ 2 / 2) =
      -(N : ℝ) * Δ / 2 := by
    rw [hδB2]
    ring
  rw [hexp] at hBound
  exact (measure_mono hsubB).trans hBound

/-- Second-moment lower bound on a set where `F = 1`: for a `[0,1]`-valued measurable `F`,
`μ(A) ≤ ∫ F² dμ`. -/
lemma integral_sq_ge_RUF047 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A : Set Ω} (hAm : MeasurableSet A) {F : Ω → ℝ}
    (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1) (hFA : ∀ x ∈ A, F x = 1) :
    μ.real A ≤ ∫ x, F x ^ 2 ∂μ := by
  have hI : Integrable (fun x => F x ^ 2) μ :=
    (integrable_const (1 : ℝ)).mono' (hFm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_one₀ (hF0 x) (hF1 x))
  have hind : Integrable (A.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hAm
  calc μ.real A = ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂μ := by
        rw [integral_indicator_const _ hAm]
        simp
    _ ≤ ∫ x, F x ^ 2 ∂μ := by
        refine integral_mono hind hI fun x => ?_
        by_cases hx : x ∈ A
        · simp [hx, hFA x hx]
        · simp [hx]
          try positivity

/-- The basin lower bound of RUF045 for a fixed RUF043 witness `(R, η, Φ)`: a uniform normalizer
bound `1 ≤ Z_N ≤ C_Z` and `P_N(A_N) ≥ (2 C_Z)⁻¹ e^{-NΔ}` for `N ≥ N_A`, where
`A_N = {smoothMean ∈ ball(z_*, R/8)}`. The proof body is that of
`remote_basin_exponential_lower_bound`, with the witness supplied as hypotheses. -/
lemma remote_basin_lower_fixed_RUF047 {L : ℝ} (hL : 0 < L)
    (hcert : RoughLandscapeCertificate (Ufeat L (1 / L)))
    (tstar : EuclideanSpace ℝ (Fin 2))
    (hcrit : fderiv ℝ (featurePotential kappa0 (Ufeat L (1 / L))) tstar = 0)
    (R η : ℝ) (hRpos : 0 < R) (hηR : η < (R / 4) / 4)
    (Φ : Torus 1 → EuclideanSpace ℝ (Fin 2)) (hΦcd : ContDiff ℝ ∞ (Φ ∘ DGPS.torusLift))
    (hΦapp : ∀ y, ‖Φ y - Ufeat L (1 / L) y‖ ≤ η) :
    ∃ C_Z : ℝ, 0 < C_Z ∧
      (∀ N : ℕ+, (1 ≤ (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N) ∧
        (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N) ≤ C_Z)) ∧
      ∃ N_A : ℕ, ∀ N : ℕ+, N_A ≤ (N : ℕ) →
        ENNReal.ofReal ((2 * C_Z)⁻¹ *
            Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar))) ≤
          particleLaw (modelData hL (1 / L)) N
            {x | smoothMean_RUF043 Φ N x ∈ Metric.ball (remoteCentre_RUF043 tstar) ((R / 4) / 2)} := by
  obtain ⟨a, r₁, R₀, b₀, ha, hr₁, hloc, hR, hb₀, hmin⟩ := normalizer_data_RUF045 hL hcert
  have hk : (0 : ℝ) < kappa := kappa_pos
  have hself := critical_selfconsistent hL (1 / L) tstar hcrit
  have hν : IsProbabilityMeasure (gibbsMeasure L (1 / L) tstar) :=
    isProbabilityMeasure_gibbs hL (1 / L) tstar
  -- self-consistency: the Gibbs mean at `t_*` is the remote centre `z_*`
  have hcentre : meanFeature L (1 / L) (gibbsMeasure L (1 / L) tstar) =
      remoteCentre_RUF043 tstar := by
    have h1 : kappa • remoteCentre_RUF043 tstar =
        kappa • meanFeature L (1 / L) (gibbsMeasure L (1 / L) tstar) := by
      rw [kappa_smul_centre_RUF043]
      exact hself
    exact (smul_right_injective _ hk.ne' h1).symm
  have hU' : ∫ y, Ufeat L (1 / L) y ∂(gibbsMeasure L (1 / L) tstar) =
      remoteCentre_RUF043 tstar := hcentre
  have hUint : Integrable (Ufeat L (1 / L)) (gibbsMeasure L (1 / L) tstar) :=
    integrable_U hL (1 / L) _
  have hΦcont : Continuous Φ := DGPS.continuous_of_comp_torusLift hΦcd.continuous
  obtain ⟨C₀, hC₀⟩ := isCompact_univ.exists_bound_of_continuousOn hΦcont.continuousOn
  have hC0 : (0 : ℝ) ≤ max C₀ 0 := le_max_right _ _
  have hC : ∀ y, ‖Φ y‖ ≤ max C₀ 0 := fun y =>
    (hC₀ y (Set.mem_univ y)).trans (le_max_left _ _)
  have hΦint : Integrable Φ (gibbsMeasure L (1 / L) tstar) :=
    Integrable.mono' (integrable_const (max C₀ 0)) hΦcont.aestronglyMeasurable (ae_of_all _ hC)
  have hmeanΦ : ‖(∫ y, Φ y ∂(gibbsMeasure L (1 / L) tstar)) - remoteCentre_RUF043 tstar‖ <
      (R / 4) / 4 := by
    have hdiff : (∫ y, Φ y ∂(gibbsMeasure L (1 / L) tstar)) - remoteCentre_RUF043 tstar =
        ∫ y, (Φ y - Ufeat L (1 / L) y) ∂(gibbsMeasure L (1 / L) tstar) := by
      rw [integral_sub hΦint hUint, hU']
    have hb : ‖∫ y, (Φ y - Ufeat L (1 / L) y) ∂(gibbsMeasure L (1 / L) tstar)‖ ≤ η := by
      have h0 := norm_integral_le_of_norm_le_const (μ := gibbsMeasure L (1 / L) tstar)
        (f := fun y => Φ y - Ufeat L (1 / L) y) (C := η) (ae_of_all _ hΦapp)
      simp only [probReal_univ, mul_one] at h0
      exact h0
    rw [hdiff]
    exact lt_of_le_of_lt hb hηR
  have hr4 : (0 : ℝ) < R / 4 := by linarith
  -- the uniform normalizer constant
  obtain ⟨Cz, hCzdef⟩ : ∃ Cz : ℝ,
      Cz = (2 * kappa0 * a)⁻¹ + 2 + R₀ ^ 2 / (2 * kappa0 * Real.exp 1 * b₀) := ⟨_, rfl⟩
  have hZ : ∀ N : ℕ+,
      1 ≤ (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N) ∧
      (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N) ≤ Cz :=
    fun N => ⟨one_le_normalizer_RUF042 hL N, by
      rw [hCzdef]; exact particle_normalizer_upper_RUF045 hL ha hb₀ hR hloc hmin N⟩
  have hCzpos : 0 < Cz := lt_of_lt_of_le one_pos ((hZ 1).1.trans (hZ 1).2)
  refine ⟨Cz, hCzpos, fun N => hZ N, ⌈128 * (max C₀ 0) ^ 2 / (R / 4) ^ 2⌉₊, ?_⟩
  intro N hNA
  have hNpos : 0 < (N : ℕ) := N.pos
  have hbig : 128 * (max C₀ 0) ^ 2 / (R / 4) ^ 2 ≤ ((N : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hNA)
  have hbasin := basin_concentration_RUF045 (gibbsMeasure L (1 / L) tstar) Φ hΦcont.measurable
    hC0 hC hr4 hmeanΦ hNpos hbig
  have hset : {x : ParticleSpace 1 N | smoothMean_RUF043 Φ N x ∈
      Metric.ball (remoteCentre_RUF043 tstar) ((R / 4) / 2)} =
      {x : ParticleSpace 1 N | ‖((N : ℝ)⁻¹ • ∑ i, Φ (x i)) - remoteCentre_RUF043 tstar‖ <
        (R / 4) / 2} := by
    ext x
    simp [smoothMean_RUF043, Metric.mem_ball, dist_eq_norm]
  rw [hset]
  -- tilt identity (RUF044), with `κ • z_* = t_*` in the Gibbs parameter
  have hT := tilt_identity_RUF044 hL N (remoteCentre_RUF043 tstar)
  have hν' : gibbsMeasure L (1 / L) (kappa • remoteCentre_RUF043 tstar) =
      gibbsMeasure L (1 / L) tstar := by
    rw [kappa_smul_centre_RUF043]
  have hD := hT.2.1
  rw [hν'] at hD
  -- pointwise lower bound of the tilted density: the square term is nonnegative
  have hpt : ∀ x : ParticleSpace 1 N,
      -((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar) ≤
        (N : ℝ) * (kappa / 2 * ‖(N : ℝ)⁻¹ • featureSum L (1 / L) N x -
            remoteCentre_RUF043 tstar‖ ^ 2 -
          featurePotential kappa0 (Ufeat L (1 / L)) (kappa • remoteCentre_RUF043 tstar)) := by
    intro x
    have hA : 0 ≤ kappa / 2 * ‖(N : ℝ)⁻¹ • featureSum L (1 / L) N x -
        remoteCentre_RUF043 tstar‖ ^ 2 :=
      mul_nonneg (by linarith [kappa_pos]) (sq_nonneg _)
    have hNn : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have hΔ : remoteLevel_RUF043 L (1 / L) tstar =
        featurePotential kappa0 (Ufeat L (1 / L)) (kappa • remoteCentre_RUF043 tstar) := rfl
    rw [hΔ, mul_sub]
    linarith [mul_nonneg hNn hA]
  -- the basin set and the Gibbs product measure
  set P := Measure.pi fun _ : Fin (N : ℕ) => gibbsMeasure L (1 / L) tstar with hPdef
  set S : Set (ParticleSpace 1 N) := {x : ParticleSpace 1 N |
      ‖((N : ℝ)⁻¹ • ∑ i, Φ (x i)) - remoteCentre_RUF043 tstar‖ < (R / 4) / 2} with hSdef
  have hcontS : Continuous (fun x : ParticleSpace 1 N =>
      ‖((N : ℝ)⁻¹ • ∑ i, Φ (x i)) - remoteCentre_RUF043 tstar‖) := by
    fun_prop
  have hSm : MeasurableSet S :=
    measurableSet_lt hcontS.measurable measurable_const
  have h1 := congrArg (fun μ : Measure (ParticleSpace 1 N) => μ S) hD
  simp only [withDensity_apply _ hSm] at h1
  have hlow : ENNReal.ofReal (Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar))) * P S ≤
      ∫⁻ x in S, ENNReal.ofReal (Real.exp (roughB L (1 / L) N x)) ∂particleHaar 1 N := by
    refine le_of_le_of_eq ?_ h1.symm
    rw [← setLIntegral_const]
    exact setLIntegral_mono' hSm fun x _ =>
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hpt x))
  have hZpos : 0 < (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N) :=
    lt_of_lt_of_le one_pos (hZ N).1
  -- particle law on the basin: the normalizer factors out
  have hLaw : particleLaw (modelData hL (1 / L)) N S =
      ENNReal.ofReal (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N)⁻¹ *
        ∫⁻ x in S, ENNReal.ofReal (Real.exp (roughB L (1 / L) N x)) ∂particleHaar 1 N := by
    rw [hT.2.2, withDensity_apply _ hSm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun x => ENNReal.ofReal_mul (inv_nonneg.mpr hZpos.le)
  have hp : (1 / 2 : ℝ) ≤ P.real S := hbasin
  have hZi : Cz⁻¹ ≤ (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N)⁻¹ :=
    inv_anti₀ hZpos (hZ N).2
  have hep : 0 ≤ Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar)) := (Real.exp_pos _).le
  have hpoint : (2 * Cz)⁻¹ * Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar)) ≤
      (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N)⁻¹ *
        (Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar)) * P.real S) := by
    have h2 : (2 * Cz)⁻¹ * Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar)) =
        Cz⁻¹ * (Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar)) * (1 / 2)) := by
      rw [mul_inv]; ring
    rw [h2]
    exact mul_le_mul hZi (mul_le_mul_of_nonneg_left hp hep)
      (mul_nonneg hep (by norm_num)) (inv_nonneg.mpr hZpos.le)
  have hPS : P S = ENNReal.ofReal (P.real S) := by
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hLaw]
  calc ENNReal.ofReal ((2 * Cz)⁻¹ *
        Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar)))
      ≤ ENNReal.ofReal ((∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N)⁻¹ *
          (Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar)) * P.real S)) :=
        ENNReal.ofReal_le_ofReal hpoint
    _ = ENNReal.ofReal (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N)⁻¹ *
          (ENNReal.ofReal (Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar))) * P S) := by
        rw [hPS, ENNReal.ofReal_mul (inv_nonneg.mpr hZpos.le),
          ENNReal.ofReal_mul hep]
    _ ≤ ENNReal.ofReal (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N)⁻¹ *
          ∫⁻ x in S, ENNReal.ofReal (Real.exp (roughB L (1 / L) N x)) ∂particleHaar 1 N :=
        mul_le_mul_of_nonneg_left hlow bot_le

/-- RUF047, the rare support entropy lower bound.

For the remote-basin particle law `P_N` with a shared RUF043 witness `(R, η, Φ)`, every measurable
`[0,1]`-valued test function `F` with `F = 1` on `A_N = {smoothMean ∈ ball(z_*, R/8)}` and
`F = 0` off `B_N = {smoothMean ∈ ball(z_*, 2(R/4))}` satisfies, for all large `N`,
`Ent_{P_N}(F²) ≥ c N e^{-NΔ}` with `c = (2 C_Z)⁻¹ Δ / 4 > 0`. -/
theorem rare_support_entropy_lower_bound {L : ℝ} (hL : 0 < L)
    (hcert : RoughLandscapeCertificate (Ufeat L (1 / L)))
    (tstar : EuclideanSpace ℝ (Fin 2)) (r₀ lam : ℝ) (hr₀ : 0 < r₀) (hlam : 0 < lam)
    (hcrit : fderiv ℝ (featurePotential kappa0 (Ufeat L (1 / L))) tstar = 0)
    (h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∉ closedBall tstar r₀)
    (hH : ∀ x ∈ closedBall tstar r₀, ∀ v : EuclideanSpace ℝ (Fin 2),
      lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (featurePotential kappa0 (Ufeat L (1 / L)))) x v v) :
    ∃ R : ℝ, 0 < R ∧
      ∃ η : ℝ, 0 < η ∧ η < (R / 4) / 4 ∧
      ∃ Φ : Torus 1 → EuclideanSpace ℝ (Fin 2), ContDiff ℝ ∞ (Φ ∘ DGPS.torusLift) ∧
        (∀ y, ‖Φ y - Ufeat L (1 / L) y‖ ≤ η) ∧
      ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ+, N0 ≤ (N : ℕ) →
        ∀ F : ParticleSpace 1 N → ℝ, Measurable F → (∀ x, 0 ≤ F x) → (∀ x, F x ≤ 1) →
          (∀ x, smoothMean_RUF043 Φ N x ∈ Metric.ball (remoteCentre_RUF043 tstar) ((R / 4) / 2) →
            F x = 1) →
          (∀ x, smoothMean_RUF043 Φ N x ∉ Metric.ball (remoteCentre_RUF043 tstar) (2 * (R / 4)) →
            F x = 0) →
          ENNReal.ofReal (c * (N : ℝ) *
              Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar))) ≤
            homogeneousEntropy (particleLaw (modelData hL (1 / L)) N) (fun x => F x ^ 2) := by
  obtain ⟨R, hR, hΔpos, -, -, -, η, hη, hηr, Φ, hΦcd, hΦapp, -, -, -, -, -, -, -, -, hBinc, -,
    hKB, -⟩ :=
    fixed_smooth_bottleneck_feature_and_compatible_neighborhoods hL (1 / L) hcert tstar r₀ lam
      hr₀ hlam hcrit h0 hH
  obtain ⟨Cz, hCz, -, NA, hA⟩ :=
    remote_basin_lower_fixed_RUF047 hL hcert tstar hcrit R η hR hηr Φ hΦcd hΦapp
  obtain ⟨JB, hJB, hB⟩ := basin_upper_fixed_RUF047 hL tstar R hR hΔpos Φ hBinc hKB
  have hΦcont : Continuous Φ := DGPS.continuous_of_comp_torusLift hΦcd.continuous
  have hJBpos : (0 : ℝ) < JB := Nat.cast_pos.mpr hJB
  set Δ : ℝ := remoteLevel_RUF043 L (1 / L) tstar with hΔ
  refine ⟨R, hR, η, hη, hηr, Φ, hΦcd, hΦapp, (2 * Cz)⁻¹ * Δ / 4,
    div_pos (mul_pos (inv_pos.mpr (by linarith)) hΔpos) (by norm_num),
    max NA ⌈4 * Real.log JB / Δ⌉₊, ?_⟩
  intro N hN F hFm hF0 hF1 hFA hFB
  have hNA : NA ≤ (N : ℕ) := le_trans (le_max_left _ _) hN
  have hNJ : ⌈4 * Real.log JB / Δ⌉₊ ≤ (N : ℕ) := le_trans (le_max_right _ _) hN
  have hNΔ : 4 * Real.log JB ≤ (N : ℝ) * Δ :=
    (div_le_iff₀ hΔpos).1 ((Nat.le_ceil _).trans (Nat.cast_le.mpr hNJ))
  have hlogJB : Real.log JB ≤ (N : ℝ) * Δ / 4 := by linarith
  have : IsProbabilityMeasure (particleLaw (modelData hL (1 / L)) N) := inferInstance
  set μ := particleLaw (modelData hL (1 / L)) N with hμ
  set A : Set (ParticleSpace 1 N) := {x | smoothMean_RUF043 Φ N x ∈
    Metric.ball (remoteCentre_RUF043 tstar) ((R / 4) / 2)} with hA_def
  set B : Set (ParticleSpace 1 N) := {x | smoothMean_RUF043 Φ N x ∈
    Metric.ball (remoteCentre_RUF043 tstar) (2 * (R / 4))} with hB_def
  have hcont : Continuous (fun x : ParticleSpace 1 N => smoothMean_RUF043 Φ N x) := by
    have hsum : Continuous (fun x : ParticleSpace 1 N => ∑ i, Φ (x i)) :=
      continuous_finsetSum _ fun i _ => hΦcont.comp (continuous_apply i)
    unfold smoothMean_RUF043
    exact hsum.const_smul ((N : ℝ)⁻¹)
  have hAm : MeasurableSet A := hcont.measurable Metric.isOpen_ball.measurableSet
  have hBm : MeasurableSet B := hcont.measurable Metric.isOpen_ball.measurableSet
  have hAB : A ⊆ B := fun x hx => Metric.ball_subset_ball (by linarith) hx
  have hAr : (2 * Cz)⁻¹ * Real.exp (-((N : ℝ) * Δ)) ≤ μ.real A :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 (hA N hNA)
  have hApos : 0 < μ.real A :=
    lt_of_lt_of_le (mul_pos (inv_pos.mpr (by linarith)) (Real.exp_pos _)) hAr
  have hBr : μ.real B ≤ (JB : ℝ) * Real.exp (-(N : ℝ) * Δ / 2) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hB N)
    rw [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)] at h
    exact h
  have hBpos : 0 < μ.real B := lt_of_lt_of_le hApos (measureReal_mono hAB)
  have hlogB : Real.log (μ.real B) ≤ Real.log JB + (-(N : ℝ) * Δ / 2) := by
    have h := Real.log_le_log hBpos hBr
    rwa [Real.log_mul hJBpos.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  have hL1 : (N : ℝ) * Δ / 4 ≤ Real.log (1 / μ.real B) := by
    rw [one_div, Real.log_inv]
    linarith
  have ha_pos : 0 < ∫ x, F x ^ 2 ∂μ :=
    lt_of_lt_of_le hApos (integral_sq_ge_RUF047 hAm hFm hF0 hF1 (fun x hx => hFA x hx))
  have hvm : Measurable (fun x => F x ^ 2) := hFm.pow_const 2
  have hvB : ∀ x, x ∉ B → F x ^ 2 = 0 := fun x hx => by
    rw [hFB x hx]
    norm_num
  have hEnt := entropy_lower_by_support_RUF047 hBm hvm (fun x => sq_nonneg (F x))
    (fun x => pow_le_one₀ (hF0 x) (hF1 x)) hvB _ rfl ha_pos hBpos
  have hkey : (2 * Cz)⁻¹ * Δ / 4 * (N : ℝ) * Real.exp (-((N : ℝ) * Δ)) ≤
      (∫ x, F x ^ 2 ∂μ) * Real.log (1 / μ.real B) := by
    have hK : (2 * Cz)⁻¹ * Real.exp (-((N : ℝ) * Δ)) ≤ ∫ x, F x ^ 2 ∂μ :=
      hAr.trans (integral_sq_ge_RUF047 hAm hFm hF0 hF1 (fun x hx => hFA x hx))
    have hNn : (0 : ℝ) ≤ (N : ℝ) * Δ / 4 :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) hΔpos.le) (by norm_num)
    have hmul := mul_le_mul hK hL1 hNn ha_pos.le
    calc (2 * Cz)⁻¹ * Δ / 4 * (N : ℝ) * Real.exp (-((N : ℝ) * Δ))
        = (2 * Cz)⁻¹ * Real.exp (-((N : ℝ) * Δ)) * ((N : ℝ) * Δ / 4) := by ring
      _ ≤ _ := hmul
  exact (ENNReal.ofReal_le_ofReal hkey).trans hEnt

end DGPS.Examples.RoughBoundary.Bottleneck
