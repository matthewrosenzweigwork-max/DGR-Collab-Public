import DGPS.Examples.RoughBoundary.BasinSupportRUF044
import DGPS.FiniteN.Tools.PositiveRate

set_option maxHeartbeats 2000000

open MeasureTheory
open scoped ENNReal ContDiff

namespace DGPS.Examples.RoughBoundary.Bottleneck

open DGPS.Examples.RoughBoundary.Feature
open DGPS.Examples.RoughBoundary.FreeEnergy
open DGPS.Examples.RoughBoundary.Model
open DGPS.Examples.RoughBoundary.Particle
open DGPS.Examples.RoughBoundary.Semicontinuity
open DGPS.Examples.RoughBoundary.Landscape

/-! ### RUF046 helpers

`F_N = χ(Y_N)` with `Y_N = N⁻¹ Σ_i Φ(x_i)` is a smooth periodic particle function, it is
permutation invariant, its partial derivatives are localized by `supp ∇χ` and bounded by
`CX CΦ / N`, and its Dirichlet energy is controlled by the annular probability bound. -/

lemma isSmoothPeriodicParticle_RUF046 {N : ℕ+} (Φ : Torus 1 → E2)
    (hΦ : ContDiff ℝ ∞ (Φ ∘ DGPS.torusLift)) (χ : E2 → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    DGPS.IsSmoothPeriodicParticle
      (fun x : DGPS.ParticleSpace 1 N => χ (smoothMean_RUF043 Φ N x)) := by
  have hcomp : ((fun x : DGPS.ParticleSpace 1 N => χ (smoothMean_RUF043 Φ N x)) ∘
      DGPS.particleLift) = fun y : Fin N → Fin 1 → ℝ =>
        χ ((N : ℝ)⁻¹ • ∑ k, (Φ ∘ DGPS.torusLift) (y k)) := rfl
  unfold DGPS.IsSmoothPeriodicParticle
  rw [hcomp]
  have hsumC : ContDiff ℝ ∞ (fun y : Fin N → Fin 1 → ℝ => ∑ k, (Φ ∘ DGPS.torusLift) (y k)) :=
    ContDiff.sum fun k _ => hΦ.comp (contDiff_apply ℝ (Fin 1 → ℝ) k)
  exact hχ.comp (hsumC.const_smul ((N : ℝ)⁻¹))

lemma measurable_smoothMean_RUF046 {N : ℕ+} (Φ : Torus 1 → E2)
    (hΦ : ContDiff ℝ ∞ (Φ ∘ DGPS.torusLift)) :
    Measurable (smoothMean_RUF043 Φ N) := by
  have hΦeq : Φ = (Φ ∘ DGPS.torusLift) ∘ SharpLSI.secT := by
    funext y
    simp [Function.comp_apply, DGPS.torusLift, SharpLSI.liftT_secT]
  have hΦm : Measurable Φ := by
    rw [hΦeq]
    exact hΦ.continuous.measurable.comp SharpLSI.measurable_secT
  unfold smoothMean_RUF043
  exact (Finset.measurable_sum _ fun k _ => hΦm.comp (measurable_pi_apply k)).const_smul ((N : ℝ)⁻¹)

lemma fderiv_bound_RUF046 {χ : E2 → ℝ} (hχ : ContDiff ℝ ∞ χ) {zs : E2} {r : ℝ} (hr : 0 ≤ r)
    (hsupp : Function.support (fderiv ℝ χ) ⊆ transitionAnnulus_RUF043 zs r) :
    ∃ CX : ℝ, 0 ≤ CX ∧ ∀ y, ‖fderiv ℝ χ y‖ ≤ CX := by
  have hcont : ContinuousOn (fderiv ℝ χ) (compactAnnulus_RUF043 zs r) :=
    (hχ.continuous_fderiv (by simp)).continuousOn
  obtain ⟨C, hC⟩ := (compactAnnulus_RUF044 zs r).exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : y ∈ transitionAnnulus_RUF043 zs r
  · have hyc : y ∈ compactAnnulus_RUF043 zs r := by
      have hy' : r ≤ ‖y - zs‖ ∧ ‖y - zs‖ ≤ 2 * r := hy
      show 3 * r / 4 ≤ ‖y - zs‖ ∧ ‖y - zs‖ ≤ 9 * r / 4
      constructor <;> linarith [hy'.1, hy'.2]
    exact (hC y hyc).trans (le_max_left _ _)
  · have h0 : fderiv ℝ χ y = 0 := by
      by_contra h
      exact hy (hsupp (Function.mem_support.2 h))
    rw [h0, norm_zero]
    exact le_max_right _ _

lemma partial_bound_RUF046 {g : (Fin 1 → ℝ) → E2} (hg : ContDiff ℝ ∞ g) :
    ∃ CΦ : ℝ, 0 ≤ CΦ ∧ ∀ t ∈ Set.Icc (0 : Fin 1 → ℝ) 1, ‖fderiv ℝ g t‖ ≤ CΦ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : Fin 1 → ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hg.continuous_fderiv (by simp)).continuousOn
  exact ⟨max C 0, le_max_right _ _, fun t ht => (hC t ht).trans (le_max_left _ _)⟩

lemma particlePartial_RUF046 {N : ℕ+} (Φ : Torus 1 → E2)
    (hΦ : ContDiff ℝ ∞ (Φ ∘ DGPS.torusLift)) (χ : E2 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (x : DGPS.ParticleSpace 1 N) (i : Fin N) :
    DGPS.particlePartial i 0 (fun x : DGPS.ParticleSpace 1 N => χ (smoothMean_RUF043 Φ N x)) x =
      fderiv ℝ χ (smoothMean_RUF043 Φ N x)
        ((N : ℝ)⁻¹ • fderiv ℝ (Φ ∘ DGPS.torusLift) (SharpLSI.secT (x i))
          (Pi.single (0 : Fin 1) (1 : ℝ))) := by
  have hgd : ∀ t : Fin 1 → ℝ, HasFDerivAt (Φ ∘ DGPS.torusLift)
      (fderiv ℝ (Φ ∘ DGPS.torusLift) t) t := fun t =>
    ((hΦ.differentiable (by simp)) t).hasFDerivAt
  have hχd : ∀ y : E2, HasFDerivAt χ (fderiv ℝ χ y) y := fun y =>
    ((hχ.differentiable (by simp)) y).hasFDerivAt
  set y0 : Fin N → Fin 1 → ℝ := fun k => SharpLSI.secT (x k) with hy0
  have hY : (N : ℝ)⁻¹ • ∑ k, (Φ ∘ DGPS.torusLift) (y0 k) = smoothMean_RUF043 Φ N x := by
    simp [hy0, smoothMean_RUF043, Function.comp_apply, DGPS.torusLift, SharpLSI.liftT_secT]
  have hk : ∀ k : Fin N, HasFDerivAt ((Φ ∘ DGPS.torusLift) ∘ fun y : Fin N → Fin 1 → ℝ => y k)
      ((fderiv ℝ (Φ ∘ DGPS.torusLift) (y0 k)).comp (ContinuousLinearMap.proj k)) y0 :=
    fun k => HasFDerivAt.comp y0 (hgd (y0 k)) (hasFDerivAt_apply k y0)
  have hsumd : HasFDerivAt (fun y : Fin N → Fin 1 → ℝ =>
      ∑ k, (Φ ∘ DGPS.torusLift) (y k))
      (∑ k, (fderiv ℝ (Φ ∘ DGPS.torusLift) (y0 k)).comp
        (ContinuousLinearMap.proj k)) y0 :=
    HasFDerivAt.fun_sum fun k _ => hk k
  have hinner : HasFDerivAt (fun y : Fin N → Fin 1 → ℝ =>
      (N : ℝ)⁻¹ • ∑ k, (Φ ∘ DGPS.torusLift) (y k))
      ((N : ℝ)⁻¹ • ∑ k, (fderiv ℝ (Φ ∘ DGPS.torusLift) (y0 k)).comp
        (ContinuousLinearMap.proj k)) y0 :=
    hsumd.const_smul ((N : ℝ)⁻¹)
  have hχd' : HasFDerivAt χ (fderiv ℝ χ (smoothMean_RUF043 Φ N x))
      ((N : ℝ)⁻¹ • ∑ k, (Φ ∘ DGPS.torusLift) (y0 k)) := by
    rw [hY]
    exact hχd _
  have hcomp := hχd'.comp y0 hinner
  have key : fderiv ℝ (fun y : Fin N → Fin 1 → ℝ =>
      χ ((N : ℝ)⁻¹ • ∑ k, (Φ ∘ DGPS.torusLift) (y k))) y0 =
      (fderiv ℝ χ (smoothMean_RUF043 Φ N x)).comp
        ((N : ℝ)⁻¹ • ∑ k, (fderiv ℝ (Φ ∘ DGPS.torusLift) (y0 k)).comp
          (ContinuousLinearMap.proj k)) :=
    hcomp.fderiv
  have hsum : ∑ k, (fderiv ℝ (Φ ∘ DGPS.torusLift) (y0 k))
      ((Pi.single i (Pi.single (0 : Fin 1) (1 : ℝ)) : Fin N → Fin 1 → ℝ) k) =
      fderiv ℝ (Φ ∘ DGPS.torusLift) (SharpLSI.secT (x i)) (Pi.single (0 : Fin 1) (1 : ℝ)) := by
    rw [Finset.sum_eq_single i]
    · simp [hy0]
    · intro k _ hk
      simp [hk]
    · intro h
      exact absurd (Finset.mem_univ i) h
  show fderiv ℝ (fun y : Fin N → Fin 1 → ℝ =>
      χ ((N : ℝ)⁻¹ • ∑ k, (Φ ∘ DGPS.torusLift) (y k))) y0
      (Pi.single i (Pi.single (0 : Fin 1) (1 : ℝ))) = _
  rw [key]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    sum_apply, ContinuousLinearMap.proj_apply]
  rw [hsum]

lemma pointwise_RUF046 {N : ℕ+} (Φ : Torus 1 → E2)
    (hΦ : ContDiff ℝ ∞ (Φ ∘ DGPS.torusLift)) (χ : E2 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    {T : Set E2} (hsupp : Function.support (fderiv ℝ χ) ⊆ T) {CX CΦ : ℝ}
    (hCX0 : 0 ≤ CX) (hCX : ∀ y, ‖fderiv ℝ χ y‖ ≤ CX) (hCΦ0 : 0 ≤ CΦ)
    (hCΦ : ∀ t ∈ Set.Icc (0 : Fin 1 → ℝ) 1, ‖fderiv ℝ (Φ ∘ DGPS.torusLift) t‖ ≤ CΦ)
    (x : DGPS.ParticleSpace 1 N) :
    ∑ i, ∑ j, DGPS.particlePartial i j
        (fun x : DGPS.ParticleSpace 1 N => χ (smoothMean_RUF043 Φ N x)) x ^ 2 ≤
      Set.indicator {x : DGPS.ParticleSpace 1 N | smoothMean_RUF043 Φ N x ∈ T}
        (fun _ => CX ^ 2 * CΦ ^ 2 / (N : ℝ)) x := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  simp only [Fin.sum_univ_one]
  by_cases hY : smoothMean_RUF043 Φ N x ∈ T
  · rw [Set.indicator_of_mem (show x ∈ {x : DGPS.ParticleSpace 1 N |
      smoothMean_RUF043 Φ N x ∈ T} from hY)]
    have hterm : ∀ i : Fin N,
        DGPS.particlePartial i 0 (fun x : DGPS.ParticleSpace 1 N =>
          χ (smoothMean_RUF043 Φ N x)) x ^ 2 ≤ (CX * ((N : ℝ)⁻¹ * CΦ)) ^ 2 := by
      intro i
      rw [particlePartial_RUF046 Φ hΦ χ hχ x i]
      set w := fderiv ℝ (Φ ∘ DGPS.torusLift) (SharpLSI.secT (x i))
        (Pi.single (0 : Fin 1) (1 : ℝ)) with hw
      have he : ‖(Pi.single (0 : Fin 1) (1 : ℝ) : Fin 1 → ℝ)‖ ≤ 1 := by
        refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
        rw [Pi.single_apply]
        split_ifs <;> simp
      have hw1 : ‖w‖ ≤ CΦ := by
        have h1 := (fderiv ℝ (Φ ∘ DGPS.torusLift) (SharpLSI.secT (x i))).le_opNorm
          (Pi.single (0 : Fin 1) (1 : ℝ))
        have h2 := hCΦ _ (DGPS.secT_mem_Icc (x i))
        calc ‖w‖ ≤ ‖fderiv ℝ (Φ ∘ DGPS.torusLift) (SharpLSI.secT (x i))‖ *
              ‖(Pi.single (0 : Fin 1) (1 : ℝ) : Fin 1 → ℝ)‖ := h1
          _ ≤ CΦ * 1 := mul_le_mul h2 he (norm_nonneg _) hCΦ0
          _ = CΦ := mul_one _
      have hfin : ‖fderiv ℝ χ (smoothMean_RUF043 Φ N x) ((N : ℝ)⁻¹ • w)‖ ≤
          CX * ((N : ℝ)⁻¹ * CΦ) := by
        have h1 := (fderiv ℝ χ (smoothMean_RUF043 Φ N x)).le_opNorm ((N : ℝ)⁻¹ • w)
        have h2 : ‖(N : ℝ)⁻¹ • w‖ ≤ (N : ℝ)⁻¹ * CΦ := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hNpos.le)]
          exact mul_le_mul_of_nonneg_left hw1 (inv_nonneg.2 hNpos.le)
        calc ‖fderiv ℝ χ (smoothMean_RUF043 Φ N x) ((N : ℝ)⁻¹ • w)‖
            ≤ ‖fderiv ℝ χ (smoothMean_RUF043 Φ N x)‖ * ‖(N : ℝ)⁻¹ • w‖ := h1
          _ ≤ CX * ((N : ℝ)⁻¹ * CΦ) := mul_le_mul (hCX _) h2 (norm_nonneg _) hCX0
      have habs : |fderiv ℝ χ (smoothMean_RUF043 Φ N x) ((N : ℝ)⁻¹ • w)| ≤
          CX * ((N : ℝ)⁻¹ * CΦ) := by
        rw [← Real.norm_eq_abs]
        exact hfin
      exact sq_le_sq' (abs_le.1 habs).1 (abs_le.1 habs).2
    calc ∑ i : Fin N, DGPS.particlePartial i 0
          (fun x : DGPS.ParticleSpace 1 N => χ (smoothMean_RUF043 Φ N x)) x ^ 2
        ≤ ∑ _i : Fin N, (CX * ((N : ℝ)⁻¹ * CΦ)) ^ 2 := Finset.sum_le_sum fun i _ => hterm i
      _ = CX ^ 2 * CΦ ^ 2 / (N : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  · have hz : fderiv ℝ χ (smoothMean_RUF043 Φ N x) = 0 := by
      by_contra h
      exact hY (hsupp (Function.mem_support.2 h))
    have hzero : ∀ i : Fin N, DGPS.particlePartial i 0
        (fun x : DGPS.ParticleSpace 1 N => χ (smoothMean_RUF043 Φ N x)) x = 0 := by
      intro i
      rw [particlePartial_RUF046 Φ hΦ χ hχ x i, hz, zero_apply]
    rw [Set.indicator_of_notMem (show x ∉ {x : DGPS.ParticleSpace 1 N |
      smoothMean_RUF043 Φ N x ∈ T} from hY)]
    simp [hzero]

/-- Energy estimate for a smooth function whose squared partial derivatives are bounded by a
constant on a set `S` of small `P_N`-probability. -/
lemma energy_le_RUF046 {A : InteractionData 1} {N : ℕ+} (F : DGPS.ParticleSpace 1 N → ℝ)
    (hF : DGPS.IsSmoothPeriodicParticle F) (S : Set (DGPS.ParticleSpace 1 N))
    (hS : MeasurableSet S) {c p : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p)
    (hpt : ∀ x, ∑ i, ∑ j, DGPS.particlePartial i j F x ^ 2 ≤ S.indicator (fun _ => c) x)
    (hprob : DGPS.particleLaw A N S ≤ ENNReal.ofReal p) :
    ∃ f : DGPS.ParticleH1 A N, f.1 = F ∧ DGPS.particleEnergy A N f ≤ c * p := by
  have hg := (DGPS.isParticleWeakGradient_iff A N F _).2
    (DGPS.FiniteN.PositiveRate.isParticleHaarWeakGradient_of_smooth hF)
  refine ⟨⟨F, ⟨_, hg⟩⟩, rfl, ?_⟩
  rw [DGPS.particleEnergy_eq_of_isParticleWeakGradient ⟨F, ⟨_, hg⟩⟩ hg]
  have hreal : (DGPS.particleLaw A N).real S ≤ p := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hp hprob
  refine (integral_mono_of_nonneg ?_ ((integrable_const c).indicator hS) ?_).trans ?_
  · exact Filter.Eventually.of_forall fun x => by
      simp only [DGPS.particleTangentNormSq]
      positivity
  · exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [DGPS.particleTangentNormSq_eq]
      exact hpt x
  · rw [integral_indicator_const c hS, smul_eq_mul, mul_comm c p]
    exact mul_le_mul_of_nonneg_right hreal hc

/-! ### Main theorem -/

/-- RUF046, smooth symmetric test and energy estimate.

Setting: the RUF043 data for the feature parameter `L > 0` with `ε = 1/L`, with the same
hypotheses as RUF043 and `z_* = remoteCentre`, `Δ = Q(z_*)`. There are a radius `R > 0`, a smooth
statistic `Φ` and a smooth cutoff `χ` supported in the transition annulus, together with constants
`CX`, `CΦ` bounding `∇χ` and `Φ′` on the fundamental domain, a level gap `b > 0` on the compact
annulus, and a positive integer `JS` such that for every `N` and every `F_N = χ(Y_N)`:
`F_N` is smooth and permutation invariant, lies in `H¹(P_N)`, satisfies the pointwise bound
`Σ_i |∂_i F_N|² ≤ (CX² CΦ² / N) 1_{Y_N ∈ S}`, and its energy obeys
`E_N(F_N) ≤ (CX² CΦ² JS / N) e^{-N(Δ + b/2)}`. -/
theorem smooth_symmetric_test_and_energy_estimate {L : ℝ} (hL : 0 < L)
    (hcert : RoughLandscapeCertificate (Ufeat L (1 / L))) (tstar : E2) (r₀ lam : ℝ)
    (hr₀ : 0 < r₀) (hlam : 0 < lam)
    (hcrit : fderiv ℝ (featurePotential kappa0 (Ufeat L (1 / L))) tstar = 0)
    (h0 : (0 : E2) ∉ Metric.closedBall tstar r₀)
    (hH : ∀ x ∈ Metric.closedBall tstar r₀, ∀ v : E2,
      lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (featurePotential kappa0 (Ufeat L (1 / L)))) x v v) :
    ∃ R : ℝ, 0 < R ∧ ∃ Φ : Torus 1 → E2, ContDiff ℝ ∞ (Φ ∘ DGPS.torusLift) ∧
      ∃ χ : E2 → ℝ, ContDiff ℝ ∞ χ ∧ (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧
        Function.support (fderiv ℝ χ) ⊆
          transitionAnnulus_RUF043 (remoteCentre_RUF043 tstar) (R / 4) ∧
        ∃ CX CΦ : ℝ, 0 ≤ CX ∧ 0 ≤ CΦ ∧ (∀ y, ‖fderiv ℝ χ y‖ ≤ CX) ∧
          (∀ t ∈ Set.Icc (0 : Fin 1 → ℝ) 1, ‖fderiv ℝ (Φ ∘ DGPS.torusLift) t‖ ≤ CΦ) ∧
          ∃ b : ℝ, 0 < b ∧
            (∀ z ∈ compactAnnulus_RUF043 (remoteCentre_RUF043 tstar) (R / 4),
              remoteLevel_RUF043 L (1 / L) tstar + b ≤ remotePotential_RUF043 L (1 / L) z) ∧
            ∃ JS : ℕ, 0 < JS ∧ ∀ N : ℕ+, ∀ F : DGPS.ParticleSpace 1 N → ℝ,
              (∀ x, F x = χ (smoothMean_RUF043 Φ N x)) →
              DGPS.IsSmoothPeriodicParticle F ∧
              DGPS.IsSymmetricParticleFun (modelData hL (1 / L)) N F ∧
              DGPS.MemParticleH1 (modelData hL (1 / L)) N F ∧
              (∀ x, ∑ i, ∑ j, DGPS.particlePartial i j F x ^ 2 ≤
                Set.indicator {x : DGPS.ParticleSpace 1 N | smoothMean_RUF043 Φ N x ∈
                  transitionAnnulus_RUF043 (remoteCentre_RUF043 tstar) (R / 4)}
                  (fun _ => CX ^ 2 * CΦ ^ 2 / (N : ℝ)) x) ∧
              ∃ f : DGPS.ParticleH1 (modelData hL (1 / L)) N, f.1 = F ∧
                DGPS.particleEnergy (modelData hL (1 / L)) N f ≤
                  (CX ^ 2 * CΦ ^ 2 * (JS : ℝ) / (N : ℝ)) *
                    Real.exp (-(N : ℝ) * (remoteLevel_RUF043 L (1 / L) tstar + b / 2)) := by
  obtain ⟨R, hR, -, -, -, -, -, -, -, Φ, hΦ, -, χ, hχ, hχr, -, -, hsupp, -, -, -, hSinc, -, b,
    hb, hKS, zmin, hzmin, -⟩ :=
    fixed_smooth_bottleneck_feature_and_compatible_neighborhoods hL (1 / L) hcert tstar r₀ lam
      hr₀ hlam hcrit h0 hH
  set zs : E2 := remoteCentre_RUF043 tstar
  set Δ : ℝ := remoteLevel_RUF043 L (1 / L) tstar
  have hκ : 0 < kappa := kappa_pos
  have hR4 : 0 ≤ R / 4 := by positivity
  obtain ⟨CX, hCX0, hCX⟩ := fderiv_bound_RUF046 hχ hR4 hsupp
  obtain ⟨CΦ, hCΦ0, hCΦ⟩ := partial_bound_RUF046 hΦ
  have hδSpos : 0 < Real.sqrt (b / kappa) := Real.sqrt_pos.2 (div_pos hb hκ)
  have hδS2 : kappa * Real.sqrt (b / kappa) ^ 2 / 2 = b / 2 := by
    rw [Real.sq_sqrt (div_pos hb hκ).le]
    field_simp
  obtain ⟨JS, hJS, cS, hcS, hcovS⟩ :=
    exists_finite_net_RUF044 (compactAnnulus_RUF044 zs (R / 4)) ⟨zmin, hzmin⟩ hδSpos
  refine ⟨R, hR, Φ, hΦ, χ, hχ, hχr, hsupp, CX, CΦ, hCX0, hCΦ0, hCX, hCΦ, b, hb, hKS, JS,
    hJS, ?_⟩
  intro N F hF
  obtain rfl : F = (fun x : DGPS.ParticleSpace 1 N => χ (smoothMean_RUF043 Φ N x)) :=
    funext hF
  have hsmooth := isSmoothPeriodicParticle_RUF046 (N := N) Φ hΦ χ hχ
  have hYm := measurable_smoothMean_RUF046 (N := N) Φ hΦ
  have hTc : IsClosed (transitionAnnulus_RUF043 zs (R / 4)) := by
    have h1 : IsClosed {y : E2 | R / 4 ≤ ‖y - zs‖} := isClosed_le continuous_const (by fun_prop)
    have h2 : IsClosed {y : E2 | ‖y - zs‖ ≤ 2 * (R / 4)} :=
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
  have hpt := pointwise_RUF046 (N := N) Φ hΦ χ hχ hsupp hCX0 hCX hCΦ0 hCΦ
  refine ⟨hsmooth, ?_, ?_, hpt, ?_⟩
  · intro σ
    refine Filter.Eventually.of_forall fun x => ?_
    have hsum : ∑ i, Φ (x (σ i)) = ∑ i, Φ (x i) :=
      Equiv.sum_comp σ (fun k => Φ (x k))
    show χ (smoothMean_RUF043 Φ N (DGPS.permuteParticles σ x)) =
      χ (smoothMean_RUF043 Φ N x)
    unfold smoothMean_RUF043 DGPS.permuteParticles
    rw [hsum]
  · exact ⟨_, (DGPS.isParticleWeakGradient_iff _ N _ _).2
      (DGPS.FiniteN.PositiveRate.isParticleHaarWeakGradient_of_smooth hsmooth)⟩
  · obtain ⟨f, hf, hE⟩ := energy_le_RUF046 (A := modelData hL (1 / L)) (N := N)
      (fun x : DGPS.ParticleSpace 1 N => χ (smoothMean_RUF043 Φ N x)) hsmooth _ hS
      (c := CX ^ 2 * CΦ ^ 2 / (N : ℝ)) (p := (JS : ℝ) *
        Real.exp (-(N : ℝ) * (Δ + b / 2))) (by positivity) (by positivity) hpt hprob
    exact ⟨f, hf, hE.trans_eq (by ring)⟩

end DGPS.Examples.RoughBoundary.Bottleneck
