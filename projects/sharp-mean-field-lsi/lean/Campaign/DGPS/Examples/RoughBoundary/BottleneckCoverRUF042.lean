import DGPS.Examples.RoughBoundary.Bottleneck
import DGPS.Examples.RoughBoundary.BottleneckNormalizerRUF040

set_option maxHeartbeats 2000000

open MeasureTheory
open scoped ENNReal

namespace DGPS.Examples.RoughBoundary.Bottleneck

open DGPS.Examples.RoughBoundary.Feature
open DGPS.Examples.RoughBoundary.FreeEnergy
open DGPS.Examples.RoughBoundary.Model
open DGPS.Examples.RoughBoundary.Particle
open DGPS.Examples.RoughBoundary.Semicontinuity
open DGPS.Examples.RoughBoundary.Landscape

/-- The rough-particle normalizer is at least one for every feature parameter, because the
exponent `roughB` is nonnegative and the particle Haar measure is a probability measure. -/
lemma one_le_normalizer_RUF042 {L ε : ℝ} (hL : 0 < L) (N : ℕ+) :
    (1 : ℝ) ≤ ∫ x : ParticleSpace 1 N, Real.exp (roughB L ε N x) ∂particleHaar 1 N := by
  have hU : Continuous (Ufeat L ε) := continuous_Ufeat hL ε
  have hk : (0 : ℝ) ≤ kappa := by unfold kappa; norm_num
  have hnn : ∀ x : ParticleSpace 1 N, 0 ≤ roughB L ε N x := fun x => by
    unfold roughB
    exact div_nonneg (mul_nonneg hk (by positivity)) (by positivity)
  have hcont : Continuous (fun x : ParticleSpace 1 N => Real.exp (roughB L ε N x)) := by
    unfold roughB featureSum
    fun_prop
  have hgi : Integrable (fun x : ParticleSpace 1 N => Real.exp (roughB L ε N x))
      (particleHaar 1 N) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc (1 : ℝ) = ∫ _x : ParticleSpace 1 N, (1 : ℝ) ∂particleHaar 1 N := by simp
    _ ≤ _ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => zero_le_one) hgi
        (Filter.Eventually.of_forall fun x => ?_)
      exact Real.one_le_exp (hnn x)

/-- RUF042, finite cover upper probability estimate. For the feature parameter `L` selected by
the exact exponential tilt identity (RUF041), a compact `K` with `Q ≥ a_K` on `K`, covered by `J`
open balls of radius `δ` centred in `K`, satisfies `P_N(M_N ∈ K) ≤ J exp(-N (a_K - κ δ² / 2))`
for every `N ≥ 1`, where `M_N = N⁻¹ ∑ U(xᵢ)` and `Q(z) = Ψ(κ z)`. -/
theorem finite_cover_upper_probability_estimate :
    ∃ L : ℝ, ∃ hL : 0 < L, FreeEnergyDecomposition L (1 / L) ∧
      ∀ K : Set E2, IsCompact K → ∀ aK : ℝ,
        (∀ z ∈ K, aK ≤ featurePotential kappa0 (Ufeat L (1 / L)) (kappa • z)) →
        ∀ δ : ℝ, 0 < δ → ∀ (J : ℕ) (c : Fin J → E2),
          (∀ j, c j ∈ K) → K ⊆ ⋃ j, Metric.ball (c j) δ →
          ∀ N : ℕ+,
            particleLaw (modelData hL (1 / L)) N
                {x | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈ K} ≤
              ENNReal.ofReal (J * Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2))) := by
  obtain ⟨L, hL, hFree, hTilt⟩ := exact_exponential_tilt_identity
  refine ⟨L, hL, hFree, ?_⟩
  intro K _hK aK hQ δ _hδ J c hc hcover N
  have hk : (0 : ℝ) ≤ kappa := by unfold kappa; norm_num
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hLaw := (hTilt N 0).2.2
  have hZ1 : (1 : ℝ) ≤ ∫ y, Real.exp (roughB L (1 / L) N y) ∂particleHaar 1 N :=
    one_le_normalizer_RUF042 hL N
  have hZinv : (∫ y, Real.exp (roughB L (1 / L) N y) ∂particleHaar 1 N)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hZ1
  have hM : Continuous (fun x : ParticleSpace 1 N => (N : ℝ)⁻¹ • featureSum L (1 / L) N x) := by
    have hU : Continuous (Ufeat L (1 / L)) := continuous_Ufeat hL (1 / L)
    unfold featureSum
    fun_prop
  -- one cover ball: the probability of its event is at most the exponential constant
  have hball : ∀ j : Fin J,
      particleLaw (modelData hL (1 / L)) N
          {x | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈ Metric.ball (c j) δ} ≤
        ENNReal.ofReal (Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2))) := by
    intro j
    have _hprob : ∀ _i : Fin N, IsProbabilityMeasure (gibbsMeasure L (1 / L) (kappa • c j)) :=
      fun _ => isProbabilityMeasure_gibbs hL (1 / L) (kappa • c j)
    set S : Set (ParticleSpace 1 N) :=
      {x | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈ Metric.ball (c j) δ} with hSdef
    have hS : MeasurableSet S := hM.measurable measurableSet_ball
    have hEq := congrArg (fun m : Measure (ParticleSpace 1 N) => m S) (hTilt N (c j)).2.1
    rw [withDensity_apply _ hS, withDensity_apply _ hS] at hEq
    -- pointwise: the tilt multiplier on the event is at most the displayed exponential
    have hpt : ∀ x ∈ S, ENNReal.ofReal (Real.exp ((N : ℝ) * (kappa / 2 *
        ‖(N : ℝ)⁻¹ • featureSum L (1 / L) N x - c j‖ ^ 2 -
          featurePotential kappa0 (Ufeat L (1 / L)) (kappa • c j)))) ≤
        ENNReal.ofReal (Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2))) := by
      intro x hx
      have hd : ‖(N : ℝ)⁻¹ • featureSum L (1 / L) N x - c j‖ < δ := mem_ball_iff_norm.1 hx
      have hd2 : ‖(N : ℝ)⁻¹ • featureSum L (1 / L) N x - c j‖ ^ 2 ≤ δ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hd.le 2
      have hQj : aK ≤ featurePotential kappa0 (Ufeat L (1 / L)) (kappa • c j) := hQ (c j) (hc j)
      have hin : kappa / 2 * ‖(N : ℝ)⁻¹ • featureSum L (1 / L) N x - c j‖ ^ 2 -
          featurePotential kappa0 (Ufeat L (1 / L)) (kappa • c j) ≤
            -(aK - kappa * δ ^ 2 / 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hd2 (show (0 : ℝ) ≤ kappa / 2 by linarith)]
      have hexp := mul_le_mul_of_nonneg_left hin hNpos.le
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      calc _ ≤ (N : ℝ) * (-(aK - kappa * δ ^ 2 / 2)) := hexp
        _ = -(N : ℝ) * (aK - kappa * δ ^ 2 / 2) := by ring
    have h1 : ∫⁻ x in S, ENNReal.ofReal ((∫ y, Real.exp (roughB L (1 / L) N y) ∂particleHaar 1 N)⁻¹ *
        Real.exp (roughB L (1 / L) N x)) ∂particleHaar 1 N ≤
        ∫⁻ x in S, ENNReal.ofReal (Real.exp (roughB L (1 / L) N x)) ∂particleHaar 1 N :=
      lintegral_mono fun x => ENNReal.ofReal_le_ofReal
        (mul_le_of_le_one_left (Real.exp_pos _).le hZinv)
    have h3 : ∫⁻ x in S, ENNReal.ofReal (Real.exp ((N : ℝ) * (kappa / 2 *
        ‖(N : ℝ)⁻¹ • featureSum L (1 / L) N x - c j‖ ^ 2 -
          featurePotential kappa0 (Ufeat L (1 / L)) (kappa • c j)))) ∂
          (Measure.pi fun _ : Fin N => gibbsMeasure L (1 / L) (kappa • c j)) ≤
        ∫⁻ _x in S, ENNReal.ofReal (Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2)))
          ∂(Measure.pi fun _ : Fin N => gibbsMeasure L (1 / L) (kappa • c j)) :=
      setLIntegral_mono' hS hpt
    have h4 := setLIntegral_const (μ := Measure.pi fun _ : Fin N => gibbsMeasure L (1 / L) (kappa • c j))
      S (ENNReal.ofReal (Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2))))
    have h5 : ENNReal.ofReal (Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2))) *
        (Measure.pi fun _ : Fin N => gibbsMeasure L (1 / L) (kappa • c j)) S ≤
        ENNReal.ofReal (Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2))) :=
      mul_le_of_le_one_right zero_le prob_le_one
    rw [hLaw, withDensity_apply _ hS]
    calc ∫⁻ x in S, ENNReal.ofReal ((∫ y, Real.exp (roughB L (1 / L) N y) ∂particleHaar 1 N)⁻¹ *
            Real.exp (roughB L (1 / L) N x)) ∂particleHaar 1 N
        ≤ ∫⁻ x in S, ENNReal.ofReal (Real.exp (roughB L (1 / L) N x)) ∂particleHaar 1 N := h1
      _ = ∫⁻ x in S, ENNReal.ofReal (Real.exp ((N : ℝ) * (kappa / 2 *
            ‖(N : ℝ)⁻¹ • featureSum L (1 / L) N x - c j‖ ^ 2 -
              featurePotential kappa0 (Ufeat L (1 / L)) (kappa • c j)))) ∂
              (Measure.pi fun _ : Fin N => gibbsMeasure L (1 / L) (kappa • c j)) := hEq
      _ ≤ ∫⁻ _x in S, ENNReal.ofReal (Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2)))
            ∂(Measure.pi fun _ : Fin N => gibbsMeasure L (1 / L) (kappa • c j)) := h3
      _ = ENNReal.ofReal (Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2))) *
            (Measure.pi fun _ : Fin N => gibbsMeasure L (1 / L) (kappa • c j)) S := h4
      _ ≤ _ := h5
  -- the event is covered by the `J` cover events
  have hsub : {x : ParticleSpace 1 N | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈ K} ⊆
      ⋃ j : Fin J,
        {x : ParticleSpace 1 N | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈ Metric.ball (c j) δ} := by
    intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcover hx)
    exact Set.mem_iUnion.2 ⟨j, hj⟩
  calc particleLaw (modelData hL (1 / L)) N {x | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈ K}
      ≤ particleLaw (modelData hL (1 / L)) N
          (⋃ j : Fin J,
            {x : ParticleSpace 1 N | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈ Metric.ball (c j) δ}) :=
        measure_mono hsub
    _ ≤ ∑ j : Fin J, particleLaw (modelData hL (1 / L)) N
          {x : ParticleSpace 1 N | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈ Metric.ball (c j) δ} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin J, ENNReal.ofReal (Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2))) :=
        Finset.sum_le_sum fun j _ => hball j
    _ = ENNReal.ofReal (J * Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg J), ENNReal.ofReal_natCast]

end DGPS.Examples.RoughBoundary.Bottleneck
