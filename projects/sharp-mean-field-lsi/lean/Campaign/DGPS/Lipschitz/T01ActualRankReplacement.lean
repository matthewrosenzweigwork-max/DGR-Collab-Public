import DGPS.Lipschitz.T01ForceThreshold
import DGPS.Lipschitz.T01ResidualForceBound
import DGPS.Lipschitz.T01ResidualMoments
import DGPS.Lipschitz.T01ParticleNormalizer
import DGPS.Lipschitz.T01ReferenceMoments
import DGPS.Lipschitz.T01RootForceBound

/-! Actual normalizer and force thresholds on the caller's same smoothing witness. -/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Lipschitz

open KernelApproximation CenteredForceExponential DGPS.Frontier.LIP051

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual particle normalizer gives the literal legacy centered partition limit. -/
theorem t01_legacy_centeredPartition_tendsto {d : ℕ} (S : Spec d) (aux : Aux S)
    (J : InteractionData d) (D : KData d) (hD : D.K = centeredKernel J S.mu)
    (hfix : (frozenGibbs J (specProbability_LIP016 S)).measure = S.mu)
    {p C : ℝ} (hp : 1 < p)
    (hN : ∀ N : ℕ+, |Real.log (centeredParticleNormalizer J (specProbability_LIP016 S) N)| ≤ C ∧
      (∫ x, centeredParticleDensity J (specProbability_LIP016 S) N x ^ p
        ∂Measure.pi (fun _ : Fin N => S.mu)) ≤ C) :
    Tendsto (fun N : ℕ => SharpLSI.centeredPartition J.W S.mu N) atTop
      (𝓝 (∫ z, Real.exp (-(((QT_LIP05101 S D.K : (ℕ → ℝ) → ℝ) z +
        dK_LIP05101 S D.K) / 2)) ∂gaussianCountable_LIP016)) := by
  have hD' : ∀ x y, D.K x y = centeredKernel J (specProbability_LIP016 S) x y := by
    intro x y
    exact congrFun (congrFun hD x) y
  have key := (t01_centered_particle_normalizer_limit S aux D J hD' hfix hp hN).2.2
  apply (tendsto_add_atTop_iff_nat 1).mp
  convert key using 1
  funext n
  rw [centeredParticleNormalizer_eq_integral J (specProbability_LIP016 S) hfix]
  simp only [SharpLSI.centeredPartition, t01_centeredParticlePotential_eq_legacy]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The genuine current residual force supplies the precise chosen-gradient threshold used by
energy replacement, under the actual centered density moment. -/
theorem t01_actual_residual_force_threshold {d : ℕ} (S : Spec d) (aux : Aux S)
    (J : InteractionData d) (D : KData d) (hD : D.K = centeredKernel J S.mu)
    (hfix : (frozenGibbs J (specProbability_LIP016 S)).measure = S.mu)
    (gδ : Torus d → Tangent d) (hδm : Measurable gδ) {Mδ : ℝ}
    (hδb : ∀ x, ‖gδ x‖ ≤ Mδ) (hδ : IsWeakGradient (fun x => D.K x x) gδ)
    (t : ℕ → ℝ) (m : ℕ → ℕ) {Cs : ℝ}
    (h1 : ∀ R x y, ‖smoothG1 S aux D (t R) (m R) x y‖ ≤ Cs)
    (h2 : ∀ R x y, ‖smoothG2 S aux D (t R) (m R) x y‖ ≤ Cs)
    (hG1 : Tendsto (fun R => ∫ p,
      ‖D.G1 p.1 p.2 - smoothG1 S aux D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu)
      atTop (𝓝 0))
    (F : SharpLSI.FL.FiniteRankApprox J.W S.mu S.v)
    (hs : ∀ R, F.s R = Finset.range (m R))
    (ha : ∀ R i j, F.a R i j = positiveKernelCoefficient S D (t R) (m R) i j)
    {p C : ℝ} (hp : 1 < p) (hC0 : 0 ≤ C)
    (hC : ∀ N : ℕ+, ∫ X, centeredParticleDensity J (specProbability_LIP016 S) N X ^ p
      ∂Measure.pi (fun _ : Fin N => S.mu) ≤ C) :
    ∀ η : ℝ, 0 < η → ∃ R₀ : ℕ, ∀ R ≥ R₀, ∀ᶠ N : ℕ+ in atTop,
      (∫⁻ X, ENNReal.ofReal (SharpLSI.gradSqC
        (fun Y => centeredParticlePotential J (specProbability_LIP016 S) N Y -
          SharpLSI.FL.URN F R N Y) X) ∂particleLaw J N) ≤ ENNReal.ofReal η := by
  let μ := specProbability_LIP016 S
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have hsym : ∀ x y, D.K x y = D.K y x := by rw [hD]; exact centeredKernel_symm J S.mu
  have hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0 := by
    intro y
    simp only [hD, centeredKernel_symm J S.mu _ y]
    exact integral_centeredKernel_right J S.mu y
  let P (N : ℕ) : Measure (Fin N → Torus d) :=
    if hN : 0 < N then particleLaw J ⟨N, hN⟩ else Measure.pi fun _ : Fin N => S.mu
  have hP : ∀ N : ℕ+, P N = particleLaw J N := by
    intro N
    simp only [P, dif_pos N.pos]
    rfl
  have hprob : ∀ N, 1 ≤ N → IsProbabilityMeasure (P N) := by
    intro N hN
    have hn : 0 < N := hN
    simp only [P, dif_pos hn]
    exact DGPS.Particle.particleLaw_isProbabilityMeasure J (⟨N, hn⟩ : ℕ+)
  have hPQ : ∀ N, 1 ≤ N → P N ≪ Measure.pi (fun _ : Fin N => S.mu) := by
    intro N hN
    have hn : 0 < N := hN
    simp only [P, dif_pos hn]
    rw [particleLaw_eq_centered_reference J μ hfix ⟨N, hn⟩]
    exact withDensity_absolutelyContinuous _ _
  let Cp : ℝ≥0 := Real.toNNReal (C ^ (1 / p))
  have hCpPN : ∀ N : ℕ+, eLpNorm (fun x => ((particleLaw J N).rnDeriv
      (Measure.pi fun _ : Fin N => S.mu) x).toReal) (ENNReal.ofReal p)
      (Measure.pi fun _ : Fin N => S.mu) ≤ Cp := by
    intro N
    have hq0 (x : ParticleSpace d N) : 0 ≤ centeredParticleDensity J μ N x :=
      (centeredParticleDensity_pos J μ N x).le
    have hi : Integrable (fun x => centeredParticleDensity J μ N x ^ p)
        (Measure.pi fun _ : Fin N => S.mu) :=
      ((Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp
        (centeredParticleDensity_continuous J μ N)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    have hlin : ∫⁻ x, ENNReal.ofReal (|centeredParticleDensity J μ N x| ^ p)
        ∂Measure.pi (fun _ : Fin N => S.mu) ≤ ENNReal.ofReal C := by
      simp_rw [abs_of_nonneg (hq0 _)]
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall fun x => Real.rpow_nonneg (hq0 x) _)]
      exact ENNReal.ofReal_le_ofReal (hC N)
    have hq := (SharpLSI.FL.ga_memLp_of_lintegral (by linarith : 0 < p) hC0
      (centeredParticleDensity_continuous J μ N).aestronglyMeasurable hlin).2
    have hae := particleLaw_rnDeriv_reference J μ hfix N
    change (fun x => ((particleLaw J N).rnDeriv (Measure.pi fun _ : Fin N => S.mu) x).toReal)
      =ᵐ[Measure.pi fun _ : Fin N => S.mu] centeredParticleDensity J μ N at hae
    rw [eLpNorm_congr_ae hae]
    change _ ≤ ENNReal.ofReal (C ^ (1 / p))
    exact hq
  have hCp : ∀ N, 1 ≤ N → eLpNorm (fun x => ((P N).rnDeriv
      (Measure.pi fun _ : Fin N => S.mu) x).toReal) (ENNReal.ofReal p)
      (Measure.pi fun _ : Fin N => S.mu) ≤ Cp := by
    intro N hN
    have hn : 0 < N := hN
    simp only [P, dif_pos hn]
    change eLpNorm (fun x => ((particleLaw J (⟨N, hn⟩ : ℕ+)).rnDeriv
      (Measure.pi fun _ : Fin N => S.mu) x).toReal) (ENNReal.ofReal p)
      (Measure.pi fun _ : Fin N => S.mu) ≤ Cp
    exact hCpPN (⟨N, hn⟩ : ℕ+)
  have hpE : 1 < ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hp
  obtain ⟨hw, hbd, hlim⟩ := t01_residualForce_changed_measure_tendsto_with_bounds S aux D
    hsym hc gδ hδm hδb hδ t m h1 h2 hG1 P hprob hPQ hpE hCp
  apply actual_force_threshold_of_real_limsup J μ hfix
    (fun R N Y => centeredParticlePotential J μ N Y - SharpLSI.FL.URN F R N Y)
    (t01ResidualForce S aux D gδ t m) ?_ P hP hbd hlim
  intro R N
  convert hw R N using 1
  funext X
  rw [t01_URN_eq_smoothK S aux D hsym hc J F R (t R) (m R) (hs R) (ha R)]
  unfold centeredParticlePotential
  have hDμ : D.K = DGPS.centeredKernel J μ := hD
  simp only [← hDμ, one_div]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]

end DGPS.Lipschitz
