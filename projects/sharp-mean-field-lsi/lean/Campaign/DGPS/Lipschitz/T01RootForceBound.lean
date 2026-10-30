import DGPS.Lipschitz.T01GroundStateSobolev
import DGPS.Lipschitz.T01SpectralCut
import DGPS.Particle.CenteredForceExponential

/-!
# Uniform actual ground-state force bounds from density moments

The actual centered kernel and its diagonal derivative supply the force. Product exponential
moments and the exact Gibbs density moment imply a uniform Gibbs second moment. This is the
force input to the reference energy bound; no bounded comparison or particle rate is assumed.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Lipschitz

open KernelApproximation CenteredForceExponential

/-- Uniform density moments control the actual centered force under the canonical Gibbs law. -/
theorem exists_centeredParticleForce_uniform_bound {d : ℕ} (A : InteractionData d)
    (hA : LipschitzData A) (hd : 0 < d) (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    {p C : ℝ} (hp : 1 < p) (hC0 : 0 ≤ C)
    (hC : ∀ N : ℕ+, ∫ x, centeredParticleDensity A μ N x ^ p
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ C) :
    ∃ (gU : (N : ℕ+) → ParticleSpace d N → Fin N → Tangent d) (M : ℝ),
      0 ≤ M ∧ (∀ N, IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) (gU N)) ∧
      ∀ N, ∫ x, particleTangentNormSq (gU N x) ∂particleLaw A N ≤ M := by
  obtain ⟨D, hD⟩ := exists_centeredKernel_data A hA (μ : Measure (Torus d))
  obtain ⟨gδ, hδm, ⟨Mδ, hδb⟩, hδ⟩ :=
    exists_centeredKernel_diagonal_gradient A hA (μ : Measure (Torus d))
  have hDK : D.K = DGPS.centeredKernel A μ := hD
  have hδ' : IsWeakGradient (fun x => D.K x x) gδ := by rw [hDK]; exact hδ
  have hsym : ∀ x y, D.K x y = D.K y x := by rw [hDK]; exact DGPS.centeredKernel_symm A μ
  have hc : ∀ x, ∫ y, D.K x y ∂(μ : Measure (Torus d)) = 0 := by
    rw [hDK]
    exact DGPS.integral_centeredKernel_right A μ
  have hac : (μ : Measure (Torus d)) ≪ haar d := by
    rw [← hμ]
    exact (frozenGibbs A μ).measure_ac_haar
  obtain ⟨⟨hU, -⟩, hb0⟩ := force_package_centered (μ := (μ : Measure (Torus d)))
    (fun _ h => hac.ae_le h) hsym D.Kc D.G1m D.G1b hδm hδb D.g1 hδ' hc
  let gU : (N : ℕ+) → ParticleSpace d N → Fin N → Tangent d := fun N x i =>
    (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, D.G1 (x i) (x j) +
      (2 * (N : ℝ))⁻¹ • gδ (x i)
  have hU' : ∀ N, IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) (gU N) := by
    intro N
    have hfun : (fun x : ParticleSpace d N => (2 * (N : ℝ))⁻¹ *
        ∑ i, ∑ j, D.K (x i) (x j)) = centeredParticlePotential A μ N := by
      funext x
      rw [hDK]
      unfold centeredParticlePotential
      rw [one_div]
    rw [← hfun]
    exact hU N
  let α : ℝ := (8 * (d : ℝ) * (1 + D.B ^ 2 + Mδ ^ 2))⁻¹
  have hα : 0 < α := by dsimp [α]; positivity
  let K : ℝ := 2 * Real.exp (1 / 16)
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hK : ∀ N : ℕ+, ∫⁻ x, ENNReal.ofReal
      (Real.exp (α * particleTangentNormSq (gU N x)))
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ ENNReal.ofReal K := by
    intro N
    simpa only [gU, particleTangentNormSq, K, ENNReal.ofReal_mul zero_le_two] using
      exp_moment_core hd D.G1m hδm D.B_nonneg D.G1b hδb hb0 rfl N.pos
  have hpE : 1 < ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hp
  obtain ⟨m, hm, hmp⟩ := exists_nat_exponent hpE
  let Cp : ℝ≥0 := Real.toNNReal (C ^ (1 / p))
  have hCp : ∀ N : ℕ+, eLpNorm (fun x => ((particleLaw A N).rnDeriv
      (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) x).toReal)
      (ENNReal.ofReal p) (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤ Cp := by
    intro N
    have hq0 (x : ParticleSpace d N) : 0 ≤ centeredParticleDensity A μ N x :=
      (centeredParticleDensity_pos A μ N x).le
    have hi : Integrable (fun x => centeredParticleDensity A μ N x ^ p)
        (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) :=
      ((Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp
        (centeredParticleDensity_continuous A μ N)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    have hlin : ∫⁻ x, ENNReal.ofReal (|centeredParticleDensity A μ N x| ^ p)
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ ENNReal.ofReal C := by
      simp_rw [abs_of_nonneg (hq0 _)]
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall fun x => Real.rpow_nonneg (hq0 x) _)]
      exact ENNReal.ofReal_le_ofReal (hC N)
    have hq := (SharpLSI.FL.ga_memLp_of_lintegral (by linarith : 0 < p) hC0
      (centeredParticleDensity_continuous A μ N).aestronglyMeasurable hlin).2
    rw [eLpNorm_congr_ae (particleLaw_rnDeriv_reference A μ hμ N)]
    change _ ≤ ENNReal.ofReal (C ^ (1 / p))
    exact hq
  let M : ℝ := (((Cp : ℝ) ^ (((m : ℝ) + 1) / m)) ^ ((m : ℝ) / ((m : ℝ) + 1)) *
    ((((2 * m + 1).factorial : ℝ) / α ^ (2 * m + 1) * K) ^
      (1 / (2 * ((m : ℝ) + 1))))) *
    (α⁻¹ * K) ^ (1 / (2 * ((m : ℝ) + 1)))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨gU, M, hM, hU', fun N => ?_⟩
  let Q := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  let F : ParticleSpace d N → ℝ := fun x => particleTangentNormSq (gU N x)
  have hFm : Measurable F := measurable_force_sq D.G1m hδm N
  have hF0 : ∀ x, 0 ≤ F x := fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hFint : Integrable F Q := by
    exact integrable_finsetSum _ fun i _ =>
      CenteredForceMoment.force_sq_integrable D.G1m hδm D.G1b hδb i
  have hFQ : ∫ x, F x ∂Q ≤ α⁻¹ * K := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ α⁻¹ * K)).mp
    rw [ofReal_integral_eq_lintegral_ofReal hFint (Eventually.of_forall hF0),
      ENNReal.ofReal_mul (by positivity : 0 ≤ α⁻¹)]
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal α⁻¹ * ENNReal.ofReal (Real.exp (α * F x)) ∂Q := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ α⁻¹)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h := Real.add_one_le_exp (α * F x)
        calc F x = α⁻¹ * (α * F x) := by field_simp
          _ ≤ α⁻¹ * Real.exp (α * F x) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ENNReal.ofReal α⁻¹ * ∫⁻ x, ENNReal.ofReal (Real.exp (α * F x)) ∂Q :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := mul_le_mul' le_rfl (hK N)
  have hPQ : particleLaw A N ≪ Q := by
    rw [particleLaw_eq_centered_reference A μ hμ N]
    exact withDensity_absolutelyContinuous _ _
  have hbound := changed_measure_bound hPQ hFm hF0 hm
    (Real.rpow_nonneg Cp.coe_nonneg _) (rnDeriv_lintegral_le hm hmp (hCp N)) hα hK0 (hK N)
  refine hbound.trans ?_
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (integral_nonneg hF0) hFQ (by positivity))
    (by positivity)

end DGPS.Lipschitz
