import DGPS.Structural.MinimizerHessian
import DGPS.Structural.SmallRateCircle
import DGPS.Variational.SpeciesGap

/-!
# Exact frozen-reference species energy identity (STR008)

Let `μ` be a free-energy minimizer (so `μ = P μ` by STR004), `K` its centered kernel, `ν = ρ̄ m`
the barycenter of a finite absolute family, `η = ν - μ`, `u = K * η` and `Q = ∬ K dη²`.  Then

* `Gθ = E_fr - Q/2 - log ∫ exp(-u) dμ`, with `E_fr = ∑ θ_s H(ν_s | P ν)` (`frozenEntropy`);
* `∫ u dμ = 0`, hence `log ∫ exp(-u) dμ ≥ 0`;
* every quantity is finite (`E_fr ≠ ⊤`, `∫ exp(-u) dμ > 0`).

Route (R5 note): self-contained. `E_fr` and `F_*` are expanded through the Gibbs identity of
STR017 (`budget_entropy_frozen`); `u` and `Q` are written out as the bilinear expressions
`∫ K(x, y) d(ν - μ)(y)` and `∫ u d(ν - μ)`, which are then evaluated by Fubini and centering.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace DGPS.Structural

variable {d : ℕ}

/-- The potential `u = K * η`, `u(x) = ∫ K(x, y) d(ν - μ)(y)`, `η = ν - μ`. -/
noncomputable def kernelPotential (A : InteractionData d) (μ ν : ProbabilityMeasure (Torus d))
    (x : Torus d) : ℝ :=
  ∫ y, centeredKernel A μ x y ∂(ν : Measure (Torus d)) -
    ∫ y, centeredKernel A μ x y ∂(μ : Measure (Torus d))

/-- The centered correction `Q = ∬ K dη² = ∫ u dη`, `η = ν - μ`. -/
noncomputable def centeredCorrection (A : InteractionData d) (μ ν : ProbabilityMeasure (Torus d)) :
    ℝ :=
  ∫ x, kernelPotential A μ ν x ∂(ν : Measure (Torus d)) -
    ∫ x, kernelPotential A μ ν x ∂(μ : Measure (Torus d))

private theorem fei_integrable {f : Torus d → ℝ} (hf : Continuous f)
    (ν : ProbabilityMeasure (Torus d)) : Integrable f (ν : Measure (Torus d)) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Closed form of `u`: `u = W*ν - W*μ - (∫ W*μ dν - ∬ W dμ²)`. -/
theorem kernelPotential_eq (A : InteractionData d) (μ ν : ProbabilityMeasure (Torus d))
    (x : Torus d) :
    kernelPotential A μ ν x =
      interactionConvolution A ν x - interactionConvolution A μ x -
        (∫ z, interactionConvolution A μ z ∂(ν : Measure (Torus d)) - meanInteraction A μ) := by
  unfold kernelPotential
  rw [integral_centeredKernel_right A μ x, sub_zero]
  have hW : Integrable (fun y => A.W x y) (ν : Measure (Torus d)) :=
    fei_integrable (A.W_continuous_right x) ν
  have hc : Integrable (interactionConvolution A μ) (ν : Measure (Torus d)) :=
    fei_integrable (continuous_interactionConvolution A μ) ν
  unfold centeredKernel
  have h1 : Integrable (fun y => A.W x y - interactionConvolution A μ x)
      (ν : Measure (Torus d)) := hW.sub (integrable_const _)
  have h2 : Integrable
      (fun y => A.W x y - interactionConvolution A μ x - interactionConvolution A μ y)
      (ν : Measure (Torus d)) := h1.sub hc
  rw [integral_add h2 (integrable_const _), integral_sub h1 hc, integral_sub hW (integrable_const _)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  unfold interactionConvolution
  ring

theorem kernelPotential_continuous (A : InteractionData d) (μ ν : ProbabilityMeasure (Torus d)) :
    Continuous (kernelPotential A μ ν) := by
  have : kernelPotential A μ ν = fun x =>
      interactionConvolution A ν x - interactionConvolution A μ x -
        (∫ z, interactionConvolution A μ z ∂(ν : Measure (Torus d)) - meanInteraction A μ) :=
    funext (kernelPotential_eq A μ ν)
  rw [this]
  have h1 := continuous_interactionConvolution A ν
  have h2 := continuous_interactionConvolution A μ
  fun_prop

/-- Fubini and symmetry of `W`: `∫ W*ν dμ = ∫ W*μ dν`. -/
theorem integral_convolution_swap (A : InteractionData d) (μ ν : ProbabilityMeasure (Torus d)) :
    ∫ x, interactionConvolution A ν x ∂(μ : Measure (Torus d)) =
      ∫ z, interactionConvolution A μ z ∂(ν : Measure (Torus d)) := by
  unfold interactionConvolution
  have hint : Integrable (Function.uncurry fun x z => A.W x z)
      ((μ : Measure (Torus d)).prod (ν : Measure (Torus d))) :=
    (A.W_continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [A.W_symm]

/-- `∫ u dμ = 0` for the potential `u = K * (ν - μ)`. -/
theorem integral_kernelPotential_self (A : InteractionData d) (μ ν : ProbabilityMeasure (Torus d)) :
    ∫ x, kernelPotential A μ ν x ∂(μ : Measure (Torus d)) = 0 := by
  have hc1 := fei_integrable (continuous_interactionConvolution A ν) μ
  have hc2 := fei_integrable (continuous_interactionConvolution A μ) μ
  have hs : Integrable (fun x => interactionConvolution A ν x - interactionConvolution A μ x)
      (μ : Measure (Torus d)) := hc1.sub hc2
  simp_rw [kernelPotential_eq]
  rw [integral_sub hs (integrable_const _), integral_sub hc1 hc2,
    integral_convolution_swap, integral_interactionConvolution]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- `Q = ∬ W dν² - 2 ∫ W*μ dν + ∬ W dμ²`. -/
theorem centeredCorrection_eq (A : InteractionData d) (μ ν : ProbabilityMeasure (Torus d)) :
    centeredCorrection A μ ν =
      interactionEnergy A (ν : Measure (Torus d)) -
        2 * ∫ z, interactionConvolution A μ z ∂(ν : Measure (Torus d)) + meanInteraction A μ := by
  unfold centeredCorrection
  rw [integral_kernelPotential_self, sub_zero]
  have hc1 := fei_integrable (continuous_interactionConvolution A ν) ν
  have hc2 := fei_integrable (continuous_interactionConvolution A μ) ν
  have hE : ∫ x, interactionConvolution A ν x ∂(ν : Measure (Torus d)) =
      interactionEnergy A (ν : Measure (Torus d)) := by
    unfold interactionConvolution interactionEnergy
    rw [integral_prod _ (integrable_W_prod A ν)]
  have hs : Integrable (fun x => interactionConvolution A ν x - interactionConvolution A μ x)
      (ν : Measure (Torus d)) := hc1.sub hc2
  simp_rw [kernelPotential_eq]
  rw [integral_sub hs (integrable_const _), integral_sub hc1 hc2, hE]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- `meanInteraction` is the interaction energy. -/
theorem meanInteraction_eq (A : InteractionData d) (μ : ProbabilityMeasure (Torus d)) :
    meanInteraction A μ = interactionEnergy A (μ : Measure (Torus d)) := rfl

/-- At a Gibbs fixed point `μ = P μ` with `μ = ρ m`, `F_* `-type identity:
`H(μ | m) + ∫ V dμ + ∬ W dμ² = - log Z_μ`. -/
theorem fixedPoint_entropy_eq (A : InteractionData d) (ρ : AbsoluteDensity d)
    (h : (densityMeasure ρ : Measure (Torus d)) = (frozenGibbs A (densityMeasure ρ)).measure) :
    (relativeEntropy (densityMeasure ρ : Measure (Torus d)) (haar d)).toReal +
      potentialEnergy A (densityMeasure ρ : Measure (Torus d)) +
      interactionEnergy A (densityMeasure ρ : Measure (Torus d)) =
      - Real.log (frozenPartition A (densityMeasure ρ : Measure (Torus d))) := by
  obtain ⟨-, h2⟩ := budget_entropy_frozen A (densityMeasure ρ) ρ
  rw [← h, relativeEntropy_self] at h2
  have := budget_integral_frozenPotential A (densityMeasure ρ)
  simp only [ENNReal.toReal_zero] at h2
  linarith

/-- The expansion of the frozen entropy: `E_fr = ∑ θ H(ν_s | m) + ∫ V dν + ∬ W dν² + log Z_ν`. -/
theorem frozenEntropy_toReal_eq (A : InteractionData d) (F : SpeciesFamily d) :
    frozenEntropy A F ≠ ⊤ ∧
    (frozenEntropy A F).toReal =
      ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s)) (haar d)).toReal +
        potentialEnergy A (densityMeasure (barycenter F) : Measure (Torus d)) +
        interactionEnergy A (densityMeasure (barycenter F) : Measure (Torus d)) +
        Real.log (frozenPartition A (densityMeasure (barycenter F) : Measure (Torus d))) := by
  set ν : ProbabilityMeasure (Torus d) := densityMeasure (barycenter F) with hν
  have hfin : ∀ s, relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
      (frozenGibbs A ν).measure ≠ ⊤ := fun s => (budget_entropy_frozen A ν (F.density s)).1
  refine ⟨ENNReal.sum_ne_top.2 fun s _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin s), ?_⟩
  have hsum : (frozenEntropy A F).toReal =
      ∑ s, F.weight s * ((relativeEntropy (densityMeasure (F.density s)) (haar d)).toReal +
        ∫ x, frozenPotential A (ν : Measure (Torus d)) x
          ∂(densityMeasure (F.density s) : Measure (Torus d)) +
        Real.log (frozenPartition A (ν : Measure (Torus d)))) := by
    unfold frozenEntropy
    rw [ENNReal.toReal_sum fun s _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin s)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (F.weight_nonneg s),
      (budget_entropy_frozen A ν (F.density s)).2]
  have hbary := budget_integral_barycenter F (frozenPotential_continuous A (ν : Measure (Torus d)))
  have hpot := budget_integral_frozenPotential A ν
  rw [hsum]
  have e : ∀ s, F.weight s * ((relativeEntropy (densityMeasure (F.density s)) (haar d)).toReal +
      ∫ x, frozenPotential A (ν : Measure (Torus d)) x
        ∂(densityMeasure (F.density s) : Measure (Torus d)) +
      Real.log (frozenPartition A (ν : Measure (Torus d)))) =
      F.weight s * (relativeEntropy (densityMeasure (F.density s)) (haar d)).toReal +
      F.weight s * ∫ x, frozenPotential A (ν : Measure (Torus d)) x
        ∂(densityMeasure (F.density s) : Measure (Torus d)) +
      F.weight s * Real.log (frozenPartition A (ν : Measure (Torus d))) := fun s => by ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← hbary, hpot, ← Finset.sum_mul,
    F.weight_sum]
  ring

/-- `∫ exp(-u) dμ = exp(∫ W*μ dν - ∬ W dμ²) Z_ν / Z_μ` at a Gibbs fixed point `μ = P μ`. -/
theorem integral_exp_neg_kernelPotential (A : InteractionData d)
    (μ ν : ProbabilityMeasure (Torus d))
    (h : (μ : Measure (Torus d)) = (frozenGibbs A μ).measure) :
    ∫ x, Real.exp (-kernelPotential A μ ν x) ∂(μ : Measure (Torus d)) =
      Real.exp (∫ z, interactionConvolution A μ z ∂(ν : Measure (Torus d)) - meanInteraction A μ)
        * frozenPartition A (ν : Measure (Torus d)) / frozenPartition A (μ : Measure (Torus d)) := by
  have hm : (μ : Measure (Torus d)) =
      (haar d).tilted (fun x => -frozenPotential A (μ : Measure (Torus d)) x) :=
    h.trans (budget_measure_eq_tilted A μ)
  set c : ℝ := ∫ z, interactionConvolution A μ z ∂(ν : Measure (Torus d)) - meanInteraction A μ
    with hc
  have ht := integral_tilted (μ := haar d) (fun x => -frozenPotential A (μ : Measure (Torus d)) x)
    (fun x => Real.exp (-kernelPotential A μ ν x))
  rw [← hm] at ht
  rw [ht]
  have hpt : ∀ x, (Real.exp (-frozenPotential A (μ : Measure (Torus d)) x) /
      ∫ x, Real.exp (-frozenPotential A (μ : Measure (Torus d)) x) ∂haar d) •
        Real.exp (-kernelPotential A μ ν x) =
      Real.exp (c + -frozenPotential A (ν : Measure (Torus d)) x) /
        frozenPartition A (μ : Measure (Torus d)) := fun x => by
    rw [smul_eq_mul, div_mul_eq_mul_div, ← Real.exp_add, kernelPotential_eq]
    unfold frozenPartition
    congr 2
    unfold frozenPotential interactionConvolution
    simp only [hc]
    unfold interactionConvolution
    ring
  simp_rw [hpt, Real.exp_add]
  rw [integral_div, integral_const_mul]
  rfl

/-- **STR008.** Exact frozen-reference species energy identity. For a free-energy minimizer `μ`,
and every finite absolute family `F` with barycenter `ν`, `u = K * (ν - μ)` and
`Q = ∬ K d(ν - μ)²`:
`E_fr` is finite, `∫ exp(-u) dμ > 0`, `∫ u dμ = 0`, `log ∫ exp(-u) dμ ≥ 0` and
`Gθ = E_fr - Q/2 - log ∫ exp(-u) dμ`. -/
theorem speciesGap_eq_frozenEntropy_centeredCorrection (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A) {μ : ProbabilityMeasure (Torus d)}
    (hμ : freeEnergy A μ = freeEnergyMinimum A) (F : SpeciesFamily d) :
    frozenEntropy A F ≠ ⊤ ∧
    ∫ x, kernelPotential A μ (densityMeasure (barycenter F)) x ∂(μ : Measure (Torus d)) = 0 ∧
    0 < ∫ x, Real.exp (-kernelPotential A μ (densityMeasure (barycenter F)) x)
      ∂(μ : Measure (Torus d)) ∧
    0 ≤ Real.log (∫ x, Real.exp (-kernelPotential A μ (densityMeasure (barycenter F)) x)
      ∂(μ : Measure (Torus d))) ∧
    (speciesGap A F : ℝ) = (frozenEntropy A F).toReal -
      centeredCorrection A μ (densityMeasure (barycenter F)) / 2 -
      Real.log (∫ x, Real.exp (-kernelPotential A μ (densityMeasure (barycenter F)) x)
        ∂(μ : Measure (Torus d))) := by
  set ν : ProbabilityMeasure (Torus d) := densityMeasure (barycenter F) with hν
  obtain ⟨hne, hE⟩ := frozenEntropy_toReal_eq A F
  have hfix := minimizer_eq_frozenGibbs A hμ
  obtain ⟨-, -, hall⟩ := gibbsMinimizer_exists A hLip b
  obtain ⟨-, -, ⟨ρ, hρ⟩, -⟩ := hall μ hμ
  have hint := integral_exp_neg_kernelPotential A μ ν hfix
  have hZν := frozenPartition_pos A (ν : Measure (Torus d))
  have hZμ := frozenPartition_pos A (μ : Measure (Torus d))
  have hpos : 0 < ∫ x, Real.exp (-kernelPotential A μ ν x) ∂(μ : Measure (Torus d)) := by
    rw [hint]; positivity
  have hzero := integral_kernelPotential_self A μ ν
  have hge : 0 ≤ Real.log (∫ x, Real.exp (-kernelPotential A μ ν x) ∂(μ : Measure (Torus d))) := by
    apply Real.log_nonneg
    have hu : Integrable (kernelPotential A μ ν) (μ : Measure (Torus d)) :=
      fei_integrable (kernelPotential_continuous A μ ν) μ
    have he : Integrable (fun x => Real.exp (-kernelPotential A μ ν x)) (μ : Measure (Torus d)) :=
      fei_integrable (Real.continuous_exp.comp (kernelPotential_continuous A μ ν).neg) μ
    have h2 : ∫ x, (-kernelPotential A μ ν x + 1) ∂(μ : Measure (Torus d)) ≤
        ∫ x, Real.exp (-kernelPotential A μ ν x) ∂(μ : Measure (Torus d)) :=
      integral_mono (hu.neg.add (integrable_const (1 : ℝ))) he
        (fun x => Real.add_one_le_exp (-kernelPotential A μ ν x))
    have hn : Integrable (fun x => -kernelPotential A μ ν x) (μ : Measure (Torus d)) := hu.neg
    rw [integral_add hn (integrable_const _), integral_neg, hzero] at h2
    simpa using h2
  refine ⟨hne, hzero, hpos, hge, ?_⟩
  -- the minimum value
  have hfin := (absoluteDensity_entropy_finite ρ).2.2.1
  have hfin' : relativeEntropy (μ : Measure (Torus d)) (haar d) ≠ ⊤ := by rw [← hρ]; exact hfin
  have hFstar : freeEnergyMinimumReal A =
      (relativeEntropy (μ : Measure (Torus d)) (haar d)).toReal + potentialEnergy A μ +
        (1 / 2 : ℝ) * interactionEnergy A μ := by
    have h1 := freeEnergy_eq_real A μ hfin'
    rw [hμ, ← coe_freeEnergyMinimumReal] at h1
    exact EReal.coe_eq_coe_iff.mp h1
  have hfp : (densityMeasure ρ : Measure (Torus d)) =
      (frozenGibbs A (densityMeasure ρ)).measure := by rw [hρ]; exact hfix
  have hent := fixedPoint_entropy_eq A ρ hfp
  rw [hρ] at hent
  have hQ := centeredCorrection_eq A μ ν
  rw [meanInteraction_eq] at hQ
  have hlog : Real.log (∫ x, Real.exp (-kernelPotential A μ ν x) ∂(μ : Measure (Torus d))) =
      (∫ z, interactionConvolution A μ z ∂(ν : Measure (Torus d)) -
        interactionEnergy A (μ : Measure (Torus d))) +
      Real.log (frozenPartition A (ν : Measure (Torus d))) -
      Real.log (frozenPartition A (μ : Measure (Torus d))) := by
    rw [hint, meanInteraction_eq, Real.log_div (by positivity) hZμ.ne',
      Real.log_mul (Real.exp_pos _).ne' hZν.ne', Real.log_exp]
  rw [hlog, hQ, coe_speciesGap, speciesRawGap, hE, hFstar]
  linarith

end DGPS.Structural
