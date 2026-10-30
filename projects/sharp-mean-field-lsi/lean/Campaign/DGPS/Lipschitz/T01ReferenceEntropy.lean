import DGPS.Lipschitz.T01ReferenceMoments
import DGPS.Variational.EquilibriumGibbs
import SharpSymmetricLSI.Paper.KLLsc

/-!
# Reference entropy comparison for arbitrary particle laws

The uniform density moment gives the reference entropy bound for arbitrary laws by entropy
duality. The test is `(p-1) log(dP/dQ)` under `P`; its exponential moment is precisely the
`p`th density moment under `Q`. No permutation averaging or symmetry premise is needed.
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace DGPS.Lipschitz

/-- A density moment bounds the entropy change of reference for every law, including the
infinite-entropy branch. The displayed constant depends only on the moment bound and exponent. -/
theorem t01_reference_entropy_of_density_moment {d : ℕ} (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) (N : ℕ+)
    {p C : ℝ} (hp : 1 < p)
    (hC : ∫ X, centeredParticleDensity A μ N X ^ p
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ C)
    (ν : Measure (ParticleSpace d N)) [IsProbabilityMeasure ν] :
    klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤
      ENNReal.ofReal ((p + Real.log (max C 1)) / (p - 1)) * (klDiv ν (particleLaw A N) + 1) := by
  let Q := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  let P := particleLaw A N
  let q := centeredParticleDensity A μ N
  let f : ParticleSpace d N → ℝ := fun X => Real.log (q X)
  let L := Real.log (max C 1)
  let D := (p + L) / (p - 1)
  have ht : 0 < p - 1 := by linarith
  have hL : 0 ≤ L := Real.log_nonneg (le_max_right _ _)
  have hD : 0 < D := div_pos (by linarith) ht
  change klDiv ν Q ≤ ENNReal.ofReal D * (klDiv ν P + 1)
  by_cases hfin : klDiv ν P = ⊤
  · rw [hfin, top_add, ENNReal.mul_top (by simpa using hD)]
    exact le_top
  have hqpos : ∀ X, 0 < q X := centeredParticleDensity_pos A μ N
  have hfc : Continuous f :=
    (centeredParticleDensity_continuous A μ N).log (fun X => (hqpos X).ne')
  obtain ⟨B, hB⟩ := SharpLSI.exists_bound_of_continuous hfc
  have hf : Measurable f := hfc.measurable
  have hZ : ∫ X, Real.exp (f X) ∂Q = 1 := by
    simpa only [f, Real.exp_log (hqpos _)] using centeredParticleDensity_mass_one A μ hμ N
  have hPf : Q.tilted f = P := by
    unfold Measure.tilted
    rw [hZ]
    simp only [f, Real.exp_log (hqpos _), div_one]
    exact (particleLaw_eq_centered_reference A μ hμ N).symm
  have hνQ : klDiv ν Q ≠ ⊤ := by
    have hνf : klDiv ν (Q.tilted f) ≠ ⊤ := by rwa [hPf]
    exact (klDiv_tilted_ne_top_iff hf hB).1 hνf
  have hid := (klDiv_tilted_forward hf hB hνQ).2
  rw [hPf, hZ, Real.log_one, add_zero] at hid
  have hgB : ∀ X, |(p - 1) * f X| ≤ (p - 1) * B := by
    intro X
    rw [abs_mul, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left (hB X) ht.le
  have hmoment : ∫ X, Real.exp ((p - 1) * f X) ∂P = ∫ X, q X ^ p ∂Q := by
    rw [integral_particleLaw_eq_centered A μ hμ N]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    change q X * Real.exp ((p - 1) * Real.log (q X)) = q X ^ p
    rw [Real.rpow_def_of_pos (hqpos X)]
    conv_lhs => lhs; rw [← Real.exp_log (hqpos X)]
    rw [← Real.exp_add]
    congr 1
    ring
  have hmoment_pos : 0 < ∫ X, Real.exp ((p - 1) * f X) ∂P :=
    integral_exp_pos (integrable_exp_of_bound (ν := P) (hf.const_mul (p - 1)) hgB)
  have hlogmoment : Real.log (∫ X, Real.exp ((p - 1) * f X) ∂P) ≤ L := by
    apply Real.log_le_log hmoment_pos
    rw [hmoment]
    exact hC.trans (le_max_left _ _)
  have hdv := SharpLSI.dvFun_le_klDiv (ρ := ν) (ν := P) (hf.const_mul (p - 1)) hgB
  rw [← ENNReal.ofReal_toReal hfin, EReal.coe_ennreal_ofReal,
    max_eq_left ENNReal.toReal_nonneg] at hdv
  have hdv' := EReal.coe_le_coe_iff.mp hdv
  unfold SharpLSI.dvFun at hdv'
  rw [integral_const_mul] at hdv'
  have hHP : 0 ≤ (klDiv ν P).toReal := ENNReal.toReal_nonneg
  have hreal : (klDiv ν Q).toReal ≤ D * ((klDiv ν P).toReal + 1) := by
    dsimp [D]
    rw [div_mul_eq_mul_div, le_div_iff₀ ht]
    nlinarith [mul_nonneg hL hHP]
  calc klDiv ν Q = ENNReal.ofReal (klDiv ν Q).toReal := (ENNReal.ofReal_toReal hνQ).symm
    _ ≤ ENNReal.ofReal (D * ((klDiv ν P).toReal + 1)) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal D * (klDiv ν P + 1) := by
      rw [ENNReal.ofReal_mul hD.le, ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one,
        ENNReal.ofReal_toReal hfin, ENNReal.ofReal_one]

/-- Uniform reference entropy comparison for every particle law, derived from genuine
mean-field entropy coercivity and the uniform density moments. -/
theorem t01_reference_entropy_of_entropy_coercivity {d : ℕ} (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hc : ∀ ρ : ProbabilityMeasure (Torus d),
      klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d)) ≠ ⊤ →
      c * (klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d))).toReal ≤
        (klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d))).toReal +
          (1 / 2 : ℝ) * ∫ p, DGPS.centeredKernel A μ p.1 p.2
            ∂((ρ : Measure (Torus d)).prod (ρ : Measure (Torus d)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ν : Measure (ParticleSpace d N)) [IsProbabilityMeasure ν],
      klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤
        ENNReal.ofReal C * (klDiv ν (particleLaw A N) + 1) := by
  obtain ⟨C, p, -, hp, hN⟩ := t01_reference_density_moments_of_entropy_coercivity A μ hμ hc0 hc1 hc
  refine ⟨(p + Real.log (max C 1)) / (p - 1), ?_, fun N ν _ => ?_⟩
  · exact div_pos (by linarith [Real.log_nonneg (le_max_right C 1)]) (by linarith)
  · exact t01_reference_entropy_of_density_moment A μ hμ N hp (hN N).2 ν

end DGPS.Lipschitz
