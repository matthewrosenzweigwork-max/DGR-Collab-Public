import DGPS.Structural.AmplitudeComparison

/-! A strict Poincare subrate supplies a normalized native test. This uses
only the infimum property, never existence of a first eigenfunction. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace DGPS.Examples.PolynomialSpecies

private def nativeScaleTest (μ : ProbabilityMeasure (Torus 1)) (f : WeakH1Test μ)
    (c : ℝ) : WeakH1Test μ where
  fn := fun x => c * f.fn x
  grad := fun x => c • f.grad x
  isWeak := {
    memLp := f.isWeak.memLp.const_mul c
    memLp_grad := f.isWeak.memLp_grad.const_smul c
    integrable := f.isWeak.integrable.const_mul c
    integrable_grad := f.isWeak.integrable_grad.smul c
    ibp := by
      intro φ hφ j
      simp only [PiLp.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul,
        f.isWeak.ibp φ hφ j]
      ring }

private theorem native_dirichlet_real (μ : ProbabilityMeasure (Torus 1)) (f : WeakH1Test μ) :
    dirichletEnergy μ f = ENNReal.ofReal (∫ x, ‖f.grad x‖ ^ 2 ∂(μ : Measure (Torus 1))) := by
  have hi := f.isWeak.memLp_grad.norm.integrable_sq
  unfold dirichletEnergy
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _)]
  apply lintegral_congr
  intro x
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- Original full weighted-H1 Rayleigh test with zero mean and unit mass,
strictly below the given finite rate. No spectral-attainment premise. -/
theorem native_normalized_rayleigh_witness (μ : ProbabilityMeasure (Torus 1))
    (r : ℝ≥0∞) (hr : r ≠ ⊤) (hPC : poincareRate μ < r) :
    ∃ f : WeakH1Test μ,
      (∫ x, f.fn x ∂(μ : Measure (Torus 1))) = 0 ∧
      (∫ x, f.fn x ^ 2 ∂(μ : Measure (Torus 1))) = 1 ∧
      (∫ x, ‖f.grad x‖ ^ 2 ∂(μ : Measure (Torus 1))) < r.toReal := by
  have hex : ∃ f : WeakH1Test μ, 0 < weightedVariance μ f.fn ∧ poincareQuotient μ f < r := by
    by_contra! hn
    exact (not_le_of_gt hPC) ((le_poincareRate_iff μ r).2 hn)
  obtain ⟨f, hV, hQ⟩ := hex
  let V := weightedVariance μ f.fn
  have hVpos : 0 < V := hV
  let m := ∫ x, f.fn x ∂(μ : Measure (Torus 1))
  let fc := Structural.shiftTest μ f m
  have hcm : (∫ x, fc.fn x ∂(μ : Measure (Torus 1))) = 0 := by
    change (∫ x, (f.fn x - m) ∂(μ : Measure (Torus 1))) = 0
    rw [integral_sub (f.isWeak.memLp.integrable (by norm_num)) (integrable_const m)]
    simp [m]
  have hcV : (∫ x, fc.fn x ^ 2 ∂(μ : Measure (Torus 1))) = V := rfl
  let c := 1 / Real.sqrt V
  have hs : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have hs2 : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV.le
  have hc2 : c ^ 2 = 1 / V := by
    dsimp only [c]
    rw [div_pow, one_pow, hs2]
  let g := nativeScaleTest μ fc c
  have hgm : (∫ x, g.fn x ∂(μ : Measure (Torus 1))) = 0 := by
    change (∫ x, c * fc.fn x ∂(μ : Measure (Torus 1))) = 0
    rw [integral_const_mul, hcm, mul_zero]
  have hgV : (∫ x, g.fn x ^ 2 ∂(μ : Measure (Torus 1))) = 1 := by
    change (∫ x, (c * fc.fn x) ^ 2 ∂(μ : Measure (Torus 1))) = 1
    simp_rw [mul_pow]
    rw [integral_const_mul, hcV, hc2]
    field_simp [hVpos.ne']
  let E := ∫ x, ‖f.grad x‖ ^ 2 ∂(μ : Measure (Torus 1))
  have hE : 0 ≤ E := integral_nonneg fun x => sq_nonneg _
  have hQreal : poincareQuotient μ f = ENNReal.ofReal (E / V) := by
    unfold poincareQuotient
    rw [native_dirichlet_real]
    exact (ENNReal.ofReal_div_of_pos hV).symm
  have hEQ : E / V < r.toReal := by
    rw [hQreal] at hQ
    have ht := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hr).2 hQ
    rw [ENNReal.toReal_ofReal (div_nonneg hE hVpos.le)] at ht
    exact ht
  have hgE : (∫ x, ‖g.grad x‖ ^ 2 ∂(μ : Measure (Torus 1))) = E / V := by
    change (∫ x, ‖c • f.grad x‖ ^ 2 ∂(μ : Measure (Torus 1))) = E / V
    simp_rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [integral_const_mul, hc2]
    dsimp only [E]
    ring
  exact ⟨g, hgm, hgV, hgE.trans_lt hEQ⟩

end DGPS.Examples.PolynomialSpecies
