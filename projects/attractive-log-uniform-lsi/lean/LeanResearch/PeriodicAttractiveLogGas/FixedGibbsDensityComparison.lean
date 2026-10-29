import LeanResearch.PeriodicAttractiveLogGas.FixedWeightFunctionalInequalities
import LeanResearch.PeriodicAttractiveLogGas.BoundedPerturbation
import LeanResearch.PeriodicAttractiveLogGas.GreenNormalization

/-! Exact bounded perturbation between the periodic product distance
weight and the canonical Green Gibbs law. The two normalizing constants
are retained separately, giving the single source variance factor. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators
namespace PeriodicAttractiveLogGas.FixedGibbsDensityComparison
open FixedWeightProbability

def halfFactor (N : ℕ) (β₀ C₀ : ℝ) : ℝ :=
  Real.exp (β₀ * C₀ * ((N : ℝ) - 1) / 2)

def factor (N : ℕ) (β₀ C₀ : ℝ) : ℝ :=
  Real.exp (β₀ * ((N : ℝ) - 1) * C₀)

lemma factor_eq_square (N : ℕ) (β₀ C₀ : ℝ) :
    factor N β₀ C₀ = halfFactor N β₀ C₀ ^ 2 := by
  unfold factor halfFactor
  rw [← Real.exp_nat_mul]
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

lemma pair_reverse {a C₀ : ℝ} (ha : 0 ≤ a)
    (hbound : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    {z : Torus} (hz : z ≠ 0) :
    torusEuclideanNorm z ^ (-a) ≤ Real.exp (a * C₀) * Real.exp (a * regularGreenRepresentative z) := by
  rw [Real.rpow_def_of_pos ((torusEuclideanNorm_pos_iff z).mpr hz), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (abs_le.mp (hbound z hz)).1 ha
  nlinarith only [hh]

lemma exponent_bound {N : ℕ} (hN : 2 ≤ N) {β β₀ C₀ : ℝ}
    (hC₀ : 0 ≤ C₀) (hle : β ≤ β₀) :
    Real.exp (β * C₀ * ((N : ℝ) - 1) / 2) ≤ halfFactor N β₀ C₀ := by
  apply Real.exp_le_exp.mpr
  have hn : 0 ≤ (N : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ N by omega))
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hC₀) hn) (by norm_num)

lemma pointwise_weights {N : ℕ} (hN : 2 ≤ N) {β β₀ C₀ : ℝ}
    (hC₀ : 0 ≤ C₀)
    (hbound : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hβ : 0 ≤ β) (hle : β ≤ β₀) {X : Configuration N} (hX : X ∉ collisionSet N) :
    gibbsWeight regularGreenRepresentative N β X ≤
        halfFactor N β₀ C₀ * torusPairWeight N (β / N) X ∧
      torusPairWeight N (β / N) X ≤ halfFactor N β₀ C₀ * gibbsWeight regularGreenRepresentative N β X := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hexp := exponent_bound hN hC₀ hle
  constructor
  · exact (gibbsWeight_le_greenFixedMajorant hC₀ hbound N hN hβ le_rfl hX).trans
      (mul_le_mul_of_nonneg_right hexp (torusPairWeight_nonneg _ _ _))
  · have hp (ij : Fin N × Fin N) (hij : ij ∈ planarOrderedPairs N) :
        torusEuclideanDist (X ij.1) (X ij.2) ^ (-(β / (N : ℝ))) ≤
          Real.exp ((β / (N : ℝ)) * C₀) * Real.exp ((β / (N : ℝ)) *
            regularGreenRepresentative (X ij.1 - X ij.2)) := by
      apply pair_reverse (div_nonneg hβ hn.le) hbound
      intro hz
      exact hX ⟨ij.1, ij.2, (mem_planarOrderedPairs ij |>.mp hij).ne, sub_eq_zero.mp hz⟩
    have hprod := Finset.prod_le_prod₀
      (fun ij _ => Real.rpow_nonneg (torusEuclideanDist_nonneg (X ij.1) (X ij.2)) _) hp
    rw [Finset.prod_mul_distrib, Finset.prod_const, card_planarOrderedPairs,
      ← Real.exp_nat_mul, Nat.cast_choose_two, ← gibbsWeight_eq_prod_orderedPairs] at hprod
    have he : ((N : ℝ) * ((N : ℝ) - 1) / 2) * ((β / (N : ℝ)) * C₀) =
        β * C₀ * ((N : ℝ) - 1) / 2 := by field_simp [hn.ne']
    rw [he] at hprod
    exact hprod.trans (mul_le_mul_of_nonneg_right hexp (gibbsWeight_pos _ _ _ _).le)

/-- Normalization of a literal density comparison; no equality between
the two normalizing constants is imposed. -/
lemma normalized_measure_comparison {α : Type*} [MeasurableSpace α] {σ : Measure α}
    {f g : α → ℝ} {u v C : ℝ} (hu : 0 < u) (hv : 0 < v) (hC : 0 ≤ C)
    (hg : Measurable g) (hfg : ∀ᵐ x ∂σ, f x ≤ C * g x) :
    (ENNReal.ofReal u)⁻¹ • σ.withDensity (fun x => ENNReal.ofReal (f x)) ≤
      ENNReal.ofReal (C * v / u) •
        ((ENNReal.ofReal v)⁻¹ • σ.withDensity (fun x => ENNReal.ofReal (g x))) := by
  have hraw : σ.withDensity (fun x => ENNReal.ofReal (f x)) ≤
      ENNReal.ofReal C • σ.withDensity (fun x => ENNReal.ofReal (g x)) := by
    have hh := withDensity_mono (hfg.mono fun x hx => ENNReal.ofReal_le_ofReal hx)
    rw [show (fun x => ENNReal.ofReal (C * g x)) =
      (ENNReal.ofReal C) • (fun x => ENNReal.ofReal (g x)) by
        funext x; exact ENNReal.ofReal_mul hC] at hh
    rw [withDensity_smul _ hg.ennreal_ofReal] at hh
    exact hh
  calc
    _ ≤ (ENNReal.ofReal u)⁻¹ • (ENNReal.ofReal C • σ.withDensity (fun x => ENNReal.ofReal (g x))) := by
      intro S
      simpa only [Measure.smul_apply, smul_eq_mul] using
        mul_le_mul_of_nonneg_left (hraw S) (show 0 ≤ (ENNReal.ofReal u)⁻¹ from zero_le)
    _ = _ := by
      rw [smul_smul, smul_smul]
      congr 1
      rw [← ENNReal.ofReal_inv_of_pos hu, ← ENNReal.ofReal_inv_of_pos hv,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr hu.le),
        ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg hC hv.le) hu.le)]
      congr 1
      field_simp [hu.ne', hv.ne']

/-- Source two-sided normalized density comparison. The product of the
actual factors is exactly the common oscillation factor, not its square. -/
theorem comparison_factors {N : ℕ} (hN : 2 ≤ N) {β β₀ C₀ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (hC₀ : 0 ≤ C₀)
    (hbound : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hβ : 0 ≤ β) (hle : β ≤ β₀) :
    ∃ u v : ℝ, 0 < u ∧ 0 < v ∧ u * v = factor N β₀ C₀ ∧
      u ≤ factor N β₀ C₀ ∧ v ≤ factor N β₀ C₀ ∧
      gibbsMeasure greenRealRepresentative N β ≤ ENNReal.ofReal u • law N (β / N) ∧
      law N (β / N) ≤ ENNReal.ofReal v • gibbsMeasure greenRealRepresentative N β := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha : 0 ≤ β / (N : ℝ) := div_nonneg hβ hn.le
  have haa : β / (N : ℝ) ≤ FixedWeightConstants.exponent N β₀ :=
    div_le_div_of_nonneg_right hle hn.le
  let Zg := (partitionFunction regularGreenRepresentative N β).toReal
  let Zw := normalizer N (β / N)
  let H := halfFactor N β₀ C₀
  have hgfin := regularGreen_partitionFunction_ne_top N hN hβ (hle.trans_lt hsub)
  have hZg : 0 < Zg := ENNReal.toReal_pos
    (partitionFunction_ne_zero regularGreenRepresentative_measurable N β) hgfin
  have hZw : 0 < Zw := zero_lt_one.trans_le (normalizer_bounds hN hβ₀ hsub ha haa).1
  have hH : 0 < H := Real.exp_pos _
  have hgof : ENNReal.ofReal Zg = partitionFunction regularGreenRepresentative N β :=
    ENNReal.ofReal_toReal hgfin
  have hnc : ∀ᵐ X ∂referenceMeasure N, X ∉ collisionSet N := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using collisionSet_null N
  have hw := hnc.mono fun X hX => pointwise_weights hN hC₀ hbound hβ hle hX
  let u := H * Zw / Zg
  let v := H * Zg / Zw
  have hu : 0 < u := div_pos (mul_pos hH hZw) hZg
  have hv : 0 < v := div_pos (mul_pos hH hZg) hZw
  have hμν : gibbsMeasure greenRealRepresentative N β ≤ ENNReal.ofReal u • law N (β / N) := by
    have hh := normalized_measure_comparison hZg hZw hH.le
      (measurable_torusPairWeight N (β / N)) (hw.mono fun _ hx => hx.1)
    rw [hgof] at hh
    change gibbsMeasure regularGreenRepresentative N β ≤ ENNReal.ofReal u • law N (β / N) at hh
    simpa only [regularGreen_gibbsMeasure_eq] using hh
  have hνμ : law N (β / N) ≤ ENNReal.ofReal v • gibbsMeasure greenRealRepresentative N β := by
    have hh := normalized_measure_comparison hZw hZg hH.le
      (measurable_gibbsWeight regularGreenRepresentative_measurable N β) (hw.mono fun _ hx => hx.2)
    rw [hgof] at hh
    change law N (β / N) ≤ ENNReal.ofReal v • gibbsMeasure regularGreenRepresentative N β at hh
    simpa only [regularGreen_gibbsMeasure_eq] using hh
  have huv : u * v = factor N β₀ C₀ := by
    rw [factor_eq_square]
    change (H * Zw / Zg) * (H * Zg / Zw) = H ^ 2
    field_simp [hZg.ne', hZw.ne']
  let : IsProbabilityMeasure (law N (β / N)) := law_probability hN hβ₀ hsub ha haa
  let : IsProbabilityMeasure (gibbsMeasure greenRealRepresentative N β) :=
    isProbabilityMeasure_greenGibbs N hN hβ (hle.trans_lt hsub)
  have hu1 : 1 ≤ u := by
    simpa only [integral_const, probReal_univ, one_smul, mul_one] using
      BoundedPerturbation.integral_nonneg_comparison hu.le hμν (fun _ => zero_le_one)
        (integrable_const (1 : ℝ))
  have hv1 : 1 ≤ v := by
    simpa only [integral_const, probReal_univ, one_smul, mul_one] using
      BoundedPerturbation.integral_nonneg_comparison hv.le hνμ (fun _ => zero_le_one)
        (integrable_const (1 : ℝ))
  refine ⟨u, v, hu, hv, huv, ?_, ?_, hμν, hνμ⟩
  · rw [← huv]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hv1 hu.le
  · rw [← huv]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hu1 hv.le

end PeriodicAttractiveLogGas.FixedGibbsDensityComparison
