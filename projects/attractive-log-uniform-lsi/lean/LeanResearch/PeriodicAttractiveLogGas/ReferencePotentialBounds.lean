import LeanResearch.PeriodicAttractiveLogGas.ReferenceSelfTerms

/-! Global reference-potential bounds and actual finite cell normalizers.
These supply the fixed-N,J lower-bound justification in source lines
2698--2702; they do not construct the reference fixed point. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PeriodicAttractiveLogGas.ReferencePotentialBounds

open MeshCells LabelOccupations ReferenceResidual ReferenceSelfTerms
  MovingPoleCalculus CanonicalPairs

def globalPotentialBound (J : ℕ) : ℝ :=
  Real.exp 1 * (J : ℝ) ^ 2 * ∫ y, |regularGreenRepresentative y| ∂torusMeasure

theorem globalPotentialBound_nonneg (J : ℕ) : 0 ≤ globalPotentialBound J := by
  unfold globalPotentialBound
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
    (integral_nonneg fun y => abs_nonneg _)

/-- The actual normalized cell law is globally dominated by J squared times
Haar; the single reference density factor is retained exactly. -/
theorem reference_le_haar {J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    (μ : Measure Torus)
    (hμ : μ ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a) :
    μ ≤ ENNReal.ofReal (Real.exp 1 * (J : ℝ) ^ 2) • torusMeasure := by
  apply hμ.trans
  rw [meshCellMeasure, smul_smul, ENNReal.ofReal_mul (Real.exp_pos 1).le,
    ENNReal.ofReal_pow (Nat.cast_nonneg J), ENNReal.ofReal_natCast]
  exact smul_le_smul_left _ Measure.restrict_le_self

theorem green_translate_integrable (x : Torus) : Integrable (greenKernel x) torusMeasure :=
  (torusMeasure.measurePreserving_sub_left x).integrable_comp_of_integrable
    regularGreenRepresentative_integrable

theorem integral_abs_green_translate (x : Torus) :
    (∫ y, |greenKernel x y| ∂torusMeasure) =
      ∫ y, |regularGreenRepresentative y| ∂torusMeasure := by
  have hmp := torusMeasure.measurePreserving_sub_left x
  have hh := integral_map_of_stronglyMeasurable (μ := torusMeasure) hmp.measurable
    regularGreenRepresentative_measurable.norm.stronglyMeasurable
  rw [hmp.map_eq] at hh
  simpa only [greenKernel, Real.norm_eq_abs] using hh.symm

/-- Actual Haar L1 and density domination imply integrability at every pole,
including poles outside the reference cell, and a uniform absolute bound. -/
theorem global_potential_bound {J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    (μ : Measure Torus)
    (hμ : μ ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a) (x : Torus) :
    Integrable (greenKernel x) μ ∧ |potential μ x| ≤ globalPotentialBound J := by
  have hd := reference_le_haar hJ a μ hμ
  have hs := (green_translate_integrable x).smul_measure
    (c := ENNReal.ofReal (Real.exp 1 * (J : ℝ) ^ 2)) ENNReal.ofReal_ne_top
  have hi := hs.mono_measure hd
  refine ⟨hi, ?_⟩
  calc
    |potential μ x| ≤ ∫ y, |greenKernel x y| ∂μ := by
      simpa only [potential, Real.norm_eq_abs] using norm_integral_le_integral_norm (greenKernel x)
    _ ≤ ∫ y, |greenKernel x y| ∂(ENNReal.ofReal (Real.exp 1 * (J : ℝ) ^ 2) • torusMeasure) :=
      integral_mono_measure hd (Eventually.of_forall fun y => abs_nonneg _) hs.abs
    _ = globalPotentialBound J := by
      rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
        integral_abs_green_translate]
      rfl

theorem global_pairAverage_bound {J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    (μ ν : Measure Torus) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ν ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a) :
    Integrable (potential ν) μ ∧ |pairAverage μ ν| ≤ globalPotentialBound J := by
  have hb : ∀ᵐ x ∂μ, |potential ν x| ≤ globalPotentialBound J :=
    Eventually.of_forall fun x => (global_potential_bound hJ a ν hν x).2
  have hi : Integrable (potential ν) μ := (integrable_const (globalPotentialBound J)).mono'
    (measurable_potential ν).aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hb)
  refine ⟨hi, ?_⟩
  calc
    |pairAverage μ ν| ≤ ∫ x, |potential ν x| ∂μ := by
      simpa only [pairAverage, Real.norm_eq_abs] using norm_integral_le_integral_norm (potential ν)
    _ ≤ ∫ _, globalPotentialBound J ∂μ := integral_mono_ae hi.abs (integrable_const _) hb
    _ = _ := by simp

theorem measurable_averagePotential {J N : ℕ}
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) : Measurable (averagePotential μ η) :=
  (Finset.measurable_sum _ fun j _ => measurable_potential (μ (η j))).div_const _

theorem global_averagePotential_bound {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    (μ : MeshIndex J → Measure Torus)
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (η : LabelVector J N) (x : Torus) :
    |averagePotential μ η x| ≤ globalPotentialBound J := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [averagePotential, abs_div, abs_of_pos hNr, div_le_iff₀ hNr]
  calc
    |∑ j, potential (μ (η j)) x| ≤ ∑ j, |potential (μ (η j)) x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin N, globalPotentialBound J := Finset.sum_le_sum fun j _ =>
      (global_potential_bound hJ (η j) (μ (η j)) (hμ (η j)) x).2
    _ = _ := by simp [mul_comm]

/-- A finite fixed-N,J lower bound for the literal residual, sufficient for
the source entropy integrability passage. The sharp own-cell s_J is untouched. -/
theorem residualSum_lower_bound {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (η : LabelVector J N) (X : Fin N → Torus) :
    -(N : ℝ) * (greenLowerConstant + 3 * globalPotentialBound J) ≤
      ResidualExponential.residualSum μ η X := by
  classical
  let D := greenLowerConstant + 3 * globalPotentialBound J
  have hD : 0 ≤ D := add_nonneg greenLowerConstant_pos.le
    (mul_nonneg (by norm_num) (globalPotentialBound_nonneg J))
  have hr (i j : Fin N) : -D ≤ residual (μ (η i)) (μ (η j)) (X i) (X j) := by
    have hi := abs_le.mp (global_potential_bound hJ (η i) (μ (η i)) (hμ (η i)) (X j)).2
    have hj := abs_le.mp (global_potential_bound hJ (η j) (μ (η j)) (hμ (η j)) (X i)).2
    have hc := abs_le.mp (global_pairAverage_bound hJ (η j) (μ (η i)) (μ (η j)) (hμ (η j))).2
    have hg : -greenLowerConstant ≤ greenKernel (X i) (X j) := green_lower_bound _
    rw [residual_eq_source_order]
    dsimp [D]
    linarith
  have hu (i j : Fin N) : -D ≤ upperKernel
      (fun i j => residual (μ (η i)) (μ (η j))) i j (X i) (X j) := by
    by_cases hij : i < j
    · simpa only [upperKernel, hij, ite_true] using hr i j
    · simp only [upperKernel, hij, ite_false]
      linarith
  have hs : (N : ℝ) * ((N : ℝ) * (-D)) ≤ CanonicalPairs.canonicalSum
      (fun i j => residual (μ (η i)) (μ (η j))) X := by
    have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      Finset.sum_le_sum (s := Finset.univ) fun j _ => hu i j
    simpa only [canonicalSum, CanonicalDecoupling.pairSum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  change -(N : ℝ) * D ≤ _
  calc
    -(N : ℝ) * D = ((N : ℝ) * ((N : ℝ) * (-D))) / (N : ℝ) := by
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hs hNr.le

/-- Global boundedness supplies true finite positive normalizers for any
probability law, hence for every cell, whether occupied or not. -/
theorem reference_exponential_normalizer {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β)
    (ν : Measure Torus) [IsProbabilityMeasure ν] :
    Measurable (fun x => Real.exp (β * averagePotential μ η x)) ∧
    Integrable (fun x => Real.exp (β * averagePotential μ η x)) ν ∧
    0 < (∫ x, Real.exp (β * averagePotential μ η x) ∂ν) ∧
    Real.exp (-β * globalPotentialBound J) ≤ (∫ x, Real.exp (β * averagePotential μ η x) ∂ν) ∧
    (∫ x, Real.exp (β * averagePotential μ η x) ∂ν) ≤ Real.exp (β * globalPotentialBound J) := by
  have hm := ((measurable_averagePotential μ η).const_mul β).exp
  have hb (x : Torus) := abs_le.mp (global_averagePotential_bound hJ hN μ hμ η x)
  have hlo (x : Torus) : Real.exp (-β * globalPotentialBound J) ≤
      Real.exp (β * averagePotential μ η x) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (hb x).1 hβ
    nlinarith
  have hup (x : Torus) : Real.exp (β * averagePotential μ η x) ≤
      Real.exp (β * globalPotentialBound J) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hb x).2 hβ)
  have hi : Integrable (fun x => Real.exp (β * averagePotential μ η x)) ν :=
    (integrable_const (Real.exp (β * globalPotentialBound J))).mono' hm.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hup x)
  have hli : Real.exp (-β * globalPotentialBound J) ≤
      ∫ x, Real.exp (β * averagePotential μ η x) ∂ν := by
    simpa only [integral_const, probReal_univ, one_smul] using
      integral_mono (integrable_const _) hi hlo
  have hui : (∫ x, Real.exp (β * averagePotential μ η x) ∂ν) ≤
      Real.exp (β * globalPotentialBound J) := by
    simpa only [integral_const, probReal_univ, one_smul] using
      integral_mono hi (integrable_const _) hup
  exact ⟨hm, hi, (Real.exp_pos _).trans_le hli, hli, hui⟩

theorem cell_exponential_normalizer {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (a : MeshIndex J) :
    Integrable (fun x => Real.exp (β * averagePotential μ η x)) (meshCellMeasure J hJ a) ∧
    0 < (∫ x, Real.exp (β * averagePotential μ η x) ∂meshCellMeasure J hJ a) ∧
    (∫ x, Real.exp (β * averagePotential μ η x) ∂meshCellMeasure J hJ a) ≤
      Real.exp (β * globalPotentialBound J) := by
  have hh := reference_exponential_normalizer hJ hN μ hμ η hβ (meshCellMeasure J hJ a)
  exact ⟨hh.2.1, hh.2.2.1, hh.2.2.2.2⟩

/-- Original two-sided source densities, with all analytical conclusions
derived internally. No occupancy condition on the normalizer cell is imposed. -/
theorem source_density_bounds {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (w : MeshIndex J → Torus → ℝ≥0∞)
    (hμw : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (w a))
    (hw : ∀ a, ∀ᵐ x ∂meshCellMeasure J hJ a,
      ENNReal.ofReal (Real.exp (-1)) ≤ w a x ∧ w a x ≤ ENNReal.ofReal (Real.exp 1))
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) :
    (∀ a x, Integrable (greenKernel x) (μ a) ∧ |potential (μ a) x| ≤ globalPotentialBound J) ∧
    (∀ x, |averagePotential μ η x| ≤ globalPotentialBound J) ∧
    (∀ a b, Integrable (potential (μ b)) (μ a) ∧ |pairAverage (μ a) (μ b)| ≤ globalPotentialBound J) ∧
    (∀ X, -(N : ℝ) * (greenLowerConstant + 3 * globalPotentialBound J) ≤
      ResidualExponential.residualSum μ η X) ∧
    (∀ a, Integrable (fun x => Real.exp (β * averagePotential μ η x)) (meshCellMeasure J hJ a) ∧
      0 < (∫ x, Real.exp (β * averagePotential μ η x) ∂meshCellMeasure J hJ a) ∧
      (∫ x, Real.exp (β * averagePotential μ η x) ∂meshCellMeasure J hJ a) ≤
        Real.exp (β * globalPotentialBound J)) := by
  have hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a := by
    intro a
    rw [hμw a]
    exact NearLogMomentBounds.withDensity_le_exp_smul _ _ ((hw a).mono fun _ h => h.2)
  exact ⟨fun a x => global_potential_bound hJ a (μ a) (hμ a) x,
    global_averagePotential_bound hJ hN μ hμ η,
    fun a b => global_pairAverage_bound hJ b (μ a) (μ b) (hμ b),
    residualSum_lower_bound hJ hN μ hμ η,
    cell_exponential_normalizer hJ hN μ hμ η hβ⟩

end PeriodicAttractiveLogGas.ReferencePotentialBounds
