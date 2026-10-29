import SharpSymmetricLSI.Paper.GibbsVariational

/-!
# Lemma 2.4, the lower half (Phase 3, lane D; R5)

`N^{-1} log Z_N ≥ -F(ρ) + W(ρ,ρ)/(2N)` for every `ρ` with finite entropy, from the Gibbs
variational identity with the product state `ρ^{⊗N}` (Jensen route; no Varadhan lemma).
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The real part `ρ(V) + ½ W(ρ,ρ)` of the free energy. -/
noncomputable def energyMF (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ : Measure (Torus d)) :
    ℝ :=
  potE V ρ + interE W ρ ρ / 2

theorem log_partition_ge (hyp : Hyp V W KV KW) {N : ℕ} (hN : 1 ≤ N) {ρ : Measure (Torus d)}
    [IsProbabilityMeasure ρ] (h : klDiv ρ (haar d) ≠ ⊤) :
    -((klDiv ρ (haar d)).toReal + energyMF V W ρ) + interE W ρ ρ / (2 * N) ≤
      Real.log (partitionFn V W N) / N := by
  have hk := klDiv_pi (N := N) h
  have hg := klDiv_gibbs hyp hk.1
  have h0 : 0 ≤ (klDiv (Measure.pi fun _ : Fin N => ρ) (gibbs V W N)).toReal := ENNReal.toReal_nonneg
  rw [hg.2, hk.2, integral_hamiltonian_pi hyp hN] at h0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [le_div_iff₀ hN0]
  unfold energyMF
  have : interE W ρ ρ / (2 * N) * N = interE W ρ ρ / 2 := by field_simp
  nlinarith [this]

/-- `|W(ρ,η)| ≤ B` for `|W| ≤ B`. -/
theorem abs_interE_le {B : ℝ} (hB : ∀ x y, |W x y| ≤ B) (hW : Continuous (Function.uncurry W))
    {ρ η : Measure (Torus d)} [IsProbabilityMeasure ρ] [IsProbabilityMeasure η] :
    |interE W ρ η| ≤ B := by
  unfold interE
  refine (abs_integral_le_integral_abs).trans ?_
  have : ∀ y, |∫ x, W x y ∂ρ| ≤ B := fun y => by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |W x y| ∂ρ ≤ ∫ _, B ∂ρ := integral_mono_of_nonneg (Eventually.of_forall fun _ =>
          abs_nonneg _) (integrable_const B) (Eventually.of_forall fun x => hB x y)
      _ = B := by simp
  calc ∫ y, |∫ x, W x y ∂ρ| ∂η ≤ ∫ _, B ∂η := integral_mono_of_nonneg (Eventually.of_forall fun _ =>
        abs_nonneg _) (integrable_const B) (Eventually.of_forall this)
    _ = B := by simp

theorem abs_potE_le {B : ℝ} (hB : ∀ x, |V x| ≤ B) {ρ : Measure (Torus d)} [IsProbabilityMeasure ρ] :
    |potE V ρ| ≤ B := by
  unfold potE
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ x, |V x| ∂ρ ≤ ∫ _, B ∂ρ := integral_mono_of_nonneg (Eventually.of_forall fun _ =>
        abs_nonneg _) (integrable_const B) (Eventually.of_forall hB)
    _ = B := by simp

theorem freeEnergy_eq (ρ : Measure (Torus d)) (h : klDiv ρ (haar d) ≠ ⊤) :
    freeEnergy V W ρ = (((klDiv ρ (haar d)).toReal + energyMF V W ρ : ℝ) : EReal) := by
  unfold freeEnergy energyMF
  rw [← EReal.coe_ennreal_toReal h, ← EReal.coe_add]

theorem freeEnergy_top (ρ : Measure (Torus d)) (h : klDiv ρ (haar d) = ⊤) :
    freeEnergy V W ρ = ⊤ := by
  unfold freeEnergy
  rw [h]; simp

/-- `F_*` is a real number. -/
theorem Fstar_bounds (hyp : Hyp V W KV KW) : ∃ c C : ℝ, (c : EReal) ≤ Fstar V W ∧ Fstar V W ≤ C ∧
    ∀ ρ : ProbabilityMeasure (Torus d), (c : EReal) ≤ freeEnergy V W ρ := by
  obtain ⟨BV, hBV⟩ := exists_bound_of_continuous hyp.continuous_V
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  have hBW' : ∀ x y, |W x y| ≤ BW := fun x y => hBW (x, y)
  have hlow : ∀ ρ : ProbabilityMeasure (Torus d), ((-BV - BW / 2 : ℝ) : EReal) ≤ freeEnergy V W ρ := by
    intro ρ
    by_cases hk : klDiv (ρ : Measure (Torus d)) (haar d) = ⊤
    · rw [freeEnergy_top _ hk]; exact le_top
    rw [freeEnergy_eq _ hk, EReal.coe_le_coe_iff]
    have h1 := abs_potE_le hBV (ρ := (ρ : Measure (Torus d)))
    have h2 := abs_interE_le hBW' hyp.continuous_W (ρ := (ρ : Measure (Torus d)))
      (η := (ρ : Measure (Torus d)))
    have h3 : 0 ≤ (klDiv (ρ : Measure (Torus d)) (haar d)).toReal := ENNReal.toReal_nonneg
    unfold energyMF
    rw [abs_le] at h1 h2
    linarith [h1.1, h2.1]
  refine ⟨-BV - BW / 2, freeEnergy V W (haar d) |>.toReal, le_iInf hlow, ?_, hlow⟩
  have hF : freeEnergy V W (haar d) = (((0 : ℝ) + energyMF V W (haar d) : ℝ) : EReal) := by
    rw [freeEnergy_eq _ (by rw [klDiv_self]; simp), klDiv_self]; simp
  calc Fstar V W ≤ freeEnergy V W ((⟨haar d, inferInstance⟩ : ProbabilityMeasure (Torus d)) :
        Measure (Torus d)) := iInf_le _ _
    _ = _ := by
        change freeEnergy V W (haar d) = _
        rw [hF, EReal.toReal_coe]

end SharpLSI
