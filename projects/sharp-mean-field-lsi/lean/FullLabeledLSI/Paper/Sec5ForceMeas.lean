import FullLabeledLSI.Paper.Sec5ForceDefs
import FullLabeledLSI.Paper.Sec5Birthday

/-!
# Lemma 5.5: measurability and disintegration facts for `B_S`
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d N : ℕ}

/-- `ρ̄_S` as a function of the revealed values `a = X_S`. -/
noncomputable def barCondA (ν : Measure (Config N d)) [IsFiniteMeasure ν] (S : Finset (Fin N))
    (a : S → Torus d) : Measure (Torus d) :=
  ((Sᶜ.card : ℝ≥0∞)⁻¹) • ∑ i ∈ Sᶜ, condLawS ν S i a

theorem barCond_eq (ν : Measure (Config N d)) [IsFiniteMeasure ν] (S : Finset (Fin N))
    (X : Config N d) : barCond ν S X = barCondA ν S (restrictS S X) := rfl

theorem isProbabilityMeasure_barCondA (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (S : Finset (Fin N)) (hS : 1 ≤ Sᶜ.card) (a : S → Torus d) :
    IsProbabilityMeasure (barCondA ν S a) := by
  have hR : Sᶜ.Nonempty := Finset.card_pos.mp (by omega)
  exact birthday_avg_isProb Sᶜ hR (fun i => condLawS ν S i a)

/-- `barCondA` as a kernel. -/
noncomputable def barKer (ν : Measure (Config N d)) [IsFiniteMeasure ν] (S : Finset (Fin N)) :
    Kernel (S → Torus d) (Torus d) where
  toFun := barCondA ν S
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [barCondA, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
    exact Measurable.const_mul (Finset.measurable_sum _ fun i _ => Kernel.measurable_coe _ hs) _

theorem barKer_apply (ν : Measure (Config N d)) [IsFiniteMeasure ν] (S : Finset (Fin N))
    (a : S → Torus d) : barKer ν S a = barCondA ν S a := rfl

instance (ν : Measure (Config N d)) [IsProbabilityMeasure ν] (S : Finset (Fin N)) :
    IsFiniteKernel (barKer ν S) := by
  refine ⟨⟨1, ENNReal.one_lt_top, fun a => ?_⟩⟩
  show barCondA ν S a Set.univ ≤ 1
  rcases Nat.eq_zero_or_pos Sᶜ.card with h0 | h0
  · simp [barCondA, h0]
  · have := isProbabilityMeasure_barCondA ν S h0 a
    exact (measure_univ (μ := barCondA ν S a)).le

/-- Integral against `barCondA` is the average of integrals against `condLawS`. -/
theorem integral_barCondA (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (S : Finset (Fin N)) (a : S → Torus d) (g : Torus d → ℝ) (hg : Measurable g) {c : ℝ}
    (hc : ∀ x, |g x| ≤ c) :
    ∫ x, g x ∂barCondA ν S a = ((Sᶜ.card : ℝ)⁻¹) * ∑ i ∈ Sᶜ, ∫ x, g x ∂condLawS ν S i a := by
  unfold barCondA
  rw [integral_smul_measure, integral_finsetSum_measure]
  · rw [smul_eq_mul]
    congr 1
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · intro i _
    exact Integrable.of_bound hg.aestronglyMeasurable c
      (Filter.Eventually.of_forall fun z => by simpa using hc z)

/-- Disintegration for one label. -/
theorem integral_eq_condLawS (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (S : Finset (Fin N)) (i : Fin N) (f : (S → Torus d) → Torus d → ℝ)
    (hf : Measurable fun p : (S → Torus d) × Torus d => f p.1 p.2) {c : ℝ}
    (hc : ∀ a x, |f a x| ≤ c) :
    ∫ X, f (restrictS S X) (X i) ∂ν =
      ∫ X, ∫ x, f (restrictS S X) x ∂condLawS ν S i (restrictS S X) ∂ν := by
  set P0 : Measure (S → Torus d) := ν.map (restrictS S) with hP0def
  have hFm : Measurable fun a : S → Torus d => ∫ x, f a x ∂condLawS ν S i a :=
    (hf.stronglyMeasurable.integral_kernel_prod_right' (κ := condLawS ν S i)).measurable
  have hlaw : ν.map (fun X => (restrictS S X, X i)) = P0 ⊗ₘ condLawS ν S i :=
    (compProd_map_condDistrib (measurable_restrictS S).aemeasurable
      (measurable_pi_apply i).aemeasurable).symm
  have hBi : Integrable (fun q : (S → Torus d) × Torus d => f q.1 q.2) (P0 ⊗ₘ condLawS ν S i) :=
    Integrable.of_bound hf.aestronglyMeasurable c
      (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hc q.1 q.2)
  have e2 : ∫ X, f (restrictS S X) (X i) ∂ν = ∫ a, ∫ x, f a x ∂condLawS ν S i a ∂P0 := by
    rw [← integral_map ((measurable_restrictS S).prodMk (measurable_pi_apply i)).aemeasurable
      hf.aestronglyMeasurable, hlaw, Measure.integral_compProd hBi]
  rw [e2, hP0def, integral_map (measurable_restrictS S).aemeasurable hFm.aestronglyMeasurable]

section
variable {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}

/-- Measurability of `(a, x) ↦ B_{S,k}(a, x)`. -/
theorem measurable_BSA (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (S : Finset (Fin N)) (k : Fin d) :
    Measurable fun p : (S → Torus d) × Torus d => ∫ y, bF p.2 y k ∂barCondA ν S p.1 := by
  have hf : Measurable fun q : ((S → Torus d) × Torus d) × Torus d => bF q.1.2 q.2 k :=
    (hB.meas k).comp (measurable_fst.snd.prodMk measurable_snd)
  have h := hf.stronglyMeasurable.integral_kernel_prod_right'
    (κ := (barKer ν S).comap (Prod.fst : (S → Torus d) × Torus d → S → Torus d) measurable_fst)
  exact h.measurable

theorem measurable_BS_comp (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (S : Finset (Fin N)) (i : Fin N) (k : Fin d) :
    Measurable fun X : Config N d => BS bF ν S X (X i) k := by
  have h := (measurable_BSA hB ν S k).comp
    ((measurable_restrictS S).prodMk (measurable_pi_apply i))
  exact h

theorem abs_BS_le (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (S : Finset (Fin N)) (hS : 1 ≤ Sᶜ.card) (X : Config N d) (x : Torus d) (k : Fin d) :
    |BS bF ν S X x k| ≤ Bb := by
  have := isProbabilityMeasure_barCondA ν S hS (restrictS S X)
  have h : IsProbabilityMeasure (barCond ν S X) := this
  have hnorm := norm_integral_le_of_norm_le_const (μ := barCond ν S X) (f := fun y => bF x y k)
    (C := Bb) (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB.bound x y k)
  simpa [BS] using hnorm

/-- `E_{i ∈ Sᶜ} ∫ f(X_S, X_i) dν = ∫ (∫ f(X_S, x) dρ̄_S(x)) dν` for a bounded measurable test. -/
theorem avg_integral_eq_barCond (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (S : Finset (Fin N)) (hS : 1 ≤ Sᶜ.card) (f : (S → Torus d) → Torus d → ℝ)
    (hf : Measurable fun p : (S → Torus d) × Torus d => f p.1 p.2) {c : ℝ}
    (hc : ∀ a x, |f a x| ≤ c) :
    ((Sᶜ.card : ℝ)⁻¹) * ∑ i ∈ Sᶜ, ∫ X, f (restrictS S X) (X i) ∂ν =
      ∫ X, ∫ x, f (restrictS S X) x ∂barCond ν S X ∂ν := by
  have hm : ∀ i, Measurable fun a : S → Torus d => ∫ x, f a x ∂condLawS ν S i a := fun i =>
    (hf.stronglyMeasurable.integral_kernel_prod_right' (κ := condLawS ν S i)).measurable
  have hb : ∀ i a, |∫ x, f a x ∂condLawS ν S i a| ≤ c := fun i a => by
    have := norm_integral_le_of_norm_le_const (μ := condLawS ν S i a) (f := fun x => f a x)
      (C := c) (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hc a y)
    simpa using this
  have hint : ∀ i, Integrable (fun X : Config N d =>
      ∫ x, f (restrictS S X) x ∂condLawS ν S i (restrictS S X)) ν := fun i =>
    Integrable.of_bound ((hm i).comp (measurable_restrictS S)).aestronglyMeasurable c
      (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hb i _)
  have hfa : ∀ a, Measurable fun x => f a x := fun a => hf.comp measurable_prodMk_left
  have step : ∀ X, ∫ x, f (restrictS S X) x ∂barCond ν S X =
      ((Sᶜ.card : ℝ)⁻¹) * ∑ i ∈ Sᶜ, ∫ x, f (restrictS S X) x ∂condLawS ν S i (restrictS S X) :=
    fun X => integral_barCondA ν S (restrictS S X) _ (hfa _) (hc _)
  simp_rw [step]
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hint i)]
  congr 1
  exact Finset.sum_congr rfl fun i _ => integral_eq_condLawS ν S i f hf hc

end

end SharpLSI.FL
