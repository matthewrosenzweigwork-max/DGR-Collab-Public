import FullLabeledLSI.Paper.Sec5ForceMeas
import FullLabeledLSI.Paper.Sec5Products

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- Integral over `Fin 3 → T` against a product measure as an iterated integral. -/
theorem integral_pi3 {ρ : Measure (Torus d)} [IsProbabilityMeasure ρ]
    (H : Torus d × (Torus d × Torus d) → ℝ) (hm : Measurable H) {c : ℝ} (hb : ∀ q, |H q| ≤ c) :
    ∫ z : Fin 3 → Torus d, H (z 0, (z 1, z 2)) ∂Measure.pi (fun _ => ρ) =
      ∫ x, ∫ y, ∫ w, H (x, (y, w)) ∂ρ ∂ρ ∂ρ := by
  let Φ : (Fin 3 → Torus d) ≃ᵐ Torus d × (Torus d × Torus d) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Torus d) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
        (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Torus d)))
  have hΦ : MeasurePreserving Φ (Measure.pi (fun _ : Fin 3 => ρ)) (ρ.prod (ρ.prod ρ)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => ρ) 0).trans
      ((MeasurePreserving.id ρ).prod (measurePreserving_piFinTwo (fun _ : Fin 2 => ρ)))
  have h1 := hΦ.integral_comp' H
  have hΦz : ∀ z : Fin 3 → Torus d, Φ z = (z 0, (z 1, z 2)) := fun z => rfl
  simp_rw [hΦz] at h1
  rw [h1]
  have hi : Integrable H (ρ.prod (ρ.prod ρ)) := integrable_of_bdd _ hm hb
  rw [integral_prod _ hi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hi2 : Integrable (fun p : Torus d × Torus d => H (x, p)) (ρ.prod ρ) :=
    integrable_of_bdd _ (hm.comp (measurable_const.prodMk measurable_id)) (fun p => hb _)
  exact integral_prod _ hi2

section
variable {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}

theorem measurable_A3 (hB : ForceRep bF bΔ Bb) : Measurable (A3 bF) := by
  unfold A3
  refine Finset.measurable_sum _ fun k _ => ?_
  have h1 : Measurable fun z : Fin 3 → Torus d => bF (z 0) (z 1) k :=
    (hB.meas k).comp (f := fun z : Fin 3 → Torus d => (z 0, z 1))
      ((measurable_pi_apply (0 : Fin 3)).prodMk (measurable_pi_apply (1 : Fin 3)))
  have h2 : Measurable fun z : Fin 3 → Torus d => bF (z 0) (z 2) k :=
    (hB.meas k).comp (f := fun z : Fin 3 → Torus d => (z 0, z 2))
      ((measurable_pi_apply (0 : Fin 3)).prodMk (measurable_pi_apply (2 : Fin 3)))
  exact h1.mul h2

theorem abs_A3_le (hB : ForceRep bF bΔ Bb) (z : Fin 3 → Torus d) :
    |A3 bF z| ≤ d * Bb ^ 2 := by
  unfold A3
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ k ∈ (Finset.univ : Finset (Fin d)),
      |bF (z 0) (z 1) k * bF (z 0) (z 2) k| ≤ Bb ^ 2 := fun k _ => by
    rw [abs_mul, sq]
    exact mul_le_mul (hB.bound (z 0) (z 1) k) (hB.bound (z 0) (z 2) k) (abs_nonneg _)
      ((abs_nonneg _).trans (hB.bound (z 0) (z 1) k))
  refine (Finset.sum_le_sum this).trans ?_
  simp

/-- For a probability measure `ρ`, `∫ ∑_k (∫ b_k(x,y) dρ(y))² dρ(x) = ∫ A₃ d ρ^{⊗3}`. -/
theorem sq_mean_eq_A3 (hB : ForceRep bF bΔ Bb) (ρ : Measure (Torus d)) [IsProbabilityMeasure ρ] :
    ∫ x, ∑ k : Fin d, (∫ y, bF x y k ∂ρ) ^ 2 ∂ρ =
      ∫ z, A3 bF z ∂Measure.pi (fun _ : Fin 3 => ρ) := by
  set H : Torus d × (Torus d × Torus d) → ℝ :=
    fun q => ∑ k : Fin d, bF q.1 q.2.1 k * bF q.1 q.2.2 k with hH
  have hHm : Measurable H := by
    refine Finset.measurable_sum _ fun k _ => ?_
    have h1 : Measurable fun q : Torus d × (Torus d × Torus d) => bF q.1 q.2.1 k :=
      (hB.meas k).comp (measurable_fst.prodMk (measurable_snd.fst))
    have h2 : Measurable fun q : Torus d × (Torus d × Torus d) => bF q.1 q.2.2 k :=
      (hB.meas k).comp (measurable_fst.prodMk (measurable_snd.snd))
    exact h1.mul h2
  have hHb : ∀ q, |H q| ≤ d * Bb ^ 2 := fun q => by
    have := abs_A3_le hB (![q.1, q.2.1, q.2.2])
    simpa [A3, hH] using this
  have hA : A3 bF = fun z => H (z 0, (z 1, z 2)) := rfl
  rw [hA, integral_pi3 H hHm hHb]
  have hsec : ∀ (x : Torus d) (k : Fin d), Measurable fun y => bF x y k := fun x k =>
    (hB.meas k).comp (measurable_const.prodMk measurable_id)
  have hbd : ∀ (x : Torus d) (k : Fin d), Integrable (fun y => bF x y k) ρ := fun x k =>
    integrable_of_bdd ρ (hsec x k) (fun y => hB.bound x y k)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e1 : ∀ y, ∫ w, H (x, (y, w)) ∂ρ = ∑ k : Fin d, bF x y k * ∫ w, bF x w k ∂ρ := fun y => by
    simp only [hH]
    rw [integral_finsetSum _ (fun k _ => (hbd x k).const_mul _)]
    exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
  simp_rw [e1]
  rw [integral_finsetSum _ (fun k _ => (hbd x k).mul_const _)]
  exact Finset.sum_congr rfl fun k _ => by
    rw [integral_mul_const, sq]

end

/-- `E|B_S(X_I)|²` is within `C (1/n + √(2 d_{j,3}))` of `C₃`. -/
theorem T1_close {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}
    (hB : ForceRep bF bΔ Bb) :
    ∃ C : ℝ, ∀ (N : ℕ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
      (ν : Measure (Config N d)) [IsProbabilityMeasure ν],
      klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤ → ∀ j, j + 3 ≤ N →
      |avg1R N j (fun S i => ∫ X, ∑ k : Fin d, (BS bF ν S X (X i) k) ^ 2 ∂ν) -
          globTupleMean ν 3 (A3 bF)| ≤
        C * (1 / ((N - j : ℕ) : ℝ) + Real.sqrt (2 * (dRev ν j 3).toReal)) := by
  refine ⟨6 * (d * Bb ^ 2), ?_⟩
  intro N μ _ ν _ hH j hj
  set c : ℝ := d * Bb ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hS : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
      ((Sᶜ.card : ℝ)⁻¹) * ∑ i ∈ Sᶜ, ∫ X, ∑ k : Fin d, (BS bF ν S X (X i) k) ^ 2 ∂ν =
        ∫ X, ∫ z, A3 bF z ∂Measure.pi (fun _ : Fin 3 => barCond ν S X) ∂ν := by
    intro S hSm
    have hcard : Sᶜ.card = N - j := by
      rw [Finset.mem_powersetCard] at hSm
      rw [Finset.card_compl, Fintype.card_fin, hSm.2]
    have h1 : 1 ≤ Sᶜ.card := by omega
    set f : (S → Torus d) → Torus d → ℝ :=
      fun a x => ∑ k : Fin d, (∫ y, bF x y k ∂barCondA ν S a) ^ 2 with hf
    have hfm : Measurable fun p : (S → Torus d) × Torus d => f p.1 p.2 :=
      Finset.measurable_sum _ fun k _ => (measurable_BSA hB ν S k).pow_const 2
    have hfb : ∀ a x, |f a x| ≤ c := by
      intro a x
      have := isProbabilityMeasure_barCondA ν S h1 a
      calc |f a x| ≤ ∑ k : Fin d, |(∫ y, bF x y k ∂barCondA ν S a) ^ 2| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k : Fin d, Bb ^ 2 := Finset.sum_le_sum fun k _ => by
            rw [abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _)
              (abs_integral_le_of_prob _ _ (fun y => hB.bound x y k)) 2
        _ = c := by simp [hc]
    have h2 := avg_integral_eq_barCond ν S h1 f hfm hfb
    refine Eq.trans h2 ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    have hp : IsProbabilityMeasure (barCond ν S X) :=
      isProbabilityMeasure_barCondA ν S h1 (restrictS S X)
    exact sq_mean_eq_A3 hB (barCond ν S X)
  have hsum : avg1R N j (fun S i => ∫ X, ∑ k : Fin d, (BS bF ν S X (X i) k) ^ 2 ∂ν) =
      condMeanS ν 3 (A3 bF) j := by
    unfold avg1R condMeanS
    congr 1
    exact Finset.sum_congr rfl hS
  have key := condMeanS_sub_glob ν μ hH (k := 3) (by norm_num) (A3 bF) (measurable_A3 hB)
    (c := c) (abs_A3_le hB) (j := j) hj
  rw [hsum]
  refine key.trans ?_
  have hs : 0 ≤ Real.sqrt (2 * (dRev ν j 3).toReal) := Real.sqrt_nonneg _
  have e : (((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) - 1)) / ((N - j : ℕ) : ℝ) =
      6 * (1 / ((N - j : ℕ) : ℝ)) := by
    push_cast; ring
  rw [e]
  nlinarith [mul_nonneg hc0 hs]

end SharpLSI.FL
