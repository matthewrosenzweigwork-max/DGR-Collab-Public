import FullLabeledLSI.Paper.Sec5ForceMeas

/-!
# Lemma 5.5: conditional Jensen
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d N : ℕ}

/-- Abstract conditional Jensen step: for bounded `𝒢`-measurable `B` and bounded measurable `G`,
`∫ (B - E[G|𝒢])² ≤ ∫ (B - G)²`, with both integrands integrable. -/
theorem sq_sub_condExp_le {Ω : Type*} {m : MeasurableSpace Ω} [m0 : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hm : m ≤ m0) {B G : Ω → ℝ} {C : ℝ}
    (hBm : Measurable[m] B) (hBb : ∀ x, |B x| ≤ C) (hGm : Measurable G) (hGb : ∀ x, |G x| ≤ C) :
    Integrable (fun X => (B X - (μ[G | m]) X) ^ 2) μ ∧
      Integrable (fun X => (B X - G X) ^ 2) μ ∧
      ∫ X, (B X - (μ[G | m]) X) ^ 2 ∂μ ≤ ∫ X, (B X - G X) ^ 2 ∂μ := by
  have hB0 : Measurable B := hBm.mono hm le_rfl
  have hBint : Integrable B μ :=
    Integrable.of_bound hB0.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBb x)
  have hGint : Integrable G μ :=
    Integrable.of_bound hGm.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hGb x)
  have hBL2 : MemLp B 2 μ :=
    MemLp.of_bound hB0.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBb x)
  have hGL2 : MemLp G 2 μ :=
    MemLp.of_bound hGm.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hGb x)
  have hZL2 : MemLp (fun X => B X - G X) 2 μ := hBL2.sub hGL2
  have hZint : Integrable (fun X => B X - G X) μ := hBint.sub hGint
  have hZ2 : Integrable (fun X => (B X - G X) ^ 2) μ := hZL2.integrable_sq
  have hcL2 : MemLp (μ[G | m]) 2 μ := hGL2.condExp one_le_two
  have hI1 : Integrable (fun X => (B X - (μ[G | m]) X) ^ 2) μ :=
    (hBL2.sub hcL2).integrable_sq
  have hBc : μ[B | m] = B :=
    condExp_of_stronglyMeasurable hm hBm.stronglyMeasurable hBint
  have hsub : μ[(fun X => B X - G X) | m] =ᵐ[μ] fun X => (μ[B | m]) X - (μ[G | m]) X :=
    condExp_sub hBint hGint m
  have hjen : ((fun x : ℝ => x ^ 2) ∘ μ[(fun X => B X - G X) | m]) ≤ᵐ[μ]
      μ[(fun x : ℝ => x ^ 2) ∘ (fun X => B X - G X) | m] :=
    ConvexOn.map_condExp_le_univ hm (Even.convexOn_pow even_two)
      (continuous_pow 2).lowerSemicontinuous hZint hZ2
  have hae : (fun X => (B X - (μ[G | m]) X) ^ 2) ≤ᵐ[μ]
      μ[(fun x : ℝ => x ^ 2) ∘ (fun X => B X - G X) | m] := by
    filter_upwards [hsub, hjen] with X h1 h2
    rw [hBc] at h1
    simp only [Function.comp_apply] at h2 ⊢
    rw [h1] at h2
    exact h2
  refine ⟨hI1, hZ2, ?_⟩
  calc ∫ X, (B X - (μ[G | m]) X) ^ 2 ∂μ
      ≤ ∫ X, (μ[(fun x : ℝ => x ^ 2) ∘ (fun X => B X - G X) | m]) X ∂μ :=
        integral_mono_ae hI1 integrable_condExp hae
    _ = ∫ X, (B X - G X) ^ 2 ∂μ := integral_condExp hm

theorem abs_Gpart_le {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}
    (hB : ForceRep bF bΔ Bb) (X : Config N d) (i : Fin N) (k : Fin d) :
    |Gpart bF bΔ N X i k| ≤ (N : ℝ)⁻¹ * ((N : ℝ) * Bb + Bb) := by
  unfold Gpart
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (abs_add_le _ _).trans (add_le_add ?_ (hB.boundΔ _ _))
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ l, |if l ≠ i then bF (X i) (X l) k else 0| ≤ ∑ _l : Fin N, Bb := by
        refine Finset.sum_le_sum fun l _ => ?_
        split_ifs
        · exact hB.bound _ _ _
        · have := (abs_nonneg (bF (X i) (X l) k)).trans (hB.bound (X i) (X l) k)
          simpa using this
    _ = (N : ℝ) * Bb := by simp

theorem measurable_Gpart {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ}
    {Bb : ℝ} (hB : ForceRep bF bΔ Bb) (i : Fin N) (k : Fin d) :
    Measurable fun X : Config N d => Gpart bF bΔ N X i k := by
  unfold Gpart
  refine Measurable.const_mul (Measurable.add (Finset.measurable_sum _ fun l _ => ?_) ?_) _
  · by_cases h : l ≠ i
    · simp only [h, ite_true, ne_eq, not_false_eq_true]
      exact (hB.meas k).comp (f := fun X : Config N d => (X i, X l))
        ((measurable_pi_apply i).prodMk (measurable_pi_apply l))
    · simp [h]
  · exact (hB.measΔ k).comp (measurable_pi_apply i)

/-- `E|B - E[G | 𝒢]|² ≤ E|B - G|²` when `B` is `𝒢`-measurable, `𝒢 = σ(X_S, X_i)`. -/
theorem jensen_force {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}
    (hB : ForceRep bF bΔ Bb) (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (S : Finset (Fin N)) (hS : 1 ≤ Sᶜ.card) (i : Fin N) :
    ∫ X, ∑ k : Fin d, (BS bF ν S X (X i) k -
        condExp (MeasurableSpace.comap (fun X : Config N d => (restrictS S X, X i)) inferInstance)
          ν (fun Y => Gpart bF bΔ N Y i k) X) ^ 2 ∂ν ≤
      ∫ X, ∑ k : Fin d, (BS bF ν S X (X i) k - Gpart bF bΔ N X i k) ^ 2 ∂ν := by
  have hm : MeasurableSpace.comap (fun X : Config N d => (restrictS S X, X i))
      (inferInstance : MeasurableSpace ((S → Torus d) × Torus d)) ≤
      (inferInstance : MeasurableSpace (Config N d)) := ((measurable_restrictS S).prodMk (measurable_pi_apply i)).comap_le
  have hBm : ∀ k, Measurable[MeasurableSpace.comap (fun X : Config N d => (restrictS S X, X i)) inferInstance] fun X : Config N d => BS bF ν S X (X i) k := fun k => by
    have h := (measurable_BSA hB ν S k).comp
      (comap_measurable (fun X : Config N d => (restrictS S X, X i)))
    exact h
  have key := fun k : Fin d => sq_sub_condExp_le ν hm (hBm k) (C := max Bb ((N : ℝ)⁻¹ * ((N : ℝ) * Bb + Bb)))
    (fun X => (abs_BS_le hB ν S hS X (X i) k).trans (le_max_left _ _)) (measurable_Gpart hB i k)
    (fun X => (abs_Gpart_le hB X i k).trans (le_max_right _ _))
  rw [integral_finsetSum _ (fun k _ => (key k).1), integral_finsetSum _ (fun k _ => (key k).2.1)]
  exact Finset.sum_le_sum fun k _ => (key k).2.2

end SharpLSI.FL
