import FullLabeledLSI.Paper.Sec5Pinsker
import FullLabeledLSI.Paper.Sec5Birthday

/-!
# Lemma 5.4 (bounded conditional product tests): assembly

`condMeanS ν k A j = E ∫ A dρ̄_S^{⊗k}` (the quantity `condProductMeanS` of S21, unfolded),
`globTupleMean ν k A = E_ν A(X_J)` for `J` a uniform ordered tuple of distinct global labels.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d N : ℕ}

/-- `E ∫ A dρ̄_S^{⊗k}` at level `j` (same expression as `condProductMeanS` in S21). -/
noncomputable def condMeanS (ν : Measure (Config N d)) [IsFiniteMeasure ν] (k : ℕ)
    (A : (Fin k → Torus d) → ℝ) (j : ℕ) : ℝ :=
  ((Nat.choose N j : ℝ)⁻¹) * ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
    ∫ X, (∫ z, A z ∂Measure.pi (fun _ : Fin k => barCond ν S X)) ∂ν

/-- `E_ν A(X_J)`, `J` uniform among the ordered tuples of distinct global labels. -/
noncomputable def globTupleMean (ν : Measure (Config N d)) (k : ℕ)
    (A : (Fin k → Torus d) → ℝ) : ℝ :=
  (((Nat.descFactorial N k : ℕ) : ℝ)⁻¹) * ∑ J ∈ injTuples N k, ∫ X, A (X ∘ J) ∂ν


section Aux

/-- A bounded integral against a probability measure is bounded by the same constant. -/
theorem abs_integral_le_of_prob {α : Type*} [MeasurableSpace α] (m : Measure α)
    [IsProbabilityMeasure m] (f : α → ℝ) {c : ℝ} (h : ∀ x, |f x| ≤ c) : |∫ x, f x ∂m| ≤ c := by
  have := norm_integral_le_of_norm_le_const (μ := m) (f := f) (C := c)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact h x)
  simpa using this

/-- Bounded measurable functions are integrable against finite measures. -/
theorem integrable_of_bdd {α : Type*} [MeasurableSpace α] (m : Measure α) [IsFiniteMeasure m]
    {f : α → ℝ} (hf : Measurable f) {c : ℝ} (h : ∀ x, |f x| ≤ c) : Integrable f m :=
  Integrable.of_bound hf.aestronglyMeasurable c
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact h x)

/-- Measurability of `a ↦ ∫ A d(⊗_l κ_l a)` for a family of Markov kernels. -/
theorem measurable_integral_pi_kernel {α : Type*} [MeasurableSpace α] {k : ℕ}
    (κ : Fin k → ProbabilityTheory.Kernel α (Torus d)) [∀ l, IsMarkovKernel (κ l)]
    {A : (Fin k → Torus d) → ℝ} (hA : Measurable A) :
    Measurable fun a => ∫ z, A z ∂Measure.pi (fun l => κ l a) := by
  have hm : Measurable (fun a => Measure.pi (fun l => κ l a)) := by
    refine Measurable.measure_of_isPiSystem generateFrom_pi.symm isPiSystem_pi ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      simp only [Measure.pi_pi]
      exact Finset.measurable_prod _ fun l _ =>
        ProbabilityTheory.Kernel.measurable_coe _ (ht l (Set.mem_univ l))
    · simp
  let κ' : ProbabilityTheory.Kernel α (Fin k → Torus d) := ⟨fun a => Measure.pi (fun l => κ l a), hm⟩
  have : IsMarkovKernel κ' := ⟨fun a => by
    show IsProbabilityMeasure (Measure.pi fun l => κ l a); infer_instance⟩
  exact ((hA.comp measurable_snd).stronglyMeasurable.integral_kernel_prod_right'
    (κ := κ')).measurable

/-- Jensen for the square root, uniform weights. -/
theorem uniform_sqrt_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    (s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.sqrt (x i) ≤ Real.sqrt ((s.card : ℝ)⁻¹ * ∑ i ∈ s, x i) := by
  have hpos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have h := Real.strictConcaveOn_sqrt.concaveOn.le_map_sum (t := s)
    (w := fun _ => (s.card : ℝ)⁻¹) (p := x)
    (fun i _ => (inv_pos.2 hpos).le)
    (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
    (fun i hi => Set.mem_Ici.2 (hx i hi))
  simpa [smul_eq_mul, ← Finset.mul_sum] using h

/-- `d_{j,k}` as a real average of the `DRev` summands. -/
theorem dRev_toReal_eq (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {j k : ℕ} (hjk : j + k ≤ N) :
    (dRev ν j k).toReal = ((Nat.choose N j : ℕ) : ℝ)⁻¹ *
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
        (((N - j).descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, (DRev ν S I).toReal := by
  have hdesc : ((N - j).descFactorial k : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.2 (by omega)).ne'
  rw [dRev_eq_avgK' ν hjk]
  unfold avgK
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_sum]
  · congr 1
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_sum]
    intro I hI; exact DRev_ne_top ν μ hH S I hI
  · intro S hS
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hdesc)
      (ENNReal.sum_ne_top.2 fun I hI => DRev_ne_top ν μ hH S I hI)

end Aux

/-- Fixed-`j` comparison (the proof of (5.12) before the global with-replacement step; also (5.15),
(5.B-square)): `|E ∫ A dρ̄_S^{⊗k} - E_ν A(X_J)| ≤ c (k(k-1)/(N-j) + √(2 d_{j,k}))`. -/
theorem condMeanS_sub_glob (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {k : ℕ} (hk : 1 ≤ k)
    (A : (Fin k → Torus d) → ℝ) (hA : Measurable A) {c : ℝ} (hc : ∀ z, |A z| ≤ c)
    {j : ℕ} (hjk : j + k ≤ N) :
    |condMeanS ν k A j - globTupleMean ν k A| ≤
      c * (((k * (k - 1) : ℝ) / ((N - j : ℕ) : ℝ)) +
        Real.sqrt (2 * (dRev ν j k).toReal)) := by
  have hjN : j < N := by omega
  obtain ⟨X0, -⟩ := nonempty_of_measure_ne_zero (μ := ν) (s := Set.univ) (by simp)
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc (fun _ => X0 ⟨0, by omega⟩))
  set n := N - j with hn
  have hn1 : 1 ≤ n := by omega
  have hnk : k ≤ n := by omega
  set 𝒮 : Finset (Finset (Fin N)) := (Finset.univ : Finset (Fin N)).powersetCard j with h𝒮
  have h𝒮card : 𝒮.card = N.choose j := by simp [h𝒮]
  have hCj : (0 : ℝ) < ((N.choose j : ℕ) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hdn : (0 : ℝ) < ((n.descFactorial k : ℕ) : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.2 hnk
  have hSc : ∀ S ∈ 𝒮, Sᶜ.card = n := fun S hS => by
    rw [Finset.card_compl, Fintype.card_fin, (Finset.mem_powersetCard.1 hS).2]
  have hdt : ∀ S ∈ 𝒮, (distinctTuples S k).card = n.descFactorial k := fun S hS =>
    card_distinctTuples (Finset.mem_powersetCard.1 hS).2 k
  obtain ⟨t₁, ht₁⟩ : ∃ t : Finset (Fin N) → (Fin k → Fin N) → ℝ, ∀ S I, t S I =
      ∫ X, (∫ z, A z ∂Measure.pi (fun l => condLawS ν S (I l) (restrictS S X))) ∂ν :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨t₂, ht₂⟩ : ∃ t : (Fin k → Fin N) → ℝ, ∀ I, t I = ∫ X, A (X ∘ I) ∂ν :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Finset (Fin N) → (Fin k → Fin N) → ℝ,
      ∀ S I, D S I = (DRev ν S I).toReal := ⟨_, fun _ _ => rfl⟩
  have hD0 : ∀ S I, 0 ≤ D S I := fun S I => by rw [hD]; exact ENNReal.toReal_nonneg
  have hgm : ∀ (S : Finset (Fin N)) (I : Fin k → Fin N), Measurable fun X : Config N d =>
      ∫ z, A z ∂Measure.pi (fun l => condLawS ν S (I l) (restrictS S X)) :=
    fun S I => (measurable_integral_pi_kernel (fun l => condLawS ν S (I l)) hA).comp
      (measurable_restrictS S)
  have hgb : ∀ (S : Finset (Fin N)) (I : Fin k → Fin N) (X : Config N d),
      |∫ z, A z ∂Measure.pi (fun l => condLawS ν S (I l) (restrictS S X))| ≤ c :=
    fun S I X => abs_integral_le_of_prob _ _ hc
  have ht₁b : ∀ S I, |t₁ S I| ≤ c := fun S I => by
    rw [ht₁]; exact abs_integral_le_of_prob ν _ (hgb S I)
  -- the conditional mean as an average of `t₁` over all tuples
  have hu : ∀ S ∈ 𝒮, ∫ X, (∫ z, A z ∂Measure.pi (fun _ : Fin k => barCond ν S X)) ∂ν =
      ((n : ℝ) ^ k)⁻¹ * ∑ I ∈ Fintype.piFinset (fun _ : Fin k => Sᶜ), t₁ S I := by
    intro S hS
    have hS1 : 1 ≤ Sᶜ.card := by rw [hSc S hS]; exact hn1
    have h1 : ∀ X : Config N d, ∫ z, A z ∂Measure.pi (fun _ : Fin k => barCond ν S X) =
        ((n : ℝ) ^ k)⁻¹ * ∑ I ∈ Fintype.piFinset (fun _ : Fin k => Sᶜ),
          ∫ z, A z ∂Measure.pi (fun l => condLawS ν S (I l) (restrictS S X)) := fun X => by
      have := integral_pi_barCond ν S hS1 X A hA hc
      rwa [hSc S hS] at this
    rw [integral_congr_ae (Filter.Eventually.of_forall h1), integral_const_mul,
      integral_finsetSum _ (fun I _ => integrable_of_bdd ν (hgm S I) (hgb S I))]
    simp_rw [ht₁]
  have hkey : condMeanS ν k A j = ((N.choose j : ℕ) : ℝ)⁻¹ * ∑ S ∈ 𝒮,
      ((n : ℝ) ^ k)⁻¹ * ∑ I ∈ Fintype.piFinset (fun _ : Fin k => Sᶜ), t₁ S I := by
    unfold condMeanS
    congr 1
    exact Finset.sum_congr rfl hu
  -- birthday correction
  have hbirth : ∀ S ∈ 𝒮, |((n : ℝ) ^ k)⁻¹ *
        ∑ I ∈ Fintype.piFinset (fun _ : Fin k => Sᶜ), t₁ S I -
      ((n.descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, t₁ S I| ≤
        c * ((k * (k - 1) : ℝ) / n) := by
    intro S hS
    have := birthday_avg_diff Sᶜ (by rw [hSc S hS]; exact hn1) k (t₁ S) (ht₁b S)
    rw [hSc S hS] at this
    rw [distinctTuples_eq_filter]
    convert this using 3
  -- Pinsker
  have hpair : ∀ S ∈ 𝒮, ∀ I ∈ distinctTuples S k,
      |t₁ S I - t₂ I| ≤ c * Real.sqrt (2 * D S I) := by
    intro S hS I hI
    have hAm : Measurable fun p : (S → Torus d) × (Fin k → Torus d) =>
        (fun (_ : S → Torus d) (z : Fin k → Torus d) => A z) p.1 p.2 := hA.comp measurable_snd
    have := condPinsker_tuple ν S I (fun _ z => A z) hAm (fun _ z => hc z)
      (DRev_ne_top ν μ hH S I hI)
    rw [ht₁, ht₂, hD]
    exact this
  -- the global tuple mean
  have hglob : globTupleMean ν k A = ((N.choose j : ℕ) : ℝ)⁻¹ * ∑ S ∈ 𝒮,
      ((n.descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, t₂ I := by
    have h1 : ∑ S ∈ 𝒮, ((n.descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, t₂ I =
        ((n.descFactorial k : ℕ) : ℝ)⁻¹ * (((N - k).choose j) • ∑ J ∈ injTuples N k, t₂ J) := by
      rw [← Finset.mul_sum]
      congr 1
      exact sum_sum_distinctTuples j k t₂
    rw [h1, nsmul_eq_mul]
    unfold globTupleMean
    simp only [← ht₂]
    have key : ((N.choose j : ℕ) : ℝ) * ((n.descFactorial k : ℕ) : ℝ) =
        ((N.descFactorial k : ℕ) : ℝ) * (((N - k).choose j : ℕ) : ℝ) := by
      exact_mod_cast choose_descFactorial_glob hjk
    have hCk : (0 : ℝ) < (((N - k).choose j : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    have hDk : (0 : ℝ) < ((N.descFactorial k : ℕ) : ℝ) := by
      exact_mod_cast Nat.descFactorial_pos.2 (by omega)
    field_simp
    linear_combination (∑ x ∈ injTuples N k, t₂ x) * key
  -- real averages
  obtain ⟨m, hm⟩ : ∃ m : Finset (Fin N) → ℝ, ∀ S, m S =
      ((n.descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, D S I := ⟨_, fun _ => rfl⟩
  have hm0 : ∀ S, 0 ≤ m S := fun S => by
    rw [hm]; exact mul_nonneg (inv_nonneg.2 hdn.le) (Finset.sum_nonneg fun I _ => hD0 S I)
  have hd : (dRev ν j k).toReal = ((N.choose j : ℕ) : ℝ)⁻¹ * ∑ S ∈ 𝒮, m S := by
    rw [dRev_toReal_eq ν μ hH hjk]
    simp_rw [hm, hD]
    rfl
  -- per-`S` bound
  have hS_bound : ∀ S ∈ 𝒮,
      |((n : ℝ) ^ k)⁻¹ * ∑ I ∈ Fintype.piFinset (fun _ : Fin k => Sᶜ), t₁ S I -
        ((n.descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, t₂ I| ≤
      c * ((k * (k - 1) : ℝ) / n) + c * Real.sqrt (2 * m S) := by
    intro S hS
    have h2 : |((n.descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, t₁ S I -
        ((n.descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, t₂ I| ≤
        c * Real.sqrt (2 * m S) := by
      rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
        abs_of_pos (inv_pos.2 hdn)]
      have h3 : |∑ I ∈ distinctTuples S k, (t₁ S I - t₂ I)| ≤
          ∑ I ∈ distinctTuples S k, c * Real.sqrt (2 * D S I) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun I hI => hpair S hS I hI)
      have hne : (distinctTuples S k).Nonempty := by
        rw [← Finset.card_pos, hdt S hS]; exact_mod_cast hdn
      have h4 := uniform_sqrt_le (distinctTuples S k) hne (fun I => 2 * D S I)
        (fun I _ => by have := hD0 S I; positivity)
      rw [hdt S hS] at h4
      have h5 : ((n.descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, 2 * D S I =
          2 * m S := by
        rw [hm, ← Finset.mul_sum]; ring
      rw [h5] at h4
      calc ((n.descFactorial k : ℕ) : ℝ)⁻¹ * |∑ I ∈ distinctTuples S k, (t₁ S I - t₂ I)|
          ≤ ((n.descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k,
              c * Real.sqrt (2 * D S I) :=
            mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hdn.le)
        _ = c * (((n.descFactorial k : ℕ) : ℝ)⁻¹ *
              ∑ I ∈ distinctTuples S k, Real.sqrt (2 * D S I)) := by
            rw [← Finset.mul_sum]; ring
        _ ≤ c * Real.sqrt (2 * m S) := mul_le_mul_of_nonneg_left h4 hc0
    calc _ ≤ |((n : ℝ) ^ k)⁻¹ * ∑ I ∈ Fintype.piFinset (fun _ : Fin k => Sᶜ), t₁ S I -
          ((n.descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, t₁ S I| +
        |((n.descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, t₁ S I -
          ((n.descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, t₂ I| :=
          abs_sub_le _ _ _
      _ ≤ _ := add_le_add (hbirth S hS) h2
  -- assemble
  rw [hkey, hglob, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_pos (inv_pos.2 hCj)]
  have hne𝒮 : 𝒮.Nonempty := by
    rw [← Finset.card_pos, h𝒮card]; exact Nat.choose_pos (by omega)
  have hJ := uniform_sqrt_le 𝒮 hne𝒮 (fun S => 2 * m S) (fun S _ => by
    have := hm0 S; positivity)
  rw [h𝒮card] at hJ
  have e3 : ((N.choose j : ℕ) : ℝ)⁻¹ * ∑ S ∈ 𝒮, 2 * m S = 2 * (dRev ν j k).toReal := by
    rw [hd, ← Finset.mul_sum]; ring
  rw [e3] at hJ
  have hsum : ∑ S ∈ 𝒮, |((n : ℝ) ^ k)⁻¹ *
        ∑ I ∈ Fintype.piFinset (fun _ : Fin k => Sᶜ), t₁ S I -
        ((n.descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, t₂ I| ≤
      ∑ S ∈ 𝒮, (c * ((k * (k - 1) : ℝ) / n) + c * Real.sqrt (2 * m S)) :=
    Finset.sum_le_sum hS_bound
  calc ((N.choose j : ℕ) : ℝ)⁻¹ * |∑ S ∈ 𝒮, (((n : ℝ) ^ k)⁻¹ *
        ∑ I ∈ Fintype.piFinset (fun _ : Fin k => Sᶜ), t₁ S I -
        ((n.descFactorial k : ℕ) : ℝ)⁻¹ * ∑ I ∈ distinctTuples S k, t₂ I)|
      ≤ ((N.choose j : ℕ) : ℝ)⁻¹ * ∑ S ∈ 𝒮, (c * ((k * (k - 1) : ℝ) / n) +
          c * Real.sqrt (2 * m S)) :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans hsum)
          (inv_nonneg.2 hCj.le)
    _ = c * ((k * (k - 1) : ℝ) / n) + c * (((N.choose j : ℕ) : ℝ)⁻¹ *
          ∑ S ∈ 𝒮, Real.sqrt (2 * m S)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, h𝒮card, nsmul_eq_mul]
        field_simp
        rw [← Finset.mul_sum]
        ring
    _ ≤ c * ((k * (k - 1) : ℝ) / n) + c * Real.sqrt (2 * (dRev ν j k).toReal) := by
        gcongr
    _ = _ := by ring

/-- Global with-replacement versus distinct tuples. -/
theorem integral_empiricalTensor_sub_glob (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (hN : 1 ≤ N) {k : ℕ} (A : (Fin k → Torus d) → ℝ) (hA : Measurable A) {c : ℝ}
    (hc : ∀ z, |A z| ≤ c) :
    |∫ X, SharpLSI.empiricalTensor k A X ∂ν - globTupleMean ν k A| ≤
      c * ((k * (k - 1) : ℝ) / N) := by
  have hmeas : ∀ J : Fin k → Fin N, Measurable fun X : Config N d => A (X ∘ J) := fun J =>
    hA.comp (measurable_pi_iff.2 fun l => measurable_pi_apply (J l))
  have hint : ∀ J : Fin k → Fin N, Integrable (fun X : Config N d => A (X ∘ J)) ν := fun J =>
    integrable_of_bdd ν (hmeas J) (fun X => hc _)
  have e1 : ∫ X, SharpLSI.empiricalTensor k A X ∂ν =
      ((N : ℝ) ^ k)⁻¹ * ∑ J : Fin k → Fin N, ∫ X, A (X ∘ J) ∂ν := by
    unfold SharpLSI.empiricalTensor
    rw [integral_const_mul, integral_finsetSum _ (fun J _ => hint J), inv_pow]
  have hf : ∀ J : Fin k → Fin N, |∫ X, A (X ∘ J) ∂ν| ≤ c := fun J =>
    abs_integral_le_of_prob ν _ (fun X => hc _)
  have := birthday_avg_diff (Finset.univ : Finset (Fin N)) (by simpa using hN) k
    (fun J => ∫ X, A (X ∘ J) ∂ν) hf
  simp only [Finset.card_univ, Fintype.card_fin, Fintype.piFinset_univ] at this
  rw [e1]
  unfold globTupleMean
  convert this using 3
  rfl

end SharpLSI.FL
