import DGPS.Lipschitz.WeightedSpectrum

open MeasureTheory ProbabilityTheory

namespace DGPS.Lipschitz.LabeledReplacement

/-- Number of nonconstant labels in the multi-index `α`. -/
def nonconstCount {N : ℕ} (α : Fin N → ℕ) : ℕ := (Finset.univ.filter fun i => α i ≠ 0).card

/-- Influence of label `i`: sum of the squared coefficients over the multi-indices of the finite
set `S` whose `i`-th label is nonconstant. -/
noncomputable def influence {N : ℕ} (S : Finset (Fin N → ℕ)) (c : (Fin N → ℕ) → ℝ) (i : Fin N) :
    ℝ := ∑ α ∈ S.filter fun α => α i ≠ 0, c α ^ 2

lemma influence_nonneg {N : ℕ} (S : Finset (Fin N → ℕ)) (c : (Fin N → ℕ) → ℝ) (i : Fin N) :
    0 ≤ influence S c i :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma nonconstCount_le {N : ℕ} {lam : ℕ → ℝ} (h0 : lam 0 = 0) (h1 : 0 < lam 1)
    (hge : ∀ j, 1 ≤ j → lam 1 ≤ lam j) {L : ℝ} {α : Fin N → ℕ}
    (hα : ∑ i, lam (α i) ≤ L) : nonconstCount α ≤ ⌊L / lam 1⌋₊ := by
  have hnn : ∀ i, 0 ≤ lam (α i) := fun i => by
    by_cases h : α i = 0
    · simp [h, h0]
    · exact h1.le.trans (hge _ (Nat.one_le_iff_ne_zero.mpr h))
  have hsum : (nonconstCount α : ℝ) * lam 1 ≤ ∑ i, lam (α i) := by
    calc (nonconstCount α : ℝ) * lam 1
        = ∑ i ∈ Finset.univ.filter fun i => α i ≠ 0, lam 1 := by simp [nonconstCount]
      _ ≤ ∑ i ∈ Finset.univ.filter fun i => α i ≠ 0, lam (α i) :=
          Finset.sum_le_sum fun i hi =>
            hge _ (Nat.one_le_iff_ne_zero.mpr (Finset.mem_filter.mp hi).2)
      _ ≤ ∑ i, lam (α i) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun i _ _ => hnn i
  apply Nat.le_floor
  rw [le_div_iff₀ h1]
  exact hsum.trans hα

/-- **LIP066.** Let `lam` be the eigenvalue sequence (`lam 0 = 0`, `0 < lam 1 ≤ lam j` for `j ≥ 1`;
this is implied by LIP009 `weighted_eigenbasis_and_growth`), `S` a finite set of multi-indices
`α : Fin N → ℕ` with spectral level `∑ i, lam (α i) ≤ L`, and `c` coefficients with
`∑ α ∈ S, c α ^ 2 ≤ B0 ^ 2`. With `D = ⌊L / lam 1⌋₊` and `Inf_i = ∑_{α i ≠ 0} c α ^ 2`:
`∑ Inf_i ≤ D B0²`, and for every `δ > 0` the set `{i | Inf_i > δ}` has at most `D B0² / δ`
elements. Moreover the remaining labels may be replaced by Gaussians: for any orthonormal system
`e` in `L²(μ)` with `e 0 = 1` (the torus eigenfunctions) and any `m`, the feature vector
`(e 1, …, e m)` has the same mean (zero) and covariance (identity) as the standard Gaussian vector
`gaussianReal 0 1 ^ m`, i.e. the first and second moments of every coordinate and pair of
coordinates agree. -/
theorem retained_labels_and_influence_counting
    {N : ℕ} {lam : ℕ → ℝ} (h0 : lam 0 = 0) (h1 : 0 < lam 1)
    (hge : ∀ j, 1 ≤ j → lam 1 ≤ lam j) {L B0 : ℝ}
    (S : Finset (Fin N → ℕ)) (hS : ∀ α ∈ S, ∑ i, lam (α i) ≤ L)
    (c : (Fin N → ℕ) → ℝ) (hc : ∑ α ∈ S, c α ^ 2 ≤ B0 ^ 2) :
    (∑ i, influence S c i ≤ (⌊L / lam 1⌋₊ : ℝ) * B0 ^ 2) ∧
    (∀ δ : ℝ, 0 < δ →
      (((Finset.univ.filter fun i => δ < influence S c i).card : ℕ) : ℝ) ≤
        (⌊L / lam 1⌋₊ : ℝ) * B0 ^ 2 / δ) ∧
    (∀ {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
      (e : ℕ → X → ℝ), (∀ j, MemLp (e j) 2 μ) →
      (∀ j k, ∫ x, e j x * e k x ∂μ = if j = k then 1 else 0) →
      (∀ᵐ x ∂μ, e 0 x = 1) → ∀ m : ℕ,
      (∀ j : Fin m, ∫ x, e (j + 1) x ∂μ =
          ∫ z, z j ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)) ∧
      (∀ j k : Fin m, ∫ x, e (j + 1) x * e (k + 1) x ∂μ =
          ∫ z, z j * z k ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1))) := by
  classical
  have hD : ∀ α ∈ S, (nonconstCount α : ℝ) ≤ (⌊L / lam 1⌋₊ : ℝ) := fun α hα =>
    by exact_mod_cast nonconstCount_le h0 h1 hge (hS α hα)
  have hsum : ∑ i, influence S c i ≤ (⌊L / lam 1⌋₊ : ℝ) * B0 ^ 2 := by
    have h1' : ∑ i, influence S c i = ∑ α ∈ S, (nonconstCount α : ℝ) * c α ^ 2 := by
      simp only [influence, Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rfl
    rw [h1']
    calc ∑ α ∈ S, (nonconstCount α : ℝ) * c α ^ 2
        ≤ ∑ α ∈ S, (⌊L / lam 1⌋₊ : ℝ) * c α ^ 2 :=
          Finset.sum_le_sum fun α hα =>
            mul_le_mul_of_nonneg_right (hD α hα) (sq_nonneg _)
      _ = (⌊L / lam 1⌋₊ : ℝ) * ∑ α ∈ S, c α ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (⌊L / lam 1⌋₊ : ℝ) * B0 ^ 2 :=
          mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)
  refine ⟨hsum, fun δ hδ => ?_, ?_⟩
  · rw [le_div_iff₀ hδ]
    calc (((Finset.univ.filter fun i => δ < influence S c i).card : ℝ) * δ)
        = ∑ i ∈ Finset.univ.filter fun i => δ < influence S c i, δ := by simp
      _ ≤ ∑ i ∈ Finset.univ.filter fun i => δ < influence S c i, influence S c i :=
          Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2.le
      _ ≤ ∑ i, influence S c i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun i _ _ => influence_nonneg S c i
      _ ≤ _ := hsum
  · intro X _ μ _ e hmem horth he0 m
    have hmean : ∀ j, 1 ≤ j → ∫ x, e j x ∂μ = 0 := fun j hj => by
      have this := horth j 0
      have hne : j ≠ 0 := by omega
      simp only [hne, ↓reduceIte] at this
      rw [← this]
      refine integral_congr_ae ?_
      filter_upwards [he0] with x hx
      simp [hx]
    set γ := Measure.pi fun _ : Fin m => gaussianReal 0 1 with hγ
    have hev : ∀ (j : Fin m) (g : ℝ → ℝ), Continuous g →
        ∫ z, g (z j) ∂γ = ∫ x, g x ∂gaussianReal 0 1 := fun j g hg => by
      rw [← (measurePreserving_eval (fun _ : Fin m => gaussianReal 0 1) j).map_eq,
        integral_map (measurable_pi_apply j).aemeasurable hg.aestronglyMeasurable]
    have hint : ∀ j : Fin m, ∫ z, z j ∂γ = 0 := fun j => by
      simpa [integral_id_gaussianReal] using hev j id continuous_id
    refine ⟨fun j => ?_, fun j k => ?_⟩
    · rw [hmean _ (by omega), hint]
    · by_cases hjk : j = k
      · subst hjk
        have h1 := horth (j + 1) (j + 1)
        simp only [↓reduceIte] at h1
        rw [h1, hev j (fun x => x * x) (by fun_prop)]
        have hv := variance_id_gaussianReal (μ := (0 : ℝ)) (v := 1)
        rw [variance_eq_integral aemeasurable_id] at hv
        simpa [integral_id_gaussianReal, sq] using hv.symm
      · have h1 := horth (j + 1) (k + 1)
        have hne : (j : ℕ) + 1 ≠ (k : ℕ) + 1 := by simpa [Fin.ext_iff] using hjk
        simp only [hne, ↓reduceIte] at h1
        rw [h1]
        have hind := (iIndepFun_pi (μ := fun _ : Fin m => gaussianReal 0 1)
          (X := fun _ => id) fun _ => aemeasurable_id).indepFun hjk
        have := hind.integral_mul_eq_mul_integral
          (continuous_apply j).aestronglyMeasurable (continuous_apply k).aestronglyMeasurable
        simp only [Pi.mul_apply, id] at this
        rw [this, hint j, hint k, zero_mul]

end DGPS.Lipschitz.LabeledReplacement
