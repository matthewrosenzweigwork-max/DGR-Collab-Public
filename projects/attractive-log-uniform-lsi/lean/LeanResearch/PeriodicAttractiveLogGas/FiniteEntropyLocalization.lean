import LeanResearch.PeriodicAttractiveLogGas.FiniteEntropyCalculus
import LeanResearch.PeriodicAttractiveLogGas.FiniteGraph

/-! Exact finite-state entropy and energy localization in the supplied local-box
proof (source2246–2291). The entire outer energy is retained. The construction
and geometric estimates for the partition are separate source obligations. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.FiniteEntropyLocalization
open FibreEntropy FiniteEntropyCalculus FiniteGraph

variable {α ι : Type*} [Fintype α] [Fintype ι]

/-- Restriction keeps the original, possibly subprobability, point masses. -/
def restrictedWeight (w : α → ℝ) (B : Finset α) (x : α) : ℝ := by
  classical
  exact if x ∈ B then w x else 0

def setMass (w : α → ℝ) (B : Finset α) : ℝ := ∑ x, restrictedWeight w B x

/-- The normalized conditional weights, extended by zero outside the set. -/
def conditionalWeight (w : α → ℝ) (B : Finset α) (x : α) : ℝ :=
  (setMass w B)⁻¹ * restrictedWeight w B x

def restrictedRates (r : α → α → ℝ) (B : Finset α) (x y : α) : ℝ := by
  classical
  exact if x ∈ B ∧ y ∈ B then r x y else 0

omit [Fintype α] in
theorem restrictedWeight_nonneg (w : α → ℝ) (B : Finset α)
    (hw : ∀ x, 0 ≤ w x) (x : α) : 0 ≤ restrictedWeight w B x := by
  classical
  unfold restrictedWeight
  split
  · exact hw x
  · exact le_rfl

theorem setMass_pos (w : α → ℝ) (B : Finset α) (hw : ∀ x, 0 < w x)
    (hB : B.Nonempty) : 0 < setMass w B := by
  classical
  obtain ⟨x, hx⟩ := hB
  have he : restrictedWeight w B x = w x := by simp [restrictedWeight, hx]
  have hh := Finset.single_le_sum
    (fun y (_ : y ∈ Finset.univ) => restrictedWeight_nonneg w B (fun z => (hw z).le) y)
    (Finset.mem_univ x)
  exact (hw x).trans_le (he ▸ hh)

theorem conditionalWeight_nonneg (w : α → ℝ) (B : Finset α)
    (hw : ∀ x, 0 ≤ w x) (x : α) : 0 ≤ conditionalWeight w B x := by
  have hM : 0 ≤ setMass w B :=
    Finset.sum_nonneg fun y _ => restrictedWeight_nonneg w B hw y
  exact mul_nonneg (inv_nonneg.mpr hM) (restrictedWeight_nonneg w B hw x)

theorem sum_conditionalWeight (w : α → ℝ) (B : Finset α)
    (hM : setMass w B ≠ 0) : (∑ x, conditionalWeight w B x) = 1 := by
  simp only [conditionalWeight, ← Finset.mul_sum]
  exact inv_mul_cancel₀ hM

theorem finiteEntropy_scale_weights (w F : α → ℝ) (c : ℝ) :
    finiteEntropy (fun x => c * w x) F = c * finiteEntropy w F -
      c * (∑ x, w x * F x) * Real.log c := by
  have hm : (∑ x, (c * w x) * F x) = c * ∑ x, w x * F x := by
    simp only [Finset.mul_sum, mul_assoc]
  unfold finiteEntropy
  rw [hm, mulLog_scale]
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

theorem mean_restricted_of_support (w F : α → ℝ) (B : Finset α)
    (hF : ∀ x, x ∉ B → F x = 0) :
    (∑ x, restrictedWeight w B x * F x) = ∑ x, w x * F x := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ B
  · simp [restrictedWeight, hx]
  · simp [restrictedWeight, hx, hF x hx]

theorem finiteEntropy_restricted_of_support (w F : α → ℝ) (B : Finset α)
    (hF : ∀ x, x ∉ B → F x = 0) :
    finiteEntropy (restrictedWeight w B) F = finiteEntropy w F := by
  unfold finiteEntropy
  rw [mean_restricted_of_support w F B hF]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  classical
  by_cases hx : x ∈ B
  · simp [restrictedWeight, hx]
  · simp [restrictedWeight, hx, hF x hx]

/-- The exact normalization cost, for a function supported on the set.
No mass-one assumption is imposed on the original weights. -/
theorem entropy_conditional_identity (w F : α → ℝ) (B : Finset α)
    (hM : setMass w B ≠ 0) (hF : ∀ x, x ∉ B → F x = 0) :
    finiteEntropy w F = setMass w B * finiteEntropy (conditionalWeight w B) F +
      (∑ x, w x * F x) * Real.log (setMass w B)⁻¹ := by
  have hh := finiteEntropy_scale_weights (restrictedWeight w B) F (setMass w B)⁻¹
  change finiteEntropy (conditionalWeight w B) F = _ at hh
  rw [finiteEntropy_restricted_of_support w F B hF,
    mean_restricted_of_support w F B hF] at hh
  rw [hh]
  field_simp
  ring

theorem energy_scale_weights (w : α → ℝ) (r : α → α → ℝ) (F : α → ℝ) (c : ℝ) :
    energy (fun x => c * w x) r F = c * energy w r F := by
  simp only [energy, mul_assoc, ← Finset.mul_sum]
  ring

theorem restricted_energy_le (w : α → ℝ) (r : α → α → ℝ) (F : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hr : ∀ x y, 0 ≤ r x y) (B : Finset α) :
    energy (restrictedWeight w B) (restrictedRates r B) F ≤ energy w r F := by
  classical
  unfold energy
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  by_cases hx : x ∈ B
  · by_cases hy : y ∈ B
    · simp [restrictedWeight, restrictedRates, hx, hy]
    · simp only [restrictedWeight, restrictedRates, hx, hy, true_and, ite_true,
        ite_false, mul_zero, zero_mul]
      exact mul_nonneg (mul_nonneg (hw x) (hr x y)) (sq_nonneg _)
  · simp only [restrictedWeight, restrictedRates, hx, false_and, ite_false, zero_mul]
    exact mul_nonneg (mul_nonneg (hw x) (hr x y)) (sq_nonneg _)

/-- Only internal edges enter the conditional form; every boundary edge
remains available on the right in the original outer graph. -/
theorem mass_mul_conditional_energy_le (w : α → ℝ) (r : α → α → ℝ) (F : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hr : ∀ x y, 0 ≤ r x y) (B : Finset α)
    (hM : setMass w B ≠ 0) :
    setMass w B * energy (conditionalWeight w B) (restrictedRates r B) F ≤
      energy w r F := by
  change setMass w B * energy (fun x => (setMass w B)⁻¹ * restrictedWeight w B x)
    (restrictedRates r B) F ≤ _
  rw [energy_scale_weights, ← mul_assoc, mul_inv_cancel₀ hM, one_mul]
  exact restricted_energy_le w r F hw hr B

/-- The pointwise cost of differentiating a squared partition. -/
def localizationCost (r : α → α → ℝ) (χ : ι → α → ℝ) (x : α) : ℝ :=
  ∑ y, r x y * ∑ i, (χ i y - χ i x) ^ 2

def normalizationCost (w : α → ℝ) (B : ι → Finset α) (χ : ι → α → ℝ)
    (x : α) : ℝ := ∑ i, χ i x ^ 2 * Real.log (setMass w (B i))⁻¹

theorem square_partition_entropy_le (w F : α → ℝ) (χ : ι → α → ℝ)
    (hw : ∀ x, 0 < w x) (hχ : ∀ x, (∑ i, χ i x ^ 2) = 1) :
    finiteEntropy w (fun x => F x ^ 2) ≤
      ∑ i, finiteEntropy w (fun x => (χ i x * F x) ^ 2) := by
  have he : (fun x => ∑ i, (χ i x * F x) ^ 2) = fun x => F x ^ 2 := by
    funext x
    simp only [mul_pow, ← Finset.sum_mul, hχ x, one_mul]
  rw [← he]
  exact finiteEntropy_finset_sum w (fun i x => (χ i x * F x) ^ 2) hw
    (fun i x => sq_nonneg _) Finset.univ

omit [Fintype α] in
theorem partition_edge_square_le (F : α → ℝ) (χ : ι → α → ℝ)
    (hχ : ∀ x, (∑ i, χ i x ^ 2) = 1) (x y : α) :
    (∑ i, (χ i y * F y - χ i x * F x) ^ 2) ≤
      2 * (F y - F x) ^ 2 + 2 * F x ^ 2 * ∑ i, (χ i y - χ i x) ^ 2 := by
  calc
    _ ≤ ∑ i, ((2 * (F y - F x) ^ 2) * χ i y ^ 2 +
        (2 * F x ^ 2) * (χ i y - χ i x) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith only [sq_nonneg (χ i y * (F y - F x) - F x * (χ i y - χ i x))]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hχ y, mul_one]

theorem sum_partition_energy (w F : α → ℝ) (r : α → α → ℝ) (χ : ι → α → ℝ) :
    (∑ i, energy w r (fun x => χ i x * F x)) =
      (1 / 2 : ℝ) * ∑ x, ∑ y, w x * r x y *
        ∑ i, (χ i y * F y - χ i x * F x) ^ 2 := by
  simp only [energy, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]

/-- Exact factor two from the square inequality and the half directed form. -/
theorem energy_partition_le (w F : α → ℝ) (r : α → α → ℝ) (χ : ι → α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hr : ∀ x y, 0 ≤ r x y)
    (hχ : ∀ x, (∑ i, χ i x ^ 2) = 1) :
    (∑ i, energy w r (fun x => χ i x * F x)) ≤
      2 * energy w r F + ∑ x, w x * F x ^ 2 * localizationCost r χ x := by
  rw [sum_partition_energy]
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ x, ∑ y, w x * r x y *
        (2 * (F y - F x) ^ 2 + 2 * F x ^ 2 * ∑ i, (χ i y - χ i x) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum; intro x _
      apply Finset.sum_le_sum; intro y _
      exact mul_le_mul_of_nonneg_left (partition_edge_square_le F χ hχ x y)
        (mul_nonneg (hw x) (hr x y))
    _ = _ := by
      have hp (x : α) :
          (∑ y, w x * r x y *
            (2 * (F y - F x) ^ 2 + 2 * F x ^ 2 * ∑ i, (χ i y - χ i x) ^ 2)) =
          2 * (∑ y, w x * r x y * (F y - F x) ^ 2) +
            2 * (w x * F x ^ 2 * localizationCost r χ x) := by
        unfold localizationCost
        have hi (y : α) : w x * r x y *
            (2 * (F y - F x) ^ 2 + 2 * F x ^ 2 * ∑ i, (χ i y - χ i x) ^ 2) =
            2 * (w x * r x y * (F y - F x) ^ 2) +
              2 * ((w x * F x ^ 2) * (r x y * ∑ i, (χ i y - χ i x) ^ 2)) := by ring
        simp_rw [hi]
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp_rw [hp]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, energy]
      ring

theorem normalization_cost_sum (w F : α → ℝ) (B : ι → Finset α) (χ : ι → α → ℝ) :
    (∑ i, (∑ x, w x * (χ i x * F x) ^ 2) * Real.log (setMass w (B i))⁻¹) =
      ∑ x, w x * F x ^ 2 * normalizationCost w B χ x := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  unfold normalizationCost
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Entropy subadditivity, exact normalization and internal-to-outer energy
comparison, applied to the actual squared partition. -/
theorem entropy_partition_bound (w F : α → ℝ) (r : α → α → ℝ)
    (B : ι → Finset α) (χ : ι → α → ℝ) {CL : ℝ}
    (hw : ∀ x, 0 < w x) (hr : ∀ x y, 0 ≤ r x y) (hCL : 0 ≤ CL)
    (hB : ∀ i, (B i).Nonempty) (hχ : ∀ x, (∑ i, χ i x ^ 2) = 1)
    (hsupp : ∀ i x, x ∉ B i → χ i x = 0)
    (hlocal : ∀ i, finiteEntropy (conditionalWeight w (B i))
        (fun x => (χ i x * F x) ^ 2) ≤
      CL * energy (conditionalWeight w (B i)) (restrictedRates r (B i))
        (fun x => χ i x * F x)) :
    finiteEntropy w (fun x => F x ^ 2) ≤
      CL * (∑ i, energy w r (fun x => χ i x * F x)) +
        ∑ x, w x * F x ^ 2 * normalizationCost w B χ x := by
  have hp (i : ι) : finiteEntropy w (fun x => (χ i x * F x) ^ 2) ≤
      CL * energy w r (fun x => χ i x * F x) +
        (∑ x, w x * (χ i x * F x) ^ 2) * Real.log (setMass w (B i))⁻¹ := by
    have hM := setMass_pos w (B i) hw (hB i)
    rw [entropy_conditional_identity w (fun x => (χ i x * F x) ^ 2) (B i) hM.ne'
      (fun x hx => by simp [hsupp i x hx])]
    refine add_le_add ?_ le_rfl
    calc
      _ ≤ setMass w (B i) * (CL * energy (conditionalWeight w (B i))
          (restrictedRates r (B i)) (fun x => χ i x * F x)) :=
        mul_le_mul_of_nonneg_left (hlocal i) hM.le
      _ = CL * (setMass w (B i) * energy (conditionalWeight w (B i))
          (restrictedRates r (B i)) (fun x => χ i x * F x)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mass_mul_conditional_energy_le w r (fun x => χ i x * F x)
          (fun x => (hw x).le) hr (B i) hM.ne') hCL
  calc
    _ ≤ ∑ i, finiteEntropy w (fun x => (χ i x * F x) ^ 2) :=
      square_partition_entropy_le w F χ hw hχ
    _ ≤ ∑ i, (CL * energy w r (fun x => χ i x * F x) +
        (∑ x, w x * (χ i x * F x) ^ 2) * Real.log (setMass w (B i))⁻¹) :=
      Finset.sum_le_sum fun i _ => hp i
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, normalization_cost_sum]

theorem supported_cost_le (w F W T : α → ℝ) (K : Finset α) (a b : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hF : ∀ x, x ∉ K → F x = 0)
    (hT : ∀ x, x ∈ K → T x ≤ a * W x + b) :
    (∑ x, w x * F x ^ 2 * T x) ≤
      a * (∑ x, w x * F x ^ 2 * W x) + b * ∑ x, w x * F x ^ 2 := by
  classical
  calc
    _ ≤ ∑ x, (a * (w x * F x ^ 2 * W x) + b * (w x * F x ^ 2)) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : x ∈ K
      · have hh := mul_le_mul_of_nonneg_left (hT x hx) (mul_nonneg (hw x) (sq_nonneg (F x)))
        nlinarith only [hh]
      · simp [hF x hx]
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The final finite-state algebra of the supplied local-box proof. Its
partition and geometric bounds remain explicit inputs to be constructed. -/
theorem entropy_from_localization (w F V : α → ℝ) (r : α → α → ℝ)
    (K : Finset α) (B : ι → Finset α) (χ : ι → α → ℝ) {CL a₁ a₂ b₁ b₂ : ℝ}
    (hw : ∀ x, 0 < w x) (hr : ∀ x y, 0 ≤ r x y)
    (hbal : ∀ x y, w x * r x y = w y * r y x) (hV : ∀ x, 0 < V x)
    (hCL : 0 ≤ CL) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hB : ∀ i, (B i).Nonempty) (hχ : ∀ x, (∑ i, χ i x ^ 2) = 1)
    (hsupp : ∀ i x, x ∉ B i → χ i x = 0) (hF : ∀ x, x ∉ K → F x = 0)
    (hlocal : ∀ i, finiteEntropy (conditionalWeight w (B i))
        (fun x => (χ i x * F x) ^ 2) ≤
      CL * energy (conditionalWeight w (B i)) (restrictedRates r (B i))
        (fun x => χ i x * F x))
    (hTheta : ∀ x, x ∈ K → normalizationCost w B χ x ≤ a₁ * groundStatePotential r V x + b₁)
    (hGamma : ∀ x, x ∈ K → localizationCost r χ x ≤ a₂ * groundStatePotential r V x + b₂) :
    finiteEntropy w (fun x => F x ^ 2) ≤
      (CL * (2 + a₂) + a₁) * energy w r F + (CL * b₂ + b₁) * ∑ x, w x * F x ^ 2 := by
  have he := energy_partition_le w F r χ (fun x => (hw x).le) hr hχ
  have ht := supported_cost_le w F (groundStatePotential r V) (normalizationCost w B χ)
    K a₁ b₁ (fun x => (hw x).le) hF hTheta
  have hg := supported_cost_le w F (groundStatePotential r V) (localizationCost r χ)
    K a₂ b₂ (fun x => (hw x).le) hF hGamma
  have hground := groundState_coercivity w r (fun x => (hw x).le) hr hbal V hV F
  have hEnt := entropy_partition_bound w F r B χ hw hr hCL hB hχ hsupp hlocal
  have he' := mul_le_mul_of_nonneg_left he hCL
  have hg' := mul_le_mul_of_nonneg_left hg hCL
  have hp := mul_le_mul_of_nonneg_left hground (add_nonneg (mul_nonneg hCL ha₂) ha₁)
  nlinarith only [hEnt, he', hg', ht, hp]

end PeriodicAttractiveLogGas.FiniteEntropyLocalization
