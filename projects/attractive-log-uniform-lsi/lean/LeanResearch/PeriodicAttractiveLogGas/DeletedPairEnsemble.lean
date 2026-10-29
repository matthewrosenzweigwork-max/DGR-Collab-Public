import LeanResearch.PeriodicAttractiveLogGas.ConditionalLawEstimates

/-! Literal omission of at most one unordered pair, and positive finite
normalization of its actual product-domain law. Source Proposition 3.8,
equation (deleted-law) and the first paragraph of its proof. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace PeriodicAttractiveLogGas.DeletedPairEnsemble

open MeshCells GreenPointWeights OneCoordinateConditionals
open LabelOccupations ConditionalParameters ConditionalLawEstimates

abbrev Pair (N : ℕ) := {p : Fin N × Fin N // p.1 < p.2}

def keptPairs {N : ℕ} (d : Option (Pair N)) : Finset (Fin N × Fin N) :=
  match d with
  | none => planarOrderedPairs N
  | some p => (planarOrderedPairs N).erase p.val

def removedValue {N : ℕ} (g : Torus → ℝ) (d : Option (Pair N)) (X : Configuration N) : ℝ :=
  match d with
  | none => 0
  | some p => g (X p.val.1 - X p.val.2)

def energy {N : ℕ} (g : Torus → ℝ) (d : Option (Pair N)) (X : Configuration N) : ℝ :=
  ∑ p ∈ keptPairs d, g (X p.1 - X p.2)

def weight {N : ℕ} (g : Torus → ℝ) (d : Option (Pair N)) (β : ℝ) (X : Configuration N) : ℝ :=
  Real.exp ((β / N) * energy g d X)

theorem energy_eq_sub {N : ℕ} (g : Torus → ℝ) (d : Option (Pair N)) (X : Configuration N) :
    energy g d X = pairEnergy g N X - removedValue g d X := by
  rw [pairEnergy_eq_sum_orderedPairs]
  cases d with
  | none => simp only [energy, keptPairs, removedValue, sub_zero]
  | some p =>
    exact eq_sub_iff_add_eq.mpr
      (Finset.sum_erase_add (planarOrderedPairs N) (fun q ↦ g (X q.1 - X q.2))
        ((mem_planarOrderedPairs p.val).mpr p.property))

theorem weight_eq_ratio {N : ℕ} (g : Torus → ℝ) (d : Option (Pair N)) (β : ℝ)
    (X : Configuration N) :
    weight g d β X = gibbsWeight g N β X * Real.exp (-(β / N) * removedValue g d X) := by
  rw [weight, energy_eq_sub, gibbsWeight, ← Real.exp_add]
  congr 1
  ring

@[simp] theorem weight_none {N : ℕ} (g : Torus → ℝ) (β : ℝ) :
    weight g (none : Option (Pair N)) β = gibbsWeight g N β := by
  funext X
  simp [weight_eq_ratio, removedValue]

theorem measurable_energy {N : ℕ} {g : Torus → ℝ} (hg : Measurable g) (d : Option (Pair N)) :
    Measurable (energy g d) := by
  unfold energy
  fun_prop

theorem measurable_weight {N : ℕ} {g : Torus → ℝ} (hg : Measurable g) (d : Option (Pair N))
    (β : ℝ) : Measurable (weight g d β) :=
  Real.continuous_exp.measurable.comp ((measurable_energy hg d).const_mul _)

theorem weight_pos {N : ℕ} (g : Torus → ℝ) (d : Option (Pair N)) (β : ℝ)
    (X : Configuration N) : 0 < weight g d β X := Real.exp_pos _

theorem removedValue_lower {N : ℕ} {g : Torus → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ z, -C ≤ g z) (d : Option (Pair N)) (X : Configuration N) :
    -C ≤ removedValue g d X := by
  cases d with
  | none => exact neg_nonpos.mpr hC
  | some p => exact hg _

/-- The source comparison uses the original law's actual integrable weight;
it is not a comparison of mixing or of already normalized laws. -/
theorem weight_le_original {N : ℕ} {g : Torus → ℝ} {C β : ℝ} (hC : 0 ≤ C)
    (hg : ∀ z, -C ≤ g z) (hβ : 0 ≤ β) (d : Option (Pair N)) (X : Configuration N) :
    weight g d β X ≤ Real.exp ((β / N) * C) * gibbsWeight g N β X := by
  have ha : 0 ≤ β / (N : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  have he : -(β / N) * removedValue g d X ≤ (β / N) * C := by
    nlinarith [mul_le_mul_of_nonneg_left (removedValue_lower hC hg d X) ha]
  rw [weight_eq_ratio, mul_comm (Real.exp _) (gibbsWeight _ _ _ _)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (gibbsWeight_pos _ _ _ _).le

theorem integrable_weight_of_original {N : ℕ} {μ : Measure (Configuration N)}
    {g : Torus → ℝ} (hgm : Measurable g) {C β : ℝ} (hC : 0 ≤ C)
    (hg : ∀ z, -C ≤ g z) (hβ : 0 ≤ β)
    (hi : Integrable (gibbsWeight g N β) μ) (d : Option (Pair N)) :
    Integrable (weight g d β) μ := by
  apply (hi.const_mul (Real.exp ((β / N) * C))).mono' (measurable_weight hgm d β).aestronglyMeasurable
  exact Eventually.of_forall fun X ↦ by
    rw [Real.norm_of_nonneg (weight_pos g d β X).le]
    exact weight_le_original hC hg hβ d X

def normalizer {N : ℕ} (μ : Measure (Configuration N)) (g : Torus → ℝ)
    (d : Option (Pair N)) (β : ℝ) : ℝ≥0∞ := ∫⁻ X, ENNReal.ofReal (weight g d β X) ∂μ

def law {N : ℕ} (μ : Measure (Configuration N)) (g : Torus → ℝ)
    (d : Option (Pair N)) (β : ℝ) : Measure (Configuration N) :=
  (normalizer μ g d β)⁻¹ • μ.withDensity (fun X ↦ ENNReal.ofReal (weight g d β X))

theorem normalizer_ne_zero {N : ℕ} (μ : Measure (Configuration N)) [NeZero μ]
    {g : Torus → ℝ} (hg : Measurable g) (d : Option (Pair N)) (β : ℝ) :
    normalizer μ g d β ≠ 0 := by
  intro hz
  have he := (lintegral_eq_zero_iff (measurable_weight hg d β).ennreal_ofReal).mp hz
  obtain ⟨X, hX⟩ := he.exists
  exact (ENNReal.ofReal_pos.mpr (weight_pos g d β X)).ne' hX

theorem normalizer_ne_top {N : ℕ} {μ : Measure (Configuration N)} {g : Torus → ℝ}
    (hg : Measurable g) (d : Option (Pair N)) (β : ℝ) (hi : Integrable (weight g d β) μ) :
    normalizer μ g d β ≠ ⊤ :=
  (lintegral_ofReal_ne_top_iff_integrable (measurable_weight hg d β).aestronglyMeasurable
    (Eventually.of_forall fun X ↦ (weight_pos g d β X).le)).mpr hi

theorem law_probability {N : ℕ} (μ : Measure (Configuration N)) [NeZero μ]
    {g : Torus → ℝ} (hg : Measurable g) (d : Option (Pair N)) (β : ℝ)
    (hi : Integrable (weight g d β) μ) : IsProbabilityMeasure (law μ g d β) := by
  constructor
  rw [law, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel (normalizer_ne_zero μ hg d β) (normalizer_ne_top hg d β hi)

theorem law_absolutelyContinuous {N : ℕ} (μ : Measure (Configuration N))
    (g : Torus → ℝ) (d : Option (Pair N)) (β : ℝ) : law μ g d β ≪ μ :=
  (withDensity_absolutelyContinuous _ _).smul_left _

theorem removedValue_ae {N : ℕ} {g h : Torus → ℝ} (hgh : g =ᵐ[torusMeasure] h)
    (d : Option (Pair N)) : removedValue g d =ᵐ[referenceMeasure N] removedValue h d := by
  cases d with
  | none => exact EventuallyEq.rfl
  | some p => exact (quasiMeasurePreserving_pair_difference N p.property.ne).ae_eq_comp hgh

theorem weight_ae {N : ℕ} {g h : Torus → ℝ} (hgh : g =ᵐ[torusMeasure] h)
    (d : Option (Pair N)) (β : ℝ) : weight g d β =ᵐ[referenceMeasure N] weight h d β := by
  filter_upwards [gibbsWeight_congr_ae_kernel hgh N β, removedValue_ae hgh d] with X hX hr
  simp only [weight_eq_ratio, hX, hr]

theorem law_congr_ae {N : ℕ} {μ : Measure (Configuration N)} {g h : Torus → ℝ}
    (d : Option (Pair N)) (β : ℝ) (he : weight g d β =ᵐ[μ] weight h d β) :
    law μ g d β = law μ h d β := by
  have hh := he.mono fun X hX ↦ congrArg ENNReal.ofReal hX
  have hn : normalizer μ g d β = normalizer μ h d β := lintegral_congr_ae hh
  rw [law, law, hn, withDensity_congr_ae hh]

def domainReference {N J : ℕ} (hJ : 0 < J) (a : Fin N → MeshIndex J) (b : Fin N → Patch) :
    Measure (Configuration N) := Measure.pi fun i ↦ patchMeasure J hJ (a i) (b i)

instance domainReference_probability {N J : ℕ} (hJ : 0 < J)
    (a : Fin N → MeshIndex J) (b : Fin N → Patch) : IsProbabilityMeasure (domainReference hJ a b) := by
  unfold domainReference
  infer_instance

theorem domainReference_absolutelyContinuous {N J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : Fin N → MeshIndex J) (b : Fin N → Patch) : domainReference hJ a b ≪ referenceMeasure N := by
  rw [domainReference, pi_patchMeasure_eq hJ hJ2 a b]
  exact Measure.absolutelyContinuous_restrict.smul_left _

theorem integrable_original_domain {N J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ N)
    (a : Fin N → MeshIndex J) (b : Fin N → Patch) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    Integrable (gibbsWeight regularGreenRepresentative N β) (domainReference hJ a b) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_gibbsWeight regularGreenRepresentative_measurable N β).aestronglyMeasurable
    (Eventually.of_forall fun X ↦ (gibbsWeight_pos _ N β X).le)).mp
  rw [domainReference, pi_patchMeasure_eq hJ hJ2 a b, lintegral_smul_measure, smul_eq_mul]
  apply ENNReal.mul_ne_top
  · exact ENNReal.prod_ne_top fun k _ ↦ patchScale_ne_top J (b k)
  · exact ne_top_of_le_ne_top (regularGreen_partitionFunction_ne_top N hN hβ hsub)
      (setLIntegral_le_lintegral _ _)

/-- Positive finite normalization for the literal raw-Green deleted law.
No occupation cap or mixing premise is needed for this normalization fact. -/
theorem domain_normalization {N J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ N)
    (a : Fin N → MeshIndex J) (b : Fin N → Patch) (d : Option (Pair N))
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    Integrable (weight greenRealRepresentative d β) (domainReference hJ a b) ∧
    normalizer (domainReference hJ a b) greenRealRepresentative d β ≠ 0 ∧
    normalizer (domainReference hJ a b) greenRealRepresentative d β ≠ ⊤ ∧
    IsProbabilityMeasure (law (domainReference hJ a b) greenRealRepresentative d β) := by
  obtain ⟨C, hC, hg⟩ := exists_regularGreenRepresentative_lower_bound
  have hi := integrable_weight_of_original regularGreenRepresentative_measurable hC.le hg hβ
    (integrable_original_domain hJ hJ2 hN a b hβ hsub) d
  have he := (domainReference_absolutelyContinuous hJ hJ2 a b).ae_le
    (weight_ae regularGreenRepresentative_ae d β)
  have hi' : Integrable (weight greenRealRepresentative d β) (domainReference hJ a b) := hi.congr he
  exact ⟨hi', normalizer_ne_zero _ greenRealRepresentative_measurable d β,
    normalizer_ne_top greenRealRepresentative_measurable d β hi',
    law_probability _ greenRealRepresentative_measurable d β hi'⟩

theorem regular_domain_law_eq {N J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : Fin N → MeshIndex J) (b : Fin N → Patch) (d : Option (Pair N)) (β : ℝ) :
    law (domainReference hJ a b) regularGreenRepresentative d β =
      law (domainReference hJ a b) greenRealRepresentative d β :=
  law_congr_ae d β ((domainReference_absolutelyContinuous hJ hJ2 a b).ae_le
    (weight_ae regularGreenRepresentative_ae d β))

theorem regular_domain_normalization {N J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ N)
    (a : Fin N → MeshIndex J) (b : Fin N → Patch) (d : Option (Pair N))
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    Integrable (weight regularGreenRepresentative d β) (domainReference hJ a b) ∧
    normalizer (domainReference hJ a b) regularGreenRepresentative d β ≠ 0 ∧
    normalizer (domainReference hJ a b) regularGreenRepresentative d β ≠ ⊤ ∧
    IsProbabilityMeasure (law (domainReference hJ a b) regularGreenRepresentative d β) := by
  obtain ⟨C, hC, hg⟩ := exists_regularGreenRepresentative_lower_bound
  have hi := integrable_weight_of_original regularGreenRepresentative_measurable hC.le hg hβ
    (integrable_original_domain hJ hJ2 hN a b hβ hsub) d
  exact ⟨hi, normalizer_ne_zero _ regularGreenRepresentative_measurable d β,
    normalizer_ne_top regularGreenRepresentative_measurable d β hi,
    law_probability _ regularGreenRepresentative_measurable d β hi⟩

/-- Whether the optional unordered deletion joins these two labelled sites. -/
def isDeleted {N : ℕ} (d : Option (Pair N)) (i j : Fin N) : Prop :=
  match d with
  | none => False
  | some p => (i = p.val.1 ∧ j = p.val.2) ∨ (i = p.val.2 ∧ j = p.val.1)

instance decidableIsDeleted {N : ℕ} (d : Option (Pair N)) (i j : Fin N) :
    Decidable (isDeleted d i j) := by
  cases d <;> unfold isDeleted <;> infer_instance

def sourceCoefficient {n : ℕ} (d : Option (Pair (n + 1))) (β : ℝ)
    (i : Fin (n + 1)) (j : Fin n) : ℝ := by
  classical
  exact if isDeleted d i (i.succAbove j) then 0 else β / (n + 1)

def outsideRemoved {n : ℕ} (g : Torus → ℝ) (d : Option (Pair (n + 1)))
    (i : Fin (n + 1)) (Y : Configuration n) : ℝ :=
  match d with
  | none => 0
  | some p => if p.val.1 = i ∨ p.val.2 = i then 0
      else g (insertSite i 0 Y p.val.1 - insertSite i 0 Y p.val.2)

theorem removedValue_insertSite {n : ℕ} (g : Torus → ℝ) (heven : ∀ z, g (-z) = g z)
    (d : Option (Pair (n + 1))) (i : Fin (n + 1)) (z : Torus) (Y : Configuration n) :
    removedValue g d (insertSite i z Y) = outsideRemoved g d i Y +
      ∑ j, (if isDeleted d i (i.succAbove j) then g (z - Y j) else 0) := by
  classical
  cases d with
  | none => simp [removedValue, outsideRemoved, isDeleted]
  | some p =>
    by_cases h₁ : p.val.1 = i
    · have h₂ : p.val.2 ≠ i := fun h ↦ p.property.ne (h₁.trans h.symm)
      obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq h₂
      have hchar (j : Fin n) : isDeleted (some p) i (i.succAbove j) ↔ j = k := by
        constructor
        · rintro (h | h)
          · exact Fin.succAbove_right_inj.mp (h.2.trans hk.symm)
          · exact (h₂ h.1.symm).elim
        · rintro rfl
          exact Or.inl ⟨h₁.symm, hk⟩
      simp_rw [hchar]
      simp only [removedValue, outsideRemoved, h₁, true_or, ite_true,
        zero_add, Finset.sum_ite_eq', Finset.mem_univ, insertSite_self, ← hk,
        insertSite_succAbove]
    · by_cases h₂ : p.val.2 = i
      · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq h₁
        have hchar (j : Fin n) : isDeleted (some p) i (i.succAbove j) ↔ j = k := by
          constructor
          · rintro (h | h)
            · exact (h₁ h.1.symm).elim
            · exact Fin.succAbove_right_inj.mp (h.2.trans hk.symm)
          · rintro rfl
            exact Or.inr ⟨h₂.symm, hk⟩
        simp_rw [hchar]
        simp only [removedValue, outsideRemoved, h₂, or_true, ite_true,
          zero_add, Finset.sum_ite_eq', Finset.mem_univ, insertSite_self, ← hk,
          insertSite_succAbove]
        simpa only [neg_sub] using heven (z - Y k)
      · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq h₁
        obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq h₂
        have hchar (j : Fin n) : ¬isDeleted (some p) i (i.succAbove j) := by
          rintro (h | h)
          · exact h₁ h.1.symm
          · exact h₂ h.1.symm
        simp only [removedValue, outsideRemoved, or_self, ite_false,
          hchar, Finset.sum_const_zero, add_zero, ← hk, ← hl, insertSite_succAbove,
          Fin.succAbove_ne]

/-- Exact conditional coefficients, with the original denominator N.
Deleting an interaction changes no other source coefficient. -/
theorem energy_insertSite {n : ℕ} (g : Torus → ℝ) (heven : ∀ z, g (-z) = g z)
    (d : Option (Pair (n + 1))) (i : Fin (n + 1)) (z : Torus) (Y : Configuration n) :
    energy g d (insertSite i z Y) = pairEnergy g n Y - outsideRemoved g d i Y +
      ∑ j, (if isDeleted d i (i.succAbove j) then 0 else g (z - Y j)) := by
  classical
  rw [energy_eq_sub, pairEnergy_insertSite g heven, removedValue_insertSite g heven]
  have hs : (∑ j : Fin n, g (z - Y j)) =
      (∑ j, if isDeleted d i (i.succAbove j) then g (z - Y j) else 0) +
        ∑ j, if isDeleted d i (i.succAbove j) then 0 else g (z - Y j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [hs]
  ring

theorem sourceCoefficient_bounds {n : ℕ} (d : Option (Pair (n + 1))) {β : ℝ}
    (hβ : 0 ≤ β) (i : Fin (n + 1)) (j : Fin n) :
    0 ≤ sourceCoefficient d β i j ∧ sourceCoefficient d β i j ≤ β / (n + 1) := by
  classical
  have h : 0 ≤ β / ((n : ℝ) + 1) := div_nonneg hβ (by positivity)
  unfold sourceCoefficient
  split_ifs
  · exact ⟨le_refl 0, h⟩
  · exact ⟨h, le_refl _⟩

theorem weight_insertSite {n : ℕ} (d : Option (Pair (n + 1))) (β : ℝ)
    (i : Fin (n + 1)) (z : Torus) (Y : Configuration n) :
    weight regularGreenRepresentative d β (insertSite i z Y) =
      Real.exp ((β / (n + 1)) * (pairEnergy regularGreenRepresentative n Y -
        outsideRemoved regularGreenRepresentative d i Y)) *
      torusWeight Y (sourceCoefficient d β i) z := by
  classical
  rw [weight, energy_insertSite _ regularGreenRepresentative_even, mul_add, Real.exp_add]
  simp only [Nat.cast_add, Nat.cast_one]
  congr 1
  unfold torusWeight
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [sourceCoefficient]
  split_ifs <;> simp

def coefficients {N : ℕ} (d : Option (Pair N)) (β : ℝ) (i j : Fin N) : ℝ :=
  if isDeleted d i j then 0 else β / N

theorem coefficients_bounds {N : ℕ} (d : Option (Pair N)) {β : ℝ} (hβ : 0 ≤ β)
    (i j : Fin N) : 0 ≤ coefficients d β i j ∧ coefficients d β i j ≤ β / N := by
  unfold coefficients
  split_ifs
  · exact ⟨le_rfl, div_nonneg hβ (Nat.cast_nonneg _)⟩
  · exact ⟨div_nonneg hβ (Nat.cast_nonneg _), le_rfl⟩

theorem coefficients_succAbove {n : ℕ} (d : Option (Pair (n + 1))) (β : ℝ)
    (i : Fin (n + 1)) (j : Fin n) :
    coefficients d β i (i.succAbove j) = sourceCoefficient d β i j := by
  simp only [coefficients, sourceCoefficient, Nat.cast_add, Nat.cast_one]

theorem coefficients_deleted {N : ℕ} (p : Pair N) (β : ℝ) :
    coefficients (some p) β p.val.1 p.val.2 = 0 ∧
      coefficients (some p) β p.val.2 p.val.1 = 0 := by
  simp [coefficients, isDeleted]

theorem sourceWeight_eq_subfamily {n : ℕ} (d : Option (Pair (n + 1))) (i : Fin (n + 1))
    (β : ℝ) (Y : Configuration n) :
    torusWeight Y (sourceCoefficient d β i) =
      torusWeight (fun k : otherParticles i ↦ insertSite i 0 Y k)
        (fun k ↦ coefficients d β i k) := by
  funext z
  unfold torusWeight
  congr 1
  apply Fintype.sum_equiv (otherIndexEquiv i)
  intro j
  change sourceCoefficient d β i j * regularGreenRepresentative (z - Y j) =
    coefficients d β i (i.succAbove j) *
      regularGreenRepresentative (z - insertSite i 0 Y (i.succAbove j))
  rw [insertSite_succAbove, coefficients_succAbove]

theorem pointDensity_subfamily {n : ℕ} (μ : Measure Torus) (d : Option (Pair (n + 1)))
    (i : Fin (n + 1)) (β : ℝ) (Y : Configuration n) :
    pointDensity μ (fun k : otherParticles i ↦ insertSite i 0 Y k)
      (fun k ↦ coefficients d β i k) = pointDensity μ Y (sourceCoefficient d β i) := by
  unfold pointDensity
  rw [← sourceWeight_eq_subfamily d i β Y]

theorem pointLaw_subfamily {n : ℕ} (μ : Measure Torus) (d : Option (Pair (n + 1)))
    (i : Fin (n + 1)) (β : ℝ) (Y : Configuration n) :
    pointLaw μ (fun k : otherParticles i ↦ insertSite i 0 Y k)
      (fun k ↦ coefficients d β i k) = pointLaw μ Y (sourceCoefficient d β i) := by
  rw [pointLaw, pointDensity_subfamily]
  rfl

/-- The actual chosen source constants apply also after deletion. Every
fixed prescribed placement, including coincident sources, has a finite
positive normalizer and the same L4 and lower density estimates. -/
theorem capped_source_bounds {n J : ℕ} (d : Option (Pair (n + 1)))
    {β β₀ δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : Fin (n + 1) → MeshIndex J) (hη : OccupationCap δ η)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside (mesh_pos hmesh) η i Y)
    (a : MeshIndex J) (b : Patch) :
    let μ := patchMeasure J (mesh_pos hmesh) a b
    Integrable (torusWeight Y (sourceCoefficient d β i)) μ ∧
      0 < (∫ z, torusWeight Y (sourceCoefficient d β i) z ∂μ) ∧
      IsProbabilityMeasure (pointLaw μ Y (sourceCoefficient d β i)) ∧
      MemLp (pointDensity μ Y (sourceCoefficient d β i)) 4 μ ∧
      (∀ᵐ z ∂μ, lowerBound β₀ ≤ pointDensity μ Y (sourceCoefficient d β i) z) ∧
      lpNorm (pointDensity μ Y (sourceCoefficient d β i)) 4 μ ≤ densityNormBound β₀ := by
  have hcap : OccupationCap (fixedDelta β₀ kernelConstant kernelConstant) η :=
    fun a ↦ (hη a).trans (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _))
  have h := CappedPointWeights.capped_pointWeight_bounds (mesh_pos hmesh) (Nat.succ_pos n)
    hβ hβ₀ kernelConstant_pos.le kernelConstant_pos.le kernel_log_bound kernel_gradient_bound
    hmesh η hcap (otherParticles i) (insertSite i 0 Y)
    (prescribedOutside_insertSite _ η i Y hY) (coefficients d β i)
    (fun k _ ↦ (coefficients_bounds d hβ i k).1)
    (fun k _ ↦ (coefficients_bounds d hβ i k).2) a b
  dsimp only at h ⊢
  rw [← sourceWeight_eq_subfamily d i β Y, pointLaw_subfamily, pointDensity_subfamily] at h
  exact h

end PeriodicAttractiveLogGas.DeletedPairEnsemble
