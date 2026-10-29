import LeanResearch.PeriodicAttractiveLogGas.TotalVariationOscillation
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! The bounded-function coordinate estimates in the supplied column-sum
Dobrushin argument. Coordinate kernels are actual Markov kernels, with
explicit independence of the coordinate they resample. -/

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped BigOperators

namespace PeriodicAttractiveLogGas.CoordinateOscillation

open NormalizedExponentialInterpolation TotalVariationOscillation

variable {ι : Type*} {E : ι → Type*} [DecidableEq ι]

def SameExcept (i : ι) (x y : ∀ k, E k) : Prop := ∀ k, k ≠ i → x k = y k

omit [DecidableEq ι] in
theorem sameExcept_refl (i : ι) (x : ∀ k, E k) : SameExcept i x x := fun _ _ ↦ rfl

theorem sameExcept_update (i : ι) (x : ∀ k, E k) (u v : E i) :
    SameExcept i (Function.update x i u) (Function.update x i v) := by
  intro k hki
  simp only [Function.update_of_ne hki]

theorem sameExcept_update_other {i j : ι} {x y : ∀ k, E k} (h : SameExcept j x y)
    (z : E i) : SameExcept j (Function.update x i z) (Function.update y i z) := by
  intro k hkj
  by_cases hki : k = i
  · subst k
    simp only [Function.update_self]
  · simpa only [Function.update_of_ne hki] using h k hkj

def differences (f : (∀ k, E k) → ℝ) (i : ι) : Set ℝ :=
  {v | ∃ x y, SameExcept i x y ∧ v = |f x - f y|}

def delta (f : (∀ k, E k) → ℝ) (i : ι) : ℝ := sSup (differences f i)

omit [DecidableEq ι] in
theorem differences_bdd {f : (∀ k, E k) → ℝ} {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (i : ι) : BddAbove (differences f i) := by
  refine ⟨2 * B, ?_⟩
  rintro _ ⟨x, y, _, rfl⟩
  exact (abs_sub _ _).trans (by linarith [hf x, hf y])

omit [DecidableEq ι] in
theorem abs_sub_le_delta {f : (∀ k, E k) → ℝ} {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) {i : ι} {x y : ∀ k, E k} (h : SameExcept i x y) :
    |f x - f y| ≤ delta f i := le_csSup (differences_bdd hf i) ⟨x, y, h, rfl⟩

omit [DecidableEq ι] in
theorem delta_nonneg [Nonempty (∀ k, E k)] {f : (∀ k, E k) → ℝ} {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (i : ι) : 0 ≤ delta f i := by
  obtain ⟨x⟩ := ‹Nonempty (∀ k, E k)›
  simpa only [sub_self, abs_zero] using abs_sub_le_delta hf (sameExcept_refl i x)

omit [DecidableEq ι] in
theorem delta_le [Nonempty (∀ k, E k)] {f : (∀ k, E k) → ℝ} {i : ι} {D : ℝ}
    (h : ∀ x y, SameExcept i x y → |f x - f y| ≤ D) : delta f i ≤ D := by
  apply csSup_le
  · obtain ⟨x⟩ := ‹Nonempty (∀ k, E k)›
    exact ⟨_, x, x, sameExcept_refl i x, rfl⟩
  · rintro _ ⟨x, y, hxy, rfl⟩
    exact h x y hxy

def mix (s : Finset ι) (x y : ∀ k, E k) (k : ι) : E k := if k ∈ s then y k else x k

theorem abs_mix_sub_le_sum {f : (∀ k, E k) → ℝ} {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (s : Finset ι) (x y : ∀ k, E k) :
    |f (mix s x y) - f x| ≤ ∑ i ∈ s, delta f i := by
  induction s using Finset.induction_on with
  | empty =>
    have he : mix ∅ x y = x := by funext k; simp [mix]
    simp only [he, sub_self, abs_zero, Finset.sum_empty, le_refl]
  | @insert i s hi ih =>
    have he : SameExcept i (mix (insert i s) x y) (mix s x y) := by
      intro k hki
      simp only [mix, Finset.mem_insert, hki, false_or]
    calc
      _ ≤ |f (mix (insert i s) x y) - f (mix s x y)| + |f (mix s x y) - f x| :=
        abs_sub_le _ _ _
      _ ≤ delta f i + ∑ k ∈ s, delta f k := add_le_add (abs_sub_le_delta hf he) ih
      _ = _ := by rw [Finset.sum_insert hi]

theorem abs_sub_le_sum_delta [Fintype ι] {f : (∀ k, E k) → ℝ} {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (x y : ∀ k, E k) :
    |f x - f y| ≤ ∑ i, delta f i := by
  have h := abs_mix_sub_le_sum hf Finset.univ y x
  have he : mix Finset.univ y x = x := by funext k; simp [mix]
  rwa [he] at h

section Kernels

variable [∀ i, MeasurableSpace (E i)]
variable (κ : ∀ i, Kernel (∀ k, E k) (E i)) [∀ i, IsMarkovKernel (κ i)]

def IndependentSite : Prop := ∀ i x y, SameExcept i x y → κ i x = κ i y

def siteAverage (f : (∀ k, E k) → ℝ) (i : ι) (x : ∀ k, E k) : ℝ :=
  ∫ z, f (Function.update x i z) ∂κ i x

theorem measurable_siteAverage {f : (∀ k, E k) → ℝ} (hf : Measurable f) (i : ι) :
    Measurable (siteAverage κ f i) := by
  have hm : Measurable (fun p : (∀ k, E k) × E i ↦ f (Function.update p.1 i p.2)) :=
    hf.comp measurable_update'
  exact hm.stronglyMeasurable.integral_kernel_prod_right'.measurable

theorem siteAverage_bound {f : (∀ k, E k) → ℝ} {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (i : ι) (x : ∀ k, E k) : |siteAverage κ f i x| ≤ B := by
  simpa only [siteAverage, Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := κ i x)
      (Eventually.of_forall fun z ↦ show ‖f (Function.update x i z)‖ ≤ B from by
        simpa only [Real.norm_eq_abs] using hf (Function.update x i z)))

theorem integrable_section {f : (∀ k, E k) → ℝ} {B : ℝ}
    (hm : Measurable f) (hf : ∀ x, |f x| ≤ B) (i : ι) (x y : ∀ k, E k) :
    Integrable (fun z ↦ f (Function.update y i z)) (κ i x) := by
  apply (integrable_const B).mono' (hm.comp (measurable_update y)).aestronglyMeasurable
  exact Eventually.of_forall fun z ↦ by
    simpa only [Real.norm_eq_abs, Function.comp_def] using hf (Function.update y i z)

omit [∀ i, IsMarkovKernel (κ i)] in
theorem siteAverage_sameExcept (hind : IndependentSite κ) {f : (∀ k, E k) → ℝ}
    {i : ι} {x y : ∀ k, E k} (h : SameExcept i x y) :
    siteAverage κ f i x = siteAverage κ f i y := by
  unfold siteAverage
  rw [hind i x y h]
  congr 1
  funext z
  congr 1
  funext k
  by_cases hki : k = i
  · subst k
    simp only [Function.update_self]
  · simpa only [Function.update_of_ne hki] using h k hki

theorem delta_siteAverage_self [Nonempty (∀ k, E k)] (hind : IndependentSite κ)
    {f : (∀ k, E k) → ℝ} {B : ℝ} (hf : ∀ x, |f x| ≤ B) (i : ι) :
    delta (siteAverage κ f i) i = 0 := by
  apply le_antisymm
  · apply delta_le
    intro x y hxy
    simp only [siteAverage_sameExcept κ hind hxy, sub_self, abs_zero, le_refl]
  · exact delta_nonneg (siteAverage_bound κ hf i) i

def influence (i j : ι) : ℝ :=
  sSup {v | ∃ x y, SameExcept j x y ∧ v = setTotalVariation (κ i x) (κ i y)}

omit [DecidableEq ι] in
theorem influence_bdd (i j : ι) :
    BddAbove {v | ∃ x y, SameExcept j x y ∧ v = setTotalVariation (κ i x) (κ i y)} := by
  refine ⟨1, ?_⟩
  rintro _ ⟨x, y, _, rfl⟩
  exact setTV_le_one

omit [DecidableEq ι] in
theorem setTV_le_influence {i j : ι} {x y : ∀ k, E k} (hxy : SameExcept j x y) :
    setTotalVariation (κ i x) (κ i y) ≤ influence κ i j :=
  le_csSup (influence_bdd κ i j) ⟨x, y, hxy, rfl⟩

omit [DecidableEq ι] in
theorem influence_nonneg [Nonempty (∀ k, E k)] (i j : ι) : 0 ≤ influence κ i j := by
  obtain ⟨x⟩ := ‹Nonempty (∀ k, E k)›
  exact setTV_nonneg.trans (setTV_le_influence κ (sameExcept_refl j x))

theorem delta_siteAverage [Nonempty (∀ k, E k)] {f : (∀ k, E k) → ℝ} {B : ℝ}
    (hm : Measurable f) (hf : ∀ x, |f x| ≤ B) (i j : ι) :
    delta (siteAverage κ f i) j ≤ delta f j + influence κ i j * delta f i := by
  apply delta_le
  intro x y hxy
  have hfirst : |(∫ z, f (Function.update x i z) ∂κ i x) -
      (∫ z, f (Function.update y i z) ∂κ i x)| ≤ delta f j := by
    rw [← integral_sub (integrable_section κ hm hf i x x) (integrable_section κ hm hf i x y)]
    have hb := norm_integral_le_of_norm_le_const (μ := κ i x)
      (Eventually.of_forall fun z ↦ show ‖f (Function.update x i z) -
        f (Function.update y i z)‖ ≤ delta f j from by
          rw [Real.norm_eq_abs]
          exact abs_sub_le_delta hf (sameExcept_update_other hxy z))
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb
  have hsecond := abs_integral_sub_le_setTV_mul_pairwise
    (μ := κ i x) (ν := κ i y) (hm.comp (measurable_update y (a := i)))
    (show BddAbove (range (fun z ↦ f (Function.update y i z))) from
      ⟨B, by rintro _ ⟨z, rfl⟩; exact (abs_le.mp (hf _)).2⟩)
    (show BddBelow (range (fun z ↦ f (Function.update y i z))) from
      ⟨-B, by rintro _ ⟨z, rfl⟩; exact (abs_le.mp (hf _)).1⟩)
    (fun u v ↦ abs_sub_le_delta hf (sameExcept_update i y u v))
  unfold siteAverage
  calc
    _ ≤ |(∫ z, f (Function.update x i z) ∂κ i x) - (∫ z, f (Function.update y i z) ∂κ i x)| +
        |(∫ z, f (Function.update y i z) ∂κ i x) - (∫ z, f (Function.update y i z) ∂κ i y)| :=
      abs_sub_le _ _ _
    _ ≤ delta f j + setTotalVariation (κ i x) (κ i y) * delta f i := add_le_add hfirst hsecond
    _ ≤ _ := add_le_add_right
      (mul_le_mul_of_nonneg_right (setTV_le_influence κ hxy) (delta_nonneg hf i)) _

section Finite

variable [Fintype ι] [Nonempty ι] [Nonempty (∀ k, E k)]

def maxDelta (f : (∀ k, E k) → ℝ) : ℝ := sSup (range (delta f))

omit [DecidableEq ι] [∀ i, MeasurableSpace (E i)] [Nonempty ι] [Nonempty (∀ k, E k)] in
theorem delta_le_maxDelta (f : (∀ k, E k) → ℝ) (i : ι) : delta f i ≤ maxDelta f :=
  le_csSup (finite_range _).bddAbove (mem_range_self i)

omit [DecidableEq ι] [∀ i, MeasurableSpace (E i)] in
theorem maxDelta_nonneg {f : (∀ k, E k) → ℝ} {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) : 0 ≤ maxDelta f := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact (delta_nonneg hf i).trans (delta_le_maxDelta f i)

omit [DecidableEq ι] [∀ i, MeasurableSpace (E i)] [Fintype ι] [Nonempty (∀ k, E k)] in
theorem maxDelta_le {f : (∀ k, E k) → ℝ} {D : ℝ} (h : ∀ i, delta f i ≤ D) :
    maxDelta f ≤ D := by
  apply csSup_le (range_nonempty _)
  rintro _ ⟨i, rfl⟩
  exact h i

omit [∀ i, MeasurableSpace (E i)] [Nonempty ι] [Nonempty (∀ k, E k)] in
theorem abs_sub_le_card_mul_maxDelta {f : (∀ k, E k) → ℝ} {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (x y : ∀ k, E k) :
    |f x - f y| ≤ (Fintype.card ι : ℝ) * maxDelta f := by
  calc
    _ ≤ ∑ i, delta f i := abs_sub_le_sum_delta hf x y
    _ ≤ ∑ _i : ι, maxDelta f := Finset.sum_le_sum fun i _ ↦ delta_le_maxDelta f i
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

def randomScan (f : (∀ k, E k) → ℝ) (x : ∀ k, E k) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, siteAverage κ f i x

omit [Nonempty ι] [Nonempty (∀ k, E k)] in
theorem measurable_randomScan {f : (∀ k, E k) → ℝ} (hf : Measurable f) :
    Measurable (randomScan κ f) :=
  (Finset.measurable_fun_sum Finset.univ fun i _ ↦ measurable_siteAverage κ hf i).const_mul _

omit [Nonempty (∀ k, E k)] in
theorem randomScan_bound {f : (∀ k, E k) → ℝ} {B : ℝ} (hf : ∀ x, |f x| ≤ B)
    (x : ∀ k, E k) : |randomScan κ f x| ≤ B := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold randomScan
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, |siteAverage κ f i x| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ siteAverage_bound κ hf i x)
        (by positivity)
    _ = B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

def columnSum (j : ι) : ℝ := ∑ i ∈ Finset.univ.erase j, influence κ i j

def maxColumnSum : ℝ := sSup (range (columnSum κ))

omit [∀ i, IsMarkovKernel (κ i)] [Nonempty ι] [Nonempty (∀ k, E k)] in
theorem columnSum_le_maxColumnSum (j : ι) : columnSum κ j ≤ maxColumnSum κ :=
  le_csSup (finite_range _).bddAbove (mem_range_self j)

omit [Nonempty ι] in
theorem columnSum_nonneg (j : ι) : 0 ≤ columnSum κ j :=
  Finset.sum_nonneg fun i _ ↦ influence_nonneg κ i j

theorem maxColumnSum_nonneg : 0 ≤ maxColumnSum κ := by
  obtain ⟨j⟩ := ‹Nonempty ι›
  exact (columnSum_nonneg κ j).trans (columnSum_le_maxColumnSum κ j)

def contractionRate (α : ℝ) : ℝ := 1 - (1 - α) / (Fintype.card ι : ℝ)

omit [DecidableEq ι] in
theorem contractionRate_nonneg {α : ℝ} (hα : 0 ≤ α) :
    0 ≤ contractionRate (ι := ι) α := by
  have hn : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hp : (0 : ℝ) < Fintype.card ι := by positivity
  unfold contractionRate
  have hd : (1 - α) / (Fintype.card ι : ℝ) ≤ 1 :=
    (div_le_iff₀ hp).mpr (by linarith)
  linarith

omit [DecidableEq ι] in
theorem contractionRate_lt_one {α : ℝ} (hα : α < 1) :
    contractionRate (ι := ι) α < 1 := by
  have hp : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  exact sub_lt_self 1 (div_pos (sub_pos.mpr hα) hp)

/-- The column index is the changed coordinate j; the sum is over the
resampled coordinates i. Diagonal terms vanish by genuine site independence. -/
theorem maxDelta_randomScan_le (hind : IndependentSite κ) {f : (∀ k, E k) → ℝ} {B α : ℝ}
    (hm : Measurable f) (hf : ∀ x, |f x| ≤ B) (hcol : ∀ j, columnSum κ j ≤ α) :
    maxDelta (randomScan κ f) ≤ contractionRate (ι := ι) α * maxDelta f := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hn1 : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hd0 : 0 ≤ maxDelta f := maxDelta_nonneg hf
  apply maxDelta_le
  intro j
  apply delta_le
  intro x y hxy
  have hzero : |siteAverage κ f j x - siteAverage κ f j y| = 0 := by
    rw [siteAverage_sameExcept κ hind hxy, sub_self, abs_zero]
  have hterm (i : ι) : |siteAverage κ f i x - siteAverage κ f i y| ≤
      (1 + influence κ i j) * maxDelta f := by
    have h := (abs_sub_le_delta (siteAverage_bound κ hf i) hxy).trans
      (delta_siteAverage κ hm hf i j)
    have hj := delta_le_maxDelta f j
    have hi := mul_le_mul_of_nonneg_left (delta_le_maxDelta f i) (influence_nonneg κ i j)
    nlinarith
  have hsum : (∑ i, |siteAverage κ f i x - siteAverage κ f i y|) ≤
      ((Fintype.card ι : ℝ) - 1 + α) * maxDelta f := by
    calc
      _ = ∑ i ∈ Finset.univ.erase j, |siteAverage κ f i x - siteAverage κ f i y| := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), hzero, add_zero]
      _ ≤ ∑ i ∈ Finset.univ.erase j, (1 + influence κ i j) * maxDelta f :=
        Finset.sum_le_sum fun i _ ↦ hterm i
      _ = ((Fintype.card ι : ℝ) - 1 + columnSum κ j) * maxDelta f := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_erase_of_mem
          (Finset.mem_univ j), Finset.card_univ, Nat.cast_sub hn1, Nat.cast_one, columnSum]
      _ ≤ _ := mul_le_mul_of_nonneg_right (add_le_add_right (hcol j) _) hd0
  have he : randomScan κ f x - randomScan κ f y =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, (siteAverage κ f i x - siteAverage κ f i y) := by
    rw [Finset.sum_sub_distrib, mul_sub]
    rfl
  rw [he, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, |siteAverage κ f i x - siteAverage κ f i y| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * (((Fintype.card ι : ℝ) - 1 + α) * maxDelta f) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by unfold contractionRate; field_simp [hn]; ring

theorem maxDelta_randomScan (hind : IndependentSite κ) {f : (∀ k, E k) → ℝ} {B : ℝ}
    (hm : Measurable f) (hf : ∀ x, |f x| ≤ B) :
    maxDelta (randomScan κ f) ≤ contractionRate (ι := ι) (maxColumnSum κ) * maxDelta f :=
  maxDelta_randomScan_le κ hind hm hf (columnSum_le_maxColumnSum κ)

def scanPower : ℕ → ((∀ k, E k) → ℝ) → (∀ k, E k) → ℝ
  | 0, f => f
  | n + 1, f => randomScan κ (scanPower n f)

omit [Nonempty ι] [Nonempty (∀ k, E k)] in
theorem measurable_scanPower {f : (∀ k, E k) → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (scanPower κ n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact measurable_randomScan κ ih

omit [Nonempty (∀ k, E k)] in
theorem scanPower_bound {f : (∀ k, E k) → ℝ} {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (n : ℕ) : ∀ x, |scanPower κ n f x| ≤ B := by
  induction n with
  | zero => exact hf
  | succ n ih => exact randomScan_bound κ ih

theorem maxDelta_scanPower (hind : IndependentSite κ) {f : (∀ k, E k) → ℝ} {B : ℝ}
    (hm : Measurable f) (hf : ∀ x, |f x| ≤ B) (n : ℕ) :
    maxDelta (scanPower κ n f) ≤
      contractionRate (ι := ι) (maxColumnSum κ) ^ n * maxDelta f := by
  induction n with
  | zero => simp only [scanPower, pow_zero, one_mul, le_refl]
  | succ n ih =>
    calc
      _ ≤ contractionRate (ι := ι) (maxColumnSum κ) * maxDelta (scanPower κ n f) :=
        maxDelta_randomScan κ hind (measurable_scanPower κ hm n) (scanPower_bound κ hf n)
      _ ≤ contractionRate (ι := ι) (maxColumnSum κ) *
          (contractionRate (ι := ι) (maxColumnSum κ) ^ n * maxDelta f) :=
        mul_le_mul_of_nonneg_left ih (contractionRate_nonneg (maxColumnSum_nonneg κ))
      _ = _ := by rw [pow_succ]; ring

theorem abs_scanPower_sub_le (hind : IndependentSite κ) {f : (∀ k, E k) → ℝ} {B : ℝ}
    (hm : Measurable f) (hf : ∀ x, |f x| ≤ B) (n : ℕ) (x y : ∀ k, E k) :
    |scanPower κ n f x - scanPower κ n f y| ≤
      (Fintype.card ι : ℝ) * contractionRate (ι := ι) (maxColumnSum κ) ^ n * maxDelta f := by
  have h := (abs_sub_le_card_mul_maxDelta (scanPower_bound κ hf n) x y).trans
    (mul_le_mul_of_nonneg_left (maxDelta_scanPower κ hind hm hf n) (Nat.cast_nonneg _))
  simpa only [mul_assoc] using h

end Finite
end Kernels
end PeriodicAttractiveLogGas.CoordinateOscillation
