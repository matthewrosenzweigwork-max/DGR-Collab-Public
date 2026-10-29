import DGRHS.Decoupling.Jensen
import DGRHS.Decoupling.Product
import DGRHS.Decoupling.Selector

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace DGRHS.Decoupling

/-- Integration along a measure-preserving map, with the measurability obligation explicit. -/
lemma integral_comp_preserving {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {g : A → B} (hg : MeasurePreserving g μ ν)
    (f : B → ℝ) (hf : AEStronglyMeasurable f ν) :
    (∫ x, f (g x) ∂μ) = ∫ y, f y ∂ν := by
  have hfm : AEStronglyMeasurable f (μ.map g) := hg.map_eq.symm ▸ hf
  calc
    (∫ x, f (g x) ∂μ) = ∫ y, f y ∂μ.map g := (integral_map hg.aemeasurable hfm).symm
    _ = ∫ y, f y ∂ν := by rw [hg.map_eq]

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable (μ : Measure S) [IsProbabilityMeasure μ]

def firstSamples (z : ι → S × S) (i : ι) : S := (z i).1

lemma firstSamples_measurePreserving :
    MeasurePreserving (firstSamples (S := S) (ι := ι)) (productSamples μ)
      (Measure.pi (fun _ : ι ↦ μ)) := by
  unfold firstSamples productSamples
  exact measurePreserving_pi (fun _ : ι ↦ μ.prod μ) (fun _ : ι ↦ μ)
    (f := fun _ ↦ Prod.fst) (fun _ ↦ measurePreserving_fst)

lemma first_eval_preserving (i : ι) :
    MeasurePreserving (fun z : ι → S × S ↦ (z i).1) (productSamples μ) μ :=
  measurePreserving_fst.comp (measurePreserving_eval (fun _ : ι ↦ μ.prod μ) i)

lemma second_eval_preserving (i : ι) :
    MeasurePreserving (fun z : ι → S × S ↦ (z i).2) (productSamples μ) μ :=
  measurePreserving_snd.comp (measurePreserving_eval (fun _ : ι ↦ μ.prod μ) i)

def coupledStatistic (h : S × S → ℝ) (z : ι → S × S) : ℝ :=
  offDiagonalSum (fun i j ↦ h ((z i).1, (z j).1))

def decoupledStatistic (h : S × S → ℝ) (z : ι → S × S) : ℝ :=
  offDiagonalSum (fun i j ↦ h ((z i).1, (z j).2))

def coupledCross (h : S × S → ℝ) (s : ι → Bool) (z : ι → S × S) : ℝ :=
  crossSum (fun i j ↦ h ((z i).1, (z j).1)) s

def decoupledCross (h : S × S → ℝ) (s : ι → Bool) (z : ι → S × S) : ℝ :=
  crossSum (fun i j ↦ h ((z i).1, (z j).2)) s

lemma memLp_coupledStatistic (h : S × S → ℝ) (p : ℝ≥0∞) (hh : MemLp h p (μ.prod μ)) :
    MemLp (coupledStatistic (ι := ι) h) p (productSamples μ) := by
  unfold coupledStatistic offDiagonalSum
  apply memLp_finsetSum
  intro i hi
  apply memLp_finsetSum
  intro j hj
  by_cases hij : i ≠ j
  · simp_rw [if_pos hij]
    exact (memLp_coupled_term μ h p hh i j hij).comp_measurePreserving
      (firstSamples_measurePreserving μ)
  · simp_rw [if_neg hij]
    simp

lemma memLp_decoupledStatistic (h : S × S → ℝ) (p : ℝ≥0∞) (hh : MemLp h p (μ.prod μ)) :
    MemLp (decoupledStatistic (ι := ι) h) p (productSamples μ) := by
  unfold decoupledStatistic offDiagonalSum
  apply memLp_finsetSum
  intro i hi
  apply memLp_finsetSum
  intro j hj
  by_cases hij : i ≠ j
  · simp_rw [if_pos hij]
    exact memLp_decoupled_term μ h p hh i j hij
  · simp_rw [if_neg hij]
    simp

lemma memLp_coupledCross (h : S × S → ℝ) (p : ℝ≥0∞) (hh : MemLp h p (μ.prod μ))
    (s : ι → Bool) : MemLp (coupledCross h s) p (productSamples μ) := by
  unfold coupledCross crossSum
  apply memLp_finsetSum
  intro i hi
  apply memLp_finsetSum
  intro j hj
  by_cases hij : i ≠ j
  · simp_rw [if_pos hij]
    exact ((memLp_coupled_term μ h p hh i j hij).comp_measurePreserving
      (firstSamples_measurePreserving μ)).const_mul (bit (s i) * (1 - bit (s j)))
  · simp_rw [if_neg hij]
    simp

lemma memLp_decoupledCross (h : S × S → ℝ) (p : ℝ≥0∞) (hh : MemLp h p (μ.prod μ))
    (s : ι → Bool) : MemLp (decoupledCross h s) p (productSamples μ) := by
  unfold decoupledCross crossSum
  apply memLp_finsetSum
  intro i hi
  apply memLp_finsetSum
  intro j hj
  by_cases hij : i ≠ j
  · simp_rw [if_pos hij]
    exact (memLp_decoupled_term μ h p hh i j hij).const_mul (bit (s i) * (1 - bit (s j)))
  · simp_rw [if_neg hij]
    simp

lemma coupledCross_swapSelected (h : S × S → ℝ) (s : ι → Bool) (z : ι → S × S) :
    coupledCross h s (swapSelected s z) = decoupledCross h s z := by
  unfold coupledCross decoupledCross crossSum
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  cases hsi : s i <;> cases hsj : s j <;> simp [swapSelected, bit, hsi, hsj]

/-- The actual cross-block moments coincide after replacing the other partition by independent copies. -/
theorem cross_even_moment_same_law (h : S × S → ℝ) (s : ι → Bool) (k : ℕ) :
    (∫ z, |coupledCross h s z| ^ (2 * k) ∂productSamples μ) =
      ∫ z, |decoupledCross h s z| ^ (2 * k) ∂productSamples μ := by
  have he : MeasurePreserving (swapSelectedEquiv μ s) (productSamples μ) (productSamples μ) :=
    swapSelected_measurePreserving μ s
  have hi := he.integral_comp' (fun z ↦ |coupledCross h s z| ^ (2 * k))
  change (∫ z, |coupledCross h s (swapSelected s z)| ^ (2 * k) ∂productSamples μ) =
    ∫ z, |coupledCross h s z| ^ (2 * k) ∂productSamples μ at hi
  simp_rw [coupledCross_swapSelected] at hi
  exact hi.symm

/-- The full pair integral is zero; kernel integrability justifies the Fubini step. -/
lemma integral_kernel_zero (h : S × S → ℝ) (hh : Integrable h (μ.prod μ))
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0) : ∫ z, h z ∂μ.prod μ = 0 := by
  rw [integral_prod h hh]
  exact integral_eq_zero_of_ae hc


/-- Each spliced term is genuinely integrable in the fresh array. -/
lemma integrable_spliced_term (h : S × S → ℝ) (hh : Integrable h (μ.prod μ))
    (s : ι → Bool) (z : ι → S × S) (i j : ι) (hij : i ≠ j)
    (hr : Integrable (fun y ↦ h ((z i).1, y)) μ)
    (hl : Integrable (fun x ↦ h (x, (z j).2)) μ) :
    Integrable (fun w ↦ h ((spliceSamples s (z, w) i).1,
      (spliceSamples s (z, w) j).2)) (productSamples μ) := by
  cases hsi : s i <;> cases hsj : s j
  · simpa only [spliceSamples, spliceCoordinate, hsi, hsj, Bool.false_eq_true, ↓reduceIte,
      Function.comp_def] using (first_eval_preserving μ i).integrable_comp_of_integrable hl
  · simpa only [spliceSamples, spliceCoordinate, hsi, hsj, Bool.false_eq_true, ↓reduceIte,
      Function.comp_def] using
      (decoupled_pair_measurePreserving μ i j hij).integrable_comp_of_integrable hh
  · simpa only [spliceSamples, spliceCoordinate, hsi, hsj, Bool.false_eq_true, ↓reduceIte] using
      (integrable_const (h ((z i).1, (z j).2)) : Integrable (fun _ : ι → S × S ↦
        h ((z i).1, (z j).2)) (productSamples μ))
  · simpa only [spliceSamples, spliceCoordinate, hsi, hsj, Bool.false_eq_true, ↓reduceIte,
      Function.comp_def] using (second_eval_preserving μ j).integrable_comp_of_integrable hr

/-- Canonicality kills all omitted spliced terms, with the coordinate law established concretely. -/
lemma integral_spliced_term (h : S × S → ℝ) (hh : Integrable h (μ.prod μ))
    (hz : (∫ p, h p ∂μ.prod μ) = 0)
    (s : ι → Bool) (z : ι → S × S) (i j : ι) (hij : i ≠ j)
    (hr : Integrable (fun y ↦ h ((z i).1, y)) μ)
    (hl : Integrable (fun x ↦ h (x, (z j).2)) μ)
    (hr0 : (∫ y, h ((z i).1, y) ∂μ) = 0)
    (hl0 : (∫ x, h (x, (z j).2) ∂μ) = 0) :
    (∫ w, h ((spliceSamples s (z, w) i).1, (spliceSamples s (z, w) j).2)
      ∂productSamples μ) = bit (s i) * (1 - bit (s j)) * h ((z i).1, (z j).2) := by
  cases hsi : s i <;> cases hsj : s j
  · simpa only [spliceSamples, spliceCoordinate, hsi, hsj, Bool.false_eq_true, ↓reduceIte,
      bit, zero_mul, one_mul, sub_zero, sub_self] using
      (integral_comp_preserving (first_eval_preserving μ i)
        (fun x ↦ h (x, (z j).2)) hl.aestronglyMeasurable).trans hl0
  · simpa only [spliceSamples, spliceCoordinate, hsi, hsj, Bool.false_eq_true, ↓reduceIte,
      bit, zero_mul, one_mul, sub_zero, sub_self] using
      (integral_comp_preserving (decoupled_pair_measurePreserving μ i j hij)
        h hh.aestronglyMeasurable).trans hz
  · simp [spliceSamples, spliceCoordinate, hsi, hsj, bit]
  · simpa only [spliceSamples, spliceCoordinate, hsi, hsj, Bool.false_eq_true, ↓reduceIte,
      bit, zero_mul, one_mul, sub_zero, sub_self] using
      (integral_comp_preserving (second_eval_preserving μ j)
        (fun y ↦ h ((z i).1, y)) hr.aestronglyMeasurable).trans hr0

/-- The full spliced statistic averages to the actual selected cross block a.e. -/
theorem mean_spliced_eq_cross (h : S × S → ℝ) (hh : Integrable h (μ.prod μ))
    (hr0 : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
    (hl0 : ∀ᵐ y ∂μ, (∫ x, h (x, y) ∂μ) = 0) (s : ι → Bool) :
    ∀ᵐ z ∂productSamples μ,
      (∫ w, decoupledStatistic (ι := ι) h (spliceSamples s (z, w)) ∂productSamples μ) =
        decoupledCross h s z := by
  have hright : ∀ᵐ z ∂productSamples μ, ∀ i : ι,
      Integrable (fun y ↦ h ((z i).1, y)) μ ∧
        (∫ y, h ((z i).1, y) ∂μ) = 0 :=
    ae_all_iff.mpr fun i ↦ (first_eval_preserving μ i).quasiMeasurePreserving.ae
      (hh.prod_right_ae.and hr0)
  have hleft : ∀ᵐ z ∂productSamples μ, ∀ j : ι,
      Integrable (fun x ↦ h (x, (z j).2)) μ ∧
        (∫ x, h (x, (z j).2) ∂μ) = 0 :=
    ae_all_iff.mpr fun j ↦ (second_eval_preserving μ j).quasiMeasurePreserving.ae
      (hh.prod_left_ae.and hl0)
  have hz := integral_kernel_zero μ h hh hr0
  filter_upwards [hright, hleft] with z hrightz hleftz
  have hint (i j : ι) : Integrable (fun w : ι → S × S ↦
      if i ≠ j then h ((spliceSamples s (z, w) i).1, (spliceSamples s (z, w) j).2)
      else 0) (productSamples μ) := by
    by_cases hij : i ≠ j
    · simp_rw [if_pos hij]
      exact integrable_spliced_term μ h hh s z i j hij (hrightz i).1 (hleftz j).1
    · simp_rw [if_neg hij]
      simp
  unfold decoupledStatistic offDiagonalSum decoupledCross crossSum
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hint i j))]
  apply sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ ↦ hint i j)]
  apply sum_congr rfl
  intro j hj
  by_cases hij : i ≠ j
  · simp_rw [if_pos hij]
    exact integral_spliced_term μ h hh hz s z i j hij
      (hrightz i).1 (hleftz j).1 (hrightz i).2 (hleftz j).2
  · simp_rw [if_neg hij]
    simp

/-- Concrete canonical cross-block domination, with high moments inherited from the kernel. -/
theorem decoupled_cross_even_moment_le (h : S × S → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hh : MemLp h (2 * k : ℕ) (μ.prod μ))
    (hr0 : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
    (hl0 : ∀ᵐ y ∂μ, (∫ x, h (x, y) ∂μ) = 0) (s : ι → Bool) :
    (∫ z, |decoupledCross h s z| ^ (2 * k) ∂productSamples μ) ≤
      ∫ z, |decoupledStatistic (ι := ι) h z| ^ (2 * k) ∂productSamples μ := by
  have hk' : (1 : ℝ≥0∞) ≤ (2 * k : ℕ) := by
    have hp : 1 ≤ 2 * k := by omega
    exact_mod_cast hp
  have hd := memLp_decoupledStatistic (ι := ι) μ h (2 * k : ℕ) hh
  have hsp := hd.comp_measurePreserving (spliceSamples_measurePreserving μ s)
  have hI : Integrable (fun p ↦ decoupledStatistic (ι := ι) h (spliceSamples s p))
      ((productSamples μ).prod (productSamples μ)) := hsp.integrable hk'
  have hpI : Integrable (fun p ↦ |decoupledStatistic (ι := ι) h (spliceSamples s p)| ^ (2 * k))
      ((productSamples μ).prod (productSamples μ)) := by
    simpa only [Real.norm_eq_abs, Function.comp_def] using hsp.integrable_norm_pow'
  have hj := product_average_even_moment (productSamples μ) (productSamples μ)
    (fun p ↦ decoupledStatistic (ι := ι) h (spliceSamples s p)) k hI hpI
  have havg := mean_spliced_eq_cross (ι := ι) μ h (hh.integrable hk') hr0 hl0 s
  have he : (∫ z, |∫ w, decoupledStatistic (ι := ι) h (spliceSamples s (z, w))
      ∂productSamples μ| ^ (2 * k) ∂productSamples μ) =
      ∫ z, |decoupledCross h s z| ^ (2 * k) ∂productSamples μ := by
    apply integral_congr_ae
    filter_upwards [havg] with z hz
    rw [hz]
  rw [he] at hj
  have hpow : AEStronglyMeasurable (fun z ↦ |decoupledStatistic (ι := ι) h z| ^ (2 * k))
      (productSamples μ) := by
    simpa only [Real.norm_eq_abs] using hd.integrable_norm_pow'.aestronglyMeasurable
  have hlaw := integral_comp_preserving (spliceSamples_measurePreserving μ s)
    (fun z ↦ |decoupledStatistic (ι := ι) h z| ^ (2 * k)) hpow
  rw [hlaw] at hj
  exact hj


/- Integrate the selector comparison using the actual finite product laws. -/

lemma measurable_coupledCross_pair (h : S × S → ℝ) (hh : Measurable h) :
    Measurable (fun p : (ι → S × S) × (ι → Bool) ↦ coupledCross h p.2 p.1) := by
  unfold coupledCross crossSum
  apply Finset.measurable_sum
  intro i hi
  apply Finset.measurable_sum
  intro j hj
  by_cases hij : i ≠ j
  · simp_rw [if_pos hij]
    have hbi : Measurable (fun p : (ι → S × S) × (ι → Bool) ↦ bit (p.2 i)) :=
      (measurable_of_finite bit).comp ((measurable_pi_apply i).comp measurable_snd)
    have hbj : Measurable (fun p : (ι → S × S) × (ι → Bool) ↦ bit (p.2 j)) :=
      (measurable_of_finite bit).comp ((measurable_pi_apply j).comp measurable_snd)
    have hhi : Measurable (fun p : (ι → S × S) × (ι → Bool) ↦ (p.1 i).1) :=
      measurable_fst.comp ((measurable_pi_apply i).comp measurable_fst)
    have hhj : Measurable (fun p : (ι → S × S) × (ι → Bool) ↦ (p.1 j).1) :=
      measurable_fst.comp ((measurable_pi_apply j).comp measurable_fst)
    exact (hbi.mul (measurable_const.sub hbj)).mul (hh.comp (hhi.prodMk hhj))
  · simp_rw [if_neg hij]
    exact measurable_const

lemma integrable_coupledCross_power_prod (h : S × S → ℝ) (hm : Measurable h)
    (k : ℕ) (hh : MemLp h (2 * k : ℕ) (μ.prod μ)) :
    Integrable (fun p : (ι → S × S) × (ι → Bool) ↦ |coupledCross h p.2 p.1| ^ (2 * k))
      ((productSamples μ).prod (selectorLaw ι)) := by
  have hmeas := (continuous_pow (2 * k)).measurable.comp
    (continuous_abs.measurable.comp (measurable_coupledCross_pair (ι := ι) h hm))
  apply (integrable_prod_iff' hmeas.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun s ↦ by
      simpa only [Real.norm_eq_abs, Function.comp_def] using
        (memLp_coupledCross (ι := ι) μ h (2 * k : ℕ) hh s).integrable_norm_pow'
  · exact Integrable.of_finite

/-- The actual coupled versus independent-copy even-moment comparison with exact factor four. -/
theorem coupled_even_moment_le (h : S × S → ℝ) (hm : Measurable h)
    (k : ℕ) (hk : 1 ≤ k) (hh : MemLp h (2 * k : ℕ) (μ.prod μ))
    (hr0 : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
    (hl0 : ∀ᵐ y ∂μ, (∫ x, h (x, y) ∂μ) = 0) :
    (∫ z, |coupledStatistic (ι := ι) h z| ^ (2 * k) ∂productSamples μ) ≤
      4 ^ (2 * k) * ∫ z, |decoupledStatistic (ι := ι) h z| ^ (2 * k) ∂productSamples μ := by
  have hpI : Integrable (fun z ↦ |coupledStatistic (ι := ι) h z| ^ (2 * k))
      (productSamples μ) := by
    simpa only [Real.norm_eq_abs] using
      (memLp_coupledStatistic (ι := ι) μ h (2 * k : ℕ) hh).integrable_norm_pow'
  have hPI := integrable_coupledCross_power_prod (ι := ι) μ h hm k hh
  have hsel : ∀ z : ι → S × S, |coupledStatistic (ι := ι) h z| ^ (2 * k) ≤
      4 ^ (2 * k) * ∫ s, |coupledCross h s z| ^ (2 * k) ∂selectorLaw ι := by
    intro z
    exact selector_even_moment (fun i j ↦ h ((z i).1, (z j).1)) k
  have hint := integral_mono_ae hpI (hPI.integral_prod_left.const_mul (4 ^ (2 * k)))
    (Filter.Eventually.of_forall hsel)
  rw [integral_const_mul] at hint
  have hswap : (∫ z, ∫ s, |coupledCross h s z| ^ (2 * k) ∂selectorLaw ι ∂productSamples μ) =
      ∫ s, ∫ z, |coupledCross h s z| ^ (2 * k) ∂productSamples μ ∂selectorLaw ι := by
    calc
      _ = ∫ p, |coupledCross h p.2 p.1| ^ (2 * k)
          ∂(productSamples μ).prod (selectorLaw ι) := (integral_prod _ hPI).symm
      _ = ∫ q : (ι → Bool) × (ι → S × S), |coupledCross h q.1 q.2| ^ (2 * k)
          ∂(selectorLaw ι).prod (productSamples μ) :=
        (integral_comp_preserving
          (Measure.measurePreserving_swap (μ := selectorLaw ι) (ν := productSamples μ))
          (fun p ↦ |coupledCross h p.2 p.1| ^ (2 * k)) hPI.aestronglyMeasurable).symm
      _ = _ := integral_prod _ hPI.swap
  rw [hswap] at hint
  have hs : ∀ s : ι → Bool, (∫ z, |coupledCross h s z| ^ (2 * k) ∂productSamples μ) ≤
      ∫ z, |decoupledStatistic (ι := ι) h z| ^ (2 * k) ∂productSamples μ := by
    intro s
    rw [cross_even_moment_same_law μ h s k]
    exact decoupled_cross_even_moment_le μ h k hk hh hr0 hl0 s
  have havg := integral_mono_ae (μ := selectorLaw ι) Integrable.of_finite
    (integrable_const (∫ z, |decoupledStatistic (ι := ι) h z| ^ (2 * k) ∂productSamples μ))
    (Filter.Eventually.of_forall hs)
  have havg' : (∫ s, ∫ z, |coupledCross h s z| ^ (2 * k)
      ∂productSamples μ ∂selectorLaw ι) ≤
      ∫ z, |decoupledStatistic (ι := ι) h z| ^ (2 * k) ∂productSamples μ := by
    simpa using havg
  exact hint.trans (mul_le_mul_of_nonneg_left havg' (by positivity))

/-- Explicitly includes empty and singleton index spaces. -/
lemma offDiagonalSum_subsingleton [Subsingleton ι] (a : ι → ι → ℝ) :
    offDiagonalSum a = 0 := by
  unfold offDiagonalSum
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  simp [Subsingleton.elim i j]

lemma coupledStatistic_subsingleton [Subsingleton ι] (h : S × S → ℝ) (z : ι → S × S) :
    coupledStatistic (ι := ι) h z = 0 := offDiagonalSum_subsingleton _

lemma decoupledStatistic_subsingleton [Subsingleton ι] (h : S × S → ℝ) (z : ι → S × S) :
    decoupledStatistic (ι := ι) h z = 0 := offDiagonalSum_subsingleton _

theorem scalar_even_moment_decoupling (h : S × S → ℝ) (hm : Measurable h)
    (k : ℕ) (hk : 1 ≤ k) (hh : MemLp h (2 * k : ℕ) (μ.prod μ))
    (hr0 : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
    (hl0 : ∀ᵐ y ∂μ, (∫ x, h (x, y) ∂μ) = 0) :
    (∫ x : ι → S, |offDiagonalSum (fun i j ↦ h (x i, x j))| ^ (2 * k)
      ∂Measure.pi (fun _ : ι ↦ μ)) ≤
      4 ^ (2 * k) * ∫ p : (ι → S) × (ι → S),
        |offDiagonalSum (fun i j ↦ h (p.1 i, p.2 j))| ^ (2 * k)
          ∂(Measure.pi (fun _ : ι ↦ μ)).prod (Measure.pi (fun _ : ι ↦ μ)) := by
  have hmC : Measurable (fun x : ι → S ↦
      |offDiagonalSum (fun i j ↦ h (x i, x j))| ^ (2 * k)) := by
    have hmS : Measurable (fun x : ι → S ↦ offDiagonalSum (fun i j ↦ h (x i, x j))) := by
      unfold offDiagonalSum
      apply Finset.measurable_sum
      intro i hi
      apply Finset.measurable_sum
      intro j hj
      by_cases hij : i ≠ j
      · simp_rw [if_pos hij]
        exact hm.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
      · simp_rw [if_neg hij]
        exact measurable_const
    exact (continuous_pow (2 * k)).measurable.comp (continuous_abs.measurable.comp hmS)
  have hmD : Measurable (fun p : (ι → S) × (ι → S) ↦
      |offDiagonalSum (fun i j ↦ h (p.1 i, p.2 j))| ^ (2 * k)) := by
    have hmS : Measurable (fun p : (ι → S) × (ι → S) ↦
        offDiagonalSum (fun i j ↦ h (p.1 i, p.2 j))) := by
      unfold offDiagonalSum
      apply Finset.measurable_sum
      intro i hi
      apply Finset.measurable_sum
      intro j hj
      by_cases hij : i ≠ j
      · simp_rw [if_pos hij]
        exact hm.comp (((measurable_pi_apply i).comp measurable_fst).prodMk
          ((measurable_pi_apply j).comp measurable_snd))
      · simp_rw [if_neg hij]
        exact measurable_const
    exact (continuous_pow (2 * k)).measurable.comp (continuous_abs.measurable.comp hmS)
  have hc := integral_comp_preserving (firstSamples_measurePreserving (ι := ι) μ)
    (fun x : ι → S ↦ |offDiagonalSum (fun i j ↦ h (x i, x j))| ^ (2 * k))
    hmC.aestronglyMeasurable
  change (∫ z, |coupledStatistic (ι := ι) h z| ^ (2 * k) ∂productSamples μ) = _ at hc
  let e := MeasurableEquiv.arrowProdEquivProdArrow S S ι
  have he : MeasurePreserving e (productSamples μ)
      ((Measure.pi (fun _ : ι ↦ μ)).prod (Measure.pi (fun _ : ι ↦ μ))) :=
    measurePreserving_arrowProdEquivProdArrow S S ι (fun _ ↦ μ) (fun _ ↦ μ)
  have hd := integral_comp_preserving he
    (fun p : (ι → S) × (ι → S) ↦
      |offDiagonalSum (fun i j ↦ h (p.1 i, p.2 j))| ^ (2 * k)) hmD.aestronglyMeasurable
  change (∫ z, |decoupledStatistic (ι := ι) h z| ^ (2 * k) ∂productSamples μ) = _ at hd
  have ht := coupled_even_moment_le (ι := ι) μ h hm k hk hh hr0 hl0
  rw [hc, hd] at ht
  exact ht

lemma left_canonical_of_symmetric (h : S × S → ℝ)
    (hsymm : ∀ x y, h (x, y) = h (y, x))
    (hr0 : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0) :
    ∀ᵐ y ∂μ, (∫ x, h (x, y) ∂μ) = 0 := by
  filter_upwards [hr0] with y hy
  calc
    (∫ x, h (x, y) ∂μ) = ∫ x, h (y, x) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x ↦ hsymm x y)
    _ = 0 := hy

/-- Source-facing specialization for a symmetric canonical scalar kernel and Fin n samples. -/
theorem scalar_even_moment_decoupling_symmetric (n : ℕ) (h : S × S → ℝ)
    (hm : Measurable h) (hsymm : ∀ x y, h (x, y) = h (y, x))
    (k : ℕ) (hk : 1 ≤ k) (hh : MemLp h (2 * k : ℕ) (μ.prod μ))
    (hr0 : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0) :
    (∫ x : Fin n → S, |offDiagonalSum (fun i j ↦ h (x i, x j))| ^ (2 * k)
      ∂Measure.pi (fun _ : Fin n ↦ μ)) ≤
      4 ^ (2 * k) * ∫ p : (Fin n → S) × (Fin n → S),
        |offDiagonalSum (fun i j ↦ h (p.1 i, p.2 j))| ^ (2 * k)
          ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ)) :=
  scalar_even_moment_decoupling (ι := Fin n) μ h hm k hk hh hr0
    (left_canonical_of_symmetric μ h hsymm hr0)



theorem scalar_even_moments_subsingleton [Subsingleton ι] (h : S × S → ℝ)
    (k : ℕ) (hk : 1 ≤ k) :
    ((∫ x : ι → S, |offDiagonalSum (fun i j ↦ h (x i, x j))| ^ (2 * k)
      ∂Measure.pi (fun _ : ι ↦ μ)) = 0) ∧
    ((∫ p : (ι → S) × (ι → S), |offDiagonalSum (fun i j ↦ h (p.1 i, p.2 j))| ^ (2 * k)
      ∂(Measure.pi (fun _ : ι ↦ μ)).prod (Measure.pi (fun _ : ι ↦ μ))) = 0) := by
  have hp : 2 * k ≠ 0 := by omega
  constructor <;> simp [offDiagonalSum_subsingleton, hp]

/-- The zero-sample endpoint is checked without any kernel integrability premise. -/
theorem scalar_even_moments_fin_zero (h : S × S → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ((∫ x : Fin 0 → S, |offDiagonalSum (fun i j ↦ h (x i, x j))| ^ (2 * k)
      ∂Measure.pi (fun _ : Fin 0 ↦ μ)) = 0) ∧
    ((∫ p : (Fin 0 → S) × (Fin 0 → S), |offDiagonalSum (fun i j ↦ h (p.1 i, p.2 j))| ^ (2 * k)
      ∂(Measure.pi (fun _ : Fin 0 ↦ μ)).prod (Measure.pi (fun _ : Fin 0 ↦ μ))) = 0) :=
  scalar_even_moments_subsingleton (ι := Fin 0) μ h k hk

/-- The manuscript's one-sample zero moment, on both the original and independent-copy laws. -/
theorem scalar_even_moments_fin_one (h : S × S → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ((∫ x : Fin 1 → S, |offDiagonalSum (fun i j ↦ h (x i, x j))| ^ (2 * k)
      ∂Measure.pi (fun _ : Fin 1 ↦ μ)) = 0) ∧
    ((∫ p : (Fin 1 → S) × (Fin 1 → S), |offDiagonalSum (fun i j ↦ h (p.1 i, p.2 j))| ^ (2 * k)
      ∂(Measure.pi (fun _ : Fin 1 ↦ μ)).prod (Measure.pi (fun _ : Fin 1 ↦ μ))) = 0) :=
  scalar_even_moments_subsingleton (ι := Fin 1) μ h k hk

#print axioms DGRHS.Decoupling.scalar_even_moments_fin_zero
#print axioms DGRHS.Decoupling.scalar_even_moments_fin_one
#print axioms DGRHS.Decoupling.coupled_even_moment_le
#print axioms DGRHS.Decoupling.scalar_even_moment_decoupling
#print axioms DGRHS.Decoupling.scalar_even_moment_decoupling_symmetric

#print axioms DGRHS.Decoupling.mean_spliced_eq_cross
#print axioms DGRHS.Decoupling.decoupled_cross_even_moment_le

#print axioms DGRHS.Decoupling.memLp_coupledStatistic
#print axioms DGRHS.Decoupling.memLp_decoupledStatistic
#print axioms DGRHS.Decoupling.cross_even_moment_same_law

end DGRHS.Decoupling
