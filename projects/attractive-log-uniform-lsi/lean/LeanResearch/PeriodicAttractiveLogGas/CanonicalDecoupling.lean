import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.Convex.Integral
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Source `thm:canonical-pairs`: actual triangular pair sums, centering and
the random-partition decoupling step. Pairwise integrability/MemLp are explicit
temporary inputs to be supplied by the source factorial-moment hypotheses. -/

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal

namespace PeriodicAttractiveLogGas.CanonicalDecoupling

variable {m : ℕ} {α : Fin m → Type*} [∀ i, MeasurableSpace (α i)]
  (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
  (f : ∀ i j, α i → α j → ℝ)

def pairSum (X : ∀ i, α i) : ℝ := ∑ i, ∑ j, f i j (X i) (X j)

def decoupledSum (Z : (∀ i, α i) × (∀ i, α i)) : ℝ :=
  ∑ i, ∑ j, f i j (Z.1 i) (Z.2 j)

theorem measurePreserving_pair_eval {i j : Fin m} (hij : i ≠ j) :
    MeasurePreserving (fun X : ∀ i, α i => (X i, X j))
      (Measure.pi ν) ((ν i).prod (ν j)) := by
  have hind : iIndepFun (fun i (X : ∀ i, α i) => X i) (Measure.pi ν) :=
    iIndepFun_pi (fun i => aemeasurable_id)
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  rw [(hind.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable]
  rw [(measurePreserving_eval ν i).map_eq, (measurePreserving_eval ν j).map_eq]

theorem measurePreserving_decoupled_eval (i j : Fin m) :
    MeasurePreserving (fun Z : (∀ i, α i) × (∀ i, α i) => (Z.1 i, Z.2 j))
      ((Measure.pi ν).prod (Measure.pi ν)) ((ν i).prod (ν j)) :=
  (measurePreserving_eval ν i).prod (measurePreserving_eval ν j)

theorem integral_comp_of_measurePreserving {β γ : Type*}
    [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure β} {ρ : Measure γ}
    {T : β → γ} (hT : MeasurePreserving T μ ρ) {g : γ → ℝ}
    (hg : AEStronglyMeasurable g ρ) :
    (∫ x, g (T x) ∂μ) = ∫ y, g y ∂ρ := by
  have hg' : AEStronglyMeasurable g (μ.map T) := hT.map_eq.symm ▸ hg
  exact (integral_map hT.aemeasurable hg').symm.trans (by rw [hT.map_eq])

theorem integrable_pair_term
    (htri : ∀ i j, ¬ i < j → ∀ x y, f i j x y = 0)
    (hint : ∀ i j, Integrable (Function.uncurry (f i j)) ((ν i).prod (ν j)))
    (i j : Fin m) : Integrable (fun X : ∀ i, α i => f i j (X i) (X j)) (Measure.pi ν) := by
  by_cases hij : i < j
  · exact (measurePreserving_pair_eval ν (ne_of_lt hij)).integrable_comp_of_integrable (hint i j)
  · have he : (fun X : ∀ i, α i => f i j (X i) (X j)) = fun _ => 0 :=
      funext (fun X => htri i j hij (X i) (X j))
    rw [he]
    exact integrable_zero _ _ _

theorem integrable_pairSum
    (htri : ∀ i j, ¬ i < j → ∀ x y, f i j x y = 0)
    (hint : ∀ i j, Integrable (Function.uncurry (f i j)) ((ν i).prod (ν j))) :
    Integrable (pairSum f) (Measure.pi ν) := by
  apply integrable_finsetSum
  intro i _
  exact integrable_finsetSum _ (fun j _ => integrable_pair_term ν f htri hint i j)

theorem integrable_decoupledSum
    (hint : ∀ i j, Integrable (Function.uncurry (f i j)) ((ν i).prod (ν j))) :
    Integrable (decoupledSum f) ((Measure.pi ν).prod (Measure.pi ν)) := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (measurePreserving_decoupled_eval ν i j).integrable_comp_of_integrable (hint i j)

theorem integral_kernel_eq_zero
    (hint : ∀ i j, Integrable (Function.uncurry (f i j)) ((ν i).prod (ν j)))
    (hzero : ∀ i j, ∀ᵐ x ∂ν i, (∫ y, f i j x y ∂ν j) = 0) (i j : Fin m) :
    (∫ z, Function.uncurry (f i j) z ∂(ν i).prod (ν j)) = 0 := by
  rw [integral_prod _ (hint i j)]
  calc
    (∫ x, ∫ y, f i j x y ∂ν j ∂ν i) = ∫ _ : α i, (0 : ℝ) ∂ν i :=
      integral_congr_ae (hzero i j)
    _ = 0 := integral_zero _ _

theorem integral_pairSum_eq_zero
    (htri : ∀ i j, ¬ i < j → ∀ x y, f i j x y = 0)
    (hint : ∀ i j, Integrable (Function.uncurry (f i j)) ((ν i).prod (ν j)))
    (hzero : ∀ i j, ∀ᵐ x ∂ν i, (∫ y, f i j x y ∂ν j) = 0) :
    (∫ X, pairSum f X ∂Measure.pi ν) = 0 := by
  unfold pairSum
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => integrable_pair_term ν f htri hint i j))]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_finsetSum _ (fun j _ => integrable_pair_term ν f htri hint i j)]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : i < j
  · exact (integral_comp_of_measurePreserving
      (measurePreserving_pair_eval ν (ne_of_lt hij)) (hint i j).aestronglyMeasurable).trans
        (integral_kernel_eq_zero ν f hint hzero i j)
  · simp [htri i j hij]

theorem memLp_pairSum {p : ℝ≥0∞}
    (htri : ∀ i j, ¬ i < j → ∀ x y, f i j x y = 0)
    (hmem : ∀ i j, MemLp (Function.uncurry (f i j)) p ((ν i).prod (ν j))) :
    MemLp (pairSum f) p (Measure.pi ν) := by
  apply memLp_finsetSum
  intro i _
  apply memLp_finsetSum
  intro j _
  by_cases hij : i < j
  · exact (hmem i j).comp_measurePreserving (measurePreserving_pair_eval ν (ne_of_lt hij))
  · have he : (fun X : ∀ i, α i => f i j (X i) (X j)) = fun _ => 0 :=
      funext (fun X => htri i j hij (X i) (X j))
    rw [he]
    exact MemLp.zero'

theorem memLp_decoupledSum {p : ℝ≥0∞}
    (hmem : ∀ i j, MemLp (Function.uncurry (f i j)) p ((ν i).prod (ν j))) :
    MemLp (decoupledSum f) p ((Measure.pi ν).prod (Measure.pi ν)) := by
  apply memLp_finsetSum
  intro i _
  apply memLp_finsetSum
  intro j _
  exact (hmem i j).comp_measurePreserving (measurePreserving_decoupled_eval ν i j)

theorem integrable_abs_rpow_pairSum {q : ℝ} (hq : 0 ≤ q)
    (htri : ∀ i j, ¬ i < j → ∀ x y, f i j x y = 0)
    (hmem : ∀ i j, MemLp (Function.uncurry (f i j)) (ENNReal.ofReal q) ((ν i).prod (ν j))) :
    Integrable (fun X => |pairSum f X| ^ q) (Measure.pi ν) := by
  simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hq] using
    (memLp_pairSum ν f htri hmem).integrable_norm_rpow'

theorem integrable_abs_rpow_decoupledSum {q : ℝ} (hq : 0 ≤ q)
    (hmem : ∀ i j, MemLp (Function.uncurry (f i j)) (ENNReal.ofReal q) ((ν i).prod (ν j))) :
    Integrable (fun Z => |decoupledSum f Z| ^ q) ((Measure.pi ν).prod (Measure.pi ν)) := by
  simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hq] using
    (memLp_decoupledSum ν f hmem).integrable_norm_rpow'

/-- A fair coin; the product law below is the source's independent Bernoulli partition. -/
def coin : Measure Bool := bernoulliMeasure true false ⟨1 / 2, by norm_num, by norm_num⟩

instance : IsProbabilityMeasure coin := by unfold coin; infer_instance

def partitionLaw (m : ℕ) : Measure (Fin m → Bool) := Measure.pi (fun _ => coin)

instance (m : ℕ) : IsProbabilityMeasure (partitionLaw m) := by
  unfold partitionLaw
  infer_instance

def crossSum (δ : Fin m → Bool) (X : ∀ i, α i) : ℝ :=
  ∑ i, ∑ j, if δ i = true ∧ δ j = false then f i j (X i) (X j) else 0

theorem integral_partition_indicator {i j : Fin m} (hij : i ≠ j) (c : ℝ) :
    (∫ δ, (if δ i = true ∧ δ j = false then c else 0) ∂partitionLaw m) = c / 4 := by
  have hmp := measurePreserving_pair_eval (fun _ : Fin m => coin) hij
  have he := integral_comp_of_measurePreserving hmp
    (g := fun z : Bool × Bool => if z.1 = true ∧ z.2 = false then c else 0)
    (Integrable.of_finite.aestronglyMeasurable)
  change (∫ δ, (if δ i = true ∧ δ j = false then c else 0)
    ∂Measure.pi (fun _ : Fin m => coin)) = _
  rw [he, integral_prod _ Integrable.of_finite]
  simp [coin, integral_bernoulliMeasure, smul_eq_mul]
  ring

omit [∀ i, MeasurableSpace (α i)] in
theorem integral_crossSum
    (htri : ∀ i j, ¬ i < j → ∀ x y, f i j x y = 0) (X : ∀ i, α i) :
    (∫ δ, crossSum f δ X ∂partitionLaw m) = pairSum f X / 4 := by
  unfold crossSum pairSum
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · exact integral_partition_indicator (ne_of_lt hij) _
  · simp [htri i j hij]

omit [∀ i, MeasurableSpace (α i)] in
/-- Pointwise random-partition identity, including empty alphabets and zero kernels. -/
theorem pairSum_eq_four_integral_crossSum
    (htri : ∀ i j, ¬ i < j → ∀ x y, f i j x y = 0) (X : ∀ i, α i) :
    pairSum f X = 4 * ∫ δ, crossSum f δ X ∂partitionLaw m := by
  rw [integral_crossSum f htri X]
  ring

/-- Select each coordinate from the first or second independent copy. -/
def mix (δ : Fin m → Bool) (Z : (∀ i, α i) × (∀ i, α i)) (i : Fin m) : α i :=
  if δ i = true then Z.1 i else Z.2 i

theorem measurable_mix (δ : Fin m → Bool) : Measurable (mix (α := α) δ) := by
  apply Measurable.of_eval
  intro i
  have hf : Measurable (fun Z : (∀ i, α i) × (∀ i, α i) => Z.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have hs : Measurable (fun Z : (∀ i, α i) × (∀ i, α i) => Z.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  by_cases hi : δ i = true
  · simpa [mix, hi] using hf
  · simpa [mix, hi] using hs

theorem measurePreserving_mix (δ : Fin m → Bool) :
    MeasurePreserving (mix (α := α) δ) ((Measure.pi ν).prod (Measure.pi ν)) (Measure.pi ν) := by
  refine ⟨measurable_mix δ, (Measure.pi_eq (μ := ν) ?_).symm⟩
  intro s hs
  rw [Measure.map_apply (measurable_mix δ) (MeasurableSet.univ_pi hs)]
  have he : mix (α := α) δ ⁻¹' Set.pi Set.univ s =
      (Set.pi Set.univ (fun i => if δ i = true then s i else Set.univ)) ×ˢ
        (Set.pi Set.univ (fun i => if δ i = true then Set.univ else s i)) := by
    ext Z
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ_pi]
    constructor
    · intro h
      constructor
      · intro i
        by_cases hi : δ i = true
        · simpa [mix, hi] using h i
        · simp [hi]
      · intro i
        by_cases hi : δ i = true
        · simp [hi]
        · simpa [mix, hi] using h i
    · rintro ⟨h₁, h₂⟩ i
      by_cases hi : δ i = true
      · simpa [mix, hi] using h₁ i
      · simpa [mix, hi] using h₂ i
  rw [he, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : δ i = true <;> simp [hi]

/-- Reorder four independent blocks. This supplies the joint law used when
integrating the missing arguments in the source's conditional expectation. -/
theorem measurePreserving_middle_swap {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μA : Measure A) (μB : Measure B) (μC : Measure C) (μD : Measure D)
    [SFinite μA] [SFinite μB] [SFinite μC] [SFinite μD] :
    MeasurePreserving (fun z : (A × B) × (C × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
      ((μA.prod μB).prod (μC.prod μD)) ((μA.prod μC).prod (μB.prod μD)) := by
  have h₁ := measurePreserving_prodAssoc μA μB (μC.prod μD)
  have h₂ := (MeasurePreserving.id μA).prod (measurePreserving_prodAssoc μB μC μD).symm
  have h₃ := (MeasurePreserving.id μA).prod
    ((Measure.measurePreserving_swap (μ := μB) (ν := μC)).prod (MeasurePreserving.id μD))
  have h₄ := (MeasurePreserving.id μA).prod (measurePreserving_prodAssoc μC μB μD)
  have h₅ := (measurePreserving_prodAssoc μA μC (μB.prod μD)).symm
  exact h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))

def resample (δ : Fin m → Bool)
    (ZW : ((∀ i, α i) × (∀ i, α i)) × ((∀ i, α i) × (∀ i, α i))) :
    (∀ i, α i) × (∀ i, α i) :=
  (mix δ (ZW.1.1, ZW.2.1), mix (fun i => !(δ i)) (ZW.1.2, ZW.2.2))

theorem measurePreserving_resample (δ : Fin m → Bool) :
    MeasurePreserving (resample (α := α) δ)
      (((Measure.pi ν).prod (Measure.pi ν)).prod ((Measure.pi ν).prod (Measure.pi ν)))
      ((Measure.pi ν).prod (Measure.pi ν)) := by
  exact ((measurePreserving_mix ν δ).prod
    (measurePreserving_mix ν (fun i => !(δ i)))).comp
      (measurePreserving_middle_swap (Measure.pi ν) (Measure.pi ν) (Measure.pi ν) (Measure.pi ν))

def decoupledCrossSum (δ : Fin m → Bool) (Z : (∀ i, α i) × (∀ i, α i)) : ℝ :=
  ∑ i, ∑ j, if δ i = true ∧ δ j = false then f i j (Z.1 i) (Z.2 j) else 0

omit [∀ i, MeasurableSpace (α i)] in
theorem crossSum_mix (δ : Fin m → Bool) (Z : (∀ i, α i) × (∀ i, α i)) :
    crossSum f δ (mix δ Z) = decoupledCrossSum f δ Z := by
  unfold crossSum decoupledCrossSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : δ i = true ∧ δ j = false
  · simp [h, mix]
  · simp [h]

/-- Jensen for the absolute real power, with both integrability obligations explicit. -/
theorem abs_integral_rpow_le {β : Type*} [MeasurableSpace β] {μ : Measure β}
    [IsProbabilityMeasure μ] {g : β → ℝ} {q : ℝ} (hq : 1 ≤ q)
    (hg : Integrable g μ) (hgq : Integrable (fun x => |g x| ^ q) μ) :
    |∫ x, g x ∂μ| ^ q ≤ ∫ x, |g x| ^ q ∂μ := by
  have hq0 : 0 ≤ q := by linarith
  calc
    |∫ x, g x ∂μ| ^ q ≤ (∫ x, |g x| ∂μ) ^ q := by
      apply Real.rpow_le_rpow (abs_nonneg _) _ hq0
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm g
    _ ≤ _ := (convexOn_rpow hq).map_integral_le
      (Real.continuous_rpow_const hq0).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall (fun x => abs_nonneg (g x))) hg.abs hgq

/-- Integrating out an independent block contracts the q-th absolute moment.
This is the finite-product form of the source's conditional Jensen step. -/
theorem integral_abs_integral_rpow_le {β γ : Type*}
    [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure β} {ρ : Measure γ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] {g : β × γ → ℝ} {q : ℝ}
    (hq : 1 ≤ q) (hg : Integrable g (μ.prod ρ))
    (hgq : Integrable (fun z => |g z| ^ q) (μ.prod ρ)) :
    Integrable (fun x => |∫ y, g (x, y) ∂ρ| ^ q) μ ∧
      (∫ x, |∫ y, g (x, y) ∂ρ| ^ q ∂μ) ≤ ∫ z, |g z| ^ q ∂μ.prod ρ := by
  have hq0 : 0 ≤ q := by linarith
  have hbound : ∀ᵐ x ∂μ, |∫ y, g (x, y) ∂ρ| ^ q ≤ ∫ y, |g (x, y)| ^ q ∂ρ := by
    filter_upwards [hg.prod_right_ae, hgq.prod_right_ae] with x hx hxq
    exact abs_integral_rpow_le hq hx hxq
  have hmeas : AEStronglyMeasurable (fun x => |∫ y, g (x, y) ∂ρ| ^ q) μ := by
    simpa only [Real.norm_eq_abs] using (Real.continuous_rpow_const hq0).comp_aestronglyMeasurable
      hg.integral_prod_left.aestronglyMeasurable.norm
  have hi : Integrable (fun x => |∫ y, g (x, y) ∂ρ| ^ q) μ := by
    apply hgq.integral_prod_left.mono' hmeas
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hx
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, ∫ y, |g (x, y)| ^ q ∂ρ ∂μ := integral_mono_ae hi hgq.integral_prod_left hbound
    _ = _ := (integral_prod _ hgq).symm

theorem integral_resampled_term
    (hf : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hint : ∀ i j, Integrable (Function.uncurry (f i j)) ((ν i).prod (ν j)))
    (hleft : ∀ i j, ∀ᵐ y ∂ν j, (∫ x, f i j x y ∂ν i) = 0)
    (hright : ∀ i j, ∀ᵐ x ∂ν i, (∫ y, f i j x y ∂ν j) = 0)
    (δ : Fin m → Bool) (i j : Fin m) :
    ∀ᵐ Z ∂(Measure.pi ν).prod (Measure.pi ν),
      (∫ W, f i j ((resample δ (Z, W)).1 i) ((resample δ (Z, W)).2 j)
        ∂(Measure.pi ν).prod (Measure.pi ν)) =
      if δ i = true ∧ δ j = false then f i j (Z.1 i) (Z.2 j) else 0 := by
  have hp₁ (i : Fin m) : MeasurePreserving
      (fun Z : (∀ i, α i) × (∀ i, α i) => Z.1 i)
      ((Measure.pi ν).prod (Measure.pi ν)) (ν i) :=
    (measurePreserving_eval ν i).comp measurePreserving_fst
  have hp₂ (i : Fin m) : MeasurePreserving
      (fun Z : (∀ i, α i) × (∀ i, α i) => Z.2 i)
      ((Measure.pi ν).prod (Measure.pi ν)) (ν i) :=
    (measurePreserving_eval ν i).comp measurePreserving_snd
  cases hi : δ i <;> cases hj : δ j
  · filter_upwards [(hp₂ j).quasiMeasurePreserving.ae (hleft i j)] with Z hZ
    have hsec : Measurable (fun x => f i j x (Z.2 j)) :=
      (hf i j).comp (measurable_id.prodMk measurable_const)
    have he := integral_comp_of_measurePreserving (hp₁ i) hsec.aestronglyMeasurable
    simpa [resample, mix, hi, hj] using he.trans hZ
  · have he := (integral_comp_of_measurePreserving (measurePreserving_decoupled_eval ν i j)
      (hint i j).aestronglyMeasurable).trans (integral_kernel_eq_zero ν f hint hright i j)
    filter_upwards [] with Z
    simpa [resample, mix, hi, hj] using he
  · filter_upwards [] with Z
    simp [resample, mix, hi, hj]
  · filter_upwards [(hp₁ i).quasiMeasurePreserving.ae (hright i j)] with Z hZ
    have hsec : Measurable (fun y => f i j (Z.1 i) y) :=
      (hf i j).comp (measurable_const.prodMk measurable_id)
    have he := integral_comp_of_measurePreserving (hp₂ j) hsec.aestronglyMeasurable
    simpa [resample, mix, hi, hj] using he.trans hZ

/-- Averaging all omitted independent coordinates gives exactly the cross sum,
with equality almost everywhere, as in the source's conditional expectation. -/
theorem integral_resampledSum
    (hf : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hint : ∀ i j, Integrable (Function.uncurry (f i j)) ((ν i).prod (ν j)))
    (hleft : ∀ i j, ∀ᵐ y ∂ν j, (∫ x, f i j x y ∂ν i) = 0)
    (hright : ∀ i j, ∀ᵐ x ∂ν i, (∫ y, f i j x y ∂ν j) = 0)
    (δ : Fin m → Bool) :
    ∀ᵐ Z ∂(Measure.pi ν).prod (Measure.pi ν),
      (∫ W, decoupledSum f (resample δ (Z, W)) ∂(Measure.pi ν).prod (Measure.pi ν)) =
        decoupledCrossSum f δ Z := by
  have hsections : ∀ᵐ Z ∂(Measure.pi ν).prod (Measure.pi ν), ∀ i j,
      Integrable (fun W => f i j ((resample δ (Z, W)).1 i) ((resample δ (Z, W)).2 j))
        ((Measure.pi ν).prod (Measure.pi ν)) := by
    simp only [ae_all_iff]
    intro i j
    have hmp := (measurePreserving_decoupled_eval ν i j).comp (measurePreserving_resample ν δ)
    exact (hmp.integrable_comp_of_integrable (hint i j)).prod_right_ae
  have heqs : ∀ᵐ Z ∂(Measure.pi ν).prod (Measure.pi ν), ∀ i j,
      (∫ W, f i j ((resample δ (Z, W)).1 i) ((resample δ (Z, W)).2 j)
        ∂(Measure.pi ν).prod (Measure.pi ν)) =
      if δ i = true ∧ δ j = false then f i j (Z.1 i) (Z.2 j) else 0 := by
    simp only [ae_all_iff]
    exact integral_resampled_term ν f hf hint hleft hright δ
  filter_upwards [hsections, heqs] with Z hZ hEq
  unfold decoupledSum decoupledCrossSum
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hZ i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hZ i j)]
  exact Finset.sum_congr rfl (fun j _ => hEq i j)

theorem measurable_crossSum
    (hf : ∀ i j, Measurable (Function.uncurry (f i j))) (δ : Fin m → Bool) :
    Measurable (crossSum f δ) := by
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  by_cases h : δ i = true ∧ δ j = false
  · simp only [ite_eq_left h]
    exact (hf i j).comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
  · simp only [ite_eq_right h]
    exact measurable_const

theorem memLp_crossSum {p : ℝ≥0∞}
    (hmem : ∀ i j, MemLp (Function.uncurry (f i j)) p ((ν i).prod (ν j)))
    (δ : Fin m → Bool) : MemLp (crossSum f δ) p (Measure.pi ν) := by
  apply memLp_finsetSum
  intro i _
  apply memLp_finsetSum
  intro j _
  by_cases h : δ i = true ∧ δ j = false
  · have hij : i ≠ j := by
      intro he
      subst j
      simp_all
    simp only [ite_eq_left h]
    exact (hmem i j).comp_measurePreserving (measurePreserving_pair_eval ν hij)
  · simp only [ite_eq_right h]
    exact MemLp.zero'

theorem integrable_abs_rpow_crossSum {q : ℝ} (hq : 0 ≤ q)
    (hmem : ∀ i j, MemLp (Function.uncurry (f i j)) (ENNReal.ofReal q) ((ν i).prod (ν j)))
    (δ : Fin m → Bool) : Integrable (fun X => |crossSum f δ X| ^ q) (Measure.pi ν) := by
  simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hq] using
    (memLp_crossSum ν f hmem δ).integrable_norm_rpow'

/-- The two deterministic steps of the source argument: same law for the
cross sum, then Jensen after integrating all independent omitted arguments. -/
theorem integral_abs_rpow_crossSum_le
    (hf : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hleft : ∀ i j, ∀ᵐ y ∂ν j, (∫ x, f i j x y ∂ν i) = 0)
    (hright : ∀ i j, ∀ᵐ x ∂ν i, (∫ y, f i j x y ∂ν j) = 0)
    {q : ℝ} (hq : 1 ≤ q)
    (hmem : ∀ i j, MemLp (Function.uncurry (f i j)) (ENNReal.ofReal q) ((ν i).prod (ν j)))
    (δ : Fin m → Bool) :
    (∫ X, |crossSum f δ X| ^ q ∂Measure.pi ν) ≤
      ∫ Z, |decoupledSum f Z| ^ q ∂(Measure.pi ν).prod (Measure.pi ν) := by
  have hq0 : 0 ≤ q := by linarith
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq
  have hint : ∀ i j, Integrable (Function.uncurry (f i j)) ((ν i).prod (ν j)) :=
    fun i j => MemLp.integrable hp (hmem i j)
  have hi := integrable_decoupledSum ν f hint
  have hiq := integrable_abs_rpow_decoupledSum ν f hq0 hmem
  have hres := measurePreserving_resample ν δ
  have hJ := integral_abs_integral_rpow_le hq
    (hres.integrable_comp_of_integrable hi) (hres.integrable_comp_of_integrable hiq)
  have hmix := integral_comp_of_measurePreserving (measurePreserving_mix ν δ)
    (integrable_abs_rpow_crossSum ν f hq0 hmem δ).aestronglyMeasurable
  simp only [crossSum_mix] at hmix
  calc
    (∫ X, |crossSum f δ X| ^ q ∂Measure.pi ν) =
        ∫ Z, |decoupledCrossSum f δ Z| ^ q ∂(Measure.pi ν).prod (Measure.pi ν) := hmix.symm
    _ = ∫ Z, |∫ W, decoupledSum f (resample δ (Z, W))
        ∂(Measure.pi ν).prod (Measure.pi ν)| ^ q ∂(Measure.pi ν).prod (Measure.pi ν) := by
      apply integral_congr_ae
      filter_upwards [integral_resampledSum ν f hf hint hleft hright δ] with Z hZ
      rw [hZ]
    _ ≤ ∫ ZW, |decoupledSum f (resample δ ZW)| ^ q
        ∂((Measure.pi ν).prod (Measure.pi ν)).prod ((Measure.pi ν).prod (Measure.pi ν)) := hJ.2
    _ = _ := integral_comp_of_measurePreserving hres hiq.aestronglyMeasurable

omit [∀ i, MeasurableSpace (α i)] in
theorem abs_rpow_pairSum_le_partition_integral
    (htri : ∀ i j, ¬ i < j → ∀ x y, f i j x y = 0) {q : ℝ} (hq : 1 ≤ q)
    (X : ∀ i, α i) :
    |pairSum f X| ^ q ≤ (4 : ℝ) ^ q * ∫ δ, |crossSum f δ X| ^ q ∂partitionLaw m := by
  rw [pairSum_eq_four_integral_crossSum f htri X, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 4), Real.mul_rpow (by norm_num) (abs_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (abs_integral_rpow_le hq Integrable.of_finite Integrable.of_finite)
    (Real.rpow_nonneg (by norm_num) _)

/-- The actual source decoupling inequality. Pairwise MemLp is a tracked
temporary input; neither a decoupling estimate nor a projection identity is assumed. -/
theorem integral_abs_rpow_pairSum_le
    (htri : ∀ i j, ¬ i < j → ∀ x y, f i j x y = 0)
    (hf : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hleft : ∀ i j, ∀ᵐ y ∂ν j, (∫ x, f i j x y ∂ν i) = 0)
    (hright : ∀ i j, ∀ᵐ x ∂ν i, (∫ y, f i j x y ∂ν j) = 0)
    {q : ℝ} (hq : 1 ≤ q)
    (hmem : ∀ i j, MemLp (Function.uncurry (f i j)) (ENNReal.ofReal q) ((ν i).prod (ν j))) :
    (∫ X, |pairSum f X| ^ q ∂Measure.pi ν) ≤
      (4 : ℝ) ^ q * ∫ Z, |decoupledSum f Z| ^ q ∂(Measure.pi ν).prod (Measure.pi ν) := by
  have hq0 : 0 ≤ q := by linarith
  let G : (Fin m → Bool) × (∀ i, α i) → ℝ := fun P => |crossSum f P.1 P.2| ^ q
  have hGmeas : Measurable G := by
    apply measurable_from_prod_countable_right
    intro δ
    have hmabs : Measurable (fun X => |crossSum f δ X|) := by
      simpa only [Function.comp_def, Real.norm_eq_abs] using
        continuous_norm.measurable.comp (measurable_crossSum f hf δ)
    exact (Real.continuous_rpow_const hq0).measurable.comp hmabs
  have hGi : Integrable G ((partitionLaw m).prod (Measure.pi ν)) := by
    apply (integrable_prod_iff hGmeas.aestronglyMeasurable).mpr
    exact ⟨Filter.Eventually.of_forall (fun δ => integrable_abs_rpow_crossSum ν f hq0 hmem δ),
      Integrable.of_finite⟩
  have hAvg : Integrable (fun X => ∫ δ, |crossSum f δ X| ^ q ∂partitionLaw m) (Measure.pi ν) :=
    hGi.integral_prod_right
  calc
    (∫ X, |pairSum f X| ^ q ∂Measure.pi ν) ≤
        ∫ X, (4 : ℝ) ^ q * (∫ δ, |crossSum f δ X| ^ q ∂partitionLaw m) ∂Measure.pi ν :=
      integral_mono (integrable_abs_rpow_pairSum ν f hq0 htri hmem) (hAvg.const_mul _)
        (fun X => abs_rpow_pairSum_le_partition_integral f htri hq X)
    _ = (4 : ℝ) ^ q * ∫ δ, (∫ X, |crossSum f δ X| ^ q ∂Measure.pi ν) ∂partitionLaw m := by
      rw [integral_const_mul]
      congr 1
      exact (integral_integral_swap hGi).symm
    _ ≤ (4 : ℝ) ^ q * ∫ _δ : Fin m → Bool,
        (∫ Z, |decoupledSum f Z| ^ q ∂(Measure.pi ν).prod (Measure.pi ν)) ∂partitionLaw m := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
      exact integral_mono hGi.integral_prod_left (integrable_const _)
        (fun δ => integral_abs_rpow_crossSum_le ν f hf hleft hright hq hmem δ)
    _ = _ := by simp

theorem integral_decoupledSum_eq_zero
    (hint : ∀ i j, Integrable (Function.uncurry (f i j)) ((ν i).prod (ν j)))
    (hzero : ∀ i j, ∀ᵐ x ∂ν i, (∫ y, f i j x y ∂ν j) = 0) :
    (∫ Z, decoupledSum f Z ∂(Measure.pi ν).prod (Measure.pi ν)) = 0 := by
  have ht (i j : Fin m) :
      Integrable (fun Z : (∀ i, α i) × (∀ i, α i) => f i j (Z.1 i) (Z.2 j))
        ((Measure.pi ν).prod (Measure.pi ν)) :=
    (measurePreserving_decoupled_eval ν i j).integrable_comp_of_integrable (hint i j)
  unfold decoupledSum
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ht i j))]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_finsetSum _ (fun j _ => ht i j)]
  apply Finset.sum_eq_zero
  intro j _
  exact (integral_comp_of_measurePreserving (measurePreserving_decoupled_eval ν i j)
    (hint i j).aestronglyMeasurable).trans (integral_kernel_eq_zero ν f hint hzero i j)

end PeriodicAttractiveLogGas.CanonicalDecoupling
