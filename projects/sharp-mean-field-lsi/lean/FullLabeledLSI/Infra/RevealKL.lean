import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import SharpSymmetricLSI.Paper.CondEntropy

/-!
# Section 5 infrastructure, part 1: abstract relative-entropy lemmas

* `klDiv_compProd_same_all`: the integral form of the conditional relative entropy,
  `H(μ ⊗ κ | μ ⊗ η) = ∫ H(κ a | η a) dμ(a)`, valid in `ℝ≥0∞` without any finiteness assumption
  (the finite case is `SharpLSI.klDiv_compProd_same`).
* `klDiv_pi_marginals`: the total-correlation decomposition for a probability `P` on `Fin k → T`
  and arbitrary reference measures `Q l`:
  `H(P | ⊗ Q l) = H(P | ⊗ P_l) + ∑ H(P_l | Q l)`, where `P_l` is the `l`-th marginal of `P`.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

section General

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace.CountableOrCountablyGenerated α β]

/-- The integrand `a ↦ H(κ a | η a)` of the conditional relative entropy is measurable. -/
theorem measurable_klDiv_kernel (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    Measurable (fun a => klDiv (κ a) (η a)) := by
  classical
  have hmeas : Measurable (fun p : α × β =>
      ENNReal.ofReal (klFun (κ.rnDeriv η p.1 p.2).toReal)) :=
    by
      have h := Kernel.measurable_rnDeriv κ η
      fun_prop
  have hfun : ∀ a, κ a ≪ η a →
      klDiv (κ a) (η a) = ∫⁻ b, ENNReal.ofReal (klFun (κ.rnDeriv η a b).toReal) ∂η a := by
    intro a h
    rw [klDiv_eq_lintegral_klFun_of_ac h]
    refine lintegral_congr_ae ?_
    filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with b hb
    rw [hb]
  have heq : (fun a => klDiv (κ a) (η a)) = fun a =>
      if κ a ≪ η a then ∫⁻ b, ENNReal.ofReal (klFun (κ.rnDeriv η a b).toReal) ∂η a else ⊤ := by
    funext a
    by_cases h : κ a ≪ η a
    · simp only [h, ite_true]; exact hfun a h
    · simp only [h, ite_false]; exact klDiv_of_not_ac h
  rw [heq]
  exact Measurable.ite (Kernel.measurableSet_absolutelyContinuous κ η)
    hmeas.lintegral_kernel_prod_right' measurable_const

/-- Conditional relative entropy, integral form, in `ℝ≥0∞` (no finiteness assumption). -/
theorem klDiv_compProd_same_all (μ : Measure α) [IsProbabilityMeasure μ]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  by_cases hac : μ ⊗ₘ κ ≪ μ ⊗ₘ η
  · have hae : ∀ᵐ a ∂μ, κ a ≪ η a := hac.kernel_of_compProd
    rw [klDiv_eq_lintegral_klFun_of_ac hac]
    have hm : Measurable (fun p : α × β =>
        ENNReal.ofReal (klFun (κ.rnDeriv η p.1 p.2).toReal)) := by
      have h := Kernel.measurable_rnDeriv κ η
      fun_prop
    rw [lintegral_congr_ae (by
      filter_upwards [rnDeriv_measure_compProd_right μ κ η] with p hp
      rw [hp] : (fun p => ENNReal.ofReal (klFun (((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p).toReal))) =ᵐ[μ ⊗ₘ η]
        fun p => ENNReal.ofReal (klFun (κ.rnDeriv η p.1 p.2).toReal)),
      Measure.lintegral_compProd hm]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with a ha
    rw [klDiv_eq_lintegral_klFun_of_ac ha]
    refine lintegral_congr_ae ?_
    filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with b hb
    rw [hb]
  · rw [klDiv_of_not_ac hac]
    by_contra hne
    have hlt : ∫⁻ a, klDiv (κ a) (η a) ∂μ < ⊤ := lt_top_iff_ne_top.mpr (Ne.symm hne)
    have hlt' := ae_lt_top (measurable_klDiv_kernel κ η) hlt.ne
    exact hac (Measure.AbsolutelyContinuous.compProd_right (by
      filter_upwards [hlt'] with a ha
      exact (klDiv_ne_top_iff.mp ha.ne).1))

end General

section Pi

variable {k : ℕ} {T : Type*} [MeasurableSpace T]

/-- Auxiliary: Fubini for a product of `ℝ≥0∞`-valued coordinate functions on `Fin n → T`. -/
private theorem lintegral_pi_prod_aux :
    ∀ (n : ℕ) (μ : Fin n → Measure T) [∀ l, SigmaFinite (μ l)] (f : Fin n → T → ℝ≥0∞),
      (∀ l, Measurable (f l)) →
      ∫⁻ x, ∏ l, f l (x l) ∂(Measure.pi μ) = ∏ l, ∫⁻ t, f l t ∂(μ l) := by
  intro n
  induction n with
  | zero =>
    intro μ _ f _
    simp
  | succ n ih =>
    intro μ _ f hf
    have h := (measurePreserving_piFinSuccAbove μ 0).symm.lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _) (fun x => ∏ l, f l (x l))
    rw [← h]
    simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
      Fin.zero_succAbove, cast_eq, Fin.cons_zero]
    have hgm : Measurable (fun y : Fin n → T => ∏ i, f i.succ (y i)) :=
      Finset.measurable_fun_prod _ fun l _ => (hf l.succ).comp (measurable_pi_apply l)
    rw [lintegral_prod_mul (f := f 0) (g := fun y : Fin n → T => ∏ i, f i.succ (y i))
      (hf 0).aemeasurable hgm.aemeasurable,
      ih (fun i => μ i.succ) (fun i => f i.succ) (fun i => hf _)]

/-- Auxiliary: a product of measures with densities is the density of the product. -/
private theorem pi_eq_withDensity_prod (Q ν : Fin k → Measure T) [∀ l, IsProbabilityMeasure (Q l)]
    [∀ l, IsProbabilityMeasure (ν l)] (g : Fin k → T → ℝ≥0∞) (hg : ∀ l, Measurable (g l))
    (hν : ∀ l, ν l = (Q l).withDensity (g l)) :
    Measure.pi ν = (Measure.pi Q).withDensity (fun x => ∏ l, g l (x l)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator
    (MeasurableSet.univ_pi hs)]
  have hind : ∀ x : Fin k → T, (Set.univ.pi s).indicator (fun x => ∏ l, g l (x l)) x =
      ∏ l, (s l).indicator (g l) (x l) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [Set.indicator_of_mem (hx l (Set.mem_univ l))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨l, hl⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ l) (Set.indicator_of_notMem hl _)).symm
  simp_rw [hind]
  rw [lintegral_pi_prod_aux k Q (fun l => (s l).indicator (g l))
    fun l => (hg l).indicator (hs l)]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [hν l, withDensity_apply _ (hs l), lintegral_indicator (hs l)]

/-- Auxiliary: change of reference measure by a density, in `ℝ≥0∞`. -/
private theorem klDiv_withDensity_split {X : Type*} [MeasurableSpace X] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (G : X → ℝ≥0∞) (hG : Measurable G)
    [IsProbabilityMeasure (Q.withDensity G)]
    (hpos : ∀ᵐ x ∂P, 0 < G x) (hlt : ∀ᵐ x ∂P, G x < ∞)
    (hint : Integrable (fun x => Real.log (G x).toReal) P)
    (hc : 0 ≤ ∫ x, Real.log (G x).toReal ∂P) :
    klDiv P Q = klDiv P (Q.withDensity G) + ENNReal.ofReal (∫ x, Real.log (G x).toReal ∂P) := by
  set R := Q.withDensity G with hR
  have hRQ : R ≪ Q := withDensity_absolutelyContinuous _ _
  have hback : P ≪ Q → P ≪ R := by
    intro h
    refine Measure.AbsolutelyContinuous.mk fun s hs hRs => ?_
    rw [hR, withDensity_apply _ hs, lintegral_eq_zero_iff hG, Filter.EventuallyEq,
      ae_restrict_iff' hs] at hRs
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h.ae_le hRs, hpos] with x hx hp hxs
    exact (hx hxs).not_gt hp
  by_cases hac : P ≪ Q
  swap
  · rw [klDiv_of_not_ac hac, klDiv_of_not_ac (fun h => hac (h.trans hRQ))]
    simp
  have hPR : P ≪ R := hback hac
  have hllr : llr P Q =ᵐ[P] fun x => llr P R x + Real.log (G x).toReal := by
    have h1 := Measure.rnDeriv_mul_rnDeriv (κ := Q) hPR
    have h2 := Measure.rnDeriv_withDensity Q hG
    filter_upwards [hac.ae_eq h1, hac.ae_eq h2, Measure.rnDeriv_pos hPR,
      hPR.ae_le (Measure.rnDeriv_lt_top P R), hpos, hlt] with x e1 e2 hp hl hg1 hg2
    have e1' : (P.rnDeriv R * R.rnDeriv Q) x = P.rnDeriv Q x := e1
    simp only [Pi.mul_apply] at e1'
    rw [e2] at e1'
    have h3 : (P.rnDeriv R x).toReal ≠ 0 := (ENNReal.toReal_pos hp.ne' hl.ne).ne'
    have h4 : (G x).toReal ≠ 0 := (ENNReal.toReal_pos hg1.ne' hg2.ne).ne'
    simp only [llr]
    rw [← e1', ENNReal.toReal_mul, Real.log_mul h3 h4]
  have hiff : Integrable (llr P Q) P ↔ Integrable (llr P R) P := by
    constructor
    · intro h
      refine ((h.congr hllr).sub hint).congr (Filter.Eventually.of_forall fun x => ?_)
      simp
    · intro h
      exact (h.add hint).congr hllr.symm
  by_cases hi : Integrable (llr P R) P
  swap
  · rw [klDiv_of_not_integrable hi, klDiv_of_not_integrable (fun h => hi (hiff.mp h))]
    simp
  have hi' := hiff.mpr hi
  have hnn := integral_llr_add_sub_measure_univ_nonneg hPR hi
  simp only [probReal_univ] at hnn
  rw [klDiv_of_ac_of_integrable hac hi', klDiv_of_ac_of_integrable hPR hi]
  simp only [probReal_univ, add_sub_cancel_right]
  rw [← ENNReal.ofReal_add (by linarith) hc, integral_congr_ae hllr, integral_add hi hint]

/-- Total-correlation decomposition of the relative entropy to a product reference, in `ℝ≥0∞`. -/
theorem klDiv_pi_marginals (P : Measure (Fin k → T)) [IsProbabilityMeasure P]
    (Q : Fin k → Measure T) [∀ l, IsProbabilityMeasure (Q l)] :
    klDiv P (Measure.pi Q) =
      klDiv P (Measure.pi fun l => P.map (fun x => x l)) +
        ∑ l, klDiv (P.map (fun x => x l)) (Q l) := by
  set Pm : Fin k → Measure T := fun l => P.map (fun x => x l) with hPm_def
  have hPm : ∀ l, IsProbabilityMeasure (Pm l) := fun l =>
    (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply l).aemeasurable).mpr inferInstance
  by_cases hA : ∃ l, klDiv (Pm l) (Q l) = ⊤
  · obtain ⟨l, hl⟩ := hA
    have h1 : klDiv (Pm l) (Q l) ≤ klDiv P (Measure.pi Q) := by
      have := klDiv_map_le P (Measure.pi Q) (measurable_pi_apply l)
      rwa [(measurePreserving_eval Q l).map_eq] at this
    have h2 : klDiv (Pm l) (Q l) ≤ ∑ l, klDiv (Pm l) (Q l) :=
      Finset.single_le_sum (f := fun l => klDiv (Pm l) (Q l)) (fun _ _ => zero_le)
        (Finset.mem_univ l)
    rw [hl] at h1 h2
    rw [top_le_iff.mp h1, top_le_iff.mp h2]
    simp
  · push Not at hA
    have hfin := fun l => klDiv_ne_top_iff.mp (hA l)
    have hac : ∀ l, Pm l ≪ Q l := fun l => (hfin l).1
    set g : Fin k → T → ℝ≥0∞ := fun l => (Pm l).rnDeriv (Q l) with hg_def
    have hg : ∀ l, Measurable (g l) := fun l => Measure.measurable_rnDeriv _ _
    have hν : ∀ l, Pm l = (Q l).withDensity (g l) := fun l =>
      (Measure.withDensity_rnDeriv_eq _ _ (hac l)).symm
    set G : (Fin k → T) → ℝ≥0∞ := fun x => ∏ l, g l (x l) with hG_def
    have hGm : Measurable G :=
      Finset.measurable_fun_prod _ fun l _ => (hg l).comp (measurable_pi_apply l)
    have hR : Measure.pi Pm = (Measure.pi Q).withDensity G :=
      pi_eq_withDensity_prod Q Pm g hg hν
    have : IsProbabilityMeasure ((Measure.pi Q).withDensity G) := hR ▸ inferInstance
    -- a.e. facts
    have hpos_l : ∀ l, ∀ᵐ x ∂P, 0 < g l (x l) := fun l =>
      ae_of_ae_map (measurable_pi_apply l).aemeasurable (Measure.rnDeriv_pos (hac l))
    have hlt_l : ∀ l, ∀ᵐ x ∂P, g l (x l) < ∞ := fun l =>
      ae_of_ae_map (f := fun x : Fin k → T => x l) (measurable_pi_apply l).aemeasurable
        ((hac l).ae_le (Measure.rnDeriv_lt_top (Pm l) (Q l)))
    have hpos : ∀ᵐ x ∂P, 0 < G x := by
      filter_upwards [ae_all_iff.mpr hpos_l] with x hx
      exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun l _ => (hx l).ne')
    have hlt : ∀ᵐ x ∂P, G x < ∞ := by
      filter_upwards [ae_all_iff.mpr hlt_l] with x hx
      exact ENNReal.prod_lt_top fun l _ => hx l
    have hlogG : (fun x => Real.log (G x).toReal) =ᵐ[P]
        fun x => ∑ l, llr (Pm l) (Q l) (x l) := by
      filter_upwards [ae_all_iff.mpr hpos_l, ae_all_iff.mpr hlt_l] with x h1 h2
      simp only [hG_def, llr, hg_def]
      rw [ENNReal.toReal_prod, Real.log_prod]
      intro l _
      exact (ENNReal.toReal_pos (h1 l).ne' (h2 l).ne).ne'
    have hint_l : ∀ l, Integrable (fun x => llr (Pm l) (Q l) (x l)) P := fun l => by
      have h := (hfin l).2
      exact (integrable_map_measure (f := fun x : Fin k → T => x l)
        (h.aestronglyMeasurable) (measurable_pi_apply l).aemeasurable).mp h
    have hI_l : ∀ l, ∫ x, llr (Pm l) (Q l) (x l) ∂P = (klDiv (Pm l) (Q l)).toReal := fun l => by
      rw [toReal_klDiv (hfin l).1 (hfin l).2]
      simp only [probReal_univ, add_sub_cancel_right]
      exact (integral_map (measurable_pi_apply l).aemeasurable
        ((hfin l).2.aestronglyMeasurable)).symm
    have hint : Integrable (fun x => Real.log (G x).toReal) P :=
      (integrable_finsetSum _ fun l _ => hint_l l).congr hlogG.symm
    have hval : ∫ x, Real.log (G x).toReal ∂P = ∑ l, (klDiv (Pm l) (Q l)).toReal := by
      rw [integral_congr_ae hlogG, integral_finsetSum _ fun l _ => hint_l l]
      exact Finset.sum_congr rfl fun l _ => hI_l l
    have hc : 0 ≤ ∫ x, Real.log (G x).toReal ∂P := by
      rw [hval]; exact Finset.sum_nonneg fun l _ => ENNReal.toReal_nonneg
    have key := klDiv_withDensity_split P (Measure.pi Q) G hGm hpos hlt hint hc
    rw [hval, ENNReal.ofReal_sum_of_nonneg (fun l _ => ENNReal.toReal_nonneg)] at key
    simp only [ENNReal.ofReal_toReal (hA _)] at key
    rw [key, hR]

/-- For `k ≤ 1` a probability on `Fin k → T` is the product of its marginals. -/
theorem klDiv_pi_marginals_of_le_one (hk : k ≤ 1) (P : Measure (Fin k → T))
    [IsProbabilityMeasure P] :
    klDiv P (Measure.pi fun l => P.map (fun x => x l)) = 0 := by
  have hPm : ∀ l : Fin k, IsProbabilityMeasure (P.map (fun x => x l)) := fun l =>
    (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply l).aemeasurable).mpr inferInstance
  have h : Measure.pi (fun l => P.map (fun x => x l)) = P := by
    refine Measure.pi_eq fun s hs => ?_
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with h0 | h1
    · subst h0
      have : Set.univ.pi s = Set.univ := Set.eq_univ_of_forall fun x l => l.elim0
      simp [this]
    · subst h1
      have : Set.univ.pi s = (fun x : Fin 1 → T => x 0) ⁻¹' (s 0) := by
        ext x
        simp [Fin.forall_fin_one]
      rw [this, Fin.prod_univ_one, Measure.map_apply (measurable_pi_apply 0) (hs 0)]
  rw [h, klDiv_self]

end Pi

end SharpLSI.FL
