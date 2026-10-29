import DGRHS.Commutator.SourceRieszBrownianProcessProperties
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-
Copyright (c) 2025 Rémy Degenne and Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the preserved LICENSE.
Selected adaptation: BrownianMotion/Auxiliary/Filtration.lean,
Auxiliary/Martingale.lean and StochasticIntegral/DoobLp.lean, commit
0d5b6eb928e616d3b1f774ad7d233c167d9f42c9. Only the proved finite weak maximal
inequality is reused. The upstream strong-Lp assertions containing sorry are
excluded. The countable strict-tail and continuous dense-set passage below
avoid those assertions and the upstream cadlag infrastructure entirely.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Finset Function TopologicalSpace
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {ι Ω : Type*} [LinearOrder ι] {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}

def sourceRieszFiltrationIndexComap {ι' : Type*} [Preorder ι'] (F : Filtration ι mΩ)
    {f : ι'→ι} (hf : Monotone f) : Filtration ι' mΩ where
  seq k := F (f k)
  mono' := F.mono'.comp hf
  le' i := F.le (f i)

private lemma submartingale_indexComap {Y : ι→Ω→ℝ} (hY : Submartingale Y F P)
    {ι' : Type*} [Preorder ι'] {f : ι'→ι} (hf : Monotone f) :
    Submartingale (Y ∘ f) (sourceRieszFiltrationIndexComap F hf) P :=
  ⟨fun i=>hY.stronglyAdapted (f i),fun _ _ hij=>hY.ae_le_condExp (hf hij),
    fun i=>hY.integrable (f i)⟩

private lemma martingale_norm {X : ι→Ω→ℝ} (hX : Martingale X F P) :
    Submartingale (fun t ω=>‖X t ω‖) F P := by
  refine ⟨fun i=>continuous_norm.comp_stronglyMeasurable (hX.stronglyAdapted i),?_,
    fun i=>(hX.integrable i).norm⟩
  intro i j hij
  calc
    _ =ᵐ[P] fun ω=>‖(P[X j | F i]) ω‖ := (hX.condExp_ae_eq hij).fun_comp norm |>.symm
    _ ≤ᵐ[P] P[fun ω=>‖X j ω‖ | F i] :=
      convexOn_univ_norm.map_condExp_le_univ (F.le i) continuous_norm.lowerSemicontinuous
        (hX.integrable j) (hX.integrable j).norm

private lemma maximal_nat {F : Filtration ℕ mΩ} {Y : ℕ→Ω→ℝ}
    (hY : Submartingale Y F P) (hnonneg : 0≤Y) (ε : ℝ≥0) (n : ℕ) :
    ε * P.real {ω | (ε:ℝ)≤(range (n+1)).sup' nonempty_range_add_one (fun k=>Y k ω)} ≤
      ∫ ω in {ω | (ε:ℝ)≤(range (n+1)).sup' nonempty_range_add_one (fun k=>Y k ω)},Y n ω ∂P := by
  calc
    _ = (ε * P {ω | (ε:ℝ)≤(range (n+1)).sup' nonempty_range_add_one (fun k=>Y k ω)}).toReal := by
      simp only [ENNReal.toReal_mul,ENNReal.coe_toReal,Measure.real]
    _ ≤ _ := by
      apply ENNReal.toReal_le_of_le_ofReal (integral_nonneg (hnonneg n))
      exact MeasureTheory.maximal_ineq hY hnonneg n

private lemma maximal_finset {Y : ι→Ω→ℝ} (hY : Submartingale Y F P)
    (hnonneg : 0≤Y) (ε : ℝ≥0) {n : ι} {J : Finset ι}
    (hJn : ∀ i∈J,i≤n) (hnJ : n∈J) :
    ε * P.real {ω | (ε:ℝ)≤J.sup' ⟨n,hnJ⟩ (fun i=>Y i ω)} ≤
      ∫ ω in {ω | (ε:ℝ)≤J.sup' ⟨n,hnJ⟩ (fun i=>Y i ω)},Y n ω ∂P := by
  classical
  let toι (k : ℕ) : ι := if hk : k<#J then J.orderEmbOfFin rfl ⟨k,hk⟩ else n
  have hm : Monotone toι := fun k l hkl=>by
    unfold toι
    split_ifs with hk hl hl
    exacts [(J.orderEmbOfFin rfl).monotone hkl,hJn _ (orderEmbOfFin_mem ..),by omega,le_rfl]
  have hc (ω : Ω) : J.sup' ⟨n,hnJ⟩ (fun i=>Y i ω)=
      (range (#J+1)).sup' nonempty_range_add_one (fun k=>Y (toι k) ω) := by
    unfold toι
    apply le_antisymm
    · refine sup'_le _ _ fun i hi=>?_
      refine le_sup'_of_le _ (b:=((J.orderIsoOfFin rfl).symm ⟨i,hi⟩:ℕ)) ?_ ?_
      · simp
      · simp [orderEmbOfFin]
    · refine sup'_le _ _ fun k hk=>?_
      apply le_sup' (fun i=>Y i ω)
      split_ifs
      exacts [orderEmbOfFin_mem ..,hnJ]
  have hh := maximal_nat (submartingale_indexComap hY hm) (fun k=>hnonneg _) ε #J
  simpa only [Function.comp_apply,toι,lt_self_iff_false,dite_false,←hc] using hh

/-- Strict-tail weak maximal inequality for countable time sets. -/
theorem sourceRiesz_submartingale_countable_maximal [Countable ι]
    {Y : ι→Ω→ℝ} (hY : Submartingale Y F P) (hnonneg : 0≤Y)
    (n : ι) {ε : ℝ} (hε : 0<ε) :
    P {ω | ∃ i, i≤n ∧ ε<Y i ω} ≤ ENNReal.ofReal (ε⁻¹*(∫ ω,Y n ω ∂P)) := by
  classical
  letI : Nonempty ι := ⟨n⟩
  obtain ⟨f,hf⟩ := exists_surjective_nat ι
  let J (k : ℕ) : Finset ι := insert n (((range k).image f).filter (·≤n))
  have hJn k : ∀ i∈J k,i≤n := by simp [J]
  have hnJ k : n∈J k := by simp [J]
  have hmono {k l : ℕ} (hkl : k≤l) : J k⊆J l := by unfold J; gcongr
  let A k : Set Ω := {ω | ∃ i∈J k,ε<Y i ω}
  have hAm : Monotone A := fun k l hkl ω ⟨i,hi,h⟩=>⟨i,hmono hkl hi,h⟩
  have he : {ω | ∃ i,i≤n ∧ ε<Y i ω}=⋃ k,A k := by
    ext ω
    simp only [mem_setOf_eq,mem_iUnion,A]
    constructor
    · rintro ⟨i,hi,h⟩
      obtain ⟨k,rfl⟩ := hf i
      exact ⟨k+1,f k,by simp [J,hi]; exact Or.inr ⟨k,by omega,rfl⟩,h⟩
    · rintro ⟨k,i,hi,h⟩
      exact ⟨i,hJn k i hi,h⟩
  rw [he,hAm.measure_iUnion]
  refine iSup_le fun k=>?_
  let C := {ω | ε≤(J k).sup' ⟨n,hnJ k⟩ (fun i=>Y i ω)}
  have hAC : A k⊆C := by
    rintro ω ⟨i,hi,h⟩
    exact h.le.trans (le_sup' (fun i=>Y i ω) hi)
  refine (measure_mono hAC).trans ?_
  have hb := maximal_finset hY hnonneg (⟨ε,hε.le⟩:ℝ≥0) (hJn k) (hnJ k)
  have hb' : ε*P.real C≤∫ ω,Y n ω ∂P :=
    hb.trans (setIntegral_le_integral (hY.integrable n) (ae_of_all _ (hnonneg n)))
  have hp : P.real C≤ε⁻¹*(∫ ω,Y n ω ∂P) := by
    calc
      P.real C = ε⁻¹*(ε*P.real C) := by rw [←mul_assoc,inv_mul_cancel₀ hε.ne',one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hb' (inv_nonneg.mpr hε.le)
  calc
    P C=ENNReal.ofReal (P.real C) := (ENNReal.ofReal_toReal (measure_ne_top P C)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hp

/-- Continuous-time strict-tail bound, proved by a countable dense set. -/
theorem sourceRiesz_martingale_continuous_maximal
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0→Ω→ℝ} (hX : Martingale X F P)
    (hc : ∀ ω,Continuous (fun t=>X t ω)) (T : ℝ≥0) {ε : ℝ} (hε : 0<ε) :
    P {ω | ∃ t, t≤T ∧ ε<‖X t ω‖} ≤ ENNReal.ofReal (ε⁻¹*(∫ ω,‖X T ω‖ ∂P)) := by
  obtain ⟨D,hDc,hDd⟩ := TopologicalSpace.exists_countable_dense (Iic T)
  let S : Set (Iic T) := insert ⟨T,by simp⟩ D
  have hSc : S.Countable := hDc.insert _
  letI : Countable S := hSc.to_subtype
  let topS : S := ⟨⟨T,by simp⟩,mem_insert _ _⟩
  have hS : Dense S := hDd.mono (subset_insert _ _)
  have hm : Monotone (fun s:S=>(s.val:ℝ≥0)) := fun _ _ h=>h
  have he : {ω | ∃ t,t≤T ∧ ε<‖X t ω‖}=
      {ω | ∃ s:S,s≤topS ∧ ε<‖X s.val ω‖} := by
    ext ω
    constructor
    · rintro ⟨t,ht,h⟩
      have hcont : Continuous (fun s:Iic T=>‖X s ω‖) := (hc ω).norm.comp continuous_subtype_val
      obtain ⟨s,hs,hval⟩ := hS.exists_mem_open (isOpen_lt continuous_const hcont) ⟨⟨t,ht⟩,h⟩
      exact ⟨⟨s,hs⟩,s.property,hval⟩
    · rintro ⟨s,hs,h⟩
      exact ⟨s.val,s.val.property,h⟩
  rw [he]
  exact sourceRiesz_submartingale_countable_maximal
    (submartingale_indexComap (martingale_norm hX) hm) (fun _ _=>norm_nonneg _) topS hε

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszFiltrationIndexComap
#print axioms DGRHS.Commutator.sourceRieszFiltrationIndexComap
#check @DGRHS.Commutator.sourceRiesz_submartingale_countable_maximal
#print axioms DGRHS.Commutator.sourceRiesz_submartingale_countable_maximal
#check @DGRHS.Commutator.sourceRiesz_martingale_continuous_maximal
#print axioms DGRHS.Commutator.sourceRiesz_martingale_continuous_maximal
