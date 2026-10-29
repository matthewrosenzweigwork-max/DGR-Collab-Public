import SharpSymmetricLSI.Defs.D14_Conditional
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# Conditional relative entropy and the coordinate chain rule (Phase 3, lane D; I2, R18)

`H(μ⊗κ | μ⊗η) = ∫ H(κ_a | η_a) dμ(a)` (finite case; pattern of
`LeanResearch/PeriodicAttractiveLogGas/ConditionalRelativeEntropy.lean`), and the chain rule
`H(ν | μ^{⊗N}) = ∑_{j<N} h_j` along the coordinates.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal

namespace SharpLSI

section General

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem klDiv_map_equiv' {γ : Type*} [MeasurableSpace γ] (Q P : Measure α) [IsFiniteMeasure Q]
    [IsFiniteMeasure P] (e : α ≃ᵐ γ) : klDiv (Q.map e) (P.map e) = klDiv Q P := by
  apply le_antisymm (klDiv_map_le Q P e.measurable)
  have h := klDiv_map_le (Q.map e) (P.map e) e.symm.measurable
  simpa only [e.map_symm_map] using h

variable [MeasurableSpace.CountableOrCountablyGenerated α β]

/-- `log (dκ/dη)` as a jointly measurable function. -/
def kernelLog (κ η : Kernel α β) (p : α × β) : ℝ :=
  Real.log (κ.rnDeriv η p.1 p.2).toReal

theorem measurable_kernelLog (κ η : Kernel α β) : Measurable (kernelLog κ η) :=
  (Kernel.measurable_rnDeriv κ η).ennreal_toReal.log

variable (μ : Measure α) [IsProbabilityMeasure μ] (κ η : Kernel α β) [IsMarkovKernel κ]
  [IsMarkovKernel η]

/-- **Conditional relative entropy** (finite case). -/
theorem klDiv_compProd_same (hfin : klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ⊤) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ ∧
      AEMeasurable (fun a => klDiv (κ a) (η a)) μ := by
  obtain ⟨hac, hi⟩ := klDiv_ne_top_iff.mp hfin
  have heq : llr (μ ⊗ₘ κ) (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ κ] kernelLog κ η := by
    filter_upwards [hac.ae_eq (rnDeriv_measure_compProd_right μ κ η)] with p hp
    simp only [llr, kernelLog, hp]
  have hlog : Integrable (kernelLog κ η) (μ ⊗ₘ κ) := hi.congr heq
  have hsections := (Measure.integrable_compProd_iff hlog.aestronglyMeasurable).mp hlog
  have hdata : ∀ᵐ a ∂μ, klDiv (κ a) (η a) ≠ ⊤ ∧
      (klDiv (κ a) (η a)).toReal = ∫ b, kernelLog κ η (a, b) ∂κ a := by
    filter_upwards [hac.kernel_of_compProd, hsections.1] with a ha hia
    have heqa : llr (κ a) (η a) =ᵐ[κ a] fun b => kernelLog κ η (a, b) := by
      filter_upwards [ha.ae_eq (Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a))]
        with b hb
      simp only [llr, kernelLog, hb]
    have hllr : Integrable (llr (κ a) (η a)) (κ a) := hia.congr heqa.symm
    refine ⟨klDiv_ne_top ha hllr, ?_⟩
    simpa only [toReal_klDiv ha hllr, probReal_univ, add_sub_cancel_right] using
      integral_congr_ae heqa
  have hout : Integrable (fun a => ∫ b, kernelLog κ η (a, b) ∂κ a) μ := hlog.integral_compProd
  have hreal : (klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal = ∫ a, ∫ b, kernelLog κ η (a, b) ∂κ a ∂μ := by
    calc (klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal = ∫ p, llr (μ ⊗ₘ κ) (μ ⊗ₘ η) p ∂(μ ⊗ₘ κ) := by
          simp only [toReal_klDiv hac hi, probReal_univ, add_sub_cancel_right]
      _ = ∫ p, kernelLog κ η p ∂(μ ⊗ₘ κ) := integral_congr_ae heq
      _ = _ := Measure.integral_compProd hlog
  have hae : (fun a => klDiv (κ a) (η a)) =ᵐ[μ]
      fun a => ENNReal.ofReal (∫ b, kernelLog κ η (a, b) ∂κ a) := by
    filter_upwards [hdata] with a ha
    rw [← ha.2, ENNReal.ofReal_toReal ha.1]
  have hnn : 0 ≤ᵐ[μ] fun a => ∫ b, kernelLog κ η (a, b) ∂κ a := by
    filter_upwards [hdata] with a ha
    rw [← ha.2]; exact ENNReal.toReal_nonneg
  refine ⟨?_, (ENNReal.measurable_ofReal.comp_aemeasurable hout.aemeasurable).congr hae.symm⟩
  rw [lintegral_congr_ae hae, ← ofReal_integral_eq_lintegral_ofReal hout hnn, ← hreal,
    ENNReal.ofReal_toReal hfin]

end General

section Coord

variable {d N : ℕ}

/-- `(Fin (j+1) → T) ≃ (Fin j → T) × T`, `X ↦ (X|_{<j}, X_j)`. -/
def initLast (d j : ℕ) : (Fin (j + 1) → Torus d) ≃ᵐ (Fin j → Torus d) × Torus d :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j + 1) => Torus d) (Fin.last j)).trans
    MeasurableEquiv.prodComm

theorem initLast_apply (j : ℕ) (X : Fin (j + 1) → Torus d) :
    initLast d j X = (fun k => X k.castSucc, X (Fin.last j)) := by
  simp only [initLast, MeasurableEquiv.trans_apply]
  ext k
  · simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]; rfl
  · simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]; rfl

theorem initLast_past {j : ℕ} (hj : j < N) (X : Config N d) :
    initLast d j (past (j + 1) hj X) = (past j hj.le X, X ⟨j, hj⟩) := by
  rw [initLast_apply]
  rfl

theorem map_initLast_pi (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (j : ℕ) :
    (Measure.pi fun _ : Fin (j + 1) => μ).map (initLast d j) =
      (Measure.pi fun _ : Fin j => μ).prod μ := by
  have h := (Measure.measurePreserving_swap (μ := μ) (ν := Measure.pi fun _ : Fin j => μ)).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (j + 1) => μ) (Fin.last j))
  exact h.map_eq

theorem measurable_past {j : ℕ} (hj : j ≤ N) : Measurable (past (d := d) j hj) :=
  measurable_pi_iff.mpr fun i => measurable_pi_apply _

theorem map_past_pi (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {j : ℕ} (hj : j ≤ N) :
    (Measure.pi fun _ : Fin N => μ).map (past j hj) = Measure.pi fun _ : Fin j => μ := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (measurable_past hj) (MeasurableSet.univ_pi hs)]
  set t : Fin N → Set (Torus d) := fun i => if h : (i : ℕ) < j then s ⟨i, h⟩ else Set.univ with ht
  have hpre : past (d := d) j hj ⁻¹' Set.univ.pi s = Set.univ.pi t := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, past, ht]
    constructor
    · intro h i
      split_ifs with hi
      · exact h ⟨i, hi⟩
      · trivial
    · intro h i
      have := h (Fin.castLE hj i)
      simpa [Fin.castLE, i.2] using this
  rw [hpre, Measure.pi_pi]
  have : ∀ i : Fin N, μ (t i) = if h : (i : ℕ) < j then μ (s ⟨i, h⟩) else 1 := fun i => by
    simp only [ht]; split_ifs <;> simp
  simp_rw [this]
  symm
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb hj))) ?_,
    Finset.prod_map]
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp [Fin.castLEEmb, i.2]
  · intro x _ hx
    have : ¬ (x : ℕ) < j := fun h => hx (Finset.mem_map.mpr ⟨⟨x, h⟩, Finset.mem_univ _, rfl⟩)
    simp [this]

instance (ν : Measure (Config N d)) [IsFiniteMeasure ν] (j : ℕ) (hj : j < N) :
    IsMarkovKernel (condNext ν j hj) := by
  unfold condNext; infer_instance

theorem law_past_succ (ν : Measure (Config N d)) [IsProbabilityMeasure ν] {j : ℕ} (hj : j < N) :
    (ν.map (past (j + 1) hj)).map (initLast d j) = (ν.map (past j hj.le)) ⊗ₘ condNext ν j hj := by
  rw [Measure.map_map (initLast d j).measurable (measurable_past _)]
  have : initLast d j ∘ past (j + 1) hj = fun X => (past j hj.le X, X ⟨j, hj⟩) :=
    funext (initLast_past hj)
  rw [this, condNext, compProd_map_condDistrib (measurable_past _).aemeasurable
    (measurable_pi_apply _).aemeasurable]

/-- One step of the coordinate chain rule. -/
theorem chain_step (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] {j : ℕ} (hj : j < N)
    (hfin : klDiv (ν.map (past (j + 1) hj)) (Measure.pi fun _ : Fin (j + 1) => μ) ≠ ⊤) :
    klDiv (ν.map (past (j + 1) hj)) (Measure.pi fun _ : Fin (j + 1) => μ) =
      klDiv (ν.map (past j hj.le)) (Measure.pi fun _ : Fin j => μ) + hCond ν μ j hj := by
  have hP : IsProbabilityMeasure (ν.map (past j hj.le)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_past _).aemeasurable).mpr inferInstance
  have hP1 : IsProbabilityMeasure (ν.map (past (j + 1) hj)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_past _).aemeasurable).mpr inferInstance
  have e : klDiv (ν.map (past (j + 1) hj)) (Measure.pi fun _ : Fin (j + 1) => μ) =
      klDiv ((ν.map (past j hj.le)) ⊗ₘ condNext ν j hj)
        ((Measure.pi fun _ : Fin j => μ) ⊗ₘ Kernel.const _ μ) := by
    rw [← klDiv_map_equiv' _ _ (initLast d j), law_past_succ, map_initLast_pi,
      Measure.compProd_const]
  rw [e, klDiv_compProd_eq_add] at hfin ⊢
  congr 1
  have hfin2 := (ENNReal.add_ne_top.mp hfin).2
  obtain ⟨heq, hmeas⟩ := klDiv_compProd_same (ν.map (past j hj.le)) (condNext ν j hj)
    (Kernel.const _ μ) hfin2
  rw [heq]
  simp only [Kernel.const_apply] at hmeas ⊢
  unfold hCond
  exact lintegral_map' hmeas (measurable_past _).aemeasurable

theorem past_self (X : Config N d) : past N le_rfl X = X := by
  funext i; simp [past]

theorem measure_eq_of_fin_zero (P Q : Measure (Fin 0 → Torus d)) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] : P = Q := by
  ext s hs
  rcases s.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · simp [h]
  · have : s = Set.univ := Set.eq_univ_of_forall fun y => by
      rwa [Subsingleton.elim y x]
    simp [this]

/-- **The coordinate chain rule**: `H(ν | μ^{⊗N}) = ∑_{j<N} h_j`. -/
theorem chain_rule (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) :
    ∑ j ∈ Finset.range N, hCondT ν μ j = klDiv ν (Measure.pi fun _ : Fin N => μ) := by
  have key : ∀ j (hj : j ≤ N), klDiv (ν.map (past j hj)) (Measure.pi fun _ : Fin j => μ) =
      ∑ i ∈ Finset.range j, hCondT ν μ i := by
    intro j
    induction j with
    | zero =>
      intro hj
      have : IsProbabilityMeasure (ν.map (past 0 hj)) :=
        (Measure.isProbabilityMeasure_map_iff (measurable_past _).aemeasurable).mpr inferInstance
      rw [measure_eq_of_fin_zero (ν.map (past 0 hj)) (Measure.pi fun _ : Fin 0 => μ), klDiv_self]
      simp
    | succ j ih =>
      intro hj1
      have hj : j < N := hj1
      have hfin : klDiv (ν.map (past (j + 1) hj)) (Measure.pi fun _ : Fin (j + 1) => μ) ≠ ⊤ := by
        refine ne_top_of_le_ne_top hH ?_
        rw [← map_past_pi μ hj1]
        exact klDiv_map_le _ _ (measurable_past _)
      rw [chain_step μ ν hj hfin, ih hj.le, Finset.sum_range_succ]
      congr 1
      simp [hCondT, hj]
  have h := key N le_rfl
  have hid : ν.map (past N le_rfl) = ν := by
    have : past (d := d) N le_rfl = id := funext past_self
    rw [this, Measure.map_id]
  rw [hid] at h
  exact h.symm

/-- `h_j` as a joint relative entropy (finite case). -/
theorem hCond_eq_klDiv (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {j : ℕ}
    (hj : j < N) :
    hCond ν μ j hj = klDiv (ν.map fun X => (past j hj.le X, X ⟨j, hj⟩))
      ((ν.map (past j hj.le)).prod μ) := by
  have hP : IsProbabilityMeasure (ν.map (past j hj.le)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_past _).aemeasurable).mpr inferInstance
  have hfin1 : klDiv (ν.map (past (j + 1) hj)) (Measure.pi fun _ : Fin (j + 1) => μ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hH ?_
    rw [← map_past_pi μ (Nat.succ_le_of_lt hj)]
    exact klDiv_map_le _ _ (measurable_past _)
  have e : klDiv (ν.map (past (j + 1) hj)) (Measure.pi fun _ : Fin (j + 1) => μ) =
      klDiv ((ν.map (past j hj.le)) ⊗ₘ condNext ν j hj)
        ((Measure.pi fun _ : Fin j => μ) ⊗ₘ Kernel.const _ μ) := by
    rw [← klDiv_map_equiv' _ _ (initLast d j), law_past_succ, map_initLast_pi,
      Measure.compProd_const]
  rw [e, klDiv_compProd_eq_add] at hfin1
  have hfin2 := (ENNReal.add_ne_top.mp hfin1).2
  obtain ⟨heq, hmeas⟩ := klDiv_compProd_same (ν.map (past j hj.le)) (condNext ν j hj)
    (Kernel.const _ μ) hfin2
  have h1 : hCond ν μ j hj = klDiv ((ν.map (past j hj.le)) ⊗ₘ condNext ν j hj)
      ((ν.map (past j hj.le)) ⊗ₘ Kernel.const _ μ) := by
    rw [heq]
    simp only [Kernel.const_apply] at hmeas ⊢
    unfold hCond
    exact (lintegral_map' hmeas (measurable_past _).aemeasurable).symm
  rw [h1, condNext, compProd_map_condDistrib (measurable_past _).aemeasurable
    (measurable_pi_apply _).aemeasurable, Measure.compProd_const]

/-- Exchangeability: `(X_{<j}, X_{j+1})` has the law of `(X_{<j}, X_j)`. -/
theorem law_past_shift (ν : Measure (Config N d)) (hsym : IsSymmetricMeasure ν) {j : ℕ}
    (hj : j + 1 < N) :
    ν.map (fun X => (past j (by omega) X, X ⟨j + 1, hj⟩)) =
      ν.map (fun X => (past j (by omega) X, X ⟨j, by omega⟩)) := by
  set σ : Equiv.Perm (Fin N) := Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩
  have hm : Measurable fun X : Config N d => X ∘ σ := measurable_pi_iff.mpr fun i =>
    measurable_pi_apply _
  conv_rhs => rw [← hsym σ]
  rw [Measure.map_map ((measurable_past _).prodMk (measurable_pi_apply _)) hm]
  congr 1
  funext X
  simp only [Function.comp]
  refine Prod.ext ?_ ?_
  · funext i
    simp only [past, Function.comp]
    congr 1
    rw [Equiv.swap_apply_of_ne_of_ne]
    · exact fun h => by have := congrArg Fin.val h; simp [Fin.castLE] at this; omega
    · exact fun h => by have := congrArg Fin.val h; simp [Fin.castLE] at this; omega
  · simp [σ, Equiv.swap_apply_left]

/-- **`h_j` is nondecreasing** (conditioning on more of the past). -/
theorem hCond_mono (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (hsym : IsSymmetricMeasure ν)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {j : ℕ} (hj : j + 1 < N) :
    hCond ν μ j (by omega) ≤ hCond ν μ (j + 1) hj := by
  rw [hCond_eq_klDiv μ ν hH, hCond_eq_klDiv μ ν hH, ← law_past_shift ν hsym hj]
  set g : (Fin (j + 1) → Torus d) → (Fin j → Torus d) := fun p k => p k.castSucc
  have hg : Measurable g := measurable_pi_iff.mpr fun k => measurable_pi_apply _
  have hmap : Measurable (Prod.map g (id : Torus d → Torus d)) := hg.prodMap measurable_id
  have e1 : (ν.map fun X => (past (j + 1) hj.le X, X ⟨j + 1, hj⟩)).map (Prod.map g id) =
      ν.map fun X => (past j (by omega) X, X ⟨j + 1, hj⟩) := by
    rw [Measure.map_map hmap ((measurable_past _).prodMk (measurable_pi_apply _))]
    rfl
  have hP : IsProbabilityMeasure (ν.map (past (j + 1) hj.le)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_past _).aemeasurable).mpr inferInstance
  have e2 : ((ν.map (past (j + 1) hj.le)).prod μ).map (Prod.map g id) =
      (ν.map (past j (by omega))).prod μ := by
    rw [← Measure.map_prod_map _ _ hg measurable_id, Measure.map_id,
      Measure.map_map hg (measurable_past _)]
    rfl
  rw [← e1, ← e2]
  exact klDiv_map_le _ _ hmap

end Coord

end SharpLSI
