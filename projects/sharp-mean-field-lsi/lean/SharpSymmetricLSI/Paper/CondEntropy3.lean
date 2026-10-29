import SharpSymmetricLSI.Paper.CondEntropy2

/-!
# Lemma 5.1: block chain rule and the identity for `D_{j,k}` (Phase 3, lane D; R18)
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal

namespace SharpLSI

variable {d N : ℕ}

theorem chain_partial (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) :
    ∀ j (hj : j ≤ N), klDiv (ν.map (past j hj)) (Measure.pi fun _ : Fin j => μ) =
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

/-- `(Fin (j+k) → T) ≃ (Fin j → T) × (Fin k → T)`. -/
def splitE (d j k : ℕ) : (Fin (j + k) → Torus d) ≃ᵐ (Fin j → Torus d) × (Fin k → Torus d) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (j + k) => Torus d) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin j ⊕ Fin k => Torus d))

theorem splitE_apply (j k : ℕ) (X : Fin (j + k) → Torus d) :
    splitE d j k X = (fun i => X (Fin.castAdd k i), fun a => X (Fin.natAdd j a)) := by
  simp only [splitE, MeasurableEquiv.trans_apply]
  ext i
  · simp [MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  · simp [MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]

theorem map_splitE_pi (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (j k : ℕ) :
    (Measure.pi fun _ : Fin (j + k) => μ).map (splitE d j k) =
      (Measure.pi fun _ : Fin j => μ).prod (Measure.pi fun _ : Fin k => μ) := by
  have h1 := (measurePreserving_piCongrLeft (fun _ : Fin (j + k) => μ) finSumFinEquiv).symm
  have h2 := measurePreserving_sumPiEquivProdPi (fun _ : Fin j ⊕ Fin k => μ)
  exact (h2.comp h1).map_eq

instance (ν : Measure (Config N d)) [IsFiniteMeasure ν] (j k : ℕ) (h : j + k ≤ N) :
    IsMarkovKernel (condBlock ν j k h) := by
  unfold condBlock; infer_instance

theorem measurable_block {j k : ℕ} (h : j + k ≤ N) : Measurable (block (d := d) j k h) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

theorem law_block (ν : Measure (Config N d)) [IsProbabilityMeasure ν] {j k : ℕ} (h : j + k ≤ N) :
    (ν.map (past (j + k) h)).map (splitE d j k) =
      (ν.map (past j (by omega))) ⊗ₘ condBlock ν j k h := by
  rw [Measure.map_map (splitE d j k).measurable (measurable_past _)]
  have : splitE d j k ∘ past (j + k) h = fun X => (past j (by omega) X, block j k h X) := by
    funext X
    rw [Function.comp_apply, splitE_apply]
    rfl
  rw [this, condBlock, compProd_map_condDistrib (measurable_past _).aemeasurable
    (measurable_block h).aemeasurable]

/-- **Block chain rule**: `H(P_j ⊗ ν_{j,k} | P_j ⊗ μ^{⊗k}) = ∑_{a<k} h_{j+a}`. -/
theorem block_chain (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {j k : ℕ}
    (h : j + k ≤ N) :
    klDiv ((ν.map (past j (by omega))) ⊗ₘ condBlock ν j k h)
        ((ν.map (past j (by omega))) ⊗ₘ Kernel.const _ (Measure.pi fun _ : Fin k => μ)) =
      ∑ a ∈ Finset.range k, hCondT ν μ (j + a) := by
  have hc := chain_partial μ ν hH
  have e : klDiv (ν.map (past (j + k) h)) (Measure.pi fun _ : Fin (j + k) => μ) =
      klDiv (ν.map (past j (by omega))) (Measure.pi fun _ : Fin j => μ) +
      klDiv ((ν.map (past j (by omega))) ⊗ₘ condBlock ν j k h)
        ((ν.map (past j (by omega))) ⊗ₘ Kernel.const _ (Measure.pi fun _ : Fin k => μ)) := by
    have hP : IsProbabilityMeasure (ν.map (past (j + k) h)) :=
      (Measure.isProbabilityMeasure_map_iff (measurable_past _).aemeasurable).mpr inferInstance
    rw [← klDiv_map_equiv' _ _ (splitE d j k), law_block, map_splitE_pi, ← Measure.compProd_const,
      klDiv_compProd_eq_add]
  rw [hc (j + k) h, hc j (by omega), Finset.sum_range_add] at e
  have hfin : ∑ x ∈ Finset.range j, hCondT ν μ x ≠ ⊤ := by
    rw [← hc j (by omega)]
    refine ne_top_of_le_ne_top hH ?_
    rw [← map_past_pi μ (by omega : j ≤ N)]
    exact klDiv_map_le _ _ (measurable_past _)
  exact (ENNReal.add_right_inj hfin).mp e.symm

/-- Exchangeability: `(X_{<j}, X_{j'})` has the law of `(X_{<j}, X_j)` for `j ≤ j' < N`. -/
theorem law_past_any (ν : Measure (Config N d)) (hsym : IsSymmetricMeasure ν) {j j' : ℕ}
    (hjj : j ≤ j') (hj' : j' < N) :
    ν.map (fun X => (past j (by omega) X, X ⟨j', hj'⟩)) =
      ν.map (fun X => (past j (by omega) X, X ⟨j, by omega⟩)) := by
  set σ : Equiv.Perm (Fin N) := Equiv.swap ⟨j, by omega⟩ ⟨j', hj'⟩
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

/-- The one-coordinate marginals of `ν_{j,k}` are `ρ_j` (exchangeability). -/
theorem condBlock_marginal (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (hsym : IsSymmetricMeasure ν) {j k : ℕ} (h : j + k ≤ N) (hj : j < N) (a : Fin k) :
    ∀ᵐ p ∂(ν.map (past j hj.le)), (condBlock ν j k h p).map (fun x => x a) = condNext ν j hj p := by
  have hja : j + a < N := by omega
  have hmeas : Measurable fun x : Fin k → Torus d => x a := measurable_pi_apply a
  -- the joint law of `(past, X_{j+a})`
  have h1 : ν.map (fun X => (past j hj.le X, X ⟨j + a, hja⟩)) =
      (ν.map (past j hj.le)) ⊗ₘ (condBlock ν j k h).map (fun x => x a) := by
    rw [Measure.compProd_map hmeas]
    have := law_block ν h
    rw [condBlock, compProd_map_condDistrib (measurable_past _).aemeasurable
      (measurable_block h).aemeasurable, Measure.map_map (measurable_id.prodMap hmeas)
      ((measurable_past _).prodMk (measurable_block h))]
    rfl
  have h2 : ν.map (fun X => (past j hj.le X, X ⟨j + a, hja⟩)) =
      (ν.map (past j hj.le)) ⊗ₘ condNext ν j hj := by
    rw [law_past_any ν hsym (by omega) hja, condNext, compProd_map_condDistrib
      (measurable_past _).aemeasurable (measurable_pi_apply _).aemeasurable]
  have e1 := condDistrib_ae_eq_of_measure_eq_compProd (μ := ν) (X := past j hj.le)
    (Y := fun X : Config N d => X ⟨j + a, hja⟩) (measurable_past _).aemeasurable
    (measurable_pi_apply _).aemeasurable h1
  have e2 := condDistrib_ae_eq_of_measure_eq_compProd (μ := ν) (X := past j hj.le)
    (Y := fun X : Config N d => X ⟨j + a, hja⟩) (measurable_past _).aemeasurable
    (measurable_pi_apply _).aemeasurable h2
  filter_upwards [e1, e2] with p hp1 hp2
  rw [← Kernel.map_apply _ hmeas, ← hp1, hp2]

theorem sum_hCondT_le (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {s : Finset ℕ}
    (hs : s ⊆ Finset.range N) : ∑ i ∈ s, hCondT ν μ i ≤ klDiv ν (Measure.pi fun _ : Fin N => μ) := by
  rw [← chain_rule μ ν hH]
  exact Finset.sum_le_sum_of_subset hs

/-- **`∑_{a<k} h_{j+a} = D_{j,k} + k h_j`.** -/
theorem DCond_add (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (hsym : IsSymmetricMeasure ν)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {j k : ℕ} (hj : j < N) (h : j + k ≤ N) :
    ∑ a ∈ Finset.range k, hCondT ν μ (j + a) = DCond ν j k hj h + k * hCond ν μ j hj := by
  set P := ν.map (past j hj.le) with hPdef
  have hP : IsProbabilityMeasure P :=
    (Measure.isProbabilityMeasure_map_iff (measurable_past _).aemeasurable).mpr inferInstance
  have hbc := block_chain μ ν hH h
  have hsumfin : ∑ a ∈ Finset.range k, hCondT ν μ (j + a) ≠ ⊤ := by
    have : ∑ a ∈ Finset.range k, hCondT ν μ (j + a) = ∑ i ∈ Finset.Ico j (j + k), hCondT ν μ i := by
      rw [Finset.sum_Ico_eq_sum_range]; simp
    rw [this]
    exact ne_top_of_le_ne_top hH (sum_hCondT_le μ ν hH fun i hi => by
      simp only [Finset.mem_Ico] at hi; simp only [Finset.mem_range]; omega)
  have hbfin : klDiv (P ⊗ₘ condBlock ν j k h) (P ⊗ₘ Kernel.const _ (Measure.pi fun _ : Fin k => μ))
      ≠ ⊤ := by rw [hbc]; exact hsumfin
  obtain ⟨hG, hGm⟩ := klDiv_compProd_same P (condBlock ν j k h)
    (Kernel.const _ (Measure.pi fun _ : Fin k => μ)) hbfin
  simp only [Kernel.const_apply] at hG hGm
  -- `h_j` as an integral over the past
  have hhfin : hCond ν μ j hj ≠ ⊤ := by
    have := sum_hCondT_le μ ν hH (s := {j}) (by simp [hj])
    simp only [Finset.sum_singleton, hCondT, hj, dif_pos] at this
    exact ne_top_of_le_ne_top hH this
  have hρfin : klDiv (P ⊗ₘ condNext ν j hj) (P ⊗ₘ Kernel.const _ μ) ≠ ⊤ := by
    have e := hCond_eq_klDiv μ ν hH hj
    rw [condNext, compProd_map_condDistrib (measurable_past _).aemeasurable
      (measurable_pi_apply _).aemeasurable, Measure.compProd_const]
    rw [← e]; exact hhfin
  obtain ⟨hF, hFm⟩ := klDiv_compProd_same P (condNext ν j hj) (Kernel.const _ μ) hρfin
  simp only [Kernel.const_apply] at hF hFm
  have hhP : hCond ν μ j hj = ∫⁻ p, klDiv (condNext ν j hj p) μ ∂P := by
    unfold hCond
    exact (lintegral_map' hFm (measurable_past _).aemeasurable).symm
  -- pointwise identity
  have hGlt : ∀ᵐ p ∂P, klDiv (condBlock ν j k h p) (Measure.pi fun _ : Fin k => μ) < ⊤ :=
    ae_lt_top' hGm (by rw [← hG]; exact hbfin)
  have hFlt : ∀ᵐ p ∂P, klDiv (condNext ν j hj p) μ < ⊤ :=
    ae_lt_top' hFm (by rw [← hhP]; exact hhfin)
  have hmarg : ∀ᵐ p ∂P, ∀ a : Fin k,
      (condBlock ν j k h p).map (fun x => x a) = condNext ν j hj p := by
    rw [ae_all_iff]; exact fun a => condBlock_marginal ν hsym h hj a
  have hpt : (fun p => klDiv (condBlock ν j k h p) (Measure.pi fun _ : Fin k => μ)) =ᵐ[P]
      fun p => klDiv (condBlock ν j k h p) (Measure.pi fun _ : Fin k => condNext ν j hj p) +
        k * klDiv (condNext ν j hj p) μ := by
    filter_upwards [hGlt, hFlt, hmarg] with p h1 h2 h3
    exact klDiv_pi_ref_change μ (condNext ν j hj p) (condBlock ν j k h p) h3 h1.ne h2.ne
  have hDm : AEMeasurable (fun p => klDiv (condBlock ν j k h p)
      (Measure.pi fun _ : Fin k => condNext ν j hj p)) P := by
    refine (hGm.sub (hFm.const_mul (k : ℝ≥0∞))).congr ?_
    filter_upwards [hpt, hFlt] with p hp hlt
    simp only [Pi.sub_apply]
    rw [hp, ENNReal.add_sub_cancel_right (ENNReal.mul_ne_top (by simp) hlt.ne)]
  have hDP : DCond ν j k hj h = ∫⁻ p, klDiv (condBlock ν j k h p)
      (Measure.pi fun _ : Fin k => condNext ν j hj p) ∂P := by
    unfold DCond
    exact (lintegral_map' hDm (measurable_past _).aemeasurable).symm
  rw [← hbc, hG, lintegral_congr_ae hpt, lintegral_add_right' _ (hFm.const_mul _),
    lintegral_const_mul' _ _ (by simp), ← hDP, ← hhP]

end SharpLSI
