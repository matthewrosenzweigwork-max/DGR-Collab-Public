import SharpSymmetricLSI.Paper.CondEntropy4
import SharpSymmetricLSI.Infra.Pinsker

/-!
# Lemma 5.1, (5.5): conditional products versus the empirical tensor (Phase 3, lane D; R18)
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal

namespace SharpLSI

variable {d N : ℕ}

/-- The `k`-fold product kernel `p ↦ κ(p)^{⊗k}`, built by iterated products. -/
def piK {α : Type*} [MeasurableSpace α] (κ : Kernel α (Torus d)) [IsMarkovKernel κ] :
    (k : ℕ) → Kernel α (Fin k → Torus d)
  | 0 => Kernel.const α (Measure.pi fun _ : Fin 0 => (volume : Measure (Torus d)))
  | k + 1 => ((piK κ k) ×ₖ κ).map (initLast d k).symm

instance isMarkovKernel_piK {α : Type*} [MeasurableSpace α] (κ : Kernel α (Torus d))
    [IsMarkovKernel κ] : ∀ k, IsMarkovKernel (piK κ k)
  | 0 => by unfold piK; infer_instance
  | k + 1 => by
    haveI := isMarkovKernel_piK κ k
    unfold piK
    exact Kernel.IsMarkovKernel.map _ (initLast d k).symm.measurable

theorem piK_apply {α : Type*} [MeasurableSpace α] (κ : Kernel α (Torus d)) [IsMarkovKernel κ] :
    ∀ k (a : α), piK κ k a = Measure.pi fun _ : Fin k => κ a
  | 0, a => by
    unfold piK
    rw [Kernel.const_apply]
    exact measure_eq_of_fin_zero _ _
  | k + 1, a => by
    haveI := isMarkovKernel_piK κ k
    unfold piK
    rw [Kernel.map_apply _ (initLast d k).symm.measurable, Kernel.prod_apply, piK_apply κ k a,
      ← map_initLast_pi (κ a) k, Measure.map_map (initLast d k).symm.measurable
        (initLast d k).measurable]
    simp

/-- Pinsker for bounded test functions. -/
theorem abs_integral_sub_le_pinsker {α : Type*} [MeasurableSpace α] {P Q : Measure α}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {B : α → ℝ} (hB : Measurable B) {C : ℝ}
    (hC : ∀ x, |B x| ≤ C) (hK : klDiv P Q ≠ ⊤) :
    |∫ x, B x ∂P - ∫ x, B x ∂Q| ≤ C * Real.sqrt (2 * (klDiv P Q).toReal) := by
  obtain ⟨hac, -⟩ := klDiv_ne_top_iff.mp hK
  set ρ : α → ℝ := fun x => (P.rnDeriv Q x).toReal with hρ
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => ENNReal.toReal_nonneg
  have hρi : Integrable ρ Q := Measure.integrable_toReal_rnDeriv
  have hρ1 : ∫ x, ρ x ∂Q = 1 := by rw [Measure.integral_toReal_rnDeriv hac]; simp
  have hBi : ∀ {m : Measure α} [IsFiniteMeasure m], Integrable B m := fun {m} _ =>
    Integrable.of_bound hB.aestronglyMeasurable C (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hC x)
  obtain ⟨x0, -⟩ := nonempty_of_measure_ne_zero (μ := P) (s := Set.univ) (by simp)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x0)
  have e1 : ∫ x, B x ∂P = ∫ x, ρ x * B x ∂Q := by
    rw [← integral_rnDeriv_smul hac]; rfl
  have hρB : Integrable (fun x => ρ x * B x) Q :=
    (hρi.norm.mul_const C).mono' (hρi.aestronglyMeasurable.mul hB.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs (B x)]
        exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _))
  have e2 : ∫ x, B x ∂P - ∫ x, B x ∂Q = ∫ x, (ρ x - 1) * B x ∂Q := by
    rw [e1, ← integral_sub hρB hBi]
    congr 1; funext x; ring
  have hL : ∫ x, |ρ x - 1| ∂Q ≤ Real.sqrt (2 * (klDiv P Q).toReal) := by
    have hp := pinsker_lintegral hρ0 hρi hρ1
    rw [← klDiv_eq_lintegral_klFun_of_ac hac] at hp
    have hn : ∫ x, |ρ x - 1| ∂Q = (∫⁻ x, ‖ρ x - 1‖ₑ ∂Q).toReal := by
      have := integral_norm_eq_lintegral_enorm (μ := Q) (hρi.sub (integrable_const 1)).aestronglyMeasurable
      simpa [Real.norm_eq_abs] using this
    rw [hn, Real.le_sqrt ENNReal.toReal_nonneg (by positivity)]
    have h2 : (2 : ℝ≥0∞) * klDiv P Q ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hK
    have := ENNReal.toReal_mono h2 hp
    rwa [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofNat] at this
  rw [e2]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ x, |(ρ x - 1) * B x| ∂Q ≤ ∫ x, |ρ x - 1| * C ∂Q :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          ((hρi.sub (integrable_const 1)).abs.mul_const C) (Eventually.of_forall fun x => by
            show |(ρ x - 1) * B x| ≤ |ρ x - 1| * C
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _))
    _ = C * ∫ x, |ρ x - 1| ∂Q := by rw [integral_mul_const, mul_comm]
    _ ≤ C * Real.sqrt (2 * (klDiv P Q).toReal) := mul_le_mul_of_nonneg_left hL hC0

theorem integrable_sqrt_of {α : Type*} [MeasurableSpace α] {P : Measure α} [IsFiniteMeasure P]
    {f : α → ℝ} (hf0 : ∀ᵐ x ∂P, 0 ≤ f x) (hfi : Integrable f P) :
    Integrable (fun x => Real.sqrt (f x)) P := by
  refine (hfi.add (integrable_const 1)).mono' (Real.continuous_sqrt.comp_aestronglyMeasurable
    hfi.aestronglyMeasurable) ?_
  filter_upwards [hf0] with x hx
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Pi.add_apply]
  have := Real.sqrt_le_sqrt (by linarith : f x ≤ f x + 1)
  have h2 : Real.sqrt (f x + 1) ≤ f x + 1 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  linarith

/-- Jensen for the square root under a probability measure. -/
theorem integral_sqrt_le {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    {f : α → ℝ} (hf0 : ∀ᵐ x ∂P, 0 ≤ f x) (hfi : Integrable f P) :
    ∫ x, Real.sqrt (f x) ∂P ≤ Real.sqrt (∫ x, f x ∂P) := by
  have hgi : Integrable (Real.sqrt ∘ f) P := by
    refine (hfi.add (integrable_const 1)).mono' (Real.continuous_sqrt.comp_aestronglyMeasurable
      hfi.aestronglyMeasurable) ?_
    filter_upwards [hf0] with x hx
    simp only [Function.comp, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Pi.add_apply]
    have := Real.sqrt_le_sqrt (by linarith : f x ≤ f x + 1)
    have h2 : Real.sqrt (f x + 1) ≤ f x + 1 := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    linarith
  exact Real.strictConcaveOn_sqrt.concaveOn.le_map_integral Real.continuous_sqrt.continuousOn
    isClosed_Ici hf0 hfi hgi

section
variable (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (ν : Measure (Config N d))
  [IsProbabilityMeasure ν]

/-- `D_p = H(ν_{j,k}(p) | ρ_j(p)^{⊗k})` is a.e. measurable and a.e. finite, and integrates to
`D_{j,k}`. -/
theorem DCond_data (hsym : IsSymmetricMeasure ν)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {j k : ℕ} (hj : j < N) (h : j + k ≤ N) :
    AEMeasurable (fun p => klDiv (condBlock ν j k h p)
      (Measure.pi fun _ : Fin k => condNext ν j hj p)) (ν.map (past j hj.le)) ∧
    (∀ᵐ p ∂(ν.map (past j hj.le)), klDiv (condBlock ν j k h p)
      (Measure.pi fun _ : Fin k => condNext ν j hj p) < ⊤) ∧
    DCond ν j k hj h = ∫⁻ p, klDiv (condBlock ν j k h p)
      (Measure.pi fun _ : Fin k => condNext ν j hj p) ∂(ν.map (past j hj.le)) := by
  set P := ν.map (past j hj.le) with hPdef
  have hP : IsProbabilityMeasure P :=
    (Measure.isProbabilityMeasure_map_iff (measurable_past _).aemeasurable).mpr inferInstance
  have hbc := block_chain μ ν hH h
  have hsumfin : ∑ a ∈ Finset.range k, hCondT ν μ (j + a) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun a _ => hCondT_ne_top μ ν hH _
  have hbfin : klDiv (P ⊗ₘ condBlock ν j k h) (P ⊗ₘ Kernel.const _ (Measure.pi fun _ : Fin k => μ))
      ≠ ⊤ := by rw [hbc]; exact hsumfin
  obtain ⟨hG, hGm⟩ := klDiv_compProd_same P (condBlock ν j k h)
    (Kernel.const _ (Measure.pi fun _ : Fin k => μ)) hbfin
  simp only [Kernel.const_apply] at hG hGm
  have hhfin : hCond ν μ j hj ≠ ⊤ := by
    have := hCondT_ne_top μ ν hH j
    simpa [hCondT, hj] using this
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
  refine ⟨hDm, ?_, ?_⟩
  · filter_upwards [hpt, hGlt] with p hp hlt
    rw [hp] at hlt
    exact lt_of_le_of_lt le_self_add hlt
  · unfold DCond
    exact (lintegral_map' hDm (measurable_past _).aemeasurable).symm

end

/-- **Per-`j` comparison**: `|E ∫B dρ_j^{⊗k} - E B(block)| ≤ C √(2 D_{j,k})`. -/
theorem condProductMean_sub_block (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (ν : Measure (Config N d)) [IsProbabilityMeasure ν] (hsym : IsSymmetricMeasure ν)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {j k : ℕ} (hj : j < N) (h : j + k ≤ N)
    {B : (Fin k → Torus d) → ℝ} (hB : Measurable B) {C : ℝ} (hC : ∀ z, |B z| ≤ C) :
    |condProductMean ν k B j - ∫ X, B (block j k h X) ∂ν| ≤
      C * Real.sqrt (2 * (DCond ν j k hj h).toReal) := by
  set P := ν.map (past j hj.le) with hPdef
  have hP : IsProbabilityMeasure P :=
    (Measure.isProbabilityMeasure_map_iff (measurable_past _).aemeasurable).mpr inferInstance
  obtain ⟨hDm, hDlt, hDeq⟩ := DCond_data μ ν hsym hH hj h
  set F : (Fin j → Torus d) → ℝ := fun p =>
    ∫ z, B z ∂(Measure.pi fun _ : Fin k => condNext ν j hj p) with hFdef
  set G : (Fin j → Torus d) → ℝ := fun p => ∫ z, B z ∂(condBlock ν j k h p) with hGdef
  have hFm : Measurable F := by
    have := (hB.comp measurable_snd).stronglyMeasurable.integral_kernel_prod_right'
      (κ := piK (condNext ν j hj) k)
    have e : F = fun p => ∫ z, B z ∂(piK (condNext ν j hj) k p) := by
      funext p; rw [piK_apply]
    rw [e]; exact this.measurable
  have hGm : Measurable G :=
    ((hB.comp measurable_snd).stronglyMeasurable.integral_kernel_prod_right'
      (κ := condBlock ν j k h)).measurable
  obtain ⟨x0, -⟩ := nonempty_of_measure_ne_zero (μ := ν) (s := Set.univ) (by simp)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (block j k h x0))
  have hbnd : ∀ (m : Measure (Fin k → Torus d)) [IsProbabilityMeasure m], |∫ z, B z ∂m| ≤ C :=
    fun m _ => by
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ z, |B z| ∂m ≤ ∫ _, C ∂m := integral_mono_of_nonneg
            (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const C)
            (Eventually.of_forall hC)
        _ = C := by simp
  have hFb : ∀ p, |F p| ≤ C := fun p => hbnd _
  have hGb : ∀ p, |G p| ≤ C := fun p => hbnd _
  have hint : ∀ {f : (Fin j → Torus d) → ℝ}, Measurable f → (∀ p, |f p| ≤ C) → Integrable f P :=
    fun hf hb => Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact hb p)
  -- the two expectations as integrals over the past
  have e1 : condProductMean ν k B j = ∫ p, F p ∂P := by
    rw [condProductMean, dif_pos hj, integral_map (measurable_past _).aemeasurable
      hFm.aestronglyMeasurable]
  have e2 : ∫ X, B (block j k h X) ∂ν = ∫ p, G p ∂P := by
    have hlaw : ν.map (fun X => (past j hj.le X, block j k h X)) = P ⊗ₘ condBlock ν j k h :=
      (compProd_map_condDistrib (measurable_past _).aemeasurable
        (measurable_block h).aemeasurable).symm
    have hBi : Integrable (fun q : (Fin j → Torus d) × (Fin k → Torus d) => B q.2)
        (P ⊗ₘ condBlock ν j k h) :=
      Integrable.of_bound (hB.comp measurable_snd).aestronglyMeasurable C
        (Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hC q.2)
    rw [← Measure.integral_compProd hBi, ← hlaw, integral_map
      (f := fun q : (Fin j → Torus d) × (Fin k → Torus d) => B q.2)
      ((measurable_past _).prodMk (measurable_block h)).aemeasurable
      (hB.comp measurable_snd).aestronglyMeasurable]
  rw [e1, e2, ← integral_sub (hint hFm hFb) (hint hGm hGb)]
  refine (abs_integral_le_integral_abs).trans ?_
  -- pointwise Pinsker
  set D : (Fin j → Torus d) → ℝ := fun p => (klDiv (condBlock ν j k h p)
    (Measure.pi fun _ : Fin k => condNext ν j hj p)).toReal with hD
  have hpt : ∀ᵐ p ∂P, |F p - G p| ≤ C * Real.sqrt (2 * D p) := by
    filter_upwards [hDlt] with p hp
    rw [abs_sub_comm]
    exact abs_integral_sub_le_pinsker hB hC hp.ne
  have hDi : Integrable D P := integrable_toReal_of_lintegral_ne_top hDm (by
    rw [← hDeq]; exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr fun a _ =>
      hCondT_ne_top μ ν hH (j + a)) (by
        rw [DCond_add μ ν hsym hH hj h]; exact le_self_add))
  have hDint : ∫ p, D p ∂P = (DCond ν j k hj h).toReal := by
    rw [hDeq, integral_toReal hDm hDlt]
  have hD0 : ∀ᵐ p ∂P, 0 ≤ 2 * D p := Eventually.of_forall fun p => by
    simp only [hD]; positivity
  calc ∫ p, |F p - G p| ∂P ≤ ∫ p, C * Real.sqrt (2 * D p) ∂P :=
        integral_mono_ae ((hint hFm hFb).sub (hint hGm hGb)).abs
          ((integrable_sqrt_of hD0 (hDi.const_mul 2)).const_mul C) hpt
    _ = C * ∫ p, Real.sqrt (2 * D p) ∂P := integral_const_mul _ _
    _ ≤ C * Real.sqrt (∫ p, 2 * D p ∂P) :=
        mul_le_mul_of_nonneg_left (integral_sqrt_le hD0 (hDi.const_mul 2)) hC0
    _ = C * Real.sqrt (2 * (DCond ν j k hj h).toReal) := by rw [integral_const_mul, hDint]

/-- Exchangeability: `E B(X ∘ i)` does not depend on the injective index map `i`. -/
theorem integral_comp_inj_eq {ν : Measure (Config N d)} (hsym : IsSymmetricMeasure ν) {k : ℕ}
    {B : (Fin k → Torus d) → ℝ} (hB : Measurable B) {i i0 : Fin k → Fin N}
    (hi : Function.Injective i) (hi0 : Function.Injective i0) :
    ∫ X, B (X ∘ i) ∂ν = ∫ X, B (X ∘ i0) ∂ν := by
  classical
  set e := (Equiv.ofInjective i0 hi0).symm.trans (Equiv.ofInjective i hi) with he
  set σ : Equiv.Perm (Fin N) := e.extendSubtype with hσdef
  have hσ : ∀ a, σ (i0 a) = i a := by
    intro a
    rw [hσdef, Equiv.extendSubtype_apply_of_mem _ _ ⟨a, rfl⟩]
    simp [he, Equiv.ofInjective_symm_apply]
  have hm : Measurable fun X : Config N d => X ∘ σ :=
    measurable_pi_iff.mpr fun a => measurable_pi_apply _
  have hm0 : Measurable fun X : Config N d => B (X ∘ i0) :=
    hB.comp (measurable_pi_iff.mpr fun a => measurable_pi_apply _)
  have e1 : (fun X : Config N d => B (X ∘ i)) = fun X => B ((X ∘ σ) ∘ i0) := by
    funext X; congr 1; funext a; simp [hσ]
  rw [e1]
  conv_rhs => rw [← hsym σ]
  rw [integral_map hm.aemeasurable hm0.aestronglyMeasurable]

/-- At most `k² N^{k-1}` index maps `Fin k → Fin N` are not injective. -/
theorem card_not_injective_le (k N : ℕ) [DecidablePred fun i : Fin k → Fin N =>
    Function.Injective i] :
    (Finset.univ.filter fun i : Fin k → Fin N => ¬ Function.Injective i).card ≤
      k * k * N ^ (k - 1) := by
  classical
  have hpair : ∀ a b : Fin k, a ≠ b →
      (Finset.univ.filter fun i : Fin k → Fin N => i a = i b).card ≤ N ^ (k - 1) := by
    intro a b hab
    have h1 : Fintype.card ({x : Fin k // x ≠ a} → Fin N) = N ^ (k - 1) := by
      simp [Fintype.card_subtype_compl]
    rw [← h1, ← Finset.card_univ]
    refine Finset.card_le_card_of_injOn (fun i x => i x) (fun _ _ => Finset.mem_univ _) ?_
    intro i hi i' hi' hfe
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hi'
    funext x
    by_cases hx : x = a
    · subst hx; rw [hi, hi']; exact congrFun hfe ⟨b, hab.symm⟩
    · exact congrFun hfe ⟨x, hx⟩
  have hsub : (Finset.univ.filter fun i : Fin k → Fin N => ¬ Function.Injective i) ⊆
      (Finset.univ : Finset (Fin k)).offDiag.biUnion
        (fun p => Finset.univ.filter fun i : Fin k → Fin N => i p.1 = i p.2) := by
    intro i hi
    obtain ⟨-, hi⟩ := Finset.mem_filter.mp hi
    simp only [Function.Injective, not_forall] at hi
    obtain ⟨a, b, hne, hab⟩ := hi
    simp only [Finset.mem_biUnion, Finset.mem_offDiag, Finset.mem_univ, true_and,
      Finset.mem_filter]
    exact ⟨(a, b), hab, hne⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  refine (Finset.sum_le_card_nsmul _ _ (N ^ (k - 1)) fun p hp => ?_).trans ?_
  · rw [Finset.mem_offDiag] at hp; exact hpair _ _ hp.2.2
  · rw [smul_eq_mul, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)

/-- The empirical tensor versus a fixed injective sample: `|E B(L^{⊗k}) - E B(X∘i0)| ≤ 2C k²/N`. -/
theorem integral_empiricalTensor_sub {ν : Measure (Config N d)} [IsProbabilityMeasure ν]
    (hsym : IsSymmetricMeasure ν) {k : ℕ} {B : (Fin k → Torus d) → ℝ} (hB : Measurable B)
    {C : ℝ} (hC : ∀ z, |B z| ≤ C) {i0 : Fin k → Fin N} (hi0 : Function.Injective i0)
    (hN : 0 < N) :
    |∫ X, empiricalTensor k B X ∂ν - ∫ X, B (X ∘ i0) ∂ν| ≤ 2 * C * (k * k) / N := by
  classical
  have hm : ∀ i : Fin k → Fin N, Measurable fun X : Config N d => B (X ∘ i) := fun i =>
    hB.comp (measurable_pi_iff.mpr fun a => measurable_pi_apply _)
  have hI : ∀ i : Fin k → Fin N, Integrable (fun X : Config N d => B (X ∘ i)) ν := fun i =>
    Integrable.of_bound (hm i).aestronglyMeasurable C (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs]; exact hC _)
  obtain ⟨z0⟩ : Nonempty (Fin k → Torus d) := inferInstance
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC z0)
  set b0 := ∫ X, B (X ∘ i0) ∂ν
  set f : (Fin k → Fin N) → ℝ := fun i => ∫ X, B (X ∘ i) ∂ν - b0 with hf
  have hfb : ∀ i, |f i| ≤ 2 * C := fun i => by
    refine (abs_sub _ _).trans ?_
    have : ∀ i : Fin k → Fin N, |∫ X, B (X ∘ i) ∂ν| ≤ C := fun i =>
      (abs_integral_le_integral_abs).trans (by
        calc ∫ X, |B (X ∘ i)| ∂ν ≤ ∫ _, C ∂ν := integral_mono_of_nonneg
              (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const C)
              (Eventually.of_forall fun _ => hC _)
          _ = C := by simp)
    linarith [this i, this i0]
  have hf0 : ∀ i, Function.Injective i → f i = 0 := fun i hi => by
    simp only [hf]; rw [integral_comp_inj_eq hsym hB hi hi0]; ring
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcard : (Fintype.card (Fin k → Fin N) : ℝ) = (N : ℝ) ^ k := by simp
  have e1 : ∫ X, empiricalTensor k B X ∂ν - b0 = (N : ℝ)⁻¹ ^ k * ∑ i, f i := by
    simp only [empiricalTensor, hf]
    rw [integral_const_mul, integral_finset_sum _ fun i _ => hI i, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, mul_sub, ← mul_assoc, ← mul_pow,
      inv_mul_cancel₀ hNr.ne', one_pow, one_mul]
  rw [e1, abs_mul, abs_of_nonneg (by positivity)]
  have hsum : |∑ i, f i| ≤ 2 * C * (k * k * N ^ (k - 1) : ℕ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← Finset.sum_filter_of_ne (p := fun i => ¬ Function.Injective i) (fun i _ h hi =>
      h (by rw [hf0 i hi, abs_zero]))]
    refine (Finset.sum_le_card_nsmul _ _ (2 * C) fun i _ => hfb i).trans ?_
    rw [nsmul_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast card_not_injective_le k N) (by linarith)
  calc (N : ℝ)⁻¹ ^ k * |∑ i, f i| ≤ (N : ℝ)⁻¹ ^ k * (2 * C * (k * k * N ^ (k - 1) : ℕ)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 2 * C * (k * k) / N := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · have : (N : ℝ) ^ k = N * N ^ (k - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [inv_pow, this]; push_cast
        rw [le_div_iff₀ hNr]
        have hp : (0 : ℝ) < N ^ (k - 1) := by positivity
        field_simp
        rfl

/-- The summed dependence (5.4) in real form, including `k = 0`. -/
theorem sum_DCondT_toReal_le (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (ν : Measure (Config N d)) [IsProbabilityMeasure ν] (hsym : IsSymmetricMeasure ν)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {M k : ℕ} (hMN : M ≤ N) (hkM : k ≤ M) :
    ∑ j ∈ Finset.range (N - M), (DCondT ν j k).toReal ≤
      ((k * (k - 1) : ℕ) : ℝ) / ((M - k + 2 : ℕ) : ℝ) *
        (klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal := by
  have hfin : ∀ j, DCondT ν j k ≠ ⊤ := fun j => by
    unfold DCondT
    split_ifs with h
    · refine ne_top_of_le_ne_top (b := ∑ a ∈ Finset.range k, hCondT ν μ (j + a))
        (ENNReal.sum_ne_top.mpr fun a _ => hCondT_ne_top μ ν hH (j + a)) ?_
      rw [DCond_add μ ν hsym hH h.1 h.2]; exact le_self_add
    · exact ENNReal.zero_ne_top
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have : ∀ j, DCondT ν j 0 = 0 := fun j => by
      unfold DCondT
      split_ifs with h
      · have := DCond_add μ ν hsym hH h.1 h.2
        simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul,
          add_zero] at this
        exact this.symm
      · rfl
    simp [this]
  · have h4 := (summed_dependence_aux μ ν hsym hH).2.2.2 M k hMN hkM hk
    rw [← ENNReal.toReal_sum fun j _ => hfin j]
    refine (ENNReal.toReal_mono ?_ h4).trans (le_of_eq ?_)
    · exact ENNReal.mul_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by
        simp)) hH
    · rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast,
        ENNReal.toReal_natCast]

/-- **Lemma 5.1, (5.5).** -/
theorem conditional_empirical_aux (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (k : ℕ)
    (B : (Fin k → Torus d) → ℝ) (hB : Measurable B) (hBb : ∃ c, ∀ z, |B z| ≤ c) :
    ∃ C : ℝ, ∀ (N M : ℕ) (δ : ℝ) (ν : Measure (Config N d)) [IsProbabilityMeasure ν],
      IsSymmetricMeasure ν → klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤ →
      M ≤ N → k ≤ M → 0 < δ → δ ≤ (M : ℝ) / N →
      |∑ j ∈ Finset.range (N - M), condProductMean ν k B j -
          ((N - M : ℕ) : ℝ) * ∫ X, empiricalTensor k B X ∂ν| ≤
        C * (1 + Real.sqrt ((klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal / δ)) := by
  obtain ⟨c, hc⟩ := hBb
  set C := max c 0 with hCdef
  have hC : ∀ z, |B z| ≤ C := fun z => (hc z).trans (le_max_left _ _)
  have hC0 : 0 ≤ C := le_max_right _ _
  set K : ℝ := Real.sqrt (2 * ((k : ℝ) * k * k)) with hK
  refine ⟨2 * C * (k * k) + C * K, ?_⟩
  intro N M δ ν _ hsym hH hMN hkM hδ hδM
  set H := (klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal with hHdef
  have hH0 : 0 ≤ H := ENNReal.toReal_nonneg
  have hR0 : 0 ≤ 1 + Real.sqrt (H / δ) := by positivity
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  rcases Nat.eq_zero_or_pos (N - M) with hℓ | hℓ
  · rw [hℓ]; simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul,
      sub_zero, abs_zero]
    positivity
  have hMN' : M < N := by omega
  have hN : 0 < N := by omega
  set i0 : Fin k → Fin N := fun a => ⟨a, by omega⟩ with hi0def
  have hi0 : Function.Injective i0 := fun a b hab => by
    simp only [hi0def, Fin.mk.injEq] at hab; exact Fin.ext hab
  set b0 := ∫ X, B (X ∘ i0) ∂ν with hb0
  set ℓ := N - M with hℓdef
  set Dr : ℕ → ℝ := fun j => (DCondT ν j k).toReal with hDr
  -- per-`j` comparison with `b0`
  have hper : ∀ j ∈ Finset.range ℓ,
      |condProductMean ν k B j - b0| ≤ C * Real.sqrt (2 * Dr j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjN : j < N := by omega
    have h : j + k ≤ N := by omega
    have hblk : ∫ X, B (block j k h X) ∂ν = b0 := by
      have hinj : Function.Injective fun a : Fin k => (⟨j + a, by omega⟩ : Fin N) :=
        fun a b hab => by simp only [Fin.mk.injEq] at hab; exact Fin.ext (by omega)
      exact integral_comp_inj_eq hsym hB hinj hi0
    have := condProductMean_sub_block μ ν hsym hH hjN h hB hC
    rw [hblk] at this
    simpa only [hDr, DCondT, dif_pos (And.intro hjN h)] using this
  have hemp := integral_empiricalTensor_sub hsym hB hC hi0 hN
  -- Cauchy–Schwarz and the summed dependence
  have hS := sum_DCondT_toReal_le μ ν hsym hH hMN hkM
  have hDr0 : ∀ j, 0 ≤ Dr j := fun j => ENNReal.toReal_nonneg
  set S := ∑ j ∈ Finset.range ℓ, Real.sqrt (2 * Dr j) with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _
  have hCS : S ^ 2 ≤ ℓ * ∑ j ∈ Finset.range ℓ, 2 * Dr j := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range ℓ) (f := fun j => Real.sqrt (2 * Dr j))
    have h2D : ∀ j, Real.sqrt (2 * Dr j) ^ 2 = 2 * Dr j := fun j =>
      Real.sq_sqrt (by linarith [hDr0 j])
    simpa only [Finset.card_range, h2D] using this
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓN : (ℓ : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N M
  have hNδ : (N : ℝ) * δ ≤ M := by
    rw [le_div_iff₀ hNr] at hδM; linarith
  have hkey : (ℓ : ℝ) * ∑ j ∈ Finset.range ℓ, 2 * Dr j ≤ 2 * ((k : ℝ) * k * k) * (H / δ) := by
    rw [← Finset.mul_sum]
    set m : ℝ := ((M - k + 2 : ℕ) : ℝ) with hm
    have hm' : m = (M : ℝ) - k + 2 := by
      rw [hm]; push_cast [show k ≤ M + 2 by omega]; rw [Nat.cast_sub hkM]
    have hmpos : 0 < m := by
      have : (k : ℝ) ≤ M := by exact_mod_cast hkM
      rw [hm']; linarith
    set Kk : ℝ := ((k * (k - 1) : ℕ) : ℝ) with hKk
    have hKk0 : 0 ≤ Kk := Nat.cast_nonneg _
    have hKM : Kk * M ≤ (k : ℝ) * k * k * m := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp [hKk]
      · have hKk' : Kk = (k : ℝ) * (k - 1) := by
          rw [hKk]; push_cast [Nat.cast_sub hk]; ring
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        have hkM' : (k : ℝ) ≤ M := by exact_mod_cast hkM
        rw [hKk', hm']
        nlinarith [mul_nonneg (sub_nonneg.mpr hk1) (sub_nonneg.mpr hkM'),
          mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ k) (sub_nonneg.mpr hk1))
            (sub_nonneg.mpr hkM')]
    have hsum : ∑ j ∈ Finset.range ℓ, Dr j ≤ Kk / m * H := hS
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range ℓ, Dr j := Finset.sum_nonneg fun j _ => hDr0 j
    calc (ℓ : ℝ) * (2 * ∑ j ∈ Finset.range ℓ, Dr j) ≤ N * (2 * (Kk / m * H)) := by
          apply mul_le_mul hℓN (by linarith) (by linarith) hNr.le
      _ = 2 * H * (N * Kk / m) := by ring
      _ ≤ 2 * H * ((k : ℝ) * k * k / δ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_div_iff₀ hmpos hδ]
          calc (N : ℝ) * Kk * δ = Kk * (N * δ) := by ring
            _ ≤ Kk * M := mul_le_mul_of_nonneg_left hNδ hKk0
            _ ≤ (k : ℝ) * k * k * m := hKM
      _ = 2 * ((k : ℝ) * k * k) * (H / δ) := by ring
  have hSle : S ≤ K * Real.sqrt (H / δ) := by
    rw [hK, ← Real.sqrt_mul (by positivity)]
    exact Real.le_sqrt_of_sq_le (hCS.trans hkey)
  -- assembly
  have hsplit : ∑ j ∈ Finset.range ℓ, condProductMean ν k B j -
      (ℓ : ℝ) * ∫ X, empiricalTensor k B X ∂ν =
      ∑ j ∈ Finset.range ℓ, (condProductMean ν k B j - b0) -
        ℓ * (∫ X, empiricalTensor k B X ∂ν - b0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  rw [hsplit]
  have h1 : |∑ j ∈ Finset.range ℓ, (condProductMean ν k B j - b0)| ≤ C * S := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hSdef, Finset.mul_sum]
    exact Finset.sum_le_sum hper
  have h2 : |(ℓ : ℝ) * (∫ X, empiricalTensor k B X ∂ν - b0)| ≤ 2 * C * (k * k) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc (ℓ : ℝ) * |∫ X, empiricalTensor k B X ∂ν - b0| ≤ N * (2 * C * (k * k) / N) :=
          mul_le_mul hℓN hemp (abs_nonneg _) hNr.le
      _ = 2 * C * (k * k) := by field_simp
  have hsq0 : 0 ≤ Real.sqrt (H / δ) := Real.sqrt_nonneg _
  calc _ ≤ |∑ j ∈ Finset.range ℓ, (condProductMean ν k B j - b0)| +
        |(ℓ : ℝ) * (∫ X, empiricalTensor k B X ∂ν - b0)| := abs_sub _ _
    _ ≤ C * (K * Real.sqrt (H / δ)) + 2 * C * (k * k) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left hSle hC0)
    _ ≤ (2 * C * (k * k) + C * K) * (1 + Real.sqrt (H / δ)) := by
        have : 0 ≤ 2 * C * ((k : ℝ) * k) := by positivity
        nlinarith [mul_nonneg this hsq0, mul_nonneg hC0 hK0]

end SharpLSI
