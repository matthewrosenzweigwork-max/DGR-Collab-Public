import FullLabeledLSI.Paper.Sec5Chain
import SharpSymmetricLSI.Paper.CondEmpirical

/-!
# Section 5: conditional Pinsker with a test depending on the revealed coordinates

* `gRev_ne_top`, `DRev_ne_top`: if `H₀ = H(ν | μ^{⊗N}) < ∞` every `g(S,i)` (`i ∉ S`) and every
  `d(S,I)` (`I` distinct in `Sᶜ`) is finite.
* `condPinsker_tuple`: for a bounded measurable test `A(X_S, z)` of the revealed coordinates and a
  `k`-tuple `z`, replacing the joint conditional law by the product of the marginal conditional
  laws costs at most `c √(2 d(S,I))` (conditional Pinsker and Jensen).
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d N : ℕ} (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
  (μ : Measure (Torus d)) [IsProbabilityMeasure μ]

/-- A product of Markov kernels is a measurable family of measures. -/
theorem measurable_pi_kernels {α T : Type*} [MeasurableSpace α] [MeasurableSpace T] {k : ℕ}
    (κ : Fin k → Kernel α T) [∀ l, IsMarkovKernel (κ l)] :
    Measurable fun a => Measure.pi fun l => κ l a := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (S := Set.pi Set.univ '' Set.pi Set.univ fun _ => {s : Set T | MeasurableSet s})
    generateFrom_pi.symm isPiSystem_pi ?_
  rintro _ ⟨s, hs, rfl⟩
  simp only [Measure.pi_pi]
  exact Finset.measurable_prod _ fun l _ => (κ l).measurable_coe (hs l (Set.mem_univ l))

/-- The product kernel `a ↦ ⊗_l κ_l a`. -/
noncomputable def kPi {α T : Type*} [MeasurableSpace α] [MeasurableSpace T] {k : ℕ}
    (κ : Fin k → Kernel α T) [∀ l, IsMarkovKernel (κ l)] : Kernel α (Fin k → T) :=
  ⟨fun a => Measure.pi fun l => κ l a, measurable_pi_kernels κ⟩

theorem kPi_apply {α T : Type*} [MeasurableSpace α] [MeasurableSpace T] {k : ℕ}
    (κ : Fin k → Kernel α T) [∀ l, IsMarkovKernel (κ l)] (a : α) :
    kPi κ a = Measure.pi fun l => κ l a := rfl

instance isMarkovKernel_kPi {α T : Type*} [MeasurableSpace α] [MeasurableSpace T] {k : ℕ}
    (κ : Fin k → Kernel α T) [∀ l, IsMarkovKernel (κ l)] : IsMarkovKernel (kPi κ) :=
  ⟨fun a => by rw [kPi_apply]; infer_instance⟩

theorem gRev_ne_top (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) (S : Finset (Fin N))
    (i : Fin N) (hi : i ∉ S) : gRev ν μ S i ≠ ⊤ := by
  have hlt : S.card < N := by
    have := Finset.card_lt_card (s := S) (t := Finset.univ)
      ⟨Finset.subset_univ _, fun h => hi (h (Finset.mem_univ i))⟩
    simpa using this
  have hsum := chain_sum ν μ
  have hh : hRev ν μ S.card ≠ ⊤ := by
    refine ne_top_of_le_ne_top hH ?_
    rw [← hsum]
    exact Finset.single_le_sum (f := fun j => hRev ν μ j) (fun _ _ => zero_le)
      (Finset.mem_range.2 hlt)
  rw [hRev_eq_avg1' ν μ hlt] at hh
  unfold avg1 at hh
  intro hg
  apply hh
  have h1 : gRev ν μ S i ≤ ∑ i' ∈ Sᶜ, gRev ν μ S i' :=
    Finset.single_le_sum (f := fun i' => gRev ν μ S i') (fun _ _ => zero_le)
      (Finset.mem_compl.2 hi)
  have hSmem : S ∈ (Finset.univ : Finset (Fin N)).powersetCard S.card :=
    Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩
  have h2 : (((N - S.card : ℕ) : ℝ≥0∞)⁻¹) * ∑ i' ∈ Sᶜ, gRev ν μ S i' ≤
      ∑ S' ∈ (Finset.univ : Finset (Fin N)).powersetCard S.card,
        (((N - S.card : ℕ) : ℝ≥0∞)⁻¹) * ∑ i' ∈ S'ᶜ, gRev ν μ S' i' :=
    Finset.single_le_sum
      (f := fun S' => (((N - S.card : ℕ) : ℝ≥0∞)⁻¹) * ∑ i' ∈ S'ᶜ, gRev ν μ S' i')
      (fun _ _ => zero_le) hSmem
  have hc0 : ((Nat.choose N S.card : ℝ≥0∞)⁻¹) ≠ 0 :=
    ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
  have hn0 : (((N - S.card : ℕ) : ℝ≥0∞)⁻¹) ≠ 0 :=
    ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
  have htop : ∑ i' ∈ Sᶜ, gRev ν μ S i' = ⊤ := top_le_iff.1 (hg ▸ h1)
  have h3 : (((N - S.card : ℕ) : ℝ≥0∞)⁻¹) * ∑ i' ∈ Sᶜ, gRev ν μ S i' = ⊤ := by
    rw [htop, ENNReal.mul_top hn0]
  rw [h3] at h2
  have h4 := top_le_iff.1 h2
  rw [h4, ENNReal.mul_top hc0]

theorem DRev_ne_top (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) (S : Finset (Fin N))
    {k : ℕ} (I : Fin k → Fin N) (hI : I ∈ distinctTuples S k) : DRev ν S I ≠ ⊤ := by
  simp only [distinctTuples, Finset.mem_filter, Finset.mem_univ, true_and] at hI
  obtain ⟨hinj, hS⟩ := hI
  have hG : GRev ν μ S I ≠ ⊤ := by
    rw [GRev_chain]
    refine ENNReal.sum_ne_top.2 fun a _ => gRev_ne_top ν μ hH _ _ ?_
    rw [mem_preSet_iff]
    rintro (h | ⟨l, hl, hla⟩)
    · exact hS a h
    · have := hinj hla
      rw [this] at hl
      exact lt_irrefl _ hl
  rw [GRev_eq_DRev_add ν μ S I] at hG
  exact ne_top_of_le_ne_top hG le_self_add

/-- Conditional Pinsker, bounded test depending on the revealed coordinates. -/
theorem condPinsker_tuple (S : Finset (Fin N)) {k : ℕ} (I : Fin k → Fin N)
    (A : (S → Torus d) → (Fin k → Torus d) → ℝ)
    (hA : Measurable fun p : (S → Torus d) × (Fin k → Torus d) => A p.1 p.2)
    {c : ℝ} (hc : ∀ a z, |A a z| ≤ c) (hD : DRev ν S I ≠ ⊤) :
    |∫ X, (∫ z, A (restrictS S X) z
          ∂Measure.pi (fun l => condLawS ν S (I l) (restrictS S X))) ∂ν -
        ∫ X, A (restrictS S X) (fun l => X (I l)) ∂ν| ≤
      c * Real.sqrt (2 * (DRev ν S I).toReal) := by
  set P0 : Measure (S → Torus d) := ν.map (restrictS S) with hP0def
  have hP0 : IsProbabilityMeasure P0 :=
    (Measure.isProbabilityMeasure_map_iff (measurable_restrictS S).aemeasurable).mpr inferInstance
  have hZm : Measurable (fun X : Config N d => fun l : Fin k => X (I l)) :=
    measurable_pi_iff.mpr fun l => measurable_pi_apply _
  set κ : Kernel (S → Torus d) (Fin k → Torus d) := condJointS ν S I with hκ
  set P' : Kernel (S → Torus d) (Fin k → Torus d) :=
    kPi (fun l => condLawS ν S (I l)) with hP'
  have hP'a : ∀ a, P' a = Measure.pi (fun l => condLawS ν S (I l) a) := fun a => rfl
  set F : (S → Torus d) → ℝ := fun a => ∫ z, A a z ∂(P' a) with hFdef
  set G : (S → Torus d) → ℝ := fun a => ∫ z, A a z ∂(κ a) with hGdef
  have hFm : Measurable F :=
    (hA.stronglyMeasurable.integral_kernel_prod_right' (κ := P')).measurable
  have hGm : Measurable G :=
    (hA.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable
  obtain ⟨x0, -⟩ := nonempty_of_measure_ne_zero (μ := ν) (s := Set.univ) (by simp)
  have hC0 : 0 ≤ c := (abs_nonneg _).trans (hc (restrictS S x0) (fun l => x0 (I l)))
  have hbnd : ∀ (a : S → Torus d) (m : Measure (Fin k → Torus d)) [IsProbabilityMeasure m],
      |∫ z, A a z ∂m| ≤ c := fun a m _ => by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ z, |A a z| ∂m ≤ ∫ _, c ∂m := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun _ => abs_nonneg _) (integrable_const c)
          (Filter.Eventually.of_forall (hc a))
      _ = c := by simp
  have hFb : ∀ a, |F a| ≤ c := fun a => hbnd a _
  have hGb : ∀ a, |G a| ≤ c := fun a => hbnd a _
  have hint : ∀ {f : (S → Torus d) → ℝ}, Measurable f → (∀ a, |f a| ≤ c) → Integrable f P0 :=
    fun hf hb => Integrable.of_bound hf.aestronglyMeasurable c (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact hb p)
  have e1 : ∫ X, (∫ z, A (restrictS S X) z
      ∂Measure.pi (fun l => condLawS ν S (I l) (restrictS S X))) ∂ν = ∫ a, F a ∂P0 := by
    rw [hP0def, integral_map (measurable_restrictS S).aemeasurable hFm.aestronglyMeasurable]
    rfl
  have e2 : ∫ X, A (restrictS S X) (fun l => X (I l)) ∂ν = ∫ a, G a ∂P0 := by
    have hlaw : ν.map (fun X => (restrictS S X, fun l : Fin k => X (I l))) = P0 ⊗ₘ κ :=
      (compProd_map_condDistrib (measurable_restrictS S).aemeasurable hZm.aemeasurable).symm
    have hBi : Integrable (fun q : (S → Torus d) × (Fin k → Torus d) => A q.1 q.2) (P0 ⊗ₘ κ) :=
      Integrable.of_bound hA.aestronglyMeasurable c
        (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hc q.1 q.2)
    rw [← integral_map ((measurable_restrictS S).prodMk hZm).aemeasurable
      hA.aestronglyMeasurable, hlaw, Measure.integral_compProd hBi]
  -- pointwise Pinsker
  set D : (S → Torus d) → ℝ≥0∞ := fun a => klDiv (κ a) (P' a) with hDdef
  have hDmeas : Measurable D := measurable_klDiv_kernel κ P'
  have hDeq : DRev ν S I = ∫⁻ a, D a ∂P0 := by
    unfold DRev
    rw [hP0def, lintegral_map hDmeas (measurable_restrictS S)]
    rfl
  have hDlt : ∀ᵐ a ∂P0, D a < ⊤ := ae_lt_top hDmeas (by rw [← hDeq]; exact hD)
  set Dr : (S → Torus d) → ℝ := fun a => (D a).toReal with hDr
  have hpt : ∀ᵐ a ∂P0, |F a - G a| ≤ c * Real.sqrt (2 * Dr a) := by
    filter_upwards [hDlt] with a ha
    rw [abs_sub_comm]
    exact abs_integral_sub_le_pinsker (P := κ a) (Q := P' a)
      (hA.comp measurable_prodMk_left) (hc a) ha.ne
  have hDi : Integrable Dr P0 :=
    integrable_toReal_of_lintegral_ne_top hDmeas.aemeasurable (by rw [← hDeq]; exact hD)
  have hDint : ∫ a, Dr a ∂P0 = (DRev ν S I).toReal := by
    rw [hDeq, integral_toReal hDmeas.aemeasurable hDlt]
  have hD0 : ∀ᵐ a ∂P0, 0 ≤ 2 * Dr a := Filter.Eventually.of_forall fun a => by
    simp only [hDr]; positivity
  rw [e1, e2, ← integral_sub (hint hFm hFb) (hint hGm hGb)]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ a, |F a - G a| ∂P0 ≤ ∫ a, c * Real.sqrt (2 * Dr a) ∂P0 :=
        integral_mono_ae ((hint hFm hFb).sub (hint hGm hGb)).abs
          ((integrable_sqrt_of hD0 (hDi.const_mul 2)).const_mul c) hpt
    _ = c * ∫ a, Real.sqrt (2 * Dr a) ∂P0 := integral_const_mul _ _
    _ ≤ c * Real.sqrt (∫ a, 2 * Dr a ∂P0) :=
        mul_le_mul_of_nonneg_left (integral_sqrt_le hD0 (hDi.const_mul 2)) hC0
    _ = c * Real.sqrt (2 * (DRev ν S I).toReal) := by rw [integral_const_mul, hDint]

end SharpLSI.FL
