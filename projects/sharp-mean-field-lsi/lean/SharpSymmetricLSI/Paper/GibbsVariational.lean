import SharpSymmetricLSI.Defs.D05_FreeEnergy
import SharpSymmetricLSI.Defs.D08_Gibbs
import SharpSymmetricLSI.Paper.Gibbs

/-!
# The Gibbs variational identity and product states (Phase 3, lane D; R5, R6)

`H(ν | P_N) = H(ν | m^{⊗N}) + ν(H_N) + log Z_N`, from Mathlib's `llr` of tilted measures
(`P_N = (m^{⊗N}).tilted (-H_N)`), and the entropy/energy of product states `ρ^{⊗N}`.
-/

open MeasureTheory InformationTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

theorem gibbs_eq_tilted (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (N : ℕ) :
    gibbs V W N = (volume : Measure (Config N d)).tilted (fun X => -hamiltonian V W N X) := rfl

/-- The product of densities is the density of the product. -/
theorem pi_withDensity_ofReal {N : ℕ} {f : Torus d → ℝ} (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f (haar d)) :
    Measure.pi (fun _ : Fin N => (haar d).withDensity (fun x => ENNReal.ofReal (f x))) =
      (volume : Measure (Config N d)).withDensity (fun X => ENNReal.ofReal (∏ i, f (X i))) := by
  haveI : IsFiniteMeasure ((haar d).withDensity (fun x => ENNReal.ofReal (f x))) :=
    isFiniteMeasure_withDensity_ofReal hfi.2
  refine Measure.pi_eq fun s hs => ?_
  have hg : ∀ i, Integrable ((s i).indicator f) (haar d) := fun i => hfi.indicator (hs i)
  have hpt : ∀ X : Config N d, (univ.pi s).indicator (fun X => ENNReal.ofReal (∏ i, f (X i))) X =
      ENNReal.ofReal (∏ i, (s i).indicator f (X i)) := fun X => by
    by_cases hX : X ∈ univ.pi s
    · rw [indicator_of_mem hX]
      congr 1
      exact Finset.prod_congr rfl fun i _ => (indicator_of_mem (hX i (mem_univ i)) f).symm
    · rw [indicator_of_notMem hX]
      simp only [Set.mem_pi, mem_univ, true_implies, not_forall] at hX
      obtain ⟨i, hi⟩ := hX
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi f), ENNReal.ofReal_zero]
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [hpt]
  have hint : Integrable (fun X : Config N d => ∏ i, (s i).indicator f (X i)) volume :=
    Integrable.fintype_prod (f := fun _ => fun x => (s _).indicator f x) hg
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun X =>
      Finset.prod_nonneg fun i _ => indicator_nonneg (fun x _ => hf0 x) _),
    volume_pi, integral_fintype_prod_eq_prod (f := fun i => (s i).indicator f),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (indicator_nonneg (fun x _ => hf0 x)))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), integral_indicator (hs i),
    ofReal_integral_eq_lintegral_ofReal hfi.integrableOn (Eventually.of_forall fun x => hf0 x)]

/-- Tensorization of the relative entropy for product states. -/
theorem klDiv_pi {N : ℕ} {ρ : Measure (Torus d)} [IsProbabilityMeasure ρ]
    (h : klDiv ρ (haar d) ≠ ⊤) :
    klDiv (Measure.pi fun _ : Fin N => ρ) (volume : Measure (Config N d)) ≠ ⊤ ∧
      (klDiv (Measure.pi fun _ : Fin N => ρ) (volume : Measure (Config N d))).toReal =
        N * (klDiv ρ (haar d)).toReal := by
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp h
  set f : Torus d → ℝ := fun x => (ρ.rnDeriv (haar d) x).toReal with hf
  have hfm : Measurable f := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hf0 : ∀ x, 0 ≤ f x := fun x => ENNReal.toReal_nonneg
  have hfi : Integrable f (haar d) := Measure.integrable_toReal_rnDeriv
  have hρ : (haar d).withDensity (fun x => ENNReal.ofReal (f x)) = ρ := by
    conv_rhs => rw [← Measure.withDensity_rnDeriv_eq ρ (haar d) hac]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top ρ (haar d)] with x hx
    simp only [hf, ENNReal.ofReal_toReal hx.ne]
  have hpi : Measure.pi (fun _ : Fin N => ρ) =
      (volume : Measure (Config N d)).withDensity (fun X => ENNReal.ofReal (∏ i, f (X i))) := by
    have := pi_withDensity_ofReal (N := N) hfm hf0 hfi
    rwa [hρ] at this
  set P := Measure.pi (fun _ : Fin N => ρ) with hP
  have hacpi : P ≪ volume := by rw [hpi]; exact withDensity_absolutelyContinuous _ _
  have hrn : P.rnDeriv volume =ᵐ[volume] fun X => ENNReal.ofReal (∏ i, f (X i)) := by
    rw [hpi]
    exact Measure.rnDeriv_withDensity _ (ENNReal.measurable_ofReal.comp
      (Finset.measurable_prod _ fun i _ => hfm.comp (measurable_pi_apply i)))
  have hpos1 : ∀ᵐ x ∂ρ, 0 < f x := by
    filter_upwards [Measure.rnDeriv_pos hac, hac.ae_le (Measure.rnDeriv_lt_top ρ (haar d))]
      with x h1 h2
    exact ENNReal.toReal_pos h1.ne' h2.ne
  have hpos : ∀ᵐ X ∂P, ∀ i, 0 < f (X i) := by
    rw [ae_all_iff]
    exact fun i => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin N => ρ) (i := i)).eventually hpos1
  have hllr : llr P volume =ᵐ[P] fun X => ∑ i, llr ρ (haar d) (X i) := by
    filter_upwards [hacpi.ae_le hrn, hpos] with X h1 h2
    rw [llr, h1, ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => hf0 _),
      Real.log_prod (fun i _ => (h2 i).ne')]
    rfl
  have hint' : Integrable (fun X : Config N d => ∑ i, llr ρ (haar d) (X i)) P :=
    integrable_finsetSum _ fun i _ => integrable_comp_eval (μ := fun _ => ρ) hint
  have hintP : Integrable (llr P volume) P := hint'.congr hllr.symm
  refine ⟨klDiv_ne_top hacpi hintP, ?_⟩
  rw [toReal_klDiv_of_measure_eq hacpi (by simp), toReal_klDiv_of_measure_eq hac (by simp),
    integral_congr_ae hllr, integral_finsetSum _ fun i _ => integrable_comp_eval (μ := fun _ => ρ) hint]
  have hc : ∀ i : Fin N, ∫ X, llr ρ (haar d) (X i) ∂P = ∫ x, llr ρ (haar d) x ∂ρ := fun i =>
    integral_comp_eval (μ := fun _ : Fin N => ρ) hint.aestronglyMeasurable
  rw [Finset.sum_congr rfl fun i _ => hc i]
  simp

section Gibbs

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem exists_bound_of_continuous {X : Type*} [TopologicalSpace X] [CompactSpace X] {f : X → ℝ}
    (hf : Continuous f) : ∃ C, ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x (mem_univ x)⟩

theorem integrable_of_continuous {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := exists_bound_of_continuous hf
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

/-- **The Gibbs variational identity**: `H(ν|P_N) = H(ν|m^{⊗N}) + ν(H_N) + log Z_N`. -/
theorem klDiv_gibbs (hyp : Hyp V W KV KW) {N : ℕ} {ν : Measure (Config N d)}
    [IsProbabilityMeasure ν] (h : klDiv ν volume ≠ ⊤) :
    klDiv ν (gibbs V W N) ≠ ⊤ ∧
      (klDiv ν (gibbs V W N)).toReal = (klDiv ν volume).toReal + (∫ X, hamiltonian V W N X ∂ν) +
        Real.log (partitionFn V W N) := by
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp h
  have hH := continuous_hamiltonian hyp N
  have hfμ : Integrable (fun X => -hamiltonian V W N X) ν := (integrable_of_continuous hH).neg
  have hfν : Integrable (fun X => Real.exp (-hamiltonian V W N X)) (volume : Measure (Config N d)) :=
    integrable_of_continuous (Real.continuous_exp.comp hH.neg)
  haveI := gibbs_isProbabilityMeasure hyp N
  have hac' : ν ≪ gibbs V W N := hac.trans (absolutelyContinuous_tilted hfν)
  refine ⟨klDiv_ne_top hac' (integrable_llr_tilted_right hac hfμ hint hfν), ?_⟩
  rw [toReal_klDiv_of_measure_eq hac' (by simp), toReal_klDiv_of_measure_eq hac (by simp),
    gibbs_eq_tilted, integral_llr_tilted_right hac hfμ hfν hint, integral_neg, partitionFn]
  ring

/-- The pair law of a product state. -/
theorem map_pair_pi {N : ℕ} {ρ : Measure (Torus d)} [IsProbabilityMeasure ρ] {i j : Fin N}
    (hij : i ≠ j) :
    (Measure.pi fun _ : Fin N => ρ).map (fun X => (X i, X j)) = ρ.prod ρ := by
  have hind := iIndepFun_pi (μ := fun _ : Fin N => ρ) (X := fun _ => id)
    (fun _ => aemeasurable_id)
  have h2 := (hind.indepFun hij)
  simp only [id_eq] at h2
  have h3 := (indepFun_iff_map_prod_eq_prod_map_map (f := fun ω : Config N d => ω i)
    (g := fun ω : Config N d => ω j) (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable).mp h2
  rw [h3, (measurePreserving_eval (fun _ : Fin N => ρ) i).map_eq,
    (measurePreserving_eval (fun _ : Fin N => ρ) j).map_eq]

/-- The energy of a product state. -/
theorem integral_hamiltonian_pi (hyp : Hyp V W KV KW) {N : ℕ} (hN : 1 ≤ N) {ρ : Measure (Torus d)}
    [IsProbabilityMeasure ρ] :
    ∫ X, hamiltonian V W N X ∂(Measure.pi fun _ : Fin N => ρ) =
      N * potE V ρ + ((N : ℝ) - 1) / 2 * interE W ρ ρ := by
  set P := Measure.pi fun _ : Fin N => ρ with hP
  have hV := hyp.continuous_V
  have hWc : Continuous (Function.uncurry W) := hyp.continuous_W
  have hWij : ∀ i j : Fin N, Continuous fun X : Config N d => W (X i) (X j) := fun i j =>
    hWc.comp ((continuous_apply i).prodMk (continuous_apply j) :
      Continuous fun X : Config N d => (X i, X j))
  have hVi : ∀ i : Fin N, ∫ X, V (X i) ∂P = potE V ρ := fun i =>
    integral_comp_eval (μ := fun _ : Fin N => ρ) hV.aestronglyMeasurable
  have hWprod : ∫ p, Function.uncurry W p ∂(ρ.prod ρ) = interE W ρ ρ := by
    rw [integral_prod_symm _ (integrable_of_continuous hWc)]
    rfl
  have hWi : ∀ i j : Fin N, ∫ X, W (X i) (X j) ∂P = if i = j then 0 else interE W ρ ρ := by
    intro i j
    split_ifs with hij
    · subst hij; simp [hyp.diag]
    · rw [← hWprod, ← map_pair_pi (ρ := ρ) hij, integral_map (by fun_prop)
        hWc.aestronglyMeasurable]
      rfl
  have i1 : Integrable (fun X : Config N d => ∑ i, V (X i)) P :=
    integrable_finsetSum _ fun i _ => integrable_of_continuous (hV.comp (continuous_apply i))
  have i2 : ∀ i, Integrable (fun X : Config N d => ∑ j, W (X i) (X j)) P := fun i =>
    integrable_finsetSum _ fun j _ => integrable_of_continuous (hWij i j)
  have i3 : Integrable (fun X : Config N d => ∑ i, ∑ j, W (X i) (X j)) P :=
    integrable_finsetSum _ fun i _ => i2 i
  unfold hamiltonian
  rw [integral_add i1 (i3.const_mul _), integral_const_mul,
    integral_finsetSum (f := fun i (X : Config N d) => V (X i)) _
      fun i _ => integrable_of_continuous (hV.comp (continuous_apply i)),
    integral_finsetSum (f := fun i (X : Config N d) => ∑ j, W (X i) (X j)) _ fun i _ => i2 i]
  have e2 : ∀ i, ∫ X, ∑ j, W (X i) (X j) ∂P = ∑ j, ∫ X, W (X i) (X j) ∂P := fun i =>
    integral_finsetSum (f := fun j (X : Config N d) => W (X i) (X j)) _
      fun j _ => integrable_of_continuous (hWij i j)
  simp_rw [e2, hVi, hWi]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ∀ i : Fin N, (∑ j : Fin N, if i = j then (0 : ℝ) else interE W ρ ρ) =
      ((N : ℝ) - 1) * interE W ρ ρ := fun i => by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hf : (Finset.univ.filter fun x : Fin N => ¬i = x) = Finset.univ.erase i := by
      ext x; simp [eq_comm]
    rw [hf, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hN, Nat.cast_one]
  simp_rw [this]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  field_simp

end Gibbs

end SharpLSI
