import SharpSymmetricLSI.Paper.GibbsVariational
import SharpSymmetricLSI.Paper.PartitionLimit
import SharpSymmetricLSI.Paper.ProductEntropy
import FullLabeledLSI.Defs.F01_Species

/-!
# Proposition 3.2: entropy of products with nonidentical factors

Generalizations of `klDiv_pi`, `map_pair_pi`, `integral_hamiltonian_pi` and
`product_state_entropy_aux` (GibbsVariational, ProductEntropy) to `⊗ᵢ μᵢ`.
-/

noncomputable section
open MeasureTheory InformationTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ}

theorem pi_withDensity_ofReal_gen {N : ℕ} {f : Fin N → Torus d → ℝ} (hfm : ∀ i, Measurable (f i))
    (hf0 : ∀ i x, 0 ≤ f i x) (hfi : ∀ i, Integrable (f i) (haar d)) :
    Measure.pi (fun i : Fin N => (haar d).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (volume : Measure (Config N d)).withDensity
        (fun X => ENNReal.ofReal (∏ i, f i (X i))) := by
  haveI : ∀ i, IsFiniteMeasure ((haar d).withDensity (fun x => ENNReal.ofReal (f i x))) :=
    fun i => isFiniteMeasure_withDensity_ofReal (hfi i).2
  refine Measure.pi_eq fun s hs => ?_
  have hg : ∀ i, Integrable ((s i).indicator (f i)) (haar d) := fun i => (hfi i).indicator (hs i)
  have hpt : ∀ X : Config N d, (univ.pi s).indicator
      (fun X => ENNReal.ofReal (∏ i, f i (X i))) X =
      ENNReal.ofReal (∏ i, (s i).indicator (f i) (X i)) := fun X => by
    by_cases hX : X ∈ univ.pi s
    · rw [indicator_of_mem hX]
      congr 1
      exact Finset.prod_congr rfl fun i _ => (indicator_of_mem (hX i (mem_univ i)) (f i)).symm
    · rw [indicator_of_notMem hX]
      simp only [Set.mem_pi, mem_univ, true_implies, not_forall] at hX
      obtain ⟨i, hi⟩ := hX
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi (f i)),
        ENNReal.ofReal_zero]
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [hpt]
  have hint : Integrable (fun X : Config N d => ∏ i, (s i).indicator (f i) (X i)) volume :=
    Integrable.fintype_prod (f := fun i => fun x => (s i).indicator (f i) x) hg
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun X =>
      Finset.prod_nonneg fun i _ => indicator_nonneg (fun x _ => hf0 i x) _),
    volume_pi, integral_fintype_prod_eq_prod (f := fun i => (s i).indicator (f i)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg
      (indicator_nonneg (fun x _ => hf0 i x)))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), integral_indicator (hs i),
    ofReal_integral_eq_lintegral_ofReal (hfi i).integrableOn
      (Eventually.of_forall fun x => hf0 i x)]


/-- Tensorization of the relative entropy for products with nonidentical factors. -/
theorem klDiv_pi_gen {N : ℕ} {ρ : Fin N → Measure (Torus d)} [∀ i, IsProbabilityMeasure (ρ i)]
    (h : ∀ i, klDiv (ρ i) (haar d) ≠ ⊤) :
    klDiv (Measure.pi ρ) (volume : Measure (Config N d)) ≠ ⊤ ∧
      (klDiv (Measure.pi ρ) (volume : Measure (Config N d))).toReal =
        ∑ i, (klDiv (ρ i) (haar d)).toReal := by
  have hac : ∀ i, ρ i ≪ haar d := fun i => (klDiv_ne_top_iff.mp (h i)).1
  have hint : ∀ i, Integrable (llr (ρ i) (haar d)) (ρ i) := fun i => (klDiv_ne_top_iff.mp (h i)).2
  set f : Fin N → Torus d → ℝ := fun i x => ((ρ i).rnDeriv (haar d) x).toReal with hf
  have hfm : ∀ i, Measurable (f i) := fun i => (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hf0 : ∀ i x, 0 ≤ f i x := fun i x => ENNReal.toReal_nonneg
  have hfi : ∀ i, Integrable (f i) (haar d) := fun i => Measure.integrable_toReal_rnDeriv
  have hρ : ∀ i, (haar d).withDensity (fun x => ENNReal.ofReal (f i x)) = ρ i := fun i => by
    conv_rhs => rw [← Measure.withDensity_rnDeriv_eq (ρ i) (haar d) (hac i)]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top (ρ i) (haar d)] with x hx
    simp only [hf, ENNReal.ofReal_toReal hx.ne]
  have hpi : Measure.pi ρ =
      (volume : Measure (Config N d)).withDensity (fun X => ENNReal.ofReal (∏ i, f i (X i))) := by
    have := pi_withDensity_ofReal_gen (N := N) hfm hf0 hfi
    simp_rw [hρ] at this
    exact this
  set P := Measure.pi ρ with hP
  have hacpi : P ≪ volume := by rw [hpi]; exact withDensity_absolutelyContinuous _ _
  have hrn : P.rnDeriv volume =ᵐ[volume] fun X => ENNReal.ofReal (∏ i, f i (X i)) := by
    rw [hpi]
    exact Measure.rnDeriv_withDensity _ (ENNReal.measurable_ofReal.comp
      (Finset.measurable_prod _ fun i _ => (hfm i).comp (measurable_pi_apply i)))
  have hpos1 : ∀ i, ∀ᵐ x ∂ρ i, 0 < f i x := fun i => by
    filter_upwards [Measure.rnDeriv_pos (hac i), (hac i).ae_le (Measure.rnDeriv_lt_top (ρ i) (haar d))]
      with x h1 h2
    exact ENNReal.toReal_pos h1.ne' h2.ne
  have hpos : ∀ᵐ X ∂P, ∀ i, 0 < f i (X i) := by
    rw [ae_all_iff]
    exact fun i => (Measure.tendsto_eval_ae_ae (μ := ρ) (i := i)).eventually (hpos1 i)
  have hllr : llr P volume =ᵐ[P] fun X => ∑ i, llr (ρ i) (haar d) (X i) := by
    filter_upwards [hacpi.ae_le hrn, hpos] with X h1 h2
    rw [llr, h1, ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => hf0 i _),
      Real.log_prod (fun i _ => (h2 i).ne')]
    rfl
  have hint' : Integrable (fun X : Config N d => ∑ i, llr (ρ i) (haar d) (X i)) P :=
    integrable_finsetSum _ fun i _ => integrable_comp_eval (μ := ρ) (hint i)
  have hintP : Integrable (llr P volume) P := hint'.congr hllr.symm
  refine ⟨klDiv_ne_top hacpi hintP, ?_⟩
  rw [toReal_klDiv_of_measure_eq hacpi (by simp)]
  rw [integral_congr_ae hllr, integral_finsetSum _ fun i _ => integrable_comp_eval (μ := ρ) (hint i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_comp_eval (μ := ρ) (hint i).aestronglyMeasurable,
    toReal_klDiv_of_measure_eq (hac i) (by simp)]


theorem map_pair_pi_gen {N : ℕ} {ρ : Fin N → Measure (Torus d)} [∀ i, IsProbabilityMeasure (ρ i)]
    {i j : Fin N} (hij : i ≠ j) :
    (Measure.pi ρ).map (fun X => (X i, X j)) = (ρ i).prod (ρ j) := by
  have hind := iIndepFun_pi (μ := ρ) (X := fun _ => id) (fun _ => aemeasurable_id)
  have h2 := (hind.indepFun hij)
  simp only [id_eq] at h2
  have h3 := (indepFun_iff_map_prod_eq_prod_map_map (f := fun ω : Config N d => ω i)
    (g := fun ω : Config N d => ω j) (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable).mp h2
  rw [h3, (measurePreserving_eval ρ i).map_eq, (measurePreserving_eval ρ j).map_eq]

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The energy of a product state with nonidentical factors. -/
theorem integral_hamiltonian_pi_gen (hyp : Hyp V W KV KW) {N : ℕ} {ρ : Fin N → Measure (Torus d)}
    [∀ i, IsProbabilityMeasure (ρ i)] :
    ∫ X, hamiltonian V W N X ∂(Measure.pi ρ) =
      ∑ i, potE V (ρ i) + 1 / (2 * (N : ℝ)) *
        ∑ i, ∑ j, (if i = j then 0 else interE W (ρ i) (ρ j)) := by
  set P := Measure.pi ρ with hP
  have hV := hyp.continuous_V
  have hWc : Continuous (Function.uncurry W) := hyp.continuous_W
  have hWij : ∀ i j : Fin N, Continuous fun X : Config N d => W (X i) (X j) := fun i j =>
    hWc.comp ((continuous_apply i).prodMk (continuous_apply j) :
      Continuous fun X : Config N d => (X i, X j))
  have hVi : ∀ i : Fin N, ∫ X, V (X i) ∂P = potE V (ρ i) := fun i =>
    integral_comp_eval (μ := ρ) hV.aestronglyMeasurable
  have hWi : ∀ i j : Fin N, ∫ X, W (X i) (X j) ∂P = if i = j then 0 else interE W (ρ i) (ρ j) := by
    intro i j
    split_ifs with hij
    · subst hij; simp [hyp.diag]
    · have hWprod : ∫ p, Function.uncurry W p ∂((ρ i).prod (ρ j)) = interE W (ρ i) (ρ j) := by
        rw [integral_prod_symm _ (integrable_of_continuous hWc)]
        rfl
      rw [← hWprod, ← map_pair_pi_gen (ρ := ρ) hij, integral_map (by fun_prop)
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


/-- The exact entropy identity for a product state with nonidentical factors. -/
theorem product_entropy_gen (hyp : Hyp V W KV KW) {N : ℕ} {ρ : Fin N → Measure (Torus d)}
    [∀ i, IsProbabilityMeasure (ρ i)] (hk : ∀ i, klDiv (ρ i) (haar d) ≠ ⊤) :
    klDiv (Measure.pi ρ) (gibbs V W N) ≠ ⊤ ∧
      (klDiv (Measure.pi ρ) (gibbs V W N)).toReal =
        ∑ i, (klDiv (ρ i) (haar d)).toReal + (∑ i, potE V (ρ i) + 1 / (2 * (N : ℝ)) *
          ∑ i, ∑ j, (if i = j then 0 else interE W (ρ i) (ρ j))) +
          Real.log (partitionFn V W N) := by
  have hp := klDiv_pi_gen hk
  have hg := klDiv_gibbs hyp hp.1
  refine ⟨hg.1, ?_⟩
  rw [hg.2, hp.2, integral_hamiltonian_pi_gen hyp]

end SharpLSI.FL
