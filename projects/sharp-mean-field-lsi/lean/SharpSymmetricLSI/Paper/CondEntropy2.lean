import SharpSymmetricLSI.Paper.CondEntropy

/-!
# Change of product reference for relative entropy (Phase 3, lane D; R18)

If all marginals of `P` on `(𝕋^d)^k` equal `ρ`, then
`H(P | μ^{⊗k}) = H(P | ρ^{⊗k}) + k H(ρ | μ)` (finite case).
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

theorem pi_withDensity_ofReal' {ι : Type*} [Fintype ι] {μ : Measure (Torus d)}
    [IsProbabilityMeasure μ] {f : Torus d → ℝ} (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f μ) :
    Measure.pi (fun _ : ι => μ.withDensity (fun x => ENNReal.ofReal (f x))) =
      (Measure.pi fun _ : ι => μ).withDensity (fun X => ENNReal.ofReal (∏ i, f (X i))) := by
  haveI : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) :=
    isFiniteMeasure_withDensity_ofReal hfi.2
  refine Measure.pi_eq fun s hs => ?_
  have hg : ∀ i, Integrable ((s i).indicator f) μ := fun i => hfi.indicator (hs i)
  have hpt : ∀ X : ι → Torus d, (Set.univ.pi s).indicator
      (fun X => ENNReal.ofReal (∏ i, f (X i))) X = ENNReal.ofReal (∏ i, (s i).indicator f (X i)) :=
    fun X => by
    by_cases hX : X ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hX]
      congr 1
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hX i (Set.mem_univ i)) f).symm
    · rw [Set.indicator_of_notMem hX]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hX
      obtain ⟨i, hi⟩ := hX
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi f), ENNReal.ofReal_zero]
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [hpt]
  have hint : Integrable (fun X : ι → Torus d => ∏ i, (s i).indicator f (X i))
      (Measure.pi fun _ : ι => μ) :=
    Integrable.fintype_prod (f := fun _ => fun x => (s _).indicator f x) hg
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun X =>
      Finset.prod_nonneg fun i _ => Set.indicator_nonneg (fun x _ => hf0 x) _),
    integral_fintype_prod_eq_prod (f := fun i => (s i).indicator f),
    ENNReal.ofReal_prod_of_nonneg (fun i _ =>
      integral_nonneg (Set.indicator_nonneg (fun x _ => hf0 x)))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), integral_indicator (hs i),
    ofReal_integral_eq_lintegral_ofReal hfi.integrableOn (Eventually.of_forall fun x => hf0 x)]

/-- **Change of product reference.** -/
theorem klDiv_pi_ref_change {k : ℕ} (μ ρ : Measure (Torus d)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ρ] (P : Measure (Fin k → Torus d)) [IsProbabilityMeasure P]
    (hmarg : ∀ a, P.map (fun x => x a) = ρ)
    (hP : klDiv P (Measure.pi fun _ => μ) ≠ ⊤) (hρ : klDiv ρ μ ≠ ⊤) :
    klDiv P (Measure.pi fun _ => μ) = klDiv P (Measure.pi fun _ => ρ) + k * klDiv ρ μ := by
  obtain ⟨hρac, hρint⟩ := klDiv_ne_top_iff.mp hρ
  obtain ⟨hPac, hPint⟩ := klDiv_ne_top_iff.mp hP
  set f : Torus d → ℝ := fun x => (ρ.rnDeriv μ x).toReal with hf
  have hfm : Measurable f := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hf0 : ∀ x, 0 ≤ f x := fun x => ENNReal.toReal_nonneg
  have hfi : Integrable f μ := Measure.integrable_toReal_rnDeriv
  have hρeq : μ.withDensity (fun x => ENNReal.ofReal (f x)) = ρ := by
    conv_rhs => rw [← Measure.withDensity_rnDeriv_eq ρ μ hρac]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top ρ μ] with x hx
    simp only [hf, ENNReal.ofReal_toReal hx.ne]
  set F : (Fin k → Torus d) → ℝ≥0∞ := fun X => ENNReal.ofReal (∏ a, f (X a)) with hFdef
  have hFm : Measurable F := ENNReal.measurable_ofReal.comp
    (Finset.measurable_prod _ fun a _ => hfm.comp (measurable_pi_apply a))
  have hpi : Measure.pi (fun _ : Fin k => ρ) = (Measure.pi fun _ : Fin k => μ).withDensity F := by
    have := pi_withDensity_ofReal' (ι := Fin k) hfm hf0 hfi
    rwa [hρeq] at this
  have hrnF : (Measure.pi fun _ : Fin k => ρ).rnDeriv (Measure.pi fun _ : Fin k => μ)
      =ᵐ[Measure.pi fun _ : Fin k => μ] F := by
    rw [hpi]; exact Measure.rnDeriv_withDensity _ hFm
  have hpos1 : ∀ᵐ x ∂ρ, 0 < f x := by
    filter_upwards [Measure.rnDeriv_pos hρac, hρac.ae_le (Measure.rnDeriv_lt_top ρ μ)] with x h1 h2
    exact ENNReal.toReal_pos h1.ne' h2.ne
  have hposP : ∀ᵐ X ∂P, ∀ a, 0 < f (X a) := by
    rw [ae_all_iff]
    intro a
    exact ae_of_ae_map (measurable_pi_apply a).aemeasurable (by rw [hmarg a]; exact hpos1)
  -- `P ≪ ρ^{⊗k}`
  have hPacρ : P ≪ Measure.pi fun _ : Fin k => ρ := by
    refine Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_
    rw [hpi, withDensity_apply _ hA] at hA0
    have h1 : ∀ᵐ X ∂(Measure.pi fun _ : Fin k => μ), X ∈ A → F X = 0 := by
      have := (lintegral_eq_zero_iff' hFm.aemeasurable).mp hA0
      exact (ae_restrict_iff' hA).mp this
    have h2 := hPac.ae_le h1
    refine measure_eq_zero_iff_ae_notMem.mpr ?_
    filter_upwards [h2, hposP] with X hX hpos hXA
    have := hX hXA
    simp only [hFdef, ENNReal.ofReal_eq_zero] at this
    have : 0 < ∏ a, f (X a) := Finset.prod_pos fun a _ => hpos a
    linarith
  -- the log-likelihood ratio identity
  set S : (Fin k → Torus d) → ℝ := fun X => ∑ a, Real.log (f (X a)) with hS
  have hllr : llr P (Measure.pi fun _ => μ) =ᵐ[P] fun X => llr P (Measure.pi fun _ => ρ) X + S X := by
    filter_upwards [hPac.ae_le (Measure.rnDeriv_mul_rnDeriv hPacρ), hPac.ae_le hrnF,
      Measure.rnDeriv_pos hPacρ, hPacρ.ae_le (Measure.rnDeriv_lt_top P _), hposP] with X h1 h2 h3 h4 h5
    simp only [llr, hS]
    rw [← h1, Pi.mul_apply, h2, ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (Finset.prod_nonneg fun a _ => hf0 _), Real.log_mul (ENNReal.toReal_pos h3.ne' h4.ne).ne'
      (Finset.prod_pos fun a _ => h5 a).ne', Real.log_prod (fun a _ => (h5 a).ne')]
  have hSi : ∀ a, Integrable (fun X : Fin k → Torus d => Real.log (f (X a))) P := fun a => by
    have h := (integrable_map_measure (μ := P) (f := fun x : Fin k → Torus d => x a)
      (g := fun x => Real.log (f x)) (by rw [hmarg a]; exact hρint.aestronglyMeasurable)
      (measurable_pi_apply a).aemeasurable).mp (by rw [hmarg a]; exact hρint)
    exact h
  have hSint : Integrable S P := integrable_finsetSum _ fun a _ => hSi a
  have hint2 : Integrable (llr P (Measure.pi fun _ => ρ)) P := by
    have : llr P (Measure.pi fun _ => ρ) =ᵐ[P] fun X => llr P (Measure.pi fun _ => μ) X - S X := by
      filter_upwards [hllr] with X hX; rw [hX]; ring
    exact (hPint.sub hSint).congr this.symm
  have hfin2 : klDiv P (Measure.pi fun _ => ρ) ≠ ⊤ := klDiv_ne_top hPacρ hint2
  have hSval : ∫ X, S X ∂P = k * (klDiv ρ μ).toReal := by
    rw [integral_finsetSum _ fun a _ => hSi a]
    have : ∀ a, ∫ X, Real.log (f (X a)) ∂P = (klDiv ρ μ).toReal := fun a => by
      have h := integral_map (μ := P) (φ := fun x : Fin k → Torus d => x a)
        (f := fun x => Real.log (f x)) (measurable_pi_apply a).aemeasurable
        (by rw [hmarg a]; exact hρint.aestronglyMeasurable)
      rw [← h, hmarg a, toReal_klDiv_of_measure_eq hρac (by simp)]
      rfl
    simp_rw [this]
    simp
  have hreal : (klDiv P (Measure.pi fun _ => μ)).toReal =
      (klDiv P (Measure.pi fun _ => ρ)).toReal + k * (klDiv ρ μ).toReal := by
    rw [toReal_klDiv_of_measure_eq hPac (by simp), toReal_klDiv_of_measure_eq hPacρ (by simp),
      integral_congr_ae hllr, integral_add hint2 hSint, hSval]
  rw [← ENNReal.ofReal_toReal hP, hreal, ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
    ENNReal.ofReal_toReal hfin2, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_toReal hρ]

end SharpLSI
