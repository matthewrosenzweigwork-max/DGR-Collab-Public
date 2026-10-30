import DGPS.Examples.PolynomialChartCriticality
import DGPS.Examples.PolynomialSpeciesRangeRestriction

/-! Identification of the genuine interacting Euler gradient from all retained
chart tests. The Fourier completeness argument uses only its continuous
periodic carrier; no ordinary cos3 Euler formula is transported. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Frontier.STR029
open DGPS.Circle.AngularNormalization
open DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

private theorem holder_zero_of_tests (G : PeriodicHolder_STR02968)
    (ht : ∀ v : PeriodicC2_STR02969, meanCLM_STR02954 (G * e0_STR02955 v) = 0) :
    ∀ t : ℝ, G.val t = 0 := by
  let g := G.val
  have hGc : Continuous g := G.isPerHolder.2.1
  have hGp : Function.Periodic g (2 * Real.pi) := G.isPerHolder.1
  have htest (v : ℝ → ℝ) (hv : IsC2Alpha_STR02901 (1 / 2) v) :
      meanT_STR02901 (fun t => g t * v t) = 0 := by
    have h := ht (PeriodicC2_STR02969.mk v hv)
    change meanT_STR02901 (fun t => g t * v t) = 0 at h
    exact h
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).exists_bound_of_continuousOn
    hGc.continuousOn
  have hbound : ∀ᵐ t ∂circleMeasure_STR02934, ‖g t‖ ≤ C := by
    rw [ae_circle_iff_STR02962]
    exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => hC t ⟨ht.1.le, ht.2⟩)
  have hGL : MemLp g 2 circleMeasure_STR02934 :=
    MemLp.of_bound hGc.aestronglyMeasurable C hbound
  set x : Lp ℝ 2 circleMeasure_STR02934 := MemLp.toLp g hGL with hxdef
  have hx_ae : ⇑x =ᵐ[circleMeasure_STR02934] g := MemLp.coeFn_toLp hGL
  have hx_restrict : ⇑x =ᵐ[volume.restrict (Set.Ioc 0 (2 * Real.pi))] g :=
    (ae_circle_iff_STR02962 (P := fun t => x t = g t)).mp hx_ae
  have hperp : ∀ i, inner ℝ (trigBasisLp_STR02934 i) x = (0 : ℝ) := by
    intro i
    rw [inner_trigBasisLp_STR02934]
    have hcongr : normInt_STR02933 (fun t => x t * trigBasisFun_STR02934 i t) =
        meanT_STR02901 (fun t => g t * trigBasisFun_STR02934 i t) := by
      rw [← normInt_eq_meanT_STR02962]
      unfold normInt_STR02933
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hx_restrict] with t ht
      simp only [ht]
    rw [hcongr]
    rcases i with _ | ⟨b, k⟩
    · simp only [trigBasisFun_STR02934, mul_one]
      have h := htest (fun _ => (1 : ℝ)) (by
        simpa using cosFreq_isC2_STR02962 0)
      simpa only [mul_one] using h
    · cases b
      · have hf : (fun t => g t * trigBasisFun_STR02934 (some (false, k)) t) =
            fun t => Real.sqrt 2 * (g t * Real.cos (((k + 1 : ℕ) : ℝ) * t)) := by
          funext t
          simp only [trigBasisFun_STR02934]
          ring
        have key : meanT_STR02901 (fun t => g t * Real.cos (((k + 1 : ℕ) : ℝ) * t)) = 0 :=
          htest _ (cosFreq_isC2_STR02962 (k + 1))
        rw [hf, meanT_const_mul_STR02962, key, mul_zero]
      · have hf : (fun t => g t * trigBasisFun_STR02934 (some (true, k)) t) =
            fun t => Real.sqrt 2 * (g t * Real.sin (((k + 1 : ℕ) : ℝ) * t)) := by
          funext t
          simp only [trigBasisFun_STR02934]
          ring
        have key : meanT_STR02901 (fun t => g t * Real.sin (((k + 1 : ℕ) : ℝ) * t)) = 0 :=
          htest _ (sinFreq_isC2_STR02962 (k + 1))
        rw [hf, meanT_const_mul_STR02962, key, mul_zero]
  have hmem : x ∈ (Submodule.span ℝ (Set.range trigBasisLp_STR02934))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hperp i
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
    | smul a y _ hy => rw [real_inner_smul_left, hy, mul_zero]
  rw [orthogonal_trigBasisLp_eq_bot_STR02934, Submodule.mem_bot] at hmem
  have hG0 : g =ᵐ[circleMeasure_STR02934] 0 := by
    have h1 := hx_ae
    rw [hmem] at h1
    exact h1.symm.trans (Lp.coeFn_zero ℝ 2 circleMeasure_STR02934)
  have hae0 : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))), g t = 0 :=
    (ae_circle_iff_STR02962 (P := fun t => g t = 0)).mp hG0
  have hae1 : ∀ᵐ t, t ∈ Set.Ioc 0 (2 * Real.pi) → g t = 0 :=
    (ae_restrict_iff' measurableSet_Ioc).mp hae0
  have hzero : ∀ t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi), g t = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t0, ht0, hGt0⟩ := hcon
    have hUopen : IsOpen (g ⁻¹' {0}ᶜ ∩ Set.Ioo 0 (2 * Real.pi)) :=
      (isClosed_singleton.isOpen_compl.preimage hGc).inter isOpen_Ioo
    have hUne : (g ⁻¹' {0}ᶜ ∩ Set.Ioo 0 (2 * Real.pi)).Nonempty := ⟨t0, hGt0, ht0⟩
    have hpos : 0 < volume (g ⁻¹' {0}ᶜ ∩ Set.Ioo 0 (2 * Real.pi)) :=
      hUopen.measure_pos volume hUne
    have hsub : g ⁻¹' {0}ᶜ ∩ Set.Ioo 0 (2 * Real.pi) ⊆
        {t | ¬ (t ∈ Set.Ioc 0 (2 * Real.pi) → g t = 0)} := by
      intro t ht
      exact fun hh => (Set.mem_compl_singleton_iff.mp ht.1) (hh ⟨ht.2.1, ht.2.2.le⟩)
    exact absurd (measure_mono_null hsub (ae_iff.mp hae1)) hpos.ne'
  have hIcc : Set.Icc (0 : ℝ) (2 * Real.pi) ⊆ {t | g t = 0} := by
    rw [← closure_Ioo (by linarith [Real.pi_pos] : (0 : ℝ) < 2 * Real.pi).ne]
    exact closure_minimal hzero (isClosed_eq hGc continuous_const)
  intro t
  obtain ⟨y, hy, hGy⟩ := hGp.exists_mem_Ico₀ Real.two_pi_pos t
  change g t = 0
  rw [hGy]
  exact hIcc ⟨hy.1, hy.2.le⟩

/-- The true full interacting Euler gradient of the actual minimizer chart
vanishes. The original global variational problem supplies all chart tests. -/
theorem polynomial_scalarMinimizer_chart_gradient_zero (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (ρ : AbsoluteDensity 1)
    (hG : 0 < scalarGap (canonical_elementary_polynomial_model h) ρ)
    (hmin : scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
      scalarRate (canonical_elementary_polynomial_model h) b)
    (u : PeriodicC2_STR02969)
    (hu : ρ.density =ᵐ[haar 1] (polynomialChartAbsolute h u).density) :
    polynomialEulerGradient h (scalarRate (canonical_elementary_polynomial_model h) b).toReal u = 0 := by
  have hD := polynomial_scalarMinimizer_chart_fderiv_zero h b ρ hG hmin u hu
  have ht (v : PeriodicC2_STR02969) : meanCLM_STR02954
      (polynomialEulerGradient h (scalarRate (canonical_elementary_polynomial_model h) b).toReal u *
        e0_STR02955 v) = 0 := by
    rw [← polynomialChartDeficit_fderiv_strong, hD, ContinuousLinearMap.zero_apply]
  apply ext_STR02954
  exact funext fun t => holder_zero_of_tests _ ht t

/-- Every actual original-domain minimizer sequence has the same vanishing
mean-zero chart representatives satisfying the true independent-reference
Euler equation after restriction to the retained physical equilibrium. -/
theorem polynomial_scalarMinimizer_projected_chart_capture (h : ℕ → ℝ)
    (hh : Tendsto h atTop (𝓝 0))
    (b : ∀ n, AbsoluteDrift (canonical_elementary_polynomial_model (h n)))
    (ρ : ℕ → AbsoluteDensity 1)
    (hG : ∀ n, 0 < scalarGap (canonical_elementary_polynomial_model (h n)) (ρ n))
    (hmin : ∀ n, scalarQuotient (canonical_elementary_polynomial_model (h n)) (b n) (ρ n) =
      scalarRate (canonical_elementary_polynomial_model (h n)) (b n)) :
    ∃ φ : ℕ → ℕ, ∃ u : ℕ → PeriodicC2_STR02969, StrictMono φ ∧
      (∀ n, meanT_STR02901 (u n).val = 0) ∧
      (∀ n, (ρ (φ n)).density =ᵐ[haar 1] (polynomialChartAbsolute (h (φ n)) (u n)).density) ∧
      Tendsto (fun n => ‖u n‖) atTop (𝓝 0) ∧
      (∀ n, PY_STR02955 (polynomialRangeEuler (h (φ n), root_EX054 (h (φ n)))
        (scalarRate (canonical_elementary_polynomial_model (h (φ n))) (b (φ n))).toReal (u n)) = 0) := by
  obtain ⟨φ, u, hφ, hm, hd, hn⟩ :=
    polynomial_scalarMinimizer_centered_chart_capture h hh b ρ hG hmin
  refine ⟨φ, u, hφ, hm, hd, hn, fun n => ?_⟩
  rw [polynomialRangeEuler_actual,
    polynomial_scalarMinimizer_chart_gradient_zero (h (φ n)) (b (φ n)) (ρ (φ n))
      (hG (φ n)) (hmin (φ n)) (u n) (hd n), map_zero]

end DGPS.Examples.PolynomialSpecies
