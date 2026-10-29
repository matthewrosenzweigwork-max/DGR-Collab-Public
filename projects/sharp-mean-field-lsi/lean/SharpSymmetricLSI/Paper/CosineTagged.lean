import SharpSymmetricLSI.Paper.Tensorize
import SharpSymmetricLSI.Paper.CosineMarginal
import SharpSymmetricLSI.Paper.CosineHyp

/-!
# R9 (3.9): one-coordinate tests and `r^all_{N,κ} ≤ a` (Phase 2, I1, milestone 5)

For `f(X) = h(x_1)`, `f ∈ H¹(P_{N,κ})`, `Ent_{P_{N,κ}}(f²) = Ent_m(h²)` and
`ℰ_N(f) = ∫ |h'|² dm` (`cosine_tagged_aux`), by tensorization of weak gradients and the uniform
one-particle marginals. With `h_ε = 1 + ε cos 2πx` this gives `r^all_{N,κ} ≤ a`
(`cosine_rAll_le_aux`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Real

namespace SharpLSI

/-- `Ent` is a functional of the law. -/
theorem ent_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (P : Measure α)
    {φ : α → β} (hφ : Measurable φ) {u : β → ℝ} (hu : AEStronglyMeasurable u (P.map φ)) :
    ent P (fun x => u (φ x)) = ent (P.map φ) u := by
  have hint : Integrable (fun x => u (φ x)) P ↔ Integrable u (P.map φ) :=
    (integrable_map_measure hu hφ.aemeasurable).symm
  unfold ent
  by_cases hi : Integrable u (P.map φ)
  · simp only [hint.mpr hi, hi, ↓reduceIte]
    rw [integral_map hφ.aemeasurable hu]
    set c := ∫ x, u (φ x) ∂P
    have hm : AEMeasurable (fun y => ENNReal.ofReal (c * InformationTheory.klFun (u y / c)))
        (P.map φ) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((InformationTheory.measurable_klFun.comp_aemeasurable
          (hu.aemeasurable.div_const c)).const_mul c)
    rw [lintegral_map' hm hφ.aemeasurable]
  · have hi' : ¬ Integrable (fun x => u (φ x)) P := fun h => hi (hint.mp h)
    simp only [hi, hi', ↓reduceIte]

theorem sqNorm_fin_one (v : Fin 1 → ℝ) : sqNorm v = v 0 ^ 2 := by simp [sqNorm]

/-- (3.9). -/
theorem cosine_tagged_aux (κ : ℝ) {N : ℕ} (hN : 1 ≤ N) {h : Torus 1 → ℝ}
    (hh : MemH1 (haar 1) h) :
    MemH1C (gibbs cosV (cosW κ) N) (fun X => h (X ⟨0, hN⟩)) ∧
    ent (gibbs cosV (cosW κ) N) (fun X => h (X ⟨0, hN⟩) ^ 2) =
      ent (haar 1) (fun x => h x ^ 2) ∧
    energy cosV (cosW κ) N (fun X => h (X ⟨0, hN⟩)) =
      ∫⁻ x, ENNReal.ofReal (weakGrad h x 0 ^ 2) ∂haar 1 := by
  have hyp := cosine_hyp_all κ
  set i : Fin N := ⟨0, hN⟩
  have hmarg := cosine_marginal_aux κ i
  have hπ : Measurable fun X : Config N 1 => X i := measurable_pi_apply i
  have hw := isWeakGrad_weakGrad hh.1
  refine ⟨memH1C_comp_eval hyp i hh, ?_, ?_⟩
  · have hu : AEStronglyMeasurable (fun x => h x ^ 2) ((gibbs cosV (cosW κ) N).map fun X => X i) :=
      by rw [hmarg]; exact hh.2.1.aestronglyMeasurable.pow 2
    rw [ent_comp _ hπ hu, hmarg]
  · rw [energy_comp_eval hyp i hh]
    have hm : AEMeasurable (fun x => ENNReal.ofReal (sqNorm (weakGrad h x)))
        ((gibbs cosV (cosW κ) N).map fun X => X i) := by
      rw [hmarg]
      exact ENNReal.measurable_ofReal.comp_aemeasurable hw.aestronglyMeasurable_sqNorm.aemeasurable
    rw [← lintegral_map' hm hπ.aemeasurable, hmarg]
    simp_rw [sqNorm_fin_one]

/-! ### `r^all ≤ a` -/

theorem contDiff_hEps_lift (ε : ℝ) :
    ContDiff ℝ 1 ((fun x : Torus 1 => 1 + ε * gCos x) ∘ liftT) := by
  have : (fun x : Torus 1 => 1 + ε * gCos x) ∘ liftT =
      fun z : Fin 1 → ℝ => 1 + ε * Real.cos (2 * π * z 0) := by
    funext z; simp only [Function.comp]; rw [gCos_coe (liftT z) (z 0) rfl]
  rw [this]; fun_prop

theorem fderiv_hEps_lift (ε : ℝ) (z : Fin 1 → ℝ) :
    fderiv ℝ ((fun x : Torus 1 => 1 + ε * gCos x) ∘ liftT) z (Pi.single 0 1) =
      -(ε * (2 * π) * Real.sin (2 * π * z 0)) := by
  have hlift : (fun x : Torus 1 => 1 + ε * gCos x) ∘ liftT =
      (fun t : ℝ => 1 + ε * Real.cos (2 * π * t)) ∘ (fun z : Fin 1 → ℝ => z 0) := by
    funext z; simp only [Function.comp]; rw [gCos_coe (liftT z) (z 0) rfl]
  have hG : HasDerivAt (fun t : ℝ => 1 + ε * Real.cos (2 * π * t))
      (-(ε * (2 * π) * Real.sin (2 * π * z 0))) (z 0) := by
    have := (((hasDerivAt_id' (z 0)).const_mul (2 * π)).cos.const_mul ε).const_add 1
    convert this using 1; ring
  have hP : HasFDerivAt (fun z : Fin 1 → ℝ => z 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) z := hasFDerivAt_apply 0 z
  rw [hlift, (hG.comp_hasFDerivAt z hP).fderiv]
  simp

theorem memH1_hEps (ε : ℝ) : MemH1 (haar 1) (fun x => 1 + ε * gCos x) := by
  have hc := contDiff_hEps_lift ε
  have hw := isWeakGrad_of_contDiff hc
  have hcont : Continuous fun x : Torus 1 => 1 + ε * gCos x :=
    continuous_const.add (continuous_const.mul continuous_gCos)
  have hww := isWeakGrad_weakGrad (⟨_, hw⟩ : HasWeakGrad fun x : Torus 1 => 1 + ε * gCos x)
  refine ⟨⟨_, hw⟩, ?_, ?_⟩
  · refine MemLp.of_bound hcont.aestronglyMeasurable (1 + |ε|) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    calc |1 + ε * gCos x| ≤ |1| + |ε * gCos x| := abs_add_le _ _
      _ ≤ 1 + |ε| := by
          rw [abs_one, abs_mul]
          linarith [mul_le_of_le_one_right (abs_nonneg ε) (abs_gCos_le x)]
  · refine MemLp.of_bound (Real.continuous_sqrt.comp_aestronglyMeasurable
      hww.aestronglyMeasurable_sqNorm) (|ε| * (2 * π)) ?_
    filter_upwards [weakGrad_ae_eq_of_contDiff hc] with y hy
    rw [hy, sqNorm_fin_one, fderiv_hEps_lift, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_sq_eq_abs, abs_neg, abs_mul, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)

theorem dirichlet_eq_lintegral_fin_one (h : Torus 1 → ℝ) :
    dirichlet (haar 1) h = ∫⁻ x, ENNReal.ofReal (weakGrad h x 0 ^ 2) ∂haar 1 := by
  unfold dirichlet; simp_rw [sqNorm_fin_one]

/-- Section 3.2: `r^all_{N,κ} ≤ a`. -/
theorem cosine_rAll_le_aux {κ : ℝ} {N : ℕ} (hN : 1 ≤ N) :
    rAll cosV (cosW κ) N ≤ ENNReal.ofReal aCos := by
  have hsmall : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), |ε| < 1 / 40 :=
    eventually_nhdsWithin_of_eventually_nhds
      ((continuous_abs.tendsto (0 : ℝ)).eventually (gt_mem_nhds (by norm_num)))
  have hne : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ε ≠ 0 := self_mem_nhdsWithin
  refine ge_of_tendsto cosine_test_quotient_aux ?_
  filter_upwards [hsmall, hne] with ε h1 h2
  obtain ⟨hmem, hent, hen⟩ := cosine_tagged_aux κ hN (memH1_hEps ε)
  beta_reduce at hmem hent hen
  have hE : 0 < entHEps ε := by
    have hb := (abs_le.mp (entHEps_approx (ε := ε) (by linarith))).1
    have he2 : 0 < ε ^ 2 := by positivity
    have h3 : |ε| ^ 3 = |ε| * ε ^ 2 := by rw [pow_succ, sq_abs]; ring
    have h4 : 0 < ε ^ 2 * (1 - 20 * |ε|) := mul_pos he2 (by linarith)
    rw [h3] at hb
    linarith
  have hpos : 0 < ent (gibbs cosV (cosW κ) N) (fun X => (1 + ε * gCos (X ⟨0, hN⟩)) ^ 2) := by
    rw [hent, ent_hEps]; exact ENNReal.ofReal_pos.mpr hE
  calc rAll cosV (cosW κ) N
      ≤ 2 * energy cosV (cosW κ) N (fun X => 1 + ε * gCos (X ⟨0, hN⟩)) /
          ent (gibbs cosV (cosW κ) N) (fun X => (1 + ε * gCos (X ⟨0, hN⟩)) ^ 2) :=
        by
          unfold rAll
          exact iInf₂_le (f := fun (f : Config N 1 → ℝ) _ =>
            2 * energy cosV (cosW κ) N f / ent (gibbs cosV (cosW κ) N) (fun X => f X ^ 2))
            (fun X => 1 + ε * gCos (X ⟨0, hN⟩)) ⟨hmem, hpos⟩
    _ = 2 * dirichlet (haar 1) (fun x => 1 + ε * gCos x) /
          ent (haar 1) (fun x => (1 + ε * gCos x) ^ 2) := by
        rw [hen, hent, dirichlet_eq_lintegral_fin_one]

end SharpLSI
