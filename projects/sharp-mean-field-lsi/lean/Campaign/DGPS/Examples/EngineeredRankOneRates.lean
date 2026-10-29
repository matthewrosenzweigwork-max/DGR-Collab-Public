import DGPS.Examples.EngineeredUniqueness
import DGPS.Variational.BinaryDilution
import DGPS.Examples.PositiveH1.SmoothApproximation
import DGPS.FiniteN.Tools.Linearization
import DGPS.Structural.SmallRateCircle
import DGPS.Structural.HarmonicRateComparison
import DGPS.Variational.PositiveRankOne

open MeasureTheory
open scoped ENNReal NNReal

namespace DGPS.Examples.EngineeredRankOneRates

open DGPS.PositiveRankOne DGPS.Structural

theorem integral_ref (M : RankOneModel) (f : Torus 1 → ℝ) :
    ∫ x, f x ∂M.ref.measure = ∫ x, M.q x * f x ∂haar 1 := by
  rw [BoundedPositiveReference.measure, integral_withDensity_eq_integral_toReal_smul₀
    M.ref.measurable_ofReal_density.aemeasurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (ENNReal.ofReal (M.q x)).toReal • f x = _
  rw [ENNReal.toReal_ofReal (M.q_pos x).le, smul_eq_mul]

theorem lsRate_le_of_smooth_test (M : RankOneModel) {u : Torus 1 → ℝ} (hu : IsSmoothPeriodic u)
    (hmean : ∫ x, u x ∂M.ref.measure = 0)
    (hV : 0 < ∫ x, u x ^ 2 ∂M.ref.measure) :
    ordinaryLSRate M.ref ≤ ENNReal.ofReal ((∫ x, coordPartial 0 u x ^ 2 ∂M.ref.measure) /
      ∫ x, u x ^ 2 ∂M.ref.measure) := by
  set P := M.ref.measure with hP
  set V := ∫ x, u x ^ 2 ∂P with hVdef
  set E0 := ∫ x, coordPartial 0 u x ^ 2 ∂P with hE0
  have hE0nn : 0 ≤ E0 := integral_nonneg fun x => sq_nonneg _
  obtain ⟨Mb, hMb⟩ := isCompact_univ.exists_bound_of_continuousOn hu.continuous_torus.continuousOn
  have hMb' : ∀ x, |u x| ≤ Mb := fun x => by simpa using hMb x (Set.mem_univ x)
  have hMb0 : 0 ≤ Mb := (abs_nonneg _).trans (hMb' 0)
  refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
  by_cases hat : a = ⊤
  · rw [hat]; exact le_top
  rw [← ENNReal.ofReal_toReal hat] at ha ⊢
  set t := a.toReal with ht
  have hct : E0 / V < t := (ENNReal.ofReal_lt_ofReal_iff'.1 ha).1
  have hE0t : E0 < t * V := by rwa [div_lt_iff₀ hV] at hct
  have ht0 : 0 < t := by
    by_contra h
    have h' := not_lt.1 h
    nlinarith [mul_nonneg (le_of_lt hV) (neg_nonneg.2 h')]
  set k := Mb ^ 3 with hk
  have hk0 : 0 ≤ k := by positivity
  set δ := t * V - E0 with hδ
  have hδ0 : 0 < δ := by linarith
  set ε := min (1 / (2 * (Mb + 1))) (min (V / (10 * (k + 1))) (δ / (5 * (k + 1) * t + 1))) with hε
  have hε0 : 0 < ε := by
    refine lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hε1 : ε ≤ 1 / (2 * (Mb + 1)) := min_le_left _ _
  have hε2 : ε ≤ V / (10 * (k + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hε3 : ε ≤ δ / (5 * (k + 1) * t + 1) := (min_le_right _ _).trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at hε1 hε2 hε3
  have hεM : |ε| * Mb ≤ 1 / 2 := by
    rw [abs_of_pos hε0]; nlinarith
  obtain ⟨hne, hA⟩ := DGPS.FiniteN.linearization_entropy_expansion (P := P) (F := u)
    hu.continuous_torus.aestronglyMeasurable hMb' hmean hεM
  set f : Torus 1 → ℝ := fun x => 1 + ε * u x with hf
  have hgrad : IsWeakGradient f (fun x => ε • smoothGrad u x) :=
    (hu.isWeakGradient.affine ε 1).congr_ae
      (Filter.Eventually.of_forall fun x => by simp only [hf]; ring)
      (Filter.Eventually.of_forall fun _ => rfl)
  have hmem : f ∈ WeightedH1 M.ref := (mem_weightedH1_iff _).2 ⟨_, hgrad⟩
  have hEnt : homogeneousEntropy P (fun x => f x ^ 2) =
      homogeneousEntropy P (fun x => (1 + ε * u x) ^ 2) := rfl
  rw [abs_of_pos hε0] at hA
  have hA1 := (abs_le.1 hA).1
  have h5 : 5 * k * ε * t ≤ δ := by nlinarith [mul_pos hε0 ht0]
  have h6 : 10 * k * ε ≤ V := by nlinarith
  set W := V - 5 * k * ε with hW
  have hW0 : V / 2 ≤ W := by rw [hW]; linarith
  have hWt : E0 ≤ t * W := by
    have : t * (5 * k * ε) ≤ δ := by nlinarith
    rw [hW]; nlinarith
  set A := (homogeneousEntropy P (fun x => (1 + ε * u x) ^ 2)).toReal with hAdef
  have hAW : 2 * ε ^ 2 * W ≤ A := by rw [hW]; nlinarith
  have hApos : 0 < A := lt_of_lt_of_le (mul_pos (by positivity) (lt_of_lt_of_le (by positivity) hW0)) hAW
  have hpos : 0 < homogeneousEntropy P (fun x => f x ^ 2) := by
    rw [hEnt]; exact pos_iff_ne_zero.2 (ENNReal.toReal_pos_iff.1 hApos).1.ne'
  have hL : ∫⁻ x, ‖weightedGradient M.ref f hmem x‖ₑ ^ 2 ∂P = ENNReal.ofReal (ε ^ 2 * E0) := by
    have hae : weightedGradient M.ref f hmem =ᵐ[haar 1] fun x => ε • smoothGrad u x :=
      weightedGradient_ae_eq _ hmem hgrad
    have hae' := M.ref.measure_ac_haar.ae_eq hae
    rw [lintegral_congr_ae (by filter_upwards [hae'] with x hx; rw [hx])]
    have hint : Integrable (fun x => ε ^ 2 * coordPartial 0 u x ^ 2) P :=
      ((hu.continuous_coordPartial 0).pow 2).const_mul _ |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have : ∀ x, ‖ε • smoothGrad u x‖ₑ ^ 2 = ENNReal.ofReal (ε ^ 2 * coordPartial 0 u x ^ 2) := by
      intro x
      rw [RankOneModel.enorm_sq_tangent]
      congr 1
      simp [mul_pow]
    simp_rw [this]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => by positivity), integral_const_mul]
  refine (iInf_le _ ⟨f, hmem, hpos⟩).trans ?_
  show 2 * (∫⁻ x, ‖weightedGradient M.ref f hmem x‖ₑ ^ 2 ∂P) / homogeneousEntropy P (fun x => f x ^ 2) ≤ _
  rw [hL, hEnt, ← ENNReal.ofReal_toReal hne]
  have e2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [e2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_div_of_pos hApos]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ hApos]
  nlinarith [mul_le_mul_of_nonneg_left hAW ht0.le, mul_nonneg (sq_nonneg ε) (sub_nonneg.2 hWt)]

theorem dlogq_eq' (M : RankOneModel) (x : Torus 1) :
    M.dlogq x = (M.q x)⁻¹ * coordPartial 0 M.q x := by
  unfold RankOneModel.dlogq
  exact RelativeFisher.coordPartial_comp M.q_smooth (φ := Real.log) (D := fun t => t⁻¹)
    (fun t ht => Real.hasDerivAt_log ht.ne') M.q_pos 0 x

theorem energy_eq_of_eigen (M : RankOneModel) (c : ℝ) (hA : ∀ x, M.Aq x = c * M.φ x) :
    ∫ x, coordPartial 0 M.φ x ^ 2 ∂M.ref.measure = c * ∫ x, M.φ x ^ 2 ∂M.ref.measure := by
  rw [integral_ref, integral_ref, ← integral_const_mul]
  have hv : IsSmoothPeriodic (fun x => M.q x * M.dφ x) := M.q_smooth.mul M.dφ_smooth
  have h := integral_mul_coordPartial_of_smooth hv M.φ_smooth 0
  have e1 : ∀ x, coordPartial 0 (fun x => M.q x * M.dφ x) x * M.φ x = -(M.q x * (c * M.φ x ^ 2)) := by
    intro x
    rw [coordPartial_mul M.q_smooth M.dφ_smooth 0 x]
    have h1 := hA x
    have h2 : coordPartial 0 M.q x = M.q x * M.dlogq x := by
      rw [dlogq_eq']; field_simp [(M.q_pos x).ne']
    have h3 : M.Aq x = -coordPartial 0 M.dφ x - M.dlogq x * M.dφ x := rfl
    rw [h2]
    have h4 : coordPartial 0 M.dφ x = -(c * M.φ x) - M.dlogq x * M.dφ x := by linarith
    rw [h4]; ring
  simp_rw [e1] at h
  rw [integral_neg, neg_neg] at h
  have h' : ∫ x, M.q x * coordPartial 0 M.φ x ^ 2 ∂haar 1 =
      ∫ x, M.q x * M.dφ x * coordPartial 0 M.φ x ∂haar 1 :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [RankOneModel.dφ]; ring)
  rw [h', h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

theorem lsRate_le_of_eigen (M : RankOneModel) (c : ℝ) (hA : ∀ x, M.Aq x = c * M.φ x)
    (hV : 0 < ∫ x, M.φ x ^ 2 ∂M.ref.measure) :
    ordinaryLSRate M.ref ≤ ENNReal.ofReal c := by
  have hmean : ∫ x, M.φ x ∂M.ref.measure = 0 := by
    rw [integral_ref]
    have := M.φ_centered
    rw [← this]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have h := lsRate_le_of_smooth_test M M.φ_smooth hmean hV
  rw [energy_eq_of_eigen M c hA, mul_div_assoc, div_self hV.ne', mul_one] at h
  exact h

theorem integral_phi_sq_pos (M : RankOneModel) {x0 : Torus 1} (h0 : M.φ x0 ≠ 0) :
    0 < ∫ x, M.φ x ^ 2 ∂M.ref.measure := by
  rw [integral_ref]
  have : (haar 1).IsAddHaarMeasure := by
    rw [DGPS.haar_eq_pi_haarAddCircle]; infer_instance
  exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x0)
    (M.q_cont.mul (M.φ_cont.pow 2)) (HasCompactSupport.of_compactSpace _)
    (fun x => mul_nonneg (M.q_pos x).le (sq_nonneg _))
    (mul_pos (M.q_pos x0) ((by positivity))).ne'

theorem ordinaryLSRate_le_speciesRate (M : RankOneModel) (b : AbsoluteDrift M.data) (c : ℝ)
    (hc : 0 ≤ c) (hA : ∀ x, M.Aq x = c * M.φ x)
    (hr : ordinaryLSRate M.ref ≤ ENNReal.ofReal c) :
    ordinaryLSRate M.ref ≤ speciesRate M.data b := by
  unfold speciesRate
  refine le_iInf fun F => ?_
  obtain ⟨hG, hIne, hDne, hD⟩ := positive_rank_one_gap_and_family_dissipation M b F.1
  set a := ordinaryLSRate M.ref with ha
  have hatop : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hr
  have ha' : a.toReal ≤ c := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hr
    rwa [ENNReal.toReal_ofReal hc] at this
  have ha0 : 0 ≤ a.toReal := ENNReal.toReal_nonneg
  set m := ∫ x, M.φ x ∂(densityMeasure (barycenter F.1) : Measure (Torus 1)) with hm
  have hH : ∀ s, 2 * a.toReal * (relativeEntropy (densityMeasure (F.1.density s) : Measure (Torus 1))
      M.ref.measure).toReal ≤
      (ordinaryRelativeFisher (densityMeasure (F.1.density s) : Measure (Torus 1)) M.ref).toReal := by
    intro s
    have hne := (relativeEntropy_reference M.ref (F.1.density s)).1
    have hac : (densityMeasure (F.1.density s) : Measure (Torus 1)) ≪ M.ref.measure := by
      by_contra hn
      exact hne (relativeEntropy_of_not_absolutelyContinuous hn)
    have h := two_mul_lsRate_mul_relativeEntropy_le M.ref _ hac
    have h2 := ENNReal.toReal_mono (hIne s) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at h2
    simpa using h2
  have hAint : ∫ x, M.Aq x ∂(densityMeasure (barycenter F.1) : Measure (Torus 1)) = c * m := by
    rw [hm, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hA)
  have hS : 0 ≤ ∫ x, M.dφ x ^ 2 ∂(densityMeasure (barycenter F.1) : Measure (Torus 1)) :=
    integral_nonneg fun x => sq_nonneg _
  have hη := M.η_nonneg
  have hGpos : 0 < (speciesGap M.data F.1 : ℝ) := by exact_mod_cast F.2
  have key : a.toReal * (2 * (speciesGap M.data F.1 : ℝ)) ≤ (speciesDissipation M.data b F.1).toReal := by
    rw [hD, hAint, hG]
    have hsum : 2 * a.toReal * ∑ s, F.1.weight s * (relativeEntropy
        (densityMeasure (F.1.density s) : Measure (Torus 1)) M.ref.measure).toReal ≤
        ∑ s, F.1.weight s * (ordinaryRelativeFisher
        (densityMeasure (F.1.density s) : Measure (Torus 1)) M.ref).toReal := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      have := mul_le_mul_of_nonneg_left (hH s) (F.1.weight_nonneg s)
      linarith
    have h1 : M.η * (a.toReal * m ^ 2) ≤ M.η * (c * m ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha' (sq_nonneg _)) hη
    have h3 : 0 ≤ M.η ^ 2 * m ^ 2 * ∫ x, M.dφ x ^ 2 ∂(densityMeasure (barycenter F.1) : Measure (Torus 1)) :=
      mul_nonneg (by positivity) hS
    nlinarith [mul_nonneg hη (mul_nonneg hc (sq_nonneg m))]
  have hq : speciesQuotient M.data b F.1 = speciesDissipation M.data b F.1 / (2 * (speciesGap M.data F.1 : ℝ≥0∞)) := rfl
  rw [hq]
  have h2G : (2 * (speciesGap M.data F.1 : ℝ≥0∞)) ≠ 0 := by
    have : (0 : ℝ≥0∞) < speciesGap M.data F.1 := by exact_mod_cast F.2
    simp [this.ne']
  have h2Gt : (2 * (speciesGap M.data F.1 : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
  rw [ENNReal.le_div_iff_mul_le (Or.inl h2G) (Or.inl h2Gt)]
  rw [← ENNReal.ofReal_toReal hatop, ← ENNReal.ofReal_toReal hDne]
  have e2G : 2 * (speciesGap M.data F.1 : ℝ≥0∞) = ENNReal.ofReal (2 * (speciesGap M.data F.1 : ℝ)) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_coe_nnreal]
    simp
  rw [e2G, ← ENNReal.ofReal_mul ha0]
  exact ENNReal.ofReal_le_ofReal key

open Filter Topology

/-- Fisher information depends on the reference only through its measure. -/
theorem fisher_congr_ref {ν : Measure (Torus 1)} {P₁ P₂ : BoundedPositiveReference 1}
    (hP : P₁.measure = P₂.measure) :
    ordinaryRelativeFisher ν P₁ = ordinaryRelativeFisher ν P₂ := by
  have hsq : relativeSqrt ν P₁ = relativeSqrt ν P₂ := by
    funext x; simp only [relativeSqrt, hP]
  by_cases hν : ν ≪ P₁.measure
  · by_cases hm : relativeSqrt ν P₁ ∈ WeightedH1 P₁
    · obtain ⟨g, hg⟩ := (mem_weightedH1_iff P₁).1 hm
      rw [ordinaryRelativeFisher_eq hν hg, ordinaryRelativeFisher_eq (hP ▸ hν) (hsq ▸ hg), hP]
    · rw [ordinaryRelativeFisher_of_not_mem hm, ordinaryRelativeFisher_of_not_mem]
      rw [hsq] at hm
      exact fun h => hm ((mem_weightedH1_iff P₁).2 ((mem_weightedH1_iff P₂).1 h))
  · rw [ordinaryRelativeFisher_of_not_absolutelyContinuous hν,
      ordinaryRelativeFisher_of_not_absolutelyContinuous (hP ▸ hν)]

theorem fisher_self (P : BoundedPositiveReference 1) :
    ordinaryRelativeFisher P.measure P = 0 := by
  have hac : P.measure ≪ P.measure := Measure.AbsolutelyContinuous.rfl
  have h1 : relativeSqrt P.measure P =ᵐ[haar 1] fun _ => (1 : ℝ) := by
    refine P.haar_ac_measure.ae_le ?_
    filter_upwards [Measure.rnDeriv_self P.measure] with x hx
    simp [relativeSqrt, hx]
  have hg : IsWeakGradient (relativeSqrt P.measure P) (fun _ => (0 : Tangent 1)) :=
    (isWeakGradient_const (d := 1) 1).congr_ae h1.symm Filter.EventuallyEq.rfl
  rw [ordinaryRelativeFisher_eq hac hg]
  simp


theorem equilibrium_gap_diss (M : RankOneModel) (b : AbsoluteDrift M.data) :
    scalarGap M.data M.absQ = 0 ∧ scalarDissipation M.data b M.absQ = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := positive_rank_one_scalar_case M b M.absQ
  have hm : ∫ x, M.φ x ∂(densityMeasure M.absQ : Measure (Torus 1)) = 0 := by
    rw [M.densityMeasure_absQ, integral_ref]
    simpa [mul_comm] using M.φ_centered
  have hH : relativeEntropy (densityMeasure M.absQ : Measure (Torus 1)) M.ref.measure = 0 := by
    rw [M.densityMeasure_absQ]; exact relativeEntropy_self _
  have hI : ordinaryRelativeFisher (densityMeasure M.absQ : Measure (Torus 1)) M.ref = 0 := by
    rw [M.densityMeasure_absQ]; exact fisher_self _
  constructor
  · rw [← speciesGap_single]
    apply NNReal.eq
    rw [h1, hm, hH]
    simp
  · rw [← speciesDissipation_single]
    have : (speciesDissipation M.data b (SpeciesFamily.single M.absQ)).toReal = 0 := by
      rw [h4, hI, hm]; simp
    exact ((ENNReal.toReal_eq_zero_iff _).1 this).resolve_right h3

/-- The reference density of a rank-one model as a smooth positive probability. -/
noncomputable def sppOfModel (M : RankOneModel) : SmoothPositiveProbability 1 :=
  ⟨M.q, M.q_smooth, M.q_pos, M.q_mass⟩

theorem sppOfModel_abs (M : RankOneModel) : (sppOfModel M).toAbsoluteDensity = M.absQ :=
  rfl

theorem sppOfModel_ref (M : RankOneModel) :
    (sppOfModel M).reference.measure = M.ref.measure := by
  rw [SmoothPositiveProbability.reference_measure, sppOfModel_abs, M.densityMeasure_absQ]

/-- A smooth positive absolute density as a smooth positive probability. -/
noncomputable def sppOfAbs (σ : AbsoluteDensity 1) (hs : IsSmoothPeriodic σ.sqrt)
    (hp : ∀ x, 0 < σ.sqrt x) : SmoothPositiveProbability 1 where
  p := σ.density
  smooth := by
    unfold IsSmoothPeriodic at hs ⊢
    exact hs.pow 2
  pos := fun x => pow_pos (hp x) 2
  mass := σ.mass_one

theorem sppOfAbs_abs (σ : AbsoluteDensity 1) (hs : IsSmoothPeriodic σ.sqrt)
    (hp : ∀ x, 0 < σ.sqrt x) : (sppOfAbs σ hs hp).toAbsoluteDensity = σ := by
  refine SmoothPositiveProbability.absoluteDensity_ext ?_
  funext x
  show Real.sqrt (σ.sqrt x ^ 2) = σ.sqrt x
  exact Real.sqrt_sq (hp x).le

theorem sppOfAbs_meas (σ : AbsoluteDensity 1) (hs : IsSmoothPeriodic σ.sqrt)
    (hp : ∀ x, 0 < σ.sqrt x) :
    (sppOfAbs σ hs hp).meas = (densityMeasure σ : Measure (Torus 1)) := by
  unfold SmoothPositiveProbability.meas
  rw [sppOfAbs_abs]

theorem speciesRate_le_of_smooth (M : RankOneModel) (b : AbsoluteDrift M.data)
    (σ : AbsoluteDensity 1) (hs : IsSmoothPeriodic σ.sqrt) (hp : ∀ x, 0 < σ.sqrt x)
    (hH : 0 < relativeEntropy (densityMeasure σ : Measure (Torus 1)) M.ref.measure) :
    speciesRate M.data b ≤ ordinaryRelativeFisher (densityMeasure σ : Measure (Torus 1)) M.ref /
      (2 * relativeEntropy (densityMeasure σ : Measure (Torus 1)) M.ref.measure) := by
  obtain ⟨hG, hD⟩ := equilibrium_gap_diss M b
  have h := (exact_barycenter_binary_dilution M.data b (sppOfModel M) (sppOfAbs σ hs hp)
    (by rw [sppOfModel_abs]; exact hG) (by rw [sppOfModel_abs]; exact hD)
    (by rw [sppOfAbs_meas, sppOfModel_ref]; exact hH)).2
  rw [sppOfAbs_meas, sppOfModel_ref] at h
  rwa [fisher_congr_ref (sppOfModel_ref M)] at h


open DGPS.Examples.PositiveH1.SmoothApproximation

theorem eLpNorm_top_cont_ne {c : Torus 1 → ℝ} (hc : Continuous c) :
    eLpNorm c ⊤ (haar 1) ≠ ⊤ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact (memLp_top_of_bound hc.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ x))).eLpNorm_ne_top

theorem cvg_mul_cont {p : ℝ≥0∞} [ENNReal.HolderTriple ⊤ p p] (hp : 1 ≤ p) {c : Torus 1 → ℝ}
    (hc : Continuous c) {a : ℕ → Torus 1 → ℝ} {b : Torus 1 → ℝ} (hb : eLpNorm b p (haar 1) ≠ ⊤)
    (h : h1015_Cvg p (haar 1) a b) :
    h1015_Cvg p (haar 1) (fun j x => c x * a j x) (fun x => c x * b x) := by
  have := h1015_smul_tendsto (p := ⊤) (q := p) (r := p) hp hp (φ := fun _ => c) (φ₀ := c)
    (f := a) (f₀ := b) (eLpNorm_top_cont_ne hc) hb (by simp) h
  exact this

theorem entropy_ref_tendsto (M : RankOneModel) {σ : ℕ → AbsoluteDensity 1} {ρ0 : AbsoluteDensity 1}
    (h : h1015_Conv σ ρ0) :
    Tendsto (fun j => (relativeEntropy (densityMeasure (σ j) : Measure (Torus 1))
      M.ref.measure).toReal) atTop
      (𝓝 (relativeEntropy (densityMeasure ρ0 : Measure (Torus 1)) M.ref.measure).toReal) := by
  have key : ∀ ρ : AbsoluteDensity 1,
      (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) M.ref.measure).toReal =
        (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) (haar 1)).toReal -
          ∫ x, ρ.density x * Real.log (M.q x) ∂haar 1 := fun ρ => by
    rw [M.entropy_ref_eq _ (absoluteDensity_entropy_finite ρ).2.2.1,
      RankOneModel.integral_densityMeasure]
  have hlog : Continuous (fun x => Real.log (M.q x)) := by
    refine M.q_cont.log (fun x => (M.q_pos x).ne')
  have hint : ∀ ρ : AbsoluteDensity 1,
      Integrable (fun x => ρ.density x * Real.log (M.q x)) (haar 1) := fun ρ =>
    (RankOneModel.memLp_mul_cont hlog (h1015_memLp_dens_two ρ)).integrable one_le_two
  have hc : h1015_Cvg 1 (haar 1) (fun j x => Real.log (M.q x) * (σ j).density x)
      (fun x => Real.log (M.q x) * ρ0.density x) :=
    h1015_cvg_mono one_le_two (cvg_mul_cont one_le_two hlog
      (h1015_memLp_dens_two ρ0).eLpNorm_ne_top (h1015_dens_two h))
  simp_rw [mul_comm (Real.log (M.q _))] at hc
  have h2 := h1015_cvg_integral (hint ρ0) (fun j => hint (σ j)) hc
  simp_rw [key]
  exact (h1015_entropy_tendsto h).sub h2

theorem fisher_integrand_memLp (M : RankOneModel) (ρ : AbsoluteDensity 1) :
    MemLp (fun x => 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x) 2 (haar 1) :=
  ((memLp_coord (isWeakGradient_weakGradient ρ.sqrt_mem).memLp_grad 0).const_mul 2).sub
    (RankOneModel.memLp_mul_cont M.dlogq_cont ρ.memLp_sqrt)

theorem fisher_ref_tendsto (M : RankOneModel) {σ : ℕ → AbsoluteDensity 1} {ρ0 : AbsoluteDensity 1}
    (h : h1015_Conv σ ρ0) :
    Tendsto (fun j => ∫ x, (2 * weakGradient (σ j).sqrt (σ j).sqrt_mem x 0 -
        (σ j).sqrt x * M.dlogq x) ^ 2 ∂haar 1) atTop
      (𝓝 (∫ x, (2 * weakGradient ρ0.sqrt ρ0.sqrt_mem x 0 - ρ0.sqrt x * M.dlogq x) ^ 2
        ∂haar 1)) := by
  have hg := h1015_cvg_coord
    (fun j => (isWeakGradient_weakGradient (σ j).sqrt_mem).memLp_grad.aestronglyMeasurable)
    (isWeakGradient_weakGradient ρ0.sqrt_mem).memLp_grad.aestronglyMeasurable h.grad2
  have h1 := cvg_mul_cont (p := 2) one_le_two (continuous_const (y := (2 : ℝ)))
    (memLp_coord (isWeakGradient_weakGradient ρ0.sqrt_mem).memLp_grad 0).eLpNorm_ne_top hg
  have h2 := cvg_mul_cont (p := 2) one_le_two M.dlogq_cont ρ0.memLp_sqrt.eLpNorm_ne_top h.sqrt2
  have h3 := h1015_cvg_sub one_le_two h1 h2
  have h4 : h1015_Cvg 2 (haar 1) (fun j x => 2 * weakGradient (σ j).sqrt (σ j).sqrt_mem x 0 -
        (σ j).sqrt x * M.dlogq x)
      (fun x => 2 * weakGradient ρ0.sqrt ρ0.sqrt_mem x 0 - ρ0.sqrt x * M.dlogq x) := by
    refine h1015_cvg_congr_ae (fun j => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_) h3
    · simp [mul_comm]
    · simp [mul_comm]
  have h5 := h1015_cvg_integral_norm_sq (fun j => fisher_integrand_memLp M (σ j))
    (fisher_integrand_memLp M ρ0) h4
  simpa only [Real.norm_eq_abs, sq_abs] using h5

theorem entropy_ref_ne_top (M : RankOneModel) (ρ : AbsoluteDensity 1) :
    relativeEntropy (densityMeasure ρ : Measure (Torus 1)) M.ref.measure ≠ ⊤ :=
  (RankOneModel.free_energy_identity M _ (absoluteDensity_entropy_finite ρ).2.2.1).1

theorem quotient_eq (M : RankOneModel) (ρ : AbsoluteDensity 1)
    (hH : 0 < (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) M.ref.measure).toReal) :
    ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) M.ref /
        (2 * relativeEntropy (densityMeasure ρ : Measure (Torus 1)) M.ref.measure) =
      ENNReal.ofReal ((∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x) ^ 2
          ∂haar 1) /
        (2 * (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) M.ref.measure).toReal)) := by
  rw [RankOneModel.fisher_eq M ρ, ENNReal.ofReal_div_of_pos (by linarith),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal (entropy_ref_ne_top M ρ)]
  simp

theorem speciesRate_le_of_density (M : RankOneModel) (b : AbsoluteDrift M.data)
    (ρ0 : AbsoluteDensity 1)
    (hH : 0 < relativeEntropy (densityMeasure ρ0 : Measure (Torus 1)) M.ref.measure) :
    speciesRate M.data b ≤ ordinaryRelativeFisher (densityMeasure ρ0 : Measure (Torus 1)) M.ref /
      (2 * relativeEntropy (densityMeasure ρ0 : Measure (Torus 1)) M.ref.measure) := by
  set t : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with ht_def
  have htp : ∀ j, 0 < t j := fun j => by simp only [ht_def]; positivity
  have ht0 : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set σ : ℕ → AbsoluteDensity 1 := fun j => h1015_approx ρ0 (htp j) (htp j) with hσ
  have hc : h1015_Conv σ ρ0 := h1015_conv_approx ρ0 htp htp ht0 ht0
  have hHp : 0 < (relativeEntropy (densityMeasure ρ0 : Measure (Torus 1)) M.ref.measure).toReal :=
    ENNReal.toReal_pos hH.ne' (entropy_ref_ne_top M ρ0)
  have hE := entropy_ref_tendsto M hc
  have hF := fisher_ref_tendsto M hc
  have hev : ∀ᶠ j in atTop, 0 < (relativeEntropy (densityMeasure (σ j) : Measure (Torus 1))
      M.ref.measure).toReal := hE.eventually (lt_mem_nhds hHp)
  have hlim : Tendsto (fun j => ENNReal.ofReal ((∫ x, (2 * weakGradient (σ j).sqrt (σ j).sqrt_mem x 0 -
        (σ j).sqrt x * M.dlogq x) ^ 2 ∂haar 1) /
        (2 * (relativeEntropy (densityMeasure (σ j) : Measure (Torus 1)) M.ref.measure).toReal)))
      atTop (𝓝 (ENNReal.ofReal ((∫ x, (2 * weakGradient ρ0.sqrt ρ0.sqrt_mem x 0 -
        ρ0.sqrt x * M.dlogq x) ^ 2 ∂haar 1) /
        (2 * (relativeEntropy (densityMeasure ρ0 : Measure (Torus 1)) M.ref.measure).toReal)))) :=
    ENNReal.tendsto_ofReal (hF.div (hE.const_mul 2) (by positivity))
  rw [quotient_eq M ρ0 hHp]
  refine ge_of_tendsto hlim ?_
  filter_upwards [hev] with j hj
  have hHj : 0 < relativeEntropy (densityMeasure (σ j) : Measure (Torus 1)) M.ref.measure := by
    exact (ENNReal.toReal_pos_iff.1 hj).1
  have := speciesRate_le_of_smooth M b (σ j)
    (h1015_w_smooth ρ0.memLp_sqrt (htp j) _) (h1015_w_pos ρ0.memLp_sqrt ρ0.sqrt_nonneg (htp j) (htp j)) hHj
  rwa [quotient_eq M (σ j) hj] at this

theorem entropyIntegrand_scale {k a t : ℝ} (hk : 0 < k) (ha : a ≠ 0) :
    entropyIntegrand (k * a) (k * t) = k * entropyIntegrand a t := by
  unfold entropyIntegrand
  have : k * t / (k * a) = t / a := by field_simp
  rw [this]; ring

theorem homogeneousEntropy_scale {α : Type*} [MeasurableSpace α] (P : Measure α) (v : α → ℝ)
    {k : ℝ} (hk : 0 < k) :
    homogeneousEntropy P (fun x => k * v x) = ENNReal.ofReal k * homogeneousEntropy P v := by
  by_cases h0 : ∫ x, v x ∂P = 0
  · rw [homogeneousEntropy_of_integral_eq_zero h0, mul_zero,
      homogeneousEntropy_of_integral_eq_zero (by rw [integral_const_mul, h0, mul_zero])]
  · have h1 : ∫ x, k * v x ∂P ≠ 0 := by
      rw [integral_const_mul]; exact mul_ne_zero hk.ne' h0
    rw [homogeneousEntropy_of_integral_ne_zero h1, homogeneousEntropy_of_integral_ne_zero h0,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    rw [integral_const_mul, entropyIntegrand_scale hk h0,
      ENNReal.ofReal_mul hk.le]

theorem smooth_isWeakGradientLp_top {v : Torus 1 → ℝ} (hv : IsSmoothPeriodic v) :
    IsWeakGradientLp ∞ v (smoothGrad v) where
  memLp := hv.memLp_top
  memLp_grad := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      hv.continuous_smoothGrad.continuousOn
    exact memLp_top_of_bound hv.continuous_smoothGrad.aestronglyMeasurable C
      (Eventually.of_forall fun x => hC x (Set.mem_univ x))
  ibp ψ hψ j := integral_mul_coordPartial_of_smooth hv hψ j

theorem sqrtq_smooth (M : RankOneModel) : IsSmoothPeriodic (fun x => √(M.q x)) :=
  DGPS.Lipschitz.isSmoothPeriodic_sqrt M.q_smooth M.q_pos

theorem coordPartial_sqrtq (M : RankOneModel) (x : Torus 1) :
    coordPartial 0 (fun y => √(M.q y)) x = √(M.q x) * M.dlogq x / 2 := by
  rw [DGPS.Lipschitz.coordPartial_sqrt M.q_smooth M.q_pos, dlogq_eq']
  have h1 : 0 < √(M.q x) := Real.sqrt_pos.2 (M.q_pos x)
  have h2 : √(M.q x) * √(M.q x) = M.q x := Real.mul_self_sqrt (M.q_pos x).le
  have h3 := (M.q_pos x).ne'
  field_simp
  rw [Real.sq_sqrt (M.q_pos x).le]

/-- The gradient of `|f|` (chain rule). -/
noncomputable def absGrad (f : Torus 1 → ℝ) (g : Torus 1 → Tangent 1) : Torus 1 → Tangent 1 :=
  fun x => if 0 < f x then g x else if f x < 0 then -g x else 0

theorem norm_absGrad_le (f : Torus 1 → ℝ) (g : Torus 1 → Tangent 1) (x : Torus 1) :
    ‖absGrad f g x‖ ≤ ‖g x‖ := by
  unfold absGrad
  split_ifs <;> simp

noncomputable def sGrad (M : RankOneModel) (c : ℝ) (f : Torus 1 → ℝ) (g : Torus 1 → Tangent 1) :
    Torus 1 → Tangent 1 :=
  fun x => √(M.q x) • (c • absGrad f g x) +
    (c * |f x|) • smoothGrad (fun y => √(M.q y)) x

theorem isWeakGradient_s (M : RankOneModel) (c : ℝ) {f : Torus 1 → ℝ} {g : Torus 1 → Tangent 1}
    (hg : IsWeakGradient f g) :
    IsWeakGradient (fun x => c * |f x| * √(M.q x)) (sGrad M c f g) :=
  (hg.abs.smul c).mul_W1infty (smooth_isWeakGradientLp_top (sqrtq_smooth M))

theorem sGrad_fisher (M : RankOneModel) (c : ℝ) (f : Torus 1 → ℝ) (g : Torus 1 → Tangent 1)
    (x : Torus 1) :
    2 * sGrad M c f g x 0 - (c * |f x| * √(M.q x)) * M.dlogq x =
      2 * (√(M.q x) * (c * absGrad f g x 0)) := by
  simp only [sGrad, PiLp.add_apply, PiLp.smul_apply, smoothGrad_apply, coordPartial_sqrtq,
    smul_eq_mul]
  ring

theorem lintegral_grad_eq (M : RankOneModel) {g wg : Torus 1 → Tangent 1}
    (hwg : wg =ᵐ[haar 1] g) (hg : MemLp g 2 (haar 1)) :
    ∫⁻ x, ‖wg x‖ₑ ^ 2 ∂M.ref.measure = ENNReal.ofReal (∫ x, M.q x * ‖g x‖ ^ 2 ∂haar 1) := by
  have hint : Integrable (fun x => M.q x * ‖g x‖ ^ 2) (haar 1) :=
    RankOneModel.integrable_cont_mul M.q_cont hg.norm.integrable_sq
  rw [BoundedPositiveReference.measure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _
      M.ref.measurable_ofReal_density.aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => mul_nonneg (M.q_pos x).le (sq_nonneg _))]
  refine lintegral_congr_ae ?_
  filter_upwards [hwg] with x hx
  show ENNReal.ofReal (M.q x) * ‖wg x‖ₑ ^ 2 = _
  rw [hx, ENNReal.ofReal_mul (M.q_pos x).le, ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm]

noncomputable def rho0 (M : RankOneModel) (c : ℝ) (hc : 0 ≤ c) {f : Torus 1 → ℝ}
    {g : Torus 1 → Tangent 1} (hg : IsWeakGradient f g)
    (hmass : ∫ x, (c * |f x| * √(M.q x)) ^ 2 ∂haar 1 = 1) : AbsoluteDensity 1 where
  sqrt := fun x => c * |f x| * √(M.q x)
  sqrt_mem := ⟨_, isWeakGradient_s M c hg⟩
  sqrt_nonneg := Filter.Eventually.of_forall fun x => by
    have := Real.sqrt_nonneg (M.q x)
    have := abs_nonneg (f x)
    show 0 ≤ c * |f x| * √(M.q x)
    positivity
  mass_one := hmass

theorem rho0_measure (M : RankOneModel) (c : ℝ) (hc : 0 ≤ c) {f : Torus 1 → ℝ}
    {g : Torus 1 → Tangent 1} (hg : IsWeakGradient f g)
    (hmass : ∫ x, (c * |f x| * √(M.q x)) ^ 2 ∂haar 1 = 1) :
    (densityMeasure (rho0 M c hc hg hmass) : Measure (Torus 1)) =
      M.ref.measure.withDensity (fun x => ENNReal.ofReal (c ^ 2 * f x ^ 2)) := by
  have hfm : AEMeasurable f (haar 1) := hg.memLp.aestronglyMeasurable.aemeasurable
  have hmul := withDensity_mul₀ (μ := haar 1)
    (f := fun x => ENNReal.ofReal (M.ref.density x))
    (g := fun x => ENNReal.ofReal (c ^ 2 * f x ^ 2))
    M.ref.measurable_ofReal_density.aemeasurable
    (ENNReal.measurable_ofReal.comp_aemeasurable ((hfm.pow_const 2).const_mul (c ^ 2)))
  rw [densityMeasure_coe, BoundedPositiveReference.measure, ← hmul]
  congr 1
  funext x
  show ENNReal.ofReal ((c * |f x| * √(M.q x)) ^ 2) = ENNReal.ofReal (M.q x) *
    ENNReal.ofReal (c ^ 2 * f x ^ 2)
  rw [← ENNReal.ofReal_mul (M.q_pos x).le]
  congr 1
  rw [mul_pow, mul_pow, sq_abs, Real.sq_sqrt (M.q_pos x).le]
  ring

theorem quotient_le (M : RankOneModel) (b : AbsoluteDrift M.data) {f : Torus 1 → ℝ}
    (hmem : f ∈ WeightedH1 M.ref)
    (hpos : 0 < homogeneousEntropy M.ref.measure (fun x => f x ^ 2)) :
    speciesRate M.data b ≤
      2 * (∫⁻ x, ‖weightedGradient M.ref f hmem x‖ₑ ^ 2 ∂M.ref.measure) /
        homogeneousEntropy M.ref.measure (fun x => f x ^ 2) := by
  obtain ⟨g, hg⟩ := (mem_weightedH1_iff M.ref).1 hmem
  have hfm : AEMeasurable f (haar 1) := hg.memLp.aestronglyMeasurable.aemeasurable
  set Ent := homogeneousEntropy M.ref.measure (fun x => f x ^ 2) with hEnt
  set Z := ∫ x, f x ^ 2 ∂M.ref.measure with hZ
  have hZ0 : Z ≠ 0 := fun h => by
    rw [hEnt, homogeneousEntropy_of_integral_eq_zero h] at hpos
    exact lt_irrefl _ hpos
  have hZpos : 0 < Z := lt_of_le_of_ne (integral_nonneg fun x => sq_nonneg _) (Ne.symm hZ0)
  set c := √(1 / Z) with hc
  have hc2 : c ^ 2 = 1 / Z := Real.sq_sqrt (by positivity)
  have hc2pos : 0 < c ^ 2 := by rw [hc2]; positivity
  have hmass : ∫ x, (c * |f x| * √(M.q x)) ^ 2 ∂haar 1 = 1 := by
    have : ∀ x, (c * |f x| * √(M.q x)) ^ 2 = c ^ 2 * (M.q x * f x ^ 2) := by
      intro x
      rw [mul_pow, mul_pow, sq_abs, Real.sq_sqrt (M.q_pos x).le]; ring
    simp_rw [this]
    rw [integral_const_mul, ← integral_ref M (fun x => f x ^ 2), ← hZ, hc2]
    field_simp
  set ρ0 := rho0 M c (Real.sqrt_nonneg _) hg hmass with hρ0
  have hmeas := rho0_measure M c (Real.sqrt_nonneg _) hg hmass
  have hac : M.ref.measure ≪ haar 1 := withDensity_absolutelyContinuous _ _
  have hH : relativeEntropy (densityMeasure ρ0 : Measure (Torus 1)) M.ref.measure =
      ENNReal.ofReal (c ^ 2) * Ent := by
    rw [hρ0, hmeas, relativeEntropy_withDensity
      (Filter.Eventually.of_forall fun x => by positivity)
      (((hfm.pow_const 2).const_mul (c ^ 2)).mono_ac hac)]
    exact homogeneousEntropy_scale M.ref.measure (fun x => f x ^ 2) hc2pos
  have hEnt_ne : Ent ≠ ⊤ := by
    intro h
    apply entropy_ref_ne_top M ρ0
    rw [hH, h, ENNReal.mul_top (ENNReal.ofReal_pos.2 hc2pos).ne']
  have hHpos : 0 < relativeEntropy (densityMeasure ρ0 : Measure (Torus 1)) M.ref.measure := by
    rw [hH]; exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hc2pos).ne' hpos.ne'
  refine (speciesRate_le_of_density M b ρ0 hHpos).trans ?_
  rw [RankOneModel.fisher_eq M ρ0, hH,
    lintegral_grad_eq M (weightedGradient_ae_eq M.ref hmem hg) hg.memLp_grad]
  set J := ∫ x, M.q x * ‖g x‖ ^ 2 ∂haar 1 with hJ
  have hJint : Integrable (fun x => M.q x * ‖g x‖ ^ 2) (haar 1) :=
    RankOneModel.integrable_cont_mul M.q_cont hg.memLp_grad.norm.integrable_sq
  have hJ0 : 0 ≤ J := integral_nonneg fun x => mul_nonneg (M.q_pos x).le (sq_nonneg _)
  have hwgs : weakGradient ρ0.sqrt ρ0.sqrt_mem =ᵐ[haar 1] sGrad M c f g :=
    (isWeakGradient_weakGradient ρ0.sqrt_mem).ae_eq (isWeakGradient_s M c hg)
  have hF : ∫ x, (2 * weakGradient ρ0.sqrt ρ0.sqrt_mem x 0 - ρ0.sqrt x * M.dlogq x) ^ 2 ∂haar 1 ≤
      4 * c ^ 2 * J := by
    calc _ = ∫ x, (2 * (√(M.q x) * (c * absGrad f g x 0))) ^ 2 ∂haar 1 := by
          refine integral_congr_ae ?_
          filter_upwards [hwgs] with x hx
          show (2 * weakGradient ρ0.sqrt ρ0.sqrt_mem x 0 -
            (c * |f x| * √(M.q x)) * M.dlogq x) ^ 2 = _
          rw [hx, sGrad_fisher]
      _ ≤ ∫ x, 4 * c ^ 2 * (M.q x * ‖g x‖ ^ 2) ∂haar 1 := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
            (hJint.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
          have h1 : |absGrad f g x 0| ≤ ‖g x‖ := by
            have := (PiLp.norm_apply_le (absGrad f g x) 0).trans (norm_absGrad_le f g x)
            simpa using this
          have h2 : absGrad f g x 0 ^ 2 ≤ ‖g x‖ ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
          have h3 : (2 * (√(M.q x) * (c * absGrad f g x 0))) ^ 2 =
              4 * c ^ 2 * (M.q x * absGrad f g x 0 ^ 2) := by
            have := Real.sq_sqrt (M.q_pos x).le
            calc _ = 4 * c ^ 2 * (√(M.q x) ^ 2 * absGrad f g x 0 ^ 2) := by ring
              _ = _ := by rw [this]
          beta_reduce
          rw [h3]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (M.q_pos x).le)
            (by positivity)
      _ = 4 * c ^ 2 * J := integral_const_mul _ _
  have hk0 : ENNReal.ofReal (2 * c ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  calc ENNReal.ofReal _ / (2 * (ENNReal.ofReal (c ^ 2) * Ent))
      ≤ ENNReal.ofReal (4 * c ^ 2 * J) / (2 * (ENNReal.ofReal (c ^ 2) * Ent)) :=
        ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hF) _
    _ = ENNReal.ofReal (2 * c ^ 2) * (2 * ENNReal.ofReal J) /
          (ENNReal.ofReal (2 * c ^ 2) * Ent) := by
        have e1 : 4 * c ^ 2 * J = (2 * c ^ 2) * (2 * J) := by ring
        rw [e1, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
        simp only [ENNReal.ofReal_ofNat]
        rw [mul_assoc 2 (ENNReal.ofReal (c ^ 2)) Ent]
    _ = 2 * ENNReal.ofReal J / Ent :=
        ENNReal.mul_div_mul_left _ _ hk0 ENNReal.ofReal_ne_top

theorem speciesRate_le_ordinaryLSRate (M : RankOneModel) (b : AbsoluteDrift M.data) :
    speciesRate M.data b ≤ ordinaryLSRate M.ref := by
  unfold ordinaryLSRate
  exact le_iInf fun ⟨f, hmem, hpos⟩ => quotient_le M b hmem hpos

theorem ordinaryLSRate_pos (M : RankOneModel) : 0 < ordinaryLSRate M.ref := by
  have hc := M.ref.lower_pos
  obtain ⟨x, h1, h2⟩ := (M.ref.lower_le.and M.ref.le_upper).exists
  have hC : 0 < M.ref.upper := lt_of_lt_of_le hc (h1.trans h2)
  refine lt_of_lt_of_le ?_ (def025_lsi_of_density_bounds M.ref hc M.ref.lower_le M.ref.le_upper)
  exact ENNReal.ofReal_pos.2 (div_pos (mul_pos DGPS.a0_pos hc) hC)

end DGPS.Examples.EngineeredRankOneRates

namespace DGPS.Examples

open DGPS.Examples.EngineeredRankOne DGPS.Models DGPS.PositiveRankOne DGPS.Structural
open DGPS.Circle.AngularNormalization

/-- EX047: for every fixed `h ≥ 2` and every absolute drift, the species rate of the engineered
rank-one model equals the ordinary logarithmic Sobolev rate of its reference measure, which is
positive, finite and at most the exact eigenvalue `a₀ Λ_h`. -/
theorem engineered_species_rate_equals_ordinary_lsi (h : ℝ) (hh : 2 ≤ h)
    (b : AbsoluteDrift (engineeredModel h hh).data) :
    speciesRate (engineeredModel h hh).data b = ordinaryLSRate (engineeredModel h hh).ref ∧
    0 < ordinaryLSRate (engineeredModel h hh).ref ∧
    ordinaryLSRate (engineeredModel h hh).ref < ⊤ ∧
    ordinaryLSRate (engineeredModel h hh).ref ≤ ENNReal.ofReal (a0 * lamH h) := by
  obtain ⟨-, -, hlam, -, -, h0, -⟩ := engineered_feature_exact_eigenfunction h hh
  have hc : 0 < a0 * lamH h := mul_pos a0_pos hlam
  have hA : ∀ x, (engineeredModel h hh).Aq x = (a0 * lamH h) * (engineeredModel h hh).φ x :=
    fun x => by rw [engineeredModel_Aq h hh x]; rfl
  have hφ : (engineeredModel h hh).φ (angEquiv.symm 0) ≠ 0 := by
    show Eang h (angEquiv (angEquiv.symm 0)) ≠ 0
    rw [MeasurableEquiv.apply_symm_apply, h0]
    norm_num
  have hV := EngineeredRankOneRates.integral_phi_sq_pos (engineeredModel h hh) hφ
  have hle := EngineeredRankOneRates.lsRate_le_of_eigen (engineeredModel h hh) _ hA hV
  have h1 := EngineeredRankOneRates.ordinaryLSRate_le_speciesRate (engineeredModel h hh) b _
    hc.le hA hle
  have h2 := EngineeredRankOneRates.speciesRate_le_ordinaryLSRate (engineeredModel h hh) b
  exact ⟨le_antisymm h2 h1, EngineeredRankOneRates.ordinaryLSRate_pos _,
    lt_of_le_of_lt hle ENNReal.ofReal_lt_top, hle⟩

end DGPS.Examples
