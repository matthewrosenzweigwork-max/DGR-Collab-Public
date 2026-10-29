import DGPS.FiniteN.FalseMinimumFIN081

/-!
# FIN082: the cutoff mass on the left branch of the false minimum

Fix `κ > 2` and `0 < h < h_c(κ)` and the roots `s1, s2, tp` of `FalseMinimumGeometryFIN076`
(`m_- = g(-s2)`, `m_b = g(-s1)`, `m_+ = g(tp)`).  For a smooth cutoff `χ` with `0 ≤ χ ≤ 1`,
`χ = 1` on `m ≤ m_b - δ` and `χ = 0` on `m ≥ m_b + δ`, the mass `n_N = P_N(χ(m_N)²)` satisfies
`N⁻¹ log n_N → -G_-`, and the transition probability `P_N(m_N ∈ [m_b - δ, m_b + δ])` has
limsup exponent `≤ -J_δ < -G_-`, `J_δ = inf_{|m - m_b| ≤ δ} J(m) > G_-`.

The main theorem is `DGPS.FiniteN.false_minimum_branch_cutoff_mass_exponent`.
-/

open MeasureTheory Filter Topology
open scoped ContDiff
open DGPS.Circle.BesselMoments DGPS.FiniteN.EmpiricalCosineCramerFIN080
  DGPS.FiniteN.FalseMinimumFIN081 DGPS.FiniteN.FalseMinimumFIN076 DGPS.Models
  DGPS.FiniteN.ScalarFoldFIN056

namespace DGPS.FiniteN.FalseMinimumFIN082

/-- The cutoff mass `n_N = P_N(f_N²)` for `f_N = χ (m_N)`. -/
noncomputable def cutoffMassFIN082 (κ h : ℝ) (χ : ℝ → ℝ) (N : ℕ+) : ℝ :=
  ∫ x, (χ (empTorusFIN081 N x)) ^ 2 ∂(DGPS.particleLaw (scalarCosine κ h) N)

theorem continuous_empTorus_FIN082 (N : ℕ+) : Continuous (empTorusFIN081 N) := by
  unfold empTorusFIN081
  exact continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_scalarCos.comp (continuous_apply i))

theorem measurable_set_emp_FIN082 (N : ℕ+) {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet {x : DGPS.ParticleSpace 1 N | empTorusFIN081 N x ∈ S} :=
  (continuous_empTorus_FIN082 N).measurable hS

theorem mass_ge_FIN082 (κ h : ℝ) {χ : ℝ → ℝ} (hχc : Continuous χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hχ1 : ∀ x, χ x ≤ 1) (N : ℕ+) {S : Set ℝ} (hS : MeasurableSet S) (hχS : ∀ x ∈ S, χ x = 1) :
    (DGPS.particleLaw (scalarCosine κ h) N {x | empTorusFIN081 N x ∈ S}).toReal ≤
      cutoffMassFIN082 κ h χ N := by
  have := DGPS.Particle.particleLaw_isProbabilityMeasure' (scalarCosine κ h) N
  have hm : Measurable fun x => (χ (empTorusFIN081 N x)) ^ 2 :=
    ((hχc.comp (continuous_empTorus_FIN082 N)).pow 2).measurable
  have hint : Integrable (fun x => (χ (empTorusFIN081 N x)) ^ 2)
      (DGPS.particleLaw (scalarCosine κ h) N) := by
    refine Integrable.of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := hχ0 (empTorusFIN081 N x)
    have := hχ1 (empTorusFIN081 N x)
    nlinarith
  have hSm := measurable_set_emp_FIN082 N hS
  have h1 : ∫ x, ({x | empTorusFIN081 N x ∈ S}.indicator (fun _ => (1 : ℝ)) x)
      ∂(DGPS.particleLaw (scalarCosine κ h) N) =
      (DGPS.particleLaw (scalarCosine κ h) N {x | empTorusFIN081 N x ∈ S}).toReal := by
    rw [integral_indicator hSm]; simp [measureReal_def]
  rw [← h1, cutoffMassFIN082]
  refine integral_mono ((integrable_const (1:ℝ)).indicator hSm) hint fun x => ?_
  by_cases hx : x ∈ {x | empTorusFIN081 N x ∈ S}
  · rw [Set.indicator_of_mem hx, hχS _ hx]; norm_num
  · rw [Set.indicator_of_notMem hx]; exact sq_nonneg _

theorem mass_le_FIN082 (κ h : ℝ) {χ : ℝ → ℝ} (hχc : Continuous χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hχ1 : ∀ x, χ x ≤ 1) (N : ℕ+) {T : Set ℝ} (hT : MeasurableSet T) (hχT : ∀ x ∉ T, χ x = 0) :
    cutoffMassFIN082 κ h χ N ≤
      (DGPS.particleLaw (scalarCosine κ h) N {x | empTorusFIN081 N x ∈ T}).toReal := by
  have := DGPS.Particle.particleLaw_isProbabilityMeasure' (scalarCosine κ h) N
  have hm : Measurable fun x => (χ (empTorusFIN081 N x)) ^ 2 :=
    ((hχc.comp (continuous_empTorus_FIN082 N)).pow 2).measurable
  have hint : Integrable (fun x => (χ (empTorusFIN081 N x)) ^ 2)
      (DGPS.particleLaw (scalarCosine κ h) N) := by
    refine Integrable.of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := hχ0 (empTorusFIN081 N x)
    have := hχ1 (empTorusFIN081 N x)
    nlinarith
  have hTm := measurable_set_emp_FIN082 N hT
  have h1 : ∫ x, ({x | empTorusFIN081 N x ∈ T}.indicator (fun _ => (1 : ℝ)) x)
      ∂(DGPS.particleLaw (scalarCosine κ h) N) =
      (DGPS.particleLaw (scalarCosine κ h) N {x | empTorusFIN081 N x ∈ T}).toReal := by
    rw [integral_indicator hTm]; simp [measureReal_def]
  rw [← h1, cutoffMassFIN082]
  refine integral_mono hint ((integrable_const (1:ℝ)).indicator hTm) fun x => ?_
  by_cases hx : x ∈ {x | empTorusFIN081 N x ∈ T}
  · rw [Set.indicator_of_mem hx]
    have := hχ0 (empTorusFIN081 N x)
    have := hχ1 (empTorusFIN081 N x)
    nlinarith
  · rw [Set.indicator_of_notMem hx, hχT _ hx]; norm_num

theorem tendsto_cutoff_mass_FIN082 (κ h : ℝ) {χ : ℝ → ℝ} (hχc : Continuous χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) {a b G : ℝ}
    (ha : ∀ x < a, χ x = 1) (hb : ∀ x, b < x → χ x = 0)
    (hlow : (⨅ x ∈ Set.Iio a, gibbsRateFIN081 κ h x) ≤ (G : EReal))
    (hup : (G : EReal) ≤ ⨅ x ∈ Set.Iic b, gibbsRateFIN081 κ h x) :
    Tendsto (fun N : ℕ+ => ((N : ℝ)⁻¹) * Real.log (cutoffMassFIN082 κ h χ N)) atTop (𝓝 (-G)) := by
  set A : ℕ+ → EReal := fun N =>
    (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (cutoffMassFIN082 κ h χ N)) with hA
  have hcoef : ∀ N : ℕ+, (0 : EReal) ≤ (((N : ℝ)⁻¹ : ℝ) : EReal) := fun N =>
    EReal.coe_nonneg.2 (inv_nonneg.2 (Nat.cast_nonneg _))
  have hge : ∀ N : ℕ+, gibbsLogProbFIN081 κ h N (Set.Iio a) ≤ A N := by
    intro N
    have := DGPS.Particle.particleLaw_isProbabilityMeasure' (scalarCosine κ h) N
    refine mul_le_mul_of_nonneg_left (ENNReal.log_monotone ?_) (hcoef N)
    calc _ = ENNReal.ofReal (DGPS.particleLaw (scalarCosine κ h) N
            {x | empTorusFIN081 N x ∈ Set.Iio a}).toReal :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mass_ge_FIN082 κ h hχc hχ0 hχ1 N measurableSet_Iio ha)
  have hle : ∀ N : ℕ+, A N ≤ gibbsLogProbFIN081 κ h N (Set.Iic b) := by
    intro N
    have := DGPS.Particle.particleLaw_isProbabilityMeasure' (scalarCosine κ h) N
    refine mul_le_mul_of_nonneg_left (ENNReal.log_monotone ?_) (hcoef N)
    calc ENNReal.ofReal (cutoffMassFIN082 κ h χ N)
        ≤ ENNReal.ofReal (DGPS.particleLaw (scalarCosine κ h) N
            {x | empTorusFIN081 N x ∈ Set.Iic b}).toReal :=
          ENNReal.ofReal_le_ofReal (mass_le_FIN082 κ h hχc hχ0 hχ1 N measurableSet_Iic
            fun x hx => hb x (not_le.1 hx))
      _ = _ := ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hlim : Tendsto A atTop (𝓝 ((-G : ℝ) : EReal)) := by
    refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
    · calc ((-G : ℝ) : EReal) = -(G : EReal) := EReal.coe_neg G
        _ ≤ -(⨅ x ∈ Set.Iio a, gibbsRateFIN081 κ h x) := EReal.neg_le_neg_iff.2 hlow
        _ ≤ liminf (fun N : ℕ+ => gibbsLogProbFIN081 κ h N (Set.Iio a)) atTop :=
          gibbs_lower_FIN081 κ h isOpen_Iio
        _ ≤ liminf A atTop := liminf_le_liminf (Filter.Eventually.of_forall hge)
    · calc limsup A atTop ≤ limsup (fun N : ℕ+ => gibbsLogProbFIN081 κ h N (Set.Iic b)) atTop :=
          limsup_le_limsup (Filter.Eventually.of_forall hle)
        _ ≤ -(⨅ x ∈ Set.Iic b, gibbsRateFIN081 κ h x) := gibbs_upper_FIN081 κ h isClosed_Iic
        _ ≤ -(G : EReal) := EReal.neg_le_neg_iff.2 hup
        _ = ((-G : ℝ) : EReal) := (EReal.coe_neg G).symm
  have hpos : ∀ᶠ N : ℕ+ in atTop, 0 < cutoffMassFIN082 κ h χ N := by
    have hev : ∀ᶠ N : ℕ+ in atTop, (⊥ : EReal) < A N :=
      hlim.eventually (eventually_gt_nhds (EReal.bot_lt_coe _))
    filter_upwards [hev] with N hN
    by_contra hneg
    have h0 : ENNReal.ofReal (cutoffMassFIN082 κ h χ N) = 0 := ENNReal.ofReal_of_nonpos (not_lt.1 hneg)
    have : A N = ⊥ := by
      rw [hA]
      simp only [h0, ENNReal.log_zero]
      refine EReal.coe_mul_bot_of_pos ?_
      exact inv_pos.2 (by positivity)
    exact absurd hN (by rw [this]; exact lt_irrefl _)
  have hcongr : ∀ᶠ N : ℕ+ in atTop, A N =
      ((((N : ℝ)⁻¹) * Real.log (cutoffMassFIN082 κ h χ N) : ℝ) : EReal) := by
    filter_upwards [hpos] with N hN
    rw [hA]
    simp only [ENNReal.log_ofReal_of_pos hN, EReal.coe_mul]
  exact EReal.tendsto_coe.1 (hlim.congr' hcongr)


/-- A continuous function without zeros on an order-connected set keeps its negative sign. -/
theorem sign_neg_FIN082 {f : ℝ → ℝ} (hf : Continuous f) {I : Set ℝ} (hI : I.OrdConnected)
    (hz : ∀ t ∈ I, f t ≠ 0) {c : ℝ} (hc : c ∈ I) (hfc : f c < 0) : ∀ t ∈ I, f t < 0 := by
  intro t ht
  by_contra hneg
  have hpos : 0 ≤ f t := not_lt.1 hneg
  have hsub : Set.uIcc t c ⊆ I := hI.uIcc_subset ht hc
  have hmem : (0 : ℝ) ∈ Set.uIcc (f t) (f c) := Set.mem_uIcc.2 (Or.inr ⟨hfc.le, hpos⟩)
  obtain ⟨u, hu, hu0⟩ := intermediate_value_uIcc hf.continuousOn hmem
  exact hz u (hsub hu) hu0

section Geometry

variable {κ h s1 s2 tp : ℝ}

theorem psiDeriv_zero_iff_FIN082 (hκ : 0 < κ) (hG : FalseMinimumGeometryFIN076 κ h s1 s2 tp)
    (t : ℝ) : psiDerivFIN056 κ h t = 0 ↔ t = -s2 ∨ t = -s1 ∨ t = tp := by
  rw [← hG.2.2.2.1 t, deriv_scalarPsi_FIN056 hκ h]

theorem psiDeriv_neg_left_FIN082 (hκ : 0 < κ) (hG : FalseMinimumGeometryFIN076 κ h s1 s2 tp)
    (hs12 : s1 < s2) (hs1 : 0 < s1) (htp : 0 < tp) {t : ℝ} (ht : t < -s2) :
    psiDerivFIN056 κ h t < 0 := by
  set c : ℝ := min (-s2 - 1) (h - κ) with hc
  have hcl : c < -s2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hc2 : c ≤ h - κ := min_le_right _ _
  have hfc : psiDerivFIN056 κ h c < 0 := by
    unfold psiDerivFIN056
    have h1 : (c - h) / κ ≤ -1 := by
      rw [div_le_iff₀ hκ]; linarith
    have h2 := neg_one_lt_ratio c
    linarith
  refine sign_neg_FIN082 (continuous_psiDeriv_FIN056 κ h) (Set.ordConnected_Iio (a := -s2)) ?_
    (Set.mem_Iio.2 hcl) hfc t (Set.mem_Iio.2 ht)
  intro u hu hu0
  have hu' : u < -s2 := hu
  rcases (psiDeriv_zero_iff_FIN082 hκ hG u).1 hu0 with h' | h' | h'
  · linarith
  · linarith
  · linarith

theorem psiDeriv_pos_mid_FIN082 (hκ : 0 < κ) (hG : FalseMinimumGeometryFIN076 κ h s1 s2 tp)
    (_hs12 : s1 < s2) (_hs1 : 0 < s1) (_htp : 0 < tp) {t : ℝ} (ht1 : -s2 < t) (ht2 : t < -s1) :
    0 < psiDerivFIN056 κ h t := by
  have hB : 0 < scalarPsi κ h (-s1) - scalarPsi κ h (-s2) := hG.2.2.2.2.2.2.2.1.1
  have hab : -s2 < -s1 := by linarith
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (scalarPsi κ h) (psiDerivFIN056 κ h) hab
    (fun x _ => (hasDerivAt_scalarPsi_FIN056 hκ h x).continuousAt.continuousWithinAt)
    (fun x _ => hasDerivAt_scalarPsi_FIN056 hκ h x)
  have hcpos : 0 < psiDerivFIN056 κ h c := by
    rw [hcd]; apply div_pos hB; linarith
  have hneg := sign_neg_FIN082 (f := fun t => -psiDerivFIN056 κ h t)
    (continuous_psiDeriv_FIN056 κ h).neg (Set.ordConnected_Ioo (a := -s2) (b := -s1)) ?_
    (c := c) hc (by simpa using hcpos) t ⟨ht1, ht2⟩
  · simpa using hneg
  · intro u hu hu0
    have : psiDerivFIN056 κ h u = 0 := by simpa using hu0
    rcases (psiDeriv_zero_iff_FIN082 hκ hG u).1 this with h' | h' | h'
    · linarith [hu.1]
    · linarith [hu.2]
    · linarith [hu.2]


theorem uf_deriv_FIN082 (hκ : 0 < κ) {m : ℝ} (hm : m ∈ Set.Ioo (-1 : ℝ) 1) :
    tInv m - (h + κ * m) = κ * psiDerivFIN056 κ h (tInv m) := by
  unfold psiDerivFIN056
  rw [ratio_tInv hm]
  field_simp
  ring

theorem uf_ge_FIN082 (hκ : 0 < κ) (hG : FalseMinimumGeometryFIN076 κ h s1 s2 tp)
    (hs12 : s1 < s2) (hs1 : 0 < s1) (htp : 0 < tp) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hxb : x ≤ besselRatio (-s1)) : scalarPsi κ h (-s2) ≤ ufFIN081 κ h x := by
  have hm2 : psiDerivFIN056 κ h (-s2) = 0 := (psiDeriv_zero_iff_FIN082 hκ hG _).2 (Or.inl rfl)
  have hUm : ufFIN081 κ h (besselRatio (-s2)) = scalarPsi κ h (-s2) :=
    uf_ratio_FIN081 hκ.ne' h hm2
  have hlt : besselRatio (-s2) < besselRatio (-s1) := strictMono_ratio (by linarith)
  have hmem : besselRatio (-s2) ∈ Set.Ioo (-1 : ℝ) 1 := ratio_mem_FIN081 _
  have hmemb : besselRatio (-s1) ∈ Set.Ioo (-1 : ℝ) 1 := ratio_mem_FIN081 _
  rcases le_total x (besselRatio (-s2)) with hxl | hxr
  · -- left piece: `U` is antitone on `[x, m_-]`
    have hsub : Set.Icc x (besselRatio (-s2)) ⊆ Set.Ioo (-1 : ℝ) 1 := fun y hy =>
      ⟨lt_of_lt_of_le hx.1 hy.1, lt_of_le_of_lt hy.2 hmem.2⟩
    have hanti : AntitoneOn (ufFIN081 κ h) (Set.Icc x (besselRatio (-s2))) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
        ((continuousOn_uf_FIN081 κ h).mono hsub) ?_ ?_
      · intro y hy
        rw [interior_Icc] at hy
        exact (hasDerivAt_uf_FIN081 κ h (hsub (Set.Ioo_subset_Icc_self hy))).differentiableAt
          |>.differentiableWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        have hy1 : y ∈ Set.Ioo (-1 : ℝ) 1 := hsub (Set.Ioo_subset_Icc_self hy)
        rw [(hasDerivAt_uf_FIN081 κ h hy1).deriv, uf_deriv_FIN082 hκ hy1]
        have : tInv y < -s2 := by
          have h1 : besselRatio (tInv y) < besselRatio (-s2) := by
            rw [ratio_tInv hy1]; exact hy.2
          exact strictMono_ratio.lt_iff_lt.1 h1
        have := psiDeriv_neg_left_FIN082 hκ hG hs12 hs1 htp this
        nlinarith
    have := hanti ⟨le_rfl, hxl⟩ ⟨hxl, le_rfl⟩ hxl
    linarith
  · have hsub : Set.Icc (besselRatio (-s2)) x ⊆ Set.Ioo (-1 : ℝ) 1 := fun y hy =>
      ⟨lt_of_lt_of_le hmem.1 hy.1, lt_of_le_of_lt hy.2 hx.2⟩
    have hmono : MonotoneOn (ufFIN081 κ h) (Set.Icc (besselRatio (-s2)) x) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        ((continuousOn_uf_FIN081 κ h).mono hsub) ?_ ?_
      · intro y hy
        rw [interior_Icc] at hy
        exact (hasDerivAt_uf_FIN081 κ h (hsub (Set.Ioo_subset_Icc_self hy))).differentiableAt
          |>.differentiableWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        have hy1 : y ∈ Set.Ioo (-1 : ℝ) 1 := hsub (Set.Ioo_subset_Icc_self hy)
        rw [(hasDerivAt_uf_FIN081 κ h hy1).deriv, uf_deriv_FIN082 hκ hy1]
        have h1 : -s2 < tInv y := by
          have : besselRatio (-s2) < besselRatio (tInv y) := by
            rw [ratio_tInv hy1]; exact hy.1
          exact strictMono_ratio.lt_iff_lt.1 this
        have h2 : tInv y < -s1 := by
          have : besselRatio (tInv y) < besselRatio (-s1) := by
            rw [ratio_tInv hy1]; exact lt_of_lt_of_le hy.2 hxb
          exact strictMono_ratio.lt_iff_lt.1 this
        have := psiDeriv_pos_mid_FIN082 hκ hG hs12 hs1 htp h1 h2
        nlinarith
    have := hmono ⟨le_rfl, hxr⟩ ⟨hxr, le_rfl⟩ hxr
    linarith

theorem rate_ge_left_FIN082 (hκ : 0 < κ) (hG : FalseMinimumGeometryFIN076 κ h s1 s2 tp)
    (hs12 : s1 < s2) (hs1 : 0 < s1) (htp : 0 < tp) {x : ℝ} (hxb : x ≤ besselRatio (-s1)) :
    ((scalarPsi κ h (-s2) - scalarPsi κ h tp : ℝ) : EReal) ≤ gibbsRateFIN081 κ h x := by
  by_cases hx : x ∈ Set.Ioo (-1 : ℝ) 1
  · rw [gibbsRate_eq_FIN081 hκ hG hx]
    exact EReal.coe_le_coe_iff.2 (by linarith [uf_ge_FIN082 hκ hG hs12 hs1 htp hx hxb])
  · rw [gibbsRate_of_not_mem_FIN081 κ h hx]; exact le_top

theorem rate_ge_near_FIN082 (hκ : 0 < κ) (hG : FalseMinimumGeometryFIN076 κ h s1 s2 tp) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : ℝ, |x - besselRatio (-s1)| ≤ η →
      ((scalarPsi κ h (-s2) - scalarPsi κ h tp +
          (scalarPsi κ h (-s1) - scalarPsi κ h (-s2)) / 2 : ℝ) : EReal) ≤ gibbsRateFIN081 κ h x := by
  have hm1 : psiDerivFIN056 κ h (-s1) = 0 := (psiDeriv_zero_iff_FIN082 hκ hG _).2 (Or.inr (Or.inl rfl))
  have hUb : ufFIN081 κ h (besselRatio (-s1)) = scalarPsi κ h (-s1) := uf_ratio_FIN081 hκ.ne' h hm1
  have hB : 0 < scalarPsi κ h (-s1) - scalarPsi κ h (-s2) := hG.2.2.2.2.2.2.2.1.1
  have hmem := ratio_mem_FIN081 (-s1)
  have hcont : ContinuousAt (ufFIN081 κ h) (besselRatio (-s1)) :=
    (hasDerivAt_uf_FIN081 κ h hmem).continuousAt
  have hev : ∀ᶠ x in 𝓝 (besselRatio (-s1)),
      ufFIN081 κ h (besselRatio (-s1)) - (scalarPsi κ h (-s1) - scalarPsi κ h (-s2)) / 2 <
        ufFIN081 κ h x :=
    hcont.eventually (lt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ x in 𝓝 (besselRatio (-s1)), x ∈ Set.Ioo (-1 : ℝ) 1 := Ioo_mem_nhds hmem.1 hmem.2
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hev.and hev2)
  refine ⟨ε / 2, by positivity, fun x hx => ?_⟩
  have hd : dist x (besselRatio (-s1)) < ε := by
    rw [Real.dist_eq]; linarith
  obtain ⟨h1, h2⟩ := hball hd
  rw [gibbsRate_eq_FIN081 hκ hG h2]
  refine EReal.coe_le_coe_iff.2 ?_
  rw [hUb] at h1
  linarith

theorem step_FIN082 (δ : ℝ) (hδ : 0 < δ) (mb : ℝ) :
    ContDiff ℝ ∞ (fun m : ℝ => Real.smoothTransition ((mb + δ - m) / (2 * δ))) ∧
      (∀ m, 0 ≤ Real.smoothTransition ((mb + δ - m) / (2 * δ)) ∧
        Real.smoothTransition ((mb + δ - m) / (2 * δ)) ≤ 1) ∧
      (∀ m, m ≤ mb - δ → Real.smoothTransition ((mb + δ - m) / (2 * δ)) = 1) ∧
      (∀ m, mb + δ ≤ m → Real.smoothTransition ((mb + δ - m) / (2 * δ)) = 0) := by
  refine ⟨?_, fun m => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
    fun m hm => Real.smoothTransition.one_of_one_le ?_,
    fun m hm => Real.smoothTransition.zero_of_nonpos ?_⟩
  · exact (Real.smoothTransition.contDiff (n := ⊤)).comp
      ((contDiff_const.sub contDiff_id).div_const _)
  · rw [le_div_iff₀ (by positivity)]; linarith
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

end Geometry


end DGPS.FiniteN.FalseMinimumFIN082

namespace DGPS.FiniteN

open DGPS.FiniteN.FalseMinimumFIN082 DGPS.FiniteN.FalseMinimumFIN081
  DGPS.FiniteN.FalseMinimumFIN076 DGPS.Models DGPS.FiniteN.ScalarFoldFIN056

/-- **False-minimum branch cutoff mass exponent.**

For `κ > 2` and `0 < h < h_c(κ)`, with the roots `s1, s2, tp` of `FalseMinimumGeometryFIN076`
(`m_- = g(-s2)`, `m_b = g(-s1)`, `m_+ = g(tp)`) and `G = ψ(-s2) - ψ(tp) = J(m_-) > 0`, there
is `δ₀ > 0` such that for every `0 < δ ≤ δ₀`:

* `m_- < m_b - δ` and `m_b + δ < m_+` (the window `[m_b - δ, m_b + δ]` excludes `m_±`);
* `J_δ = inf_{|m - m_b| ≤ δ} J(m) > G`;
* a smooth cutoff `χ` with `0 ≤ χ ≤ 1`, `χ = 1` on `m ≤ m_b - δ`, `χ = 0` on `m ≥ m_b + δ`
  exists, and for every such `χ` the mass `n_N = P_N(χ(m_N)²)` satisfies
  `N⁻¹ log n_N → -G`, while the transition probability `P_N(m_N ∈ [m_b - δ, m_b + δ])` has
  `limsup N⁻¹ log (·) ≤ -J_δ < -G`. -/
theorem false_minimum_branch_cutoff_mass_exponent :
    ∀ κ h : ℝ, 2 < κ → 0 < h → h < scalarFoldField κ →
      ∃ s1 s2 tp : ℝ, 0 < s1 ∧ s1 < scalarFoldPoint κ ∧ scalarFoldPoint κ < s2 ∧ 0 < tp ∧
        FalseMinimumGeometryFIN076 κ h s1 s2 tp ∧
        ∃ G : ℝ, 0 < G ∧ G = scalarPsi κ h (-s2) - scalarPsi κ h tp ∧
          gibbsRateFIN081 κ h (besselRatio (-s2)) = (G : EReal) ∧
          ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
            besselRatio (-s2) < besselRatio (-s1) - δ ∧
            besselRatio (-s1) + δ < besselRatio tp ∧
            (G : EReal) < ⨅ x ∈ Set.Icc (besselRatio (-s1) - δ) (besselRatio (-s1) + δ),
              gibbsRateFIN081 κ h x ∧
            (∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
              (∀ x, x ≤ besselRatio (-s1) - δ → χ x = 1) ∧
              (∀ x, besselRatio (-s1) + δ ≤ x → χ x = 0)) ∧
            ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
              (∀ x, x ≤ besselRatio (-s1) - δ → χ x = 1) →
              (∀ x, besselRatio (-s1) + δ ≤ x → χ x = 0) →
              Tendsto (fun N : ℕ+ => ((N : ℝ)⁻¹) * Real.log (cutoffMassFIN082 κ h χ N)) atTop
                  (nhds (-G)) ∧
                Filter.limsup (fun N : ℕ+ => gibbsLogProbFIN081 κ h N
                    (Set.Icc (besselRatio (-s1) - δ) (besselRatio (-s1) + δ))) Filter.atTop ≤
                  -(⨅ x ∈ Set.Icc (besselRatio (-s1) - δ) (besselRatio (-s1) + δ),
                    gibbsRateFIN081 κ h x) ∧
                -(⨅ x ∈ Set.Icc (besselRatio (-s1) - δ) (besselRatio (-s1) + δ),
                    gibbsRateFIN081 κ h x) < -(G : EReal) := by
  intro κ h hκ hh0 hhc
  obtain ⟨s1, s2, tp, hs1, hs1', hs2', htp, hG⟩ := general_FIN076 κ h hκ hh0 hhc
  have hκ0 : 0 < κ := by linarith
  have hs12 : s1 < s2 := by linarith
  have hGpos : 0 < scalarPsi κ h (-s2) - scalarPsi κ h tp := hG.2.2.2.2.2.2.2.2.1
  have hBpos : 0 < scalarPsi κ h (-s1) - scalarPsi κ h (-s2) := hG.2.2.2.2.2.2.2.1.1
  have hcrit := hG.2.2.2.1
  set G : ℝ := scalarPsi κ h (-s2) - scalarPsi κ h tp with hGdef
  set B : ℝ := scalarPsi κ h (-s1) - scalarPsi κ h (-s2) with hBdef
  have hJm : gibbsRateFIN081 κ h (besselRatio (-s2)) = (G : EReal) :=
    gibbsRate_critical_FIN081 hκ0 hG ((hcrit _).2 (Or.inl rfl))
  refine ⟨s1, s2, tp, hs1, hs1', hs2', htp, hG, G, hGpos, rfl, hJm, ?_⟩
  obtain ⟨η, hη, hnear⟩ := rate_ge_near_FIN082 hκ0 hG
  have hlt1 : besselRatio (-s2) < besselRatio (-s1) := strictMono_ratio (by linarith)
  have hlt2 : besselRatio (-s1) < besselRatio tp := strictMono_ratio (by linarith)
  refine ⟨min η (min ((besselRatio (-s1) - besselRatio (-s2)) / 2)
    ((besselRatio tp - besselRatio (-s1)) / 2)), ?_, ?_⟩
  · refine lt_min hη (lt_min ?_ ?_) <;> linarith
  intro δ hδ hδ0
  have hδη : δ ≤ η := le_trans hδ0 (min_le_left _ _)
  have hδ1 : δ ≤ (besselRatio (-s1) - besselRatio (-s2)) / 2 :=
    le_trans hδ0 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ2 : δ ≤ (besselRatio tp - besselRatio (-s1)) / 2 :=
    le_trans hδ0 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hwin : ((G + B / 2 : ℝ) : EReal) ≤
      ⨅ x ∈ Set.Icc (besselRatio (-s1) - δ) (besselRatio (-s1) + δ), gibbsRateFIN081 κ h x := by
    refine le_iInf₂ fun x hx => hnear x ?_
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hGlt : (G : EReal) < ⨅ x ∈ Set.Icc (besselRatio (-s1) - δ) (besselRatio (-s1) + δ),
      gibbsRateFIN081 κ h x :=
    lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by linarith)) hwin
  refine ⟨by linarith, by linarith, hGlt, ?_, ?_⟩
  · obtain ⟨c1, c2, c3, c4⟩ := step_FIN082 δ hδ (besselRatio (-s1))
    exact ⟨_, c1, c2, c3, c4⟩
  intro χ hχ hχ01 hχ1 hχ0
  have hχc : Continuous χ := hχ.continuous
  refine ⟨?_, ?_, EReal.neg_lt_neg_iff.2 hGlt⟩
  · refine tendsto_cutoff_mass_FIN082 κ h hχc (fun x => (hχ01 x).1) (fun x => (hχ01 x).2)
      (a := besselRatio (-s1) - δ) (b := besselRatio (-s1) + δ)
      (fun x hx => hχ1 x hx.le) (fun x hx => hχ0 x hx.le) ?_ ?_
    · refine le_trans (iInf₂_le (besselRatio (-s2)) ?_) hJm.le
      exact (Set.mem_Iio.2 (by linarith))
    · refine le_iInf₂ fun x hx => ?_
      by_cases hxb : x ≤ besselRatio (-s1)
      · exact rate_ge_left_FIN082 hκ0 hG hs12 hs1 htp hxb
      · have : x ∈ Set.Icc (besselRatio (-s1) - δ) (besselRatio (-s1) + δ) :=
          ⟨by linarith [not_le.1 hxb], hx⟩
        refine le_trans ?_ (le_trans hwin (iInf₂_le x this))
        exact EReal.coe_le_coe_iff.2 (by linarith)
  · exact gibbs_upper_FIN081 κ h isClosed_Icc

end DGPS.FiniteN
