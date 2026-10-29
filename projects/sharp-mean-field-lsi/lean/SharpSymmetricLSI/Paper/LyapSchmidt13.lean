import SharpSymmetricLSI.Paper.LyapSchmidt12

/-!
# Section 4.2 (lane s42; R14): the graph of (4.5) consists of minimizers

On the graph `h(a) = kC a + ψ(a)` of the implicit function, the reduced energy `Φ(a) = Ψ(h(a))`
equals `G(ρ_a)`, `ρ_a = p(1+h(a)) m`, and has gradient `b(a) = (⟨log(1+h) + T h, φᵢ⟩)ᵢ`;
`b` is smooth with `b(0) = 0`, `Db(0) = 0`. The mean-field inequality `r_* > 0` and (4.6) give
`c Φ ≤ |b|²`, and the descent argument (`eq_zero_of_PL`) gives `Φ = 0` near `0`: every point of
the graph is a minimizer (manuscript, text after (4.6)).
-/

noncomputable section
open MeasureTheory InformationTheory Filter Real Topology Metric
open scoped ENNReal ContDiff

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section assembly
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis' W μ φ)

/-- `b` as a continuous linear map of `log(1+h) + T h`. -/
def bOp : CT d →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => pairC (μ : Measure (Torus d)) (phiC hyp hφ i))

theorem bOp_apply (h : CT d) (i : Fin n) :
    bOp hyp hφ (PhiC hyp (μ : Measure (Torus d)) h) i = bvec hyp hφ h i := rfl

theorem gap_nonneg' (hyp : Hyp V W KV KW) (ρ : ProbabilityMeasure (Torus d)) : 0 ≤ gap V W ρ := by
  have hF : Fstar V W ≤ freeEnergy V W ρ :=
    iInf_le (fun ρ' : ProbabilityMeasure (Torus d) => freeEnergy V W ρ') ρ
  have h1 := Fstar_eq_coe hyp
  unfold gap
  rw [EReal.sub_nonneg (Or.inr (by rw [h1]; exact EReal.coe_ne_top _))
    (Or.inr (by rw [h1]; exact EReal.coe_ne_bot _))]
  exact hF

include hyp hμ hφ

theorem pairC_kC_add {e : EuclideanSpace ℝ (Fin n)} {y : CT d} (hy : y ∈ YC hyp hφ) (i : Fin n) :
    ∫ x, (kC hyp hφ e + y) x * phiC hyp hφ i x ∂(μ : Measure (Torus d)) = e i := by
  obtain ⟨-, h2⟩ := (mem_YC hyp hφ).mp hy
  have i1 : Integrable (fun x => kC hyp hφ e x * phiC hyp hφ i x) (μ : Measure (Torus d)) :=
    integrable_of_continuous ((kC hyp hφ e).continuous.mul (phiC hyp hφ i).continuous)
  have i2 : Integrable (fun x => y x * phiC hyp hφ i x) (μ : Measure (Torus d)) :=
    integrable_of_continuous (y.continuous.mul (phiC hyp hφ i).continuous)
  simp only [ContinuousMap.add_apply, add_mul]
  rw [integral_add i1 i2, h2 i, add_zero, integral_kC_mul_phiC hyp hφ]

theorem mean_kC_add {e : EuclideanSpace ℝ (Fin n)} {y : CT d} (hy : y ∈ YC hyp hφ) :
    ∫ x, (kC hyp hφ e + y) x ∂(μ : Measure (Torus d)) = 0 := by
  obtain ⟨h1, -⟩ := (mem_YC hyp hφ).mp hy
  simp only [ContinuousMap.add_apply]
  rw [integral_add (integrable_of_continuous (kC hyp hφ e).continuous)
    (integrable_of_continuous y.continuous), h1, add_zero, integral_kC hyp hφ]

/-- **Every point of the graph near `0` is a minimizer** (`G(ρ_a) = 0`). -/
theorem graph_minimizers (hr : 0 < rStar V W) :
    ∃ ψ : EuclideanSpace ℝ (Fin n) → CT d, ψ 0 = 0 ∧
      HasFDerivAt ψ (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] CT d) 0 ∧
      (∃ ε > 0, ContDiffOn ℝ ∞ ψ (ball 0 ε) ∧
        ∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε,
          ψ a ∈ YC hyp hφ ∧
          QCraw hyp hφ (PhiC hyp (μ : Measure (Torus d)) (kC hyp hφ a + ψ a)) = 0 ∧
          kC hyp hφ a + ψ a ∈ posSet ∧
          PsiC hyp (μ : Measure (Torus d)) (kC hyp hφ a + ψ a) = 0) ∧
      ∃ N ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n) × CT d),
        ∀ q ∈ N, FC hyp hφ q = 0 → ψ q.1 = q.2 := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨ψ, hψ0, hψd, ⟨ε₀, hε₀, hψs, hψz⟩, N, hN, hNu⟩ := exists_implicit hyp hμ hφ
  -- the graph data
  have hgraph : ∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε₀,
      ψ a ∈ YC hyp hφ ∧ QCraw hyp hφ (PhiC hyp μm (kC hyp hφ a + ψ a)) = 0 ∧
        kC hyp hφ a + ψ a ∈ posSet := fun a ha => by
    obtain ⟨hF, hO⟩ := hψz a ha
    obtain ⟨h1, h2⟩ := (FC_eq_zero_iff hyp hφ (a, ψ a)).mp hF
    have h1' : QCraw hyp hφ (ψ a) = ψ a := h1
    have h2' : QCraw hyp hφ (PhiC hyp μm (kC hyp hφ a + ψ a)) = 0 := h2
    have h3 : ψ a ∈ YC hyp hφ := by rw [← h1']; exact QCraw_mem hyp hφ (ψ a)
    refine ⟨h3, h2', ?_⟩
    have hO' : LC hyp hφ (a, ψ a) ∈ posSet := hO
    rw [LC_apply] at hO'
    simpa only [h1'] using hO'
  set hg : EuclideanSpace ℝ (Fin n) → CT d := fun a => kC hyp hφ a + ψ a with hhg
  set Φ : EuclideanSpace ℝ (Fin n) → ℝ := fun a => PsiC hyp μm (hg a) with hΦ
  set bb : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun a => bOp hyp hφ (PhiC hyp μm (hg a)) with hbb
  have hψdiff : ∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε₀,
      HasFDerivAt ψ (fderiv ℝ ψ a) a := fun a ha =>
    ((hψs.differentiableOn (by simp)).differentiableAt
      (isOpen_ball.mem_nhds ha)).hasFDerivAt
  have hhgd : ∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε₀,
      HasFDerivAt hg (kC hyp hφ + fderiv ℝ ψ a) a := fun a ha =>
    (kC hyp hφ).hasFDerivAt.add (hψdiff a ha)
  -- the derivative of `ψ` takes values in `YC`
  have hDψY : ∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε₀, ∀ e,
      fderiv ℝ ψ a e ∈ YC hyp hφ := fun a ha e => by
    have h1 : HasFDerivAt (fun b => QCraw hyp hφ (ψ b)) ((QCraw hyp hφ).comp (fderiv ℝ ψ a)) a :=
      (QCraw hyp hφ).hasFDerivAt.comp a (hψdiff a ha)
    have h2 : (fun b => QCraw hyp hφ (ψ b)) =ᶠ[𝓝 a] ψ := by
      filter_upwards [isOpen_ball.mem_nhds ha] with b hb
      exact QCraw_of_mem hyp hφ (hgraph b hb).1
    have h3 := (h1.congr_of_eventuallyEq h2.symm).unique (hψdiff a ha)
    rw [← h3]
    exact QCraw_mem hyp hφ _
  -- `∇Φ = b`
  have hΦd : ∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε₀,
      HasFDerivAt Φ (innerSL ℝ (bb a)) a := fun a ha => by
    obtain ⟨hY, hz, hpos⟩ := hgraph a ha
    have h1 := (hasFDerivAt_PsiC hyp μm hpos).comp a (hhgd a ha)
    refine h1.congr_fderiv ?_
    ext e
    have hk0 : ∫ x, (kC hyp hφ e + fderiv ℝ ψ a e) x ∂μm = 0 :=
      mean_kC_add hyp hμ hφ (hDψY a ha e)
    have hh0 : ∫ x, hg a x ∂μm = 0 := mean_kC_add hyp hμ hφ hY
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      DPsiC_eq hyp hφ hz hh0 hk0, innerSL_apply_apply]
    simp_rw [pairC_kC_add hyp hμ hφ (hDψY a ha e)]
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    rw [hbb, bOp_apply]
    ring
  -- `b` is smooth on the ball
  have hbOp : ContDiff ℝ ∞ (fun u : CT d => bOp hyp hφ u) := by
    exact ContinuousLinearMap.contDiff _
  have hT : ContDiff ℝ ∞ (fun u : CT d => TC hyp μm u) := by exact ContinuousLinearMap.contDiff _
  have hkC : ContDiff ℝ ∞ (fun a : EuclideanSpace ℝ (Fin n) => kC hyp hφ a) := by
    exact ContinuousLinearMap.contDiff _
  have hhgs : ∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε₀, ContDiffAt ℝ ∞ hg a := fun a ha =>
    hkC.contDiffAt.add (hψs.contDiffAt (isOpen_ball.mem_nhds ha))
  have hbbs : ContDiffOn ℝ ∞ bb (ball 0 ε₀) := fun a ha => by
    have hPhi : ContDiffAt ℝ ∞ (PhiC hyp μm) (hg a) :=
      (contDiffAt_logC (hgraph a ha).2.2).add hT.contDiffAt
    have h1 : ContDiffAt ℝ ∞ (fun a => bOp hyp hφ (PhiC hyp μm (hg a))) a :=
      hbOp.contDiffAt.comp a (hPhi.comp a (hhgs a ha))
    exact h1.contDiffWithinAt
  have hg0 : hg 0 = 0 := by simp [hhg, hψ0]
  have hbb0 : bb 0 = 0 := by simp [hbb, hg0, PhiC, logC_zero]
  have hDψ0 : fderiv ℝ ψ 0 = 0 := hψd.fderiv
  have hDbb0 : fderiv ℝ bb 0 = 0 := by
    have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε₀ :=
      mem_ball_self hε₀
    have hpos0 : hg 0 ∈ posSet := (hgraph 0 h0).2.2
    have hP0 : HasFDerivAt (PhiC hyp μm) (logCDeriv (hg 0) + TC hyp μm) (hg 0) :=
      hasFDerivAt_PhiC hyp μm hpos0
    have hP : HasFDerivAt (fun a => PhiC hyp μm (hg a))
        ((logCDeriv (hg 0) + TC hyp μm).comp (kC hyp hφ + fderiv ℝ ψ 0)) 0 :=
      hP0.comp 0 (hhgd 0 h0)
    have h1 : HasFDerivAt bb ((bOp hyp hφ).comp ((logCDeriv (hg 0) + TC hyp μm).comp
        (kC hyp hφ + fderiv ℝ ψ 0))) 0 :=
      (bOp hyp hφ).hasFDerivAt.comp 0 hP
    rw [h1.fderiv, hg0, logCDeriv_zero, hDψ0, add_zero]
    ext e : 1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply]
    rw [TC_kC hyp hφ e, add_neg_cancel, map_zero]
  -- the PL constant
  obtain ⟨r₀, hr₀0, hr₀1, hr₀2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hr
  have hr₀ : 0 < r₀ := ENNReal.ofReal_pos.mp hr₀1
  obtain ⟨CD, hCD, hdiss⟩ := dissipation_graph_bound hyp hμ hφ
  set c := 2 * r₀ / CD with hc
  have hc0 : 0 < c := by positivity
  set L := c / 4 with hL
  have hL0 : 0 < L := by positivity
  -- a ball where `‖Db‖ ≤ L`
  have hDc : ContinuousAt (fderiv ℝ bb) 0 :=
    (hbbs.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).continuousAt
      (ball_mem_nhds 0 hε₀)
  obtain ⟨δ, hδ, hδL⟩ := Metric.continuousAt_iff.mp hDc L hL0
  set r₁ := min δ ε₀ with hr₁
  have hr₁0 : 0 < r₁ := lt_min hδ hε₀
  have hr₁ε : ball (0 : EuclideanSpace ℝ (Fin n)) r₁ ⊆ ball 0 ε₀ :=
    ball_subset_ball (min_le_right _ _)
  have hDbL : ∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r₁, ‖fderiv ℝ bb a‖ ≤ L := fun a ha => by
    have h1 := hδL (lt_of_lt_of_le (mem_ball.mp ha) (min_le_left _ _))
    rw [dist_eq_norm, hDbb0, sub_zero] at h1
    exact h1.le
  have hbdiff : ∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r₁, DifferentiableAt ℝ bb a :=
    fun a ha => (hbbs.differentiableOn (by simp)).differentiableAt
      (isOpen_ball.mem_nhds (hr₁ε ha))
  have hLip : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r₁, ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r₁,
      ‖bb x - bb y‖ ≤ L * ‖x - y‖ := fun x hx y hy =>
    (convex_ball (0 : EuclideanSpace ℝ (Fin n)) r₁).norm_image_sub_le_of_norm_fderiv_le
      hbdiff hDbL hy hx
  -- the PL inequality
  have hPL : ∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r₁, c * Φ a ≤ ‖bb a‖ ^ 2 ∧ 0 ≤ Φ a :=
    fun a ha => by
    obtain ⟨hY, hz, hpos⟩ := hgraph a (hr₁ε ha)
    have hh0 : ∫ x, hg a x ∂μm = 0 := mean_kC_add hyp hμ hφ hY
    have hP := PhiC_eq_of_zero hyp hφ hz
    obtain ⟨hH1, hD⟩ := hdiss (hg a) hpos hh0 _ (fun i => bvec hyp hφ (hg a) i) hP
    have hgap := gap_graph hyp hμ hpos hh0
    obtain ⟨h0, h1⟩ := graph_density_props hyp hμ hpos hh0
    haveI hρp := isProbabilityMeasure_densMeasure' (fun x => (h0 x).le) h1
    have hΦ0 : 0 ≤ Φ a := by
      have h' : 0 ≤ gap V W (densMeasure fun x => elDens V W μm x * (1 + hg a x)) :=
        gap_nonneg' hyp ⟨_, hρp⟩
      rw [hgap] at h'
      exact_mod_cast h'
    have hnorm : ‖bb a‖ ^ 2 = ∑ i, bvec hyp hφ (hg a) i ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.sum_congr rfl fun i _ => by rw [hbb, bOp_apply]
    refine ⟨?_, hΦ0⟩
    rcases hΦ0.eq_or_lt with hΦz | hΦp
    · rw [← hΦz, mul_zero]; positivity
    have hadm : Admissible V W (fun x => elDens V W μm x * (1 + hg a x)) := by
      refine ⟨fun x => (h0 x).le, h1, hH1, ?_⟩
      rw [hgap]; exact_mod_cast hΦp
    have hle : rStar V W ≤ dissipation V W (fun x => elDens V W μm x * (1 + hg a x)) /
        (2 * (gap V W (densMeasure fun x => elDens V W μm x * (1 + hg a x))).toENNReal) := by
      unfold rStar
      exact iInf₂_le _ hadm
    rw [hgap, EReal.real_coe_toENNReal] at hle
    have h2e : (2 : ℝ≥0∞) * ENNReal.ofReal (Φ a) = ENNReal.ofReal (2 * Φ a) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    rw [h2e] at hle
    have h2 : ENNReal.ofReal r₀ * ENNReal.ofReal (2 * Φ a) ≤
        dissipation V W (fun x => elDens V W μm x * (1 + hg a x)) :=
      (ENNReal.le_div_iff_mul_le (Or.inl (by simp; positivity)) (Or.inl ENNReal.ofReal_ne_top)).mp
        (hr₀2.le.trans hle)
    have h3 := h2.trans hD
    rw [← ENNReal.ofReal_mul hr₀0,
      ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCD.le (Finset.sum_nonneg fun i _ => sq_nonneg _))]
      at h3
    rw [hnorm, hc, div_mul_eq_mul_div, div_le_iff₀ hCD]
    nlinarith
  -- vanishing of the reduced energy
  have hzero := eq_zero_of_PL (Φ := Φ) (b := bb) (r := r₁) hL0 (by rw [hL]; linarith)
    (fun a ha => (hPL a ha).2) (fun a ha => hΦd a (hr₁ε ha)) hbb0 hLip (fun a ha => (hPL a ha).1)
  refine ⟨ψ, hψ0, hψd, ⟨r₁ / 2, by positivity,
    hψs.mono (ball_subset_ball (by linarith [min_le_right δ ε₀])), fun a ha => ?_⟩, N, hN, hNu⟩
  have ha' : a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε₀ :=
    ball_subset_ball (by linarith [min_le_right δ ε₀]) ha
  obtain ⟨hY, hz, hpos⟩ := hgraph a ha'
  exact ⟨hY, hz, hpos, hzero a ha⟩

end assembly

end SharpLSI
