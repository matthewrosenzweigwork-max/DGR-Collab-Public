import SharpSymmetricLSI.Paper.LyapSchmidt19

/-!
# Section 4.2 (lane s42; R14): assembly of the Lyapunov–Schmidt parametrization

`lyapunov_schmidt_aux` is the conclusion of R14 `lyapunov_schmidt` (with `gLS'`, `IsKerBasis'`,
`elDens` the copies of `gLS`, `IsKerBasis`, `elDensity`). The statement's `y(a)` is
`ψ(a) + (kC a - k a)` (`kC` uses the continuous representatives `-Tφᵢ` of `φᵢ`, `k` the `φᵢ`
themselves), so that `k a + y a = kC a + ψ a` everywhere; `y(a) = ψ(a)` almost everywhere.
-/

noncomputable section
open MeasureTheory Filter Real Topology Metric
open scoped ENNReal ContDiff

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- A copy of `gLS` from the R14 statement file. -/
def gLS' (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (h : Torus d → ℝ)
    (x : Torus d) : ℝ :=
  (Real.log (1 + h x) + ∫ y, W x y * h y ∂μ) -
    ∫ x', (Real.log (1 + h x') + ∫ y, W x' y * h y ∂μ) ∂μ

section final
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis' W μ φ)
include hyp hμ hφ

omit hμ in
theorem gLS'_eq {h : CT d} (hpos : h ∈ posSet) (x : Torus d) :
    gLS' W (μ : Measure (Torus d)) h x = PhiC hyp (μ : Measure (Torus d)) h x -
      ∫ x', PhiC hyp (μ : Measure (Torus d)) h x' ∂(μ : Measure (Torus d)) := by
  have hc : Continuous fun x => ∫ y, W x y * h y ∂(μ : Measure (Torus d)) :=
    cont_integral_right (cont_kernel_mul hyp.continuous_W h.continuous) (μ : Measure (Torus d))
  have hl : Continuous fun x => Real.log (1 + h x) :=
    (continuous_const.add h.continuous).log fun x => (hpos x).ne'
  have hP : ∀ x, PhiC hyp (μ : Measure (Torus d)) h x = Real.log (1 + h x) +
      ∫ y, W x y * h y ∂(μ : Measure (Torus d)) -
      ∫ x', (∫ y, W x' y * h y ∂(μ : Measure (Torus d))) ∂(μ : Measure (Torus d)) := fun x => by
    show logC h x + Top W (μ : Measure (Torus d)) (⇑h) x = _
    rw [logC_apply hpos]
    unfold Top
    ring
  have i1 : Integrable (fun x => Real.log (1 + h x) +
      ∫ y, W x y * h y ∂(μ : Measure (Torus d))) (μ : Measure (Torus d)) :=
    integrable_of_continuous (hl.add hc)
  rw [integral_congr_ae (Eventually.of_forall hP), hP x,
    integral_sub i1 (integrable_const _)]
  unfold gLS'
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

omit hyp hμ hφ in
theorem mulLinf_toLinf_one (g : Linf d) : mulLinf (toLinf (1 : CT d)) g = g := by
  refine Lp.ext ?_
  filter_upwards [mulLinf_ae (toLinf (1 : CT d)) g, toLinf_ae (1 : CT d)] with x h1 h2
  rw [h1, h2]; simp

/-- **The gradient package**: smoothness on the ball, value and derivative at `0`. -/
theorem Yb_props {ψ : EuclideanSpace ℝ (Fin n) → CT d} {ε : ℝ} (hψ0 : ψ 0 = 0)
    (hψd : HasFDerivAt ψ (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] CT d) 0)
    (hψs : ContDiffOn ℝ ∞ ψ (ball 0 ε)) (hε : 0 < ε)
    (hpos : ∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε, kC hyp hφ a + ψ a ∈ posSet) :
    ContDiffOn ℝ ∞ (fun a => (toLinf (ψ a), fun j => gradL hyp hμ hφ a (kC hyp hφ a + ψ a)
        (bOp hyp hφ (PhiC hyp (μ : Measure (Torus d)) (kC hyp hφ a + ψ a))) j)) (ball 0 ε) ∧
    (toLinf (ψ 0), fun j => gradL hyp hμ hφ 0 (kC hyp hφ 0 + ψ 0)
        (bOp hyp hφ (PhiC hyp (μ : Measure (Torus d)) (kC hyp hφ 0 + ψ 0))) j) = 0 ∧
    HasFDerivAt (fun a => (toLinf (ψ a), fun j => gradL hyp hμ hφ a (kC hyp hφ a + ψ a)
        (bOp hyp hφ (PhiC hyp (μ : Measure (Torus d)) (kC hyp hφ a + ψ a))) j))
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] Linf d × (Fin d → Linf d)) 0 := by
  set μm := (μ : Measure (Torus d))
  set hg : EuclideanSpace ℝ (Fin n) → CT d := fun a => kC hyp hφ a + ψ a with hhg
  set bb : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun a => bOp hyp hφ (PhiC hyp μm (hg a)) with hbb
  have hT : ContDiff ℝ ∞ (fun u : CT d => TC hyp μm u) := by exact ContinuousLinearMap.contDiff _
  have hkC : ContDiff ℝ ∞ (fun a : EuclideanSpace ℝ (Fin n) => kC hyp hφ a) := by
    exact ContinuousLinearMap.contDiff _
  have hbOp : ContDiff ℝ ∞ (fun u : CT d => bOp hyp hφ u) := by exact ContinuousLinearMap.contDiff _
  have htoL : ContDiff ℝ ∞ (fun u : CT d => toLinf u) := by exact ContinuousLinearMap.contDiff _
  have hmul : ContDiff ℝ ∞ (fun f : Linf d => mulLinf f) := by exact ContinuousLinearMap.contDiff _
  have hF : ∀ j, ContDiff ℝ ∞ (fun u : CT d => forceL hyp hμ j u) := fun j => by
    exact ContinuousLinearMap.contDiff _
  have hhgs : ContDiffOn ℝ ∞ hg (ball 0 ε) := hkC.contDiffOn.add hψs
  have hPhis : ContDiffOn ℝ ∞ (fun a => PhiC hyp μm (hg a)) (ball 0 ε) := fun a ha => by
    have h1 : ContDiffAt ℝ ∞ (PhiC hyp μm) (hg a) := (contDiffAt_logC (hpos a ha)).add hT.contDiffAt
    exact (h1.comp a (hhgs.contDiffAt (isOpen_ball.mem_nhds ha))).contDiffWithinAt
  have hbbs : ContDiffOn ℝ ∞ bb (ball 0 ε) := hbOp.comp_contDiffOn hPhis
  have hg0 : hg 0 = 0 := by simp [hhg, hψ0]
  have hbb0 : bb 0 = 0 := by simp [hbb, hg0, PhiC, logC_zero]
  refine ⟨?_, ?_, ?_⟩
  · refine (htoL.comp_contDiffOn hψs).prodMk (contDiffOn_pi.mpr fun j => ?_)
    have hA : ContDiffOn ℝ ∞ (fun a => forceL hyp hμ j (kC hyp hφ a)) (ball 0 ε) :=
      ((hF j).comp hkC).contDiffOn
    have hB : ContDiffOn ℝ ∞ (fun a => mulLinf (toLinf (1 + hg a))) (ball 0 ε) :=
      (hmul.comp htoL).comp_contDiffOn (contDiffOn_const.add hhgs)
    have hC : ContDiffOn ℝ ∞ (fun a => forceL hyp hμ j (hg a + kC hyp hφ (bb a))) (ball 0 ε) :=
      (hF j).comp_contDiffOn (hhgs.add (hkC.comp_contDiffOn hbbs))
    exact hA.sub (hB.clm_apply hC)
  · show (toLinf (ψ 0), fun j => gradL hyp hμ hφ 0 (hg 0) (bb 0) j) = 0
    rw [hg0, hbb0, hψ0]
    ext1
    · simp
    · funext j; simp [gradL]
  · -- the derivative at `0`
    have hψ' := hψd
    have hhg' : HasFDerivAt hg (kC hyp hφ) 0 := by
      have h' : HasFDerivAt (fun a => kC hyp hφ a + ψ a) (kC hyp hφ + 0) 0 :=
        (kC hyp hφ).hasFDerivAt.add hψd
      rw [add_zero] at h'
      exact h'
    have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε :=
      mem_ball_self hε
    have hpos0 : hg 0 ∈ posSet := hpos 0 h0
    have hP0 : HasFDerivAt (PhiC hyp μm) (logCDeriv (hg 0) + TC hyp μm) (hg 0) :=
      hasFDerivAt_PhiC hyp μm hpos0
    have hbb' : HasFDerivAt bb (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) 0 := by
      have h1 : HasFDerivAt (fun a => PhiC hyp μm (hg a))
          ((logCDeriv (hg 0) + TC hyp μm).comp (kC hyp hφ)) 0 := hP0.comp 0 hhg'
      have h2 : HasFDerivAt bb ((bOp hyp hφ).comp ((logCDeriv (hg 0) + TC hyp μm).comp
          (kC hyp hφ))) 0 := (bOp hyp hφ).hasFDerivAt.comp 0 h1
      refine h2.congr_fderiv ?_
      rw [hg0, logCDeriv_zero]
      ext e : 1
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply]
      rw [TC_kC hyp hφ e, add_neg_cancel, map_zero]
    have hfirst : HasFDerivAt (fun a => toLinf (ψ a))
        (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] Linf d) 0 := by
      have h' : HasFDerivAt (fun a => toLinf (ψ a)) (toLinf.comp 0) 0 :=
        toLinf.hasFDerivAt.comp 0 hψd
      rw [ContinuousLinearMap.comp_zero] at h'
      exact h'
    have hsecond : ∀ j, HasFDerivAt (fun a => gradL hyp hμ hφ a (hg a) (bb a) j)
        (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] Linf d) 0 := fun j => by
      have hA : HasFDerivAt (fun a => forceL hyp hμ j (kC hyp hφ a))
          ((forceL hyp hμ j).comp (kC hyp hφ)) 0 :=
        (forceL hyp hμ j).hasFDerivAt.comp 0 (kC hyp hφ).hasFDerivAt
      have hB0 : HasFDerivAt (fun a => toLinf (1 + hg a)) (toLinf.comp (kC hyp hφ)) 0 :=
        toLinf.hasFDerivAt.comp 0 (hhg'.const_add 1)
      have hB : HasFDerivAt (fun a => mulLinf (toLinf (1 + hg a)))
          (mulLinf.comp (toLinf.comp (kC hyp hφ))) 0 := mulLinf.hasFDerivAt.comp 0 hB0
      have hC0 : HasFDerivAt (fun a => hg a + kC hyp hφ (bb a)) (kC hyp hφ) 0 := by
        have h' : HasFDerivAt (fun a => hg a + kC hyp hφ (bb a))
            (kC hyp hφ + (kC hyp hφ).comp 0) 0 := hhg'.add ((kC hyp hφ).hasFDerivAt.comp 0 hbb')
        rw [ContinuousLinearMap.comp_zero, add_zero] at h'
        exact h'
      have hC : HasFDerivAt (fun a => forceL hyp hμ j (hg a + kC hyp hφ (bb a)))
          ((forceL hyp hμ j).comp (kC hyp hφ)) 0 := (forceL hyp hμ j).hasFDerivAt.comp 0 hC0
      have hBC := hB.clm_apply hC
      have hall := hA.sub hBC
      refine hall.congr_fderiv ?_
      rw [hg0, hbb0]
      ext e : 1
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, map_zero, add_zero,
        ContinuousLinearMap.zero_apply, zero_add, mulLinf_toLinf_one, sub_self]
    have hpi : HasFDerivAt (fun a => fun j => gradL hyp hμ hφ a (hg a) (bb a) j)
        (ContinuousLinearMap.pi fun _ => (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] Linf d)) 0 :=
      hasFDerivAt_pi.mpr hsecond
    have := hfirst.prodMk hpi
    refine this.congr_fderiv ?_
    ext1 e
    simp
    try rfl

end final

end SharpLSI
