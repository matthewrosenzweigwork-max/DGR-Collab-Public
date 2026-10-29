import SharpSymmetricLSI.Paper.LyapSchmidt6

/-!
# Section 4.2 (lane s42; R14): the implicit function `y(a)` of (4.5)

The implicit function theorem (Mathlib's `ContDiffAt.implicitFunction`) applied to `FC` at `0`
gives `ψ` with `ψ 0 = 0`, `Dψ(0) = 0`, `FC (a, ψ a) = 0` near `0`, and local uniqueness. Applying
it again at nearby points of the graph (where `∂_y FC` stays invertible) and using uniqueness
shows that `ψ` is `C^∞` on a whole ball.
-/

noncomputable section
open MeasureTheory Filter Real Topology Metric
open scoped ContDiff

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section ift
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis' W μ φ)

/-- `∂_y FC p`. -/
def DyFC (p : EuclideanSpace ℝ (Fin n) × CT d) : CT d →L[ℝ] CT d :=
  (fderiv ℝ (FC hyp hφ) p).comp (ContinuousLinearMap.inr ℝ _ _)

include hμ

theorem isInvertible_DyFC_zero : (DyFC hyp hφ 0).IsInvertible := by
  rw [DyFC, fderiv_FC_inr]; exact isInvertible_one_add_TP hyp hμ hφ

theorem eventually_isInvertible_DyFC :
    ∀ᶠ p in 𝓝 (0 : EuclideanSpace ℝ (Fin n) × CT d), (DyFC hyp hφ p).IsInvertible := by
  have h1 : ContinuousOn (fderiv ℝ (FC hyp hφ)) (OC hyp hφ) :=
    (contDiffOn_FC hyp hφ).continuousOn_fderiv_of_isOpen (isOpen_OC hyp hφ) (by simp)
  have h2 := h1.continuousAt ((isOpen_OC hyp hφ).mem_nhds (zero_mem_OC hyp hφ))
  have hc : ContinuousAt (DyFC hyp hφ) 0 := h2.clm_comp continuousAt_const
  have ho : IsOpen (Set.range ((↑) : (CT d ≃L[ℝ] CT d) → CT d →L[ℝ] CT d)) :=
    ContinuousLinearEquiv.isOpen
  obtain ⟨e, he⟩ := isInvertible_DyFC_zero hyp hμ hφ
  filter_upwards [hc.preimage_mem_nhds (ho.mem_nhds ⟨e, he⟩)] with p ⟨e', he'⟩
  exact ⟨e', he'⟩

/-- **The implicit function of (4.5).** -/
theorem exists_implicit :
    ∃ ψ : EuclideanSpace ℝ (Fin n) → CT d, ψ 0 = 0 ∧
      HasFDerivAt ψ (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] CT d) 0 ∧
      (∃ ε > 0, ContDiffOn ℝ ∞ ψ (ball 0 ε) ∧
        ∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε,
          FC hyp hφ (a, ψ a) = 0 ∧ (a, ψ a) ∈ OC hyp hφ) ∧
      ∃ N ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n) × CT d),
        ∀ p ∈ N, FC hyp hφ p = 0 → ψ p.1 = p.2 := by
  have pn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have cdf : ContDiffAt ℝ ∞ (FC hyp hφ) 0 := contDiffAt_FC hyp hφ (zero_mem_OC hyp hφ)
  have if₂ : ((fderiv ℝ (FC hyp hφ) 0).comp (ContinuousLinearMap.inr ℝ _ _)).IsInvertible :=
    isInvertible_DyFC_zero hyp hμ hφ
  set ψ := cdf.implicitFunction pn if₂ with hψ
  have hψ0 : ψ 0 = 0 := by
    have := cdf.implicitFunction_apply_self pn if₂
    simpa using this
  have hder := cdf.hasStrictFDerivAt_implicitFunction pn if₂
  rw [fderiv_FC_inl hyp hφ, ContinuousLinearMap.comp_zero, neg_zero] at hder
  have hψc : ContinuousAt ψ 0 := by simpa using hder.continuousAt
  have hU := cdf.eventually_apply_eq_iff_implicitFunction pn if₂
  rw [FC_zero] at hU
  have hZ := cdf.eventually_apply_implicitFunction pn if₂
  simp only [Prod.fst_zero, FC_zero] at hZ
  -- an open neighbourhood with uniqueness
  obtain ⟨N₀, hN₀U, hN₀o, hN₀0⟩ := _root_.mem_nhds_iff.mp hU
  -- the good set
  have hG : {p : EuclideanSpace ℝ (Fin n) × CT d |
      p ∈ OC hyp hφ ∧ (DyFC hyp hφ p).IsInvertible ∧ p ∈ N₀} ∈ 𝓝 0 :=
    Filter.inter_mem ((isOpen_OC hyp hφ).mem_nhds (zero_mem_OC hyp hφ))
      (Filter.inter_mem (eventually_isInvertible_DyFC hyp hμ hφ) (hN₀o.mem_nhds hN₀0))
  have hgraph : ContinuousAt (fun a => (a, ψ a)) 0 := continuousAt_id.prodMk hψc
  have hA : ∀ᶠ a in 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      ((a, ψ a) ∈ OC hyp hφ ∧ (DyFC hyp hφ (a, ψ a)).IsInvertible ∧ (a, ψ a) ∈ N₀) ∧
        FC hyp hφ (a, ψ a) = 0 := by
    have hG' : {p : EuclideanSpace ℝ (Fin n) × CT d |
        p ∈ OC hyp hφ ∧ (DyFC hyp hφ p).IsInvertible ∧ p ∈ N₀} ∈ 𝓝 ((0 : EuclideanSpace ℝ (Fin n)),
          ψ 0) := by
      rw [hψ0]; exact hG
    have hpre := hgraph.preimage_mem_nhds hG'
    filter_upwards [hpre, hZ] with a ha hb
    exact ⟨ha, hb⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hA
  refine ⟨ψ, hψ0, hder.hasFDerivAt, ⟨ε, hε, ?_, fun a ha => ⟨(hball a ha).2, (hball a ha).1.1⟩⟩,
    N₀, hN₀o.mem_nhds hN₀0, fun p hp hFp => (hN₀U hp).mp hFp⟩
  -- smoothness at every point of the ball
  intro a₀ ha₀
  obtain ⟨⟨hO, hI, hN⟩, hF0⟩ := hball a₀ ha₀
  set p₀ : EuclideanSpace ℝ (Fin n) × CT d := (a₀, ψ a₀)
  have cdf₀ : ContDiffAt ℝ ∞ (FC hyp hφ) p₀ := contDiffAt_FC hyp hφ hO
  set ψ₀ := cdf₀.implicitFunction pn hI with hψ₀
  have h1 : ψ₀ a₀ = ψ a₀ := cdf₀.implicitFunction_apply_self pn hI
  have h2 := cdf₀.eventually_apply_implicitFunction pn hI
  rw [hF0] at h2
  have h3 : ContDiffAt ℝ ∞ ψ₀ a₀ := cdf₀.contDiffAt_implicitFunction pn hI
  have h4 : ContinuousAt (fun a => (a, ψ₀ a)) a₀ := continuousAt_id.prodMk h3.continuousAt
  have h5 : ∀ᶠ a in 𝓝 a₀, (a, ψ₀ a) ∈ N₀ := h4.preimage_mem_nhds (by
    rw [show (a₀, ψ₀ a₀) = p₀ by rw [h1]]; exact hN₀o.mem_nhds hN)
  have h6 : ψ =ᶠ[𝓝 a₀] ψ₀ := by
    filter_upwards [h2, h5] with a ha hb
    exact ((hN₀U hb).mp ha)
  exact (h3.congr_of_eventuallyEq h6).contDiffWithinAt

end ift

end SharpLSI
