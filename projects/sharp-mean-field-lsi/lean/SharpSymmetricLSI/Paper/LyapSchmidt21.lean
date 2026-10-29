import SharpSymmetricLSI.Paper.LyapSchmidt20

/-!
# Section 4.2 (lane s42; R14): the Lyapunov–Schmidt parametrization, final form

`lyapunov_schmidt_aux` is the conclusion of R14 `lyapunov_schmidt` (stated with the copies
`IsKerBasis'`, `gLS'`, `elDens` of `IsKerBasis`, `gLS`, `elDensity`), and
`minSet_topological_chart_aux` that of R14 `minSet_topological_chart`.
-/

noncomputable section
open MeasureTheory Filter Real Topology Metric
open scoped ENNReal ContDiff

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section assemble
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis' W μ φ)
include hyp hμ hφ

open Classical in
/-- **R14 `lyapunov_schmidt`.** -/
theorem lyapunov_schmidt_aux (hr : 0 < rStar V W) :
    let k : EuclideanSpace ℝ (Fin n) → Torus d → ℝ := fun a x => ∑ i, a i * φ i x
    let p := elDens V W μ
    ∃ ε : ℝ, 0 < ε ∧ ∃ y : EuclideanSpace ℝ (Fin n) → Torus d → ℝ,
    ∃ Y : EuclideanSpace ℝ (Fin n) → Lp ℝ ⊤ (haar d) × (Fin d → Lp ℝ ⊤ (haar d)),
      (∀ a, HasWeakGrad (y a) ∧ ((Y a).1 : Torus d → ℝ) =ᵐ[haar d] y a ∧
        ∀ j, ((Y a).2 j : Torus d → ℝ) =ᵐ[haar d] fun x => weakGrad (y a) x j) ∧
      ContDiffOn ℝ ∞ Y (ball 0 ε) ∧ Y 0 = 0 ∧ fderiv ℝ Y 0 = 0 ∧
      (∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε, ∫ x, y a x ∂(μ : Measure (Torus d)) = 0 ∧
        ∀ i, ∫ x, y a x * φ i x ∂(μ : Measure (Torus d)) = 0) ∧
      (∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε, ∃ b : Fin n → ℝ,
        gLS' W μ (fun x => k a x + y a x) =ᵐ[(μ : Measure (Torus d))] fun x => ∑ i, b i * φ i x) ∧
      (∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε,
        (∀ x, 0 < 1 + k a x + y a x) ∧
        freeEnergy V W (densMeasure fun x => p x * (1 + k a x + y a x)) = Fstar V W) ∧
      (∃ U : Set (ProbabilityMeasure (Torus d)), IsOpen U ∧ μ ∈ U ∧
        ∃ e : ball (0 : EuclideanSpace ℝ (Fin n)) ε ≃ₜ
            {ν : ProbabilityMeasure (Torus d) // ν ∈ U ∧ IsMinimizer V W ν},
          ∀ a, ((e a : ProbabilityMeasure (Torus d)) : Measure (Torus d)) =
            densMeasure fun x => p x * (1 + k a x + y a x)) ∧
      (∃ (Z : EuclideanSpace ℝ (Fin n) → Lp ℝ 2 (μ : Measure (Torus d)))
          (ι : EuclideanSpace ℝ (Fin n) →L[ℝ] Lp ℝ 2 (μ : Measure (Torus d))),
        (∀ a, (Z a : Torus d → ℝ) =ᵐ[(μ : Measure (Torus d))] fun x => k a x + y a x) ∧
        (∀ a, (ι a : Torus d → ℝ) =ᵐ[(μ : Measure (Torus d))] k a) ∧
        HasFDerivAt Z ι 0) := by
  intro k p
  set μm := (μ : Measure (Torus d))
  obtain ⟨ψ, hψ0, hψd, ε, hε, hψs, hgr, U, hUo, hμU, eH, heH⟩ := minimizer_chart hyp hμ hφ hr
  let B := ball (0 : EuclideanSpace ℝ (Fin n)) ε
  set yC : EuclideanSpace ℝ (Fin n) → CT d := fun a => if a ∈ B then ψ a else 0 with hyC
  set y : EuclideanSpace ℝ (Fin n) → Torus d → ℝ :=
    fun a x => yC a x + (kC hyp hφ a x - k a x) with hy
  have hky : ∀ a x, k a x + y a x = kC hyp hφ a x + yC a x := fun a x => by
    simp only [hy]; ring
  have hyCB : ∀ a ∈ B, yC a = ψ a := fun a ha => by simp [hyC, ha]
  -- `kC a = k a` almost everywhere
  have hkCae : ∀ a, (⇑(kC hyp hφ a)) =ᵐ[μm] k a := fun a => by
    have hall : ∀ᵐ x ∂μm, ∀ i, phiC hyp hφ i x = φ i x :=
      ae_all_iff.mpr fun i => phiC_ae hyp hφ i
    filter_upwards [hall] with x hx
    rw [kC_apply]; simp only [k, hx]
  have hyae : ∀ a, y a =ᵐ[μm] yC a := fun a => by
    filter_upwards [hkCae a] with x hx
    simp only [hy, hx, sub_self, add_zero]
  have hyae' : ∀ a, y a =ᵐ[haar d] yC a := fun a => haar_ae_of_ae hyp hμ hφ (hyae a)
  -- the `L^∞` data
  set hg : EuclideanSpace ℝ (Fin n) → CT d := fun a => kC hyp hφ a + ψ a with hhg
  set bb : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun a => bOp hyp hφ (PhiC hyp μm (hg a)) with hbb
  set Yb : EuclideanSpace ℝ (Fin n) → Linf d × (Fin d → Linf d) :=
    fun a => (toLinf (ψ a), fun j => gradL hyp hμ hφ a (hg a) (bb a) j) with hYb
  set Y : EuclideanSpace ℝ (Fin n) → Lp ℝ ⊤ (haar d) × (Fin d → Lp ℝ ⊤ (haar d)) :=
    fun a => if a ∈ B then Yb a else 0 with hY
  obtain ⟨hYbs, hYb0, hYbd⟩ := Yb_props hyp hμ hφ hψ0 hψd hψs hε fun a ha => (hgr a ha).2.2.1
  have hYB : ∀ a ∈ B, Y a = Yb a := fun a ha => by simp [hY, ha]
  have h0B : (0 : EuclideanSpace ℝ (Fin n)) ∈ B := mem_ball_self hε
  refine ⟨ε, hε, y, Y, fun a => ?_, ?_, ?_, ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_,
    ⟨U, hUo, hμU, eH, fun a => ?_⟩, ?_⟩
  · -- weak gradients and the `L^∞` representatives
    by_cases ha : a ∈ B
    · obtain ⟨hY', hz, hpos, -⟩ := hgr a ha
      have hh0 := mean_kC_add hyp hμ hφ (e := a) hY'
      have hP := PhiC_eq_of_zero hyp hφ hz
      have h1 := isWeakGrad_graph hyp hμ hφ hpos hh0 hP
      have h2 := isWeakGrad_kC hyp hμ hφ a
      have h3 := h1.add (h2.cmul (-1))
      have hψeq : (fun x => (kC hyp hφ a + ψ a) x + -1 * kC hyp hφ a x) = ⇑(ψ a) := by
        funext x; simp only [ContinuousMap.add_apply]; ring
      rw [hψeq] at h3
      have h4 : (⇑(ψ a)) =ᵐ[haar d] y a := by
        filter_upwards [hyae' a] with x hx; rw [hx, hyCB a ha]
      have h5 := h3.congr_ae h4
      refine ⟨⟨_, h5⟩, ?_, fun j => ?_⟩
      · rw [hYB a ha]
        filter_upwards [toLinf_ae (ψ a), h4] with x h6 h7
        simp only [hYb]; rw [h6, h7]
      · rw [hYB a ha]
        have h6 := weakGrad_ae_eq h5
        filter_upwards [gradL_ae hyp hμ hφ a (bb a) (hg a) j, h6] with x h7 h8
        simp only [hYb]
        rw [h7, h8]
        simp only [hbb, hhg, ContinuousMap.add_apply]
        have hb : ∀ i, (bOp hyp hφ (PhiC hyp μm (kC hyp hφ a + ψ a))).ofLp i =
            bvec hyp hφ (kC hyp hφ a + ψ a) i := fun i => rfl
        simp only [hb]
        ring
    · have hy0 : y a =ᵐ[haar d] 0 := by
        filter_upwards [hyae' a] with x hx; rw [hx]; simp [hyC, ha]
      have h1 : IsWeakGrad (y a) 0 := (isWeakGrad_const (ι := Fin d) (0 : ℝ)).congr_ae
        (hy0.symm.trans (Eventually.of_forall fun x => rfl))
      refine ⟨⟨_, h1⟩, ?_, fun j => ?_⟩
      · have : Y a = 0 := by simp [hY, ha]
        rw [this]
        filter_upwards [Lp.coeFn_zero ℝ ⊤ (haar d), hy0] with x h2 h3
        simp only [Prod.fst_zero]; rw [h2, h3]
      · have : Y a = 0 := by simp [hY, ha]
        rw [this]
        filter_upwards [Lp.coeFn_zero ℝ ⊤ (haar d), weakGrad_ae_eq h1] with x h2 h3
        simp only [Prod.snd_zero, Pi.zero_apply]; rw [h2, h3]; rfl
  · -- smoothness
    exact hYbs.congr fun a ha => hYB a ha
  · -- `Y 0 = 0`
    rw [hYB 0 h0B]; exact hYb0
  · -- `DY(0) = 0`
    have hev : Y =ᶠ[𝓝 0] Yb := by
      filter_upwards [isOpen_ball.mem_nhds h0B] with a ha
      exact hYB a ha
    exact (hYbd.congr_of_eventuallyEq hev).fderiv
  · -- orthogonality
    obtain ⟨hY', -, -, -⟩ := hgr a ha
    obtain ⟨h1, h2⟩ := (mem_YC hyp hφ).mp hY'
    refine ⟨?_, fun i => ?_⟩
    · rw [integral_congr_ae (hyae a), hyCB a ha, h1]
    · have : (fun x => y a x * φ i x) =ᵐ[μm] fun x => ψ a x * phiC hyp hφ i x := by
        filter_upwards [hyae a, phiC_ae hyp hφ i] with x hx hx'
        rw [hx, hx', hyCB a ha]
      rw [integral_congr_ae this, h2 i]
  · -- (4.5)
    obtain ⟨-, hz, hpos, -⟩ := hgr a ha
    refine ⟨bvec hyp hφ (kC hyp hφ a + ψ a), ?_⟩
    have hfun : (fun x => k a x + y a x) = ⇑(kC hyp hφ a + ψ a) := by
      funext x; rw [hky, hyCB a ha]; rfl
    rw [hfun]
    have hall : ∀ᵐ x ∂μm, ∀ i, phiC hyp hφ i x = φ i x :=
      ae_all_iff.mpr fun i => phiC_ae hyp hφ i
    filter_upwards [hall] with x hx
    rw [gLS'_eq hyp hφ hpos x, PhiC_eq_of_zero hyp hφ hz x]
    simp only [hx]
    ring
  · -- minimizers
    obtain ⟨hY', hz, hpos, hΨ⟩ := hgr a ha
    have hh0 := mean_kC_add hyp hμ hφ (e := a) hY'
    obtain ⟨h0, h1⟩ := graph_density_props hyp hμ hpos hh0
    have hp := isProbabilityMeasure_densMeasure' (fun x => (h0 x).le) h1
    have hmin := (graph_point_minimizer hyp hμ hpos hh0 hΨ hp).1
    have hfun : (fun x => p x * (1 + k a x + y a x)) =
        fun x => elDens V W μm x * (1 + (kC hyp hφ a + ψ a) x) := by
      funext x; rw [add_assoc, hky, hyCB a ha]; rfl
    refine ⟨fun x => ?_, ?_⟩
    · rw [add_assoc, hky, hyCB a ha]; exact hpos x
    · rw [hfun]; exact hmin
  · -- the homeomorphism
    refine (heH a).trans ?_
    congr 1
    funext x
    rw [add_assoc, hky, hyCB a a.2]
    rfl
  · -- the tangent space
    set toL2 : CT d →L[ℝ] Lp ℝ 2 μm := ContinuousMap.toLp (E := ℝ) 2 μm ℝ
    refine ⟨fun a => toL2 (kC hyp hφ a + yC a), toL2.comp (kC hyp hφ), fun a => ?_, fun a => ?_, ?_⟩
    · filter_upwards [ContinuousMap.coeFn_toLp (E := ℝ) (μ := μm) (p := 2) (𝕜 := ℝ)
        (kC hyp hφ a + yC a)] with x hx
      rw [hx, hky]; rfl
    · filter_upwards [ContinuousMap.coeFn_toLp (E := ℝ) (μ := μm) (p := 2) (𝕜 := ℝ)
        (kC hyp hφ a), hkCae a] with x hx hx'
      simp only [ContinuousLinearMap.comp_apply]
      rw [hx, hx']
    · have hev : (fun a => toL2 (kC hyp hφ a + yC a)) =ᶠ[𝓝 0]
          fun a => toL2 (kC hyp hφ a + ψ a) := by
        filter_upwards [isOpen_ball.mem_nhds h0B] with a ha
        rw [hyCB a ha]
      have h1 : HasFDerivAt (fun a => kC hyp hφ a + ψ a) (kC hyp hφ) 0 := by
        have h' : HasFDerivAt (fun a => kC hyp hφ a + ψ a) (kC hyp hφ + 0) 0 :=
          (kC hyp hφ).hasFDerivAt.add hψd
        rw [add_zero] at h'
        exact h'
      exact (toL2.hasFDerivAt.comp 0 h1).congr_of_eventuallyEq hev

/-- **R14 `minSet_topological_chart`.** -/
theorem minSet_topological_chart_aux (hr : 0 < rStar V W) :
    ∃ U : Set (ProbabilityMeasure (Torus d)), IsOpen U ∧ μ ∈ U ∧
    ∃ O : Set (EuclideanSpace ℝ (Fin n)), IsOpen O ∧
      Nonempty ({ν : ProbabilityMeasure (Torus d) // ν ∈ U ∧ IsMinimizer V W ν} ≃ₜ O) := by
  obtain ⟨ψ, -, -, ε, -, -, -, U, hUo, hμU, e, -⟩ := minimizer_chart hyp hμ hφ hr
  exact ⟨U, hUo, hμU, ball 0 ε, isOpen_ball, ⟨e.symm⟩⟩

end assemble

end SharpLSI
