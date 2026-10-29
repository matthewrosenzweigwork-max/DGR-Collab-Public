import SharpSymmetricLSI.Paper.LyapSchmidt15

/-!
# Section 4.2 (lane s42; R14): the homeomorphism onto a neighbourhood of `μ` in `𝒮`

`a ↦ ρ_a = p(1 + kC a + ψ a) m` is a homeomorphism (weak topology) from a ball onto
`{ν ∈ U : ν ∈ 𝒮}`, `U` a weakly open neighbourhood of `μ`; its inverse is `ν ↦ (∫ φᵢ dν)ᵢ`.
-/

noncomputable section
open MeasureTheory InformationTheory Filter Real Topology Metric BoundedContinuousFunction
open scoped ENNReal ContDiff

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

open Classical in
/-- The probability `p(1+h) m` (and `μ` if it is not one). -/
def rhoPM (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (μ : ProbabilityMeasure (Torus d))
    (h : CT d) : ProbabilityMeasure (Torus d) :=
  if hp : IsProbabilityMeasure (densMeasure fun x => elDens V W (μ : Measure (Torus d)) x *
      (1 + h x)) then ⟨_, hp⟩ else μ

theorem rhoPM_eq {μ : ProbabilityMeasure (Torus d)} {h : CT d}
    (hp : IsProbabilityMeasure (densMeasure fun x => elDens V W (μ : Measure (Torus d)) x *
      (1 + h x))) : rhoPM V W μ h = ⟨_, hp⟩ := dif_pos hp

section homeo
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis' W μ φ)
include hyp hμ hφ

/-- **The chart of `𝒮` near `μ`.** -/
theorem minimizer_chart (hr : 0 < rStar V W) :
    ∃ ψ : EuclideanSpace ℝ (Fin n) → CT d, ψ 0 = 0 ∧
      HasFDerivAt ψ (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] CT d) 0 ∧
      ∃ ε > 0, ContDiffOn ℝ ∞ ψ (ball 0 ε) ∧
        (∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε,
          ψ a ∈ YC hyp hφ ∧
          QCraw hyp hφ (PhiC hyp (μ : Measure (Torus d)) (kC hyp hφ a + ψ a)) = 0 ∧
          kC hyp hφ a + ψ a ∈ posSet ∧
          PsiC hyp (μ : Measure (Torus d)) (kC hyp hφ a + ψ a) = 0) ∧
        ∃ U : Set (ProbabilityMeasure (Torus d)), IsOpen U ∧ μ ∈ U ∧
          ∃ e : ball (0 : EuclideanSpace ℝ (Fin n)) ε ≃ₜ
              {ν : ProbabilityMeasure (Torus d) // ν ∈ U ∧ IsMinimizer V W ν},
            ∀ a, ((e a : ProbabilityMeasure (Torus d)) : Measure (Torus d)) =
              densMeasure fun x => elDens V W (μ : Measure (Torus d)) x *
                (1 + (kC hyp hφ a + ψ a) x) := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨ψ, hψ0, hψd, ⟨ε, hε, hψs, hgr⟩, N, hN, hNu⟩ := graph_minimizers hyp hμ hφ hr
  obtain ⟨N₀, hN₀N, hN₀o, hN₀0⟩ := _root_.mem_nhds_iff.mp hN
  -- a ball on which the graph stays in `N₀`
  have hgc : ContinuousAt (fun a => (a, ψ a)) (0 : EuclideanSpace ℝ (Fin n)) :=
    continuousAt_id.prodMk hψd.continuousAt
  have hev : ∀ᶠ a in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), (a, ψ a) ∈ N₀ :=
    hgc.preimage_mem_nhds (by rw [hψ0]; exact hN₀o.mem_nhds hN₀0)
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set ε₂ := min ε ε₁ with hε₂
  have hε₂0 : 0 < ε₂ := lt_min hε hε₁
  have hsub : ball (0 : EuclideanSpace ℝ (Fin n)) ε₂ ⊆ ball 0 ε := ball_subset_ball (min_le_left _ _)
  have hsub₁ : ball (0 : EuclideanSpace ℝ (Fin n)) ε₂ ⊆ ball 0 ε₁ :=
    ball_subset_ball (min_le_right _ _)
  -- the map `Θ`
  set Θ : ProbabilityMeasure (Torus d) → EuclideanSpace ℝ (Fin n) × CT d :=
    fun ν => (coordE hyp hφ ν, QCraw hyp hφ (hR hyp μ ν)) with hΘ
  have hΘc : Continuous Θ :=
    (continuous_coordE hyp hφ).prodMk ((QCraw hyp hφ).continuous.comp (continuous_hR hyp (μ := μ)))
  set S : Set (EuclideanSpace ℝ (Fin n) × CT d) :=
    N₀ ∩ (ball (0 : EuclideanSpace ℝ (Fin n)) ε₂ ×ˢ Set.univ) with hS
  set U : Set (ProbabilityMeasure (Torus d)) := Θ ⁻¹' S with hU
  have hmemU : ∀ ν, ν ∈ U ↔ Θ ν ∈ S := fun ν => Iff.rfl
  have hUo : IsOpen U := (hN₀o.inter (isOpen_ball.prod isOpen_univ)).preimage hΘc
  have hcoord0 : coordE hyp hφ μ = 0 := by
    show (EuclideanSpace.equiv (Fin n) ℝ).symm _ = 0
    rw [show (fun i => ∫ x, phiC hyp hφ i x ∂μm) = 0 from funext fun i => integral_phiC hyp hφ i]
    exact map_zero _
  have hμU : μ ∈ U := by
    rw [hmemU]
    have h1 : Θ μ = 0 := by
      rw [hΘ]
      simp only [hcoord0, hR_self hyp hμ, map_zero, Prod.mk_zero_zero]
    rw [h1]
    exact ⟨hN₀0, mem_ball_self hε₂0, Set.mem_univ _⟩
  -- graph points
  have hgp : ∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε₂,
      IsMinimizer V W (rhoPM V W μ (kC hyp hφ a + ψ a)) ∧
        hR hyp μ (rhoPM V W μ (kC hyp hφ a + ψ a)) = kC hyp hφ a + ψ a ∧
        ((rhoPM V W μ (kC hyp hφ a + ψ a) : ProbabilityMeasure (Torus d)) : Measure (Torus d)) =
          densMeasure fun x => elDens V W μm x * (1 + (kC hyp hφ a + ψ a) x) := fun a ha => by
    obtain ⟨hY, hz, hpos, hΨ⟩ := hgr a (hsub ha)
    have hh0 := mean_kC_add hyp hμ hφ (e := a) hY
    obtain ⟨h0, h1⟩ := graph_density_props hyp hμ hpos hh0
    have hp := isProbabilityMeasure_densMeasure' (fun x => (h0 x).le) h1
    rw [rhoPM_eq hp]
    exact ⟨(graph_point_minimizer hyp hμ hpos hh0 hΨ hp).1,
      (graph_point_minimizer hyp hμ hpos hh0 hΨ hp).2, rfl⟩
  have hcoord : ∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε₂,
      coordE hyp hφ (rhoPM V W μ (kC hyp hφ a + ψ a)) = a := fun a ha => by
    obtain ⟨hmin, hRa, -⟩ := hgp a ha
    ext i
    rw [coordE_apply, coord_minimizer hyp hμ hφ hmin, hRa]
    exact pairC_kC_add hyp hμ hφ (hgr a (hsub ha)).1 i
  have hΘa : ∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε₂,
      Θ (rhoPM V W μ (kC hyp hφ a + ψ a)) = (a, ψ a) := fun a ha => by
    obtain ⟨-, hRa, -⟩ := hgp a ha
    rw [hΘ]
    simp only [hcoord a ha, hRa, map_add, QCraw_kC hyp hφ, zero_add,
      QCraw_of_mem hyp hφ (hgr a (hsub ha)).1]
  have hgU : ∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε₂, rhoPM V W μ (kC hyp hφ a + ψ a) ∈ U :=
    fun a ha => by
    rw [hmemU, hΘa a ha]
    exact ⟨hball₁ a (hsub₁ ha), ha, Set.mem_univ _⟩
  -- minimizers in `U` are graph points
  have hmU : ∀ ν : ProbabilityMeasure (Torus d), ν ∈ U → IsMinimizer V W ν →
      coordE hyp hφ ν ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε₂ ∧
        hR hyp μ ν = kC hyp hφ (coordE hyp hφ ν) + ψ (coordE hyp hφ ν) := by
    intro ν hνU hν
    rw [hmemU] at hνU
    obtain ⟨hN0, hball, -⟩ := hνU
    refine ⟨hball, ?_⟩
    have hF : FC hyp hφ (coordE hyp hφ ν, QCraw hyp hφ (hR hyp μ ν)) = 0 := by
      rw [FC_eq_zero_iff]
      refine ⟨QCraw_idem hyp hφ _, ?_⟩
      show QCraw hyp hφ (PhiC hyp μm (kC hyp hφ (coordE hyp hφ ν) +
        QCraw hyp hφ (hR hyp μ ν))) = 0
      rw [← hR_decomp hyp hμ hφ hν]
      exact QCraw_PhiC_hR hyp hμ hφ hν
    have := hNu _ (hN₀N hN0) hF
    rw [this]
    exact hR_decomp hyp hμ hφ hν
  have hmU' : ∀ ν : ProbabilityMeasure (Torus d), (hν : ν ∈ U ∧ IsMinimizer V W ν) →
      rhoPM V W μ (kC hyp hφ (coordE hyp hφ ν) + ψ (coordE hyp hφ ν)) = ν := by
    intro ν hν
    obtain ⟨hb, hRe⟩ := hmU ν hν.1 hν.2
    apply Subtype.ext
    show ((rhoPM V W μ (kC hyp hφ (coordE hyp hφ ν) + ψ (coordE hyp hφ ν)) :
      ProbabilityMeasure (Torus d)) : Measure (Torus d)) = (ν : Measure (Torus d))
    rw [(hgp _ hb).2.2, minimizer_eq_graph hyp hμ hν.2, hRe]
  -- continuity of `a ↦ ρ_a`
  have hint : ∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε₂, ∀ f : Torus d →ᵇ ℝ,
      ∫ x, f x ∂((rhoPM V W μ (kC hyp hφ a + ψ a) : ProbabilityMeasure (Torus d)) : Measure (Torus d))
        = meanC μm ((1 + (kC hyp hφ a + ψ a)) * f.toContinuousMap) := fun a ha f => by
    obtain ⟨hY, -, hpos, -⟩ := hgr a (hsub ha)
    rw [(hgp a ha).2.2, integral_graph_density hyp hμ hpos (mean_kC_add hyp hμ hφ (e := a) hY), meanC_apply]
    rfl
  have hρc : Continuous fun a : ball (0 : EuclideanSpace ℝ (Fin n)) ε₂ =>
      rhoPM V W μ (kC hyp hφ a + ψ a) := by
    rw [continuous_iff_continuousAt]
    intro a₀
    rw [ContinuousAt, ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have e : (fun a : ball (0 : EuclideanSpace ℝ (Fin n)) ε₂ =>
        ∫ x, f x ∂((rhoPM V W μ (kC hyp hφ a + ψ a) : ProbabilityMeasure (Torus d)) :
          Measure (Torus d))) = fun a : ball (0 : EuclideanSpace ℝ (Fin n)) ε₂ =>
        meanC μm ((1 + (kC hyp hφ (a : EuclideanSpace ℝ (Fin n)) +
          ψ (a : EuclideanSpace ℝ (Fin n)))) * f.toContinuousMap) := by
      funext a; exact hint a a.2 f
    rw [e, hint (a₀ : EuclideanSpace ℝ (Fin n)) a₀.2 f]
    have hcont : ContinuousOn
        (fun a => meanC μm ((1 + (kC hyp hφ a + ψ a)) * f.toContinuousMap))
        (ball (0 : EuclideanSpace ℝ (Fin n)) ε₂) :=
      (meanC μm).continuous.comp_continuousOn
        ((continuousOn_const.add ((kC hyp hφ).continuous.continuousOn.add
          ((hψs.continuousOn).mono hsub))).mul continuousOn_const)
    exact (hcont.continuousAt (isOpen_ball.mem_nhds a₀.2)).tendsto.comp
      continuous_subtype_val.continuousAt
  refine ⟨ψ, hψ0, hψd, ε₂, hε₂0, hψs.mono hsub, fun a ha => hgr a (hsub ha), U, hUo, hμU,
    { toFun := fun a => ⟨rhoPM V W μ (kC hyp hφ a + ψ a), hgU a a.2, (hgp a a.2).1⟩
      invFun := fun ν => ⟨coordE hyp hφ ν.1, (hmU ν.1 ν.2.1 ν.2.2).1⟩
      left_inv := fun a => Subtype.ext (hcoord a a.2)
      right_inv := fun ν => Subtype.ext (hmU' ν.1 ν.2)
      continuous_toFun := hρc.subtype_mk _
      continuous_invFun := ((continuous_coordE hyp hφ).comp continuous_subtype_val).subtype_mk _ },
    fun a => (hgp a a.2).2.2⟩

end homeo

end SharpLSI
