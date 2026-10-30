import DGPS.Examples.ThreeSpeciesCircle.InteractingRangeAgreement

/-! Fixed-h local branches of the projected ACTUAL feedback-gradient rows and
physical deficit. Only the ordinary zero-slice variation identity is used. The
old unadmitted derivative-of-reduced-deficit source is retained by hash in checks. -/

noncomputable section
open Filter Topology Set Metric
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem gradient_cos_mean (h γ : ℝ) (u : PeriodicC2_STR02969) :
    meanCLM_STR02954 (Gfun_STR02955 h γ u * e0_STR02955 cosC2_STR02915) =
      meanT_STR02901 (fun t => gradG_STR02950 h γ u.val t * Real.cos t) := by
  rw [meanCLM_apply_STR02954]
  congr 1
  funext t
  rw [val_mul_STR02954, Pi.mul_apply, Gfun_val_STR02955, e0_val_STR02955,
    cosC2_val_STR02915]

private theorem gradient_sin_mean (h γ : ℝ) (u : PeriodicC2_STR02969) :
    meanCLM_STR02954 (Gfun_STR02955 h γ u * e0_STR02955 sinC2_STR02915) =
      meanT_STR02901 (fun t => gradG_STR02950 h γ u.val t * Real.sin t) := by
  rw [meanCLM_apply_STR02954]
  congr 1
  funext t
  rw [val_mul_STR02954, Pi.mul_apply, Gfun_val_STR02955, e0_val_STR02955,
    sinC2_val_STR02915]

private theorem projected_system_germ (D : OrdinaryRootGraphData) (h : ℝ) (z : Fin 3 → ℝ)
    (K : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)) (S : Set (ℝ × (Fin 3 → ℝ)))
    (hSo : IsOpen S) (hKS : ContDiffOn ℝ ∞ K S) (hzS : (0, z) ∈ S)
    (hzO : (h, z) ∈ D.O)
    (he : (fun v => K (0, v)) =ᶠ[𝓝 z] fun v => Kfun_STR02923 D.reduced (h, v)) :
    K (0, z) = Kfun_STR02923 D.reduced (h, z) ∧
      fderiv ℝ K (0, z) ∘L ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ) =
        Mz_STR02923 D.reduced (h, z) := by
  have hnew := ((hKS.contDiffAt (hSo.mem_nhds hzS)).differentiableAt (by simp)).hasFDerivAt.comp z
    (hasFDerivAt_prodMk_right (0 : ℝ) z)
  have hold := (((contDiffOn_Kfun_STR02923 D.openO D.smooth_reduced).contDiffAt
    (D.openO.mem_nhds hzO)).differentiableAt (by simp)).hasFDerivAt.comp z
      (hasFDerivAt_prodMk_right h z)
  have hnewD : fderiv ℝ (fun v => K (0, v)) z =
      fderiv ℝ K (0, z) ∘L ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ) := hnew.fderiv
  have holdD : fderiv ℝ (fun v => Kfun_STR02923 D.reduced (h, v)) z =
      Mz_STR02923 D.reduced (h, z) := hold.fderiv
  exact ⟨he.eq_of_nhds, hnewD.symm.trans (he.fderiv_eq.trans holdD)⟩

private theorem det_ne_of_invertible {L : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)}
    (hL : L.IsInvertible) : L.det ≠ 0 := by
  obtain ⟨e, he⟩ := hL
  rw [← he]
  change LinearMap.det (e.toLinearEquiv : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) ≠ 0
  exact e.toLinearEquiv.isUnit_det'.ne_zero

/-- Local smooth branches of the projected nonlinear feedback-gradient and
actual deficit equations, one near each SAME ordinary root. This is a zero-set
result; no interacting optimizer or capture conclusion is an assumption. -/
theorem interactingChartReduced_local_branches (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ → ∀ j : Fin 3,
      ∃ (U : Set (ℝ × ℝ × ℝ × ℝ)) (V : Set E_STR02969) (ψ : (ℝ × ℝ × ℝ × ℝ) → E_STR02969)
          (E : ℝ × (Fin 3 → ℝ) → ℝ) (K : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ))
          (S : Set (ℝ × (Fin 3 → ℝ))),
        IsOpen U ∧ IsOpen V ∧ D.ψ (ptPar_STR02923 h (D.Z j h)) ∈ V ∧
          ContDiffOn ℝ ∞ ψ U ∧
          ψ (0, h * D.Z j h 0, h * D.Z j h 1, h ^ 2 * D.Z j h 2) =
            D.ψ (ptPar_STR02923 h (D.Z j h)) ∧
          (∀ p ∈ U, ψ p ∈ V) ∧
          (∀ p ∈ U, ∀ w ∈ V, interactingChartRange h (p, w) = 0 ↔ ψ p = w) ∧
          (∀ p ∈ U, interactingChartRange h (p, ψ p) = 0) ∧
          IsOpen S ∧ (0, D.Z j h) ∈ S ∧ ContDiffOn ℝ ∞ E S ∧ ContDiffOn ℝ ∞ K S ∧
          (∀ x, let u := (h * x.2 0) • cosC2_STR02915 + (h * x.2 1) • sinC2_STR02915 +
              (ψ (x.1, h * x.2 0, h * x.2 1, h ^ 2 * x.2 2) : PeriodicC2_STR02969)
            E x = interactingChartDeficit h (x.1, h ^ 2 * x.2 2, u) / h ^ 4 ∧
            K x = ![(h ^ 3)⁻¹ * meanCLM_STR02954
                (interactingChartGradient h (x.1, h ^ 2 * x.2 2, u) * e0_STR02955 cosC2_STR02915),
              (h ^ 3)⁻¹ * meanCLM_STR02954
                (interactingChartGradient h (x.1, h ^ 2 * x.2 2, u) * e0_STR02955 sinC2_STR02915), E x]) ∧
          ∃ (Z : ℝ → (Fin 3 → ℝ)) (η r : ℝ), 0 < η ∧ 0 < r ∧ Z 0 = D.Z j h ∧
            ContDiffOn ℝ ∞ Z (Ioo (-η) η) ∧
            (∀ ε : ℝ, |ε| < η → K (ε, Z ε) = 0 ∧
              (ε, h * Z ε 0, h * Z ε 1, h ^ 2 * Z ε 2) ∈ U) ∧
            ∀ x ∈ ball ((0 : ℝ), D.Z j h) r, K x = 0 ↔ x.2 = Z x.1 := by
  obtain ⟨δg, hδg, hδgr, hgraphs⟩ := interactingChartRange_graphs_zero_agreement D
  obtain ⟨δi, hδi, hδir, hinv⟩ := ordinaryRoot_reduced_augmented_invertible D
  refine ⟨min δg δi, lt_min hδg hδi, (min_le_left _ _).trans hδgr, fun h hh hhd j => ?_⟩
  have hhg := hhd.trans_le (min_le_left δg δi)
  have hhi : |h| < δi := by simpa only [abs_of_pos hh] using hhd.trans_le (min_le_right δg δi)
  obtain ⟨U, V, ψ, hUo, hp0, hVo, hw0, hψ, hψ0, hψV, hgraph, hzeroψ, hzeroE⟩ :=
    hgraphs h hh hhg j
  let p : (ℝ × (Fin 3 → ℝ)) → ℝ × ℝ × ℝ × ℝ :=
    fun x => (x.1, h * x.2 0, h * x.2 1, h ^ 2 * x.2 2)
  have hpc : ContDiff ℝ ∞ p := by dsimp [p]; fun_prop
  let S := p ⁻¹' U
  have hSo : IsOpen S := hUo.preimage hpc.continuous
  have hzS : ((0 : ℝ), D.Z j h) ∈ S := hp0
  have hψp : ContDiffOn ℝ ∞ (fun x => ψ (p x)) S :=
    hψ.comp hpc.contDiffOn (fun _ hx => hx)
  let u : (ℝ × (Fin 3 → ℝ)) → PeriodicC2_STR02969 := fun x =>
    (h * x.2 0) • cosC2_STR02915 + (h * x.2 1) • sinC2_STR02915 +
      (ψ (p x) : PeriodicC2_STR02969)
  have huc : ContDiffOn ℝ ∞ u S := by
    have ha : ContDiffOn ℝ ∞ (fun x : ℝ × (Fin 3 → ℝ) => h * x.2 0) S := by fun_prop
    have hb : ContDiffOn ℝ ∞ (fun x : ℝ × (Fin 3 → ℝ) => h * x.2 1) S := by fun_prop
    exact ((ha.smul contDiffOn_const).add (hb.smul contDiffOn_const)).add
      (E_STR02969.subtypeL.contDiff.contDiffOn.comp hψp (fun _ _ => mem_univ _))
  have hγ : ContDiffOn ℝ ∞ (fun x : ℝ × (Fin 3 → ℝ) => h ^ 2 * x.2 2) S := by fun_prop
  have hinner := contDiffOn_fst.prodMk (hγ.prodMk huc)
  let E : ℝ × (Fin 3 → ℝ) → ℝ := fun x =>
    interactingChartDeficit h (x.1, h ^ 2 * x.2 2, u x) / h ^ 4
  have hES : ContDiffOn ℝ ∞ E S :=
    ((interactingChartDeficit_smooth h).contDiffOn.comp hinner (fun _ _ => mem_univ _)).div_const _
  let G : ℝ × (Fin 3 → ℝ) → PeriodicHolder_STR02968 := fun x =>
    interactingChartGradient h (x.1, h ^ 2 * x.2 2, u x)
  have hGS : ContDiffOn ℝ ∞ G S :=
    (interactingChartGradient_smooth h).contDiffOn.comp hinner (fun _ _ => mem_univ _)
  let K : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun x =>
    ![(h ^ 3)⁻¹ * meanCLM_STR02954 (G x * e0_STR02955 cosC2_STR02915),
      (h ^ 3)⁻¹ * meanCLM_STR02954 (G x * e0_STR02955 sinC2_STR02915), E x]
  have hKS : ContDiffOn ℝ ∞ K S := by
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact contDiffOn_const.mul (meanCLM_STR02954.contDiff.contDiffOn.comp
        (hGS.mul contDiffOn_const) (fun _ _ => mem_univ _))
    · exact contDiffOn_const.mul (meanCLM_STR02954.contDiff.contDiffOn.comp
        (hGS.mul contDiffOn_const) (fun _ _ => mem_univ _))
    · exact hES
  have hhr : h ∈ Ioo (-D.radius) D.radius := by
    constructor <;> linarith [D.radius_pos, hhg.trans_le hδgr]
  have heO : ∀ᶠ z in 𝓝 (D.Z j h), (h, z) ∈ D.O :=
    (show Continuous (fun z : Fin 3 → ℝ => (h, z)) from
      continuous_const.prodMk continuous_id).continuousAt.eventually_mem
        (D.openO.mem_nhds (D.branch_memO j h hhr))
  have hq : Continuous (ptPar_STR02923 h) := by unfold ptPar_STR02923; fun_prop
  have heU : ∀ᶠ z in 𝓝 (D.Z j h), ptPar_STR02923 h z ∈ D.U :=
    hq.continuousAt.eventually_mem (D.openU.mem_nhds (D.branch_memU j h hhr))
  have heK : (fun z => K (0, z)) =ᶠ[𝓝 (D.Z j h)] fun z => Kfun_STR02923 D.reduced (h, z) := by
    filter_upwards [hzeroψ, hzeroE, heO, heU] with z hzψ hzE hzO hzU
    have hu0 : u (0, z) = Lamp_STR02956 D.ψ (h, h ^ 2 * z 2) (h * z 0, h * z 1) := by
      dsimp only [u, p]
      rw [hzψ]
      rfl
    have hk := kfun_STR02924 D.openU D.smoothψ D.memψ D.range_eq D.openO D.smooth_reduced
      D.reduced_value h hh.ne' z hzO hzU
    ext i
    fin_cases i
    · change (h ^ 3)⁻¹ * meanCLM_STR02954
        (interactingChartGradient h (0, h ^ 2 * z 2, u (0, z)) * e0_STR02955 cosC2_STR02915) = _
      rw [interactingChartGradient_zero, hu0, gradient_cos_mean]
      exact hk.1.symm
    · change (h ^ 3)⁻¹ * meanCLM_STR02954
        (interactingChartGradient h (0, h ^ 2 * z 2, u (0, z)) * e0_STR02955 sinC2_STR02915) = _
      rw [interactingChartGradient_zero, hu0, gradient_sin_mean]
      exact hk.2.1.symm
    · exact hzE
  obtain ⟨hKzero, hM⟩ := projected_system_germ D h (D.Z j h) K S hSo hKS hzS
    (D.branch_memO j h hhr) heK
  have hKi : (fderiv ℝ K (0, D.Z j h) ∘L ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ)).IsInvertible := by
    rw [hM]
    exact (hinv h hhi j).1
  have hK0 : K (0, D.Z j h) = 0 := hKzero.trans (hinv h hhi j).2
  obtain ⟨Z, r, hr, hZ0, hbox, hZsmooth⟩ := ift_box_STR02923 hSo hKS
    isOpen_univ hzS (mem_univ _) hK0 (det_ne_of_invertible hKi)
  have hZc0 : ContDiffAt ℝ ∞ Z 0 := hZsmooth 0 (by rw [hZ0]; exact mem_ball_self hr)
  have hevent : ∀ᶠ ε in 𝓝 (0 : ℝ), (ε, Z ε) ∈ ball ((0 : ℝ), D.Z j h) r :=
    (continuousAt_id.prodMk hZc0.continuousAt).eventually_mem (by rw [hZ0]; exact ball_mem_nhds _ hr)
  obtain ⟨η, hη, hηbox⟩ := Metric.eventually_nhds_iff.mp hevent
  have hZin (ε : ℝ) (hε : |ε| < η) : (ε, Z ε) ∈ ball ((0 : ℝ), D.Z j h) r :=
    hηbox (by simpa only [Real.dist_eq, sub_zero] using hε)
  have hgraph0 : ∀ p ∈ U, interactingChartRange h (p, ψ p) = 0 :=
    fun p hp => (hgraph p hp (ψ p) (hψV p hp)).mpr rfl
  refine ⟨U, V, ψ, E, K, S, hUo, hVo, hw0, hψ, hψ0, hψV, hgraph, hgraph0, hSo, hzS, hES, hKS,
    fun _ => ⟨rfl, rfl⟩, Z, η, r, hη, hr, hZ0, ?_, ?_, ?_⟩
  · intro ε hε
    exact (hZsmooth ε (hZin ε (abs_lt.mpr hε))).contDiffWithinAt
  · intro ε hε
    exact ⟨(hbox (ε, Z ε) (hZin ε hε)).2.2.2.mpr rfl,
      (hbox (ε, Z ε) (hZin ε hε)).1⟩
  · intro x hx
    exact (hbox x hx).2.2.2

end DGPS.Examples.ThreeSpeciesCircle
