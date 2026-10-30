import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootGraphData

/-! Same-graph ordinary base inverses for the actual interacting perturbation.
These are factual base-point inputs, not an interacting branch or optimizer factory. -/

noncomputable section
open Filter Topology Set
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem reduced_zero_matrix (D : OrdinaryRootGraphData) (z : Fin 3 → ℝ) :
    LinearMap.toMatrix' (Mz_STR02923 D.reduced (0, z) :
      (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) = jacobian_STR02922 D.reduced z := by
  rw [← Mz_slice_STR02923 D.reduced D.openO D.smooth_reduced (D.zero_memO z)]
  ext i j
  simp [LinearMap.toMatrix'_apply, jacobian_STR02922]

private theorem reduced_zero_det_ne (D : OrdinaryRootGraphData) (j : Fin 3) :
    (Mz_STR02923 D.reduced (0, D.Z j 0)).det ≠ 0 := by
  have hz : (0 : ℝ) ∈ Ioo (-D.radius) D.radius := by
    constructor <;> linarith [D.radius_pos]
  have hZ1 : D.Z 1 0 = ![-1, Real.sqrt 3, -16 / 15] := by
    rw [(D.Z_rotation 0 hz).1, D.Z_zero, rotP0_STR02923]
  have hZ2 : D.Z 2 0 = ![-1, -Real.sqrt 3, -16 / 15] := by
    rw [(D.Z_rotation 0 hz).2, (D.Z_rotation 0 hz).1, D.Z_zero,
      rotrotP0_STR02923]
  have hdata := str029_22_invertible_finite_dimensional_jacobian_of_slice
    D.reduced D.reduced_zero
  fin_cases j
  · change (Mz_STR02923 D.reduced (0, D.Z 0 0)).det ≠ 0
    rw [D.Z_zero, det_Mz_STR02923 D.openO D.smooth_reduced
      (D.zero_memO _) D.reduced_zero]
    norm_num
  · change (Mz_STR02923 D.reduced (0, D.Z 1 0)).det ≠ 0
    rw [hZ1]
    have hunit := (Matrix.isUnit_iff_isUnit_det _).mp hdata.2.2.2.1
    have hd := LinearMap.det_toMatrix'
      (Mz_STR02923 D.reduced (0, D.Z 1 0) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
    rw [reduced_zero_matrix, hZ1] at hd
    change LinearMap.det (Mz_STR02923 D.reduced (0, ![-1, Real.sqrt 3, -16 / 15]) :
      (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) ≠ 0
    rw [← hd]
    exact hunit.ne_zero
  · change (Mz_STR02923 D.reduced (0, D.Z 2 0)).det ≠ 0
    rw [hZ2]
    have hunit := (Matrix.isUnit_iff_isUnit_det _).mp hdata.2.2.2.2
    have hd := LinearMap.det_toMatrix'
      (Mz_STR02923 D.reduced (0, D.Z 2 0) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
    rw [reduced_zero_matrix, hZ2] at hd
    change LinearMap.det (Mz_STR02923 D.reduced (0, ![-1, -Real.sqrt 3, -16 / 15]) :
      (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) ≠ 0
    rw [← hd]
    exact hunit.ne_zero

/-- The augmented amplitude/rate Jacobian is genuinely invertible along all
three SAME retained ordinary branches on one common two-sided h interval. -/
theorem ordinaryRoot_reduced_augmented_invertible (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, |h| < δ → ∀ j : Fin 3,
      (Mz_STR02923 D.reduced (h, D.Z j h)).IsInvertible ∧
        Kfun_STR02923 D.reduced (h, D.Z j h) = 0 := by
  have hz : (0 : ℝ) ∈ Ioo (-D.radius) D.radius := by
    constructor <;> linarith [D.radius_pos]
  have hev (j : Fin 3) : ∀ᶠ h in 𝓝 (0 : ℝ),
      (Mz_STR02923 D.reduced (h, D.Z j h)).det ≠ 0 := by
    have hZ := (D.smoothZ j).continuousOn.continuousAt (Ioo_mem_nhds hz.1 hz.2)
    have hc := ContinuousAt.comp (f := fun h : ℝ => (h, D.Z j h))
      (continuousAt_det_STR02923 D.openO
        (contDiffOn_Kfun_STR02923 D.openO D.smooth_reduced) (D.zero_memO (D.Z j 0)))
      (continuousAt_id.prodMk hZ)
    exact hc.eventually_ne (reduced_zero_det_ne D j)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (Filter.eventually_all.mpr hev)
  refine ⟨min r D.radius, lt_min hr D.radius_pos, min_le_right _ _, fun h hh j => ?_⟩
  have hhr : h ∈ Ioo (-D.radius) D.radius := by
    have hs := hh.trans_le (min_le_right r D.radius)
    exact abs_lt.mp hs
  refine ⟨isInvertible_of_det_STR02923 ?_, D.Z_critical j h hhr⟩
  have hhball : dist h 0 < r := by
    simpa only [Real.dist_eq, sub_zero] using (hh.trans_le (min_le_left r D.radius))
  exact hball hhball j

/-- The actual variational complement derivative stays invertible at the
SAME retained graph points. No Hessian-to-Banach inverse implication is assumed. -/
theorem ordinaryRoot_range_partial_invertible (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, |h| < δ → ∀ j : Fin 3,
      (fderiv ℝ Fp_STR02916 (ptPar_STR02923 h (D.Z j h),
        D.ψ (ptPar_STR02923 h (D.Z j h))) ∘L
          ContinuousLinearMap.inr ℝ Par_STR02916 E_STR02969).IsInvertible := by
  have hz : (0 : ℝ) ∈ Ioo (-D.radius) D.radius := by
    constructor <;> linarith [D.radius_pos]
  letI : CompleteSpace E_STR02969 :=
    str029_69_completeness_closed_complements_range_spaces_E.2.2
  letI : CompleteSpace Y_STR02969 :=
    str029_69_completeness_closed_complements_range_spaces_Y.2.2
  have hDc : Continuous (fun q : Par_STR02916 × E_STR02969 =>
      fderiv ℝ Fp_STR02916 q ∘L ContinuousLinearMap.inr ℝ Par_STR02916 E_STR02969) :=
    (Fp_smooth_STR02916.continuous_fderiv (by simp)).clm_comp continuous_const
  have hSinv : IsOpen {q : Par_STR02916 × E_STR02969 |
      (fderiv ℝ Fp_STR02916 q ∘L
        ContinuousLinearMap.inr ℝ Par_STR02916 E_STR02969).IsInvertible} :=
    ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hDc
  have hev (j : Fin 3) : ∀ᶠ h in 𝓝 (0 : ℝ),
      (fderiv ℝ Fp_STR02916 (ptPar_STR02923 h (D.Z j h),
        D.ψ (ptPar_STR02923 h (D.Z j h))) ∘L
          ContinuousLinearMap.inr ℝ Par_STR02916 E_STR02969).IsInvertible := by
    have hZ := (D.smoothZ j).continuousOn.continuousAt (Ioo_mem_nhds hz.1 hz.2)
    have hp : ContinuousAt (fun h => ptPar_STR02923 h (D.Z j h)) 0 :=
      continuous_ptPar_STR02923.continuousAt.comp (continuousAt_id.prodMk hZ)
    have hp0 : ptPar_STR02923 0 (D.Z j 0) = 0 := ptPar_zero_STR02923 _
    have hψ := D.smoothψ.continuousOn.continuousAt (D.openU.mem_nhds D.zero_memU)
    have hψp : ContinuousAt D.ψ (ptPar_STR02923 0 (D.Z j 0)) := by
      simpa only [hp0] using hψ
    have hq : ContinuousAt (fun h =>
        (ptPar_STR02923 h (D.Z j h), D.ψ (ptPar_STR02923 h (D.Z j h)))) 0 :=
      hp.prodMk (hψp.comp (f := fun h : ℝ => ptPar_STR02923 h (D.Z j h)) hp)
    have hmem : {q : Par_STR02916 × E_STR02969 |
        (fderiv ℝ Fp_STR02916 q ∘L
          ContinuousLinearMap.inr ℝ Par_STR02916 E_STR02969).IsInvertible} ∈
        𝓝 (ptPar_STR02923 0 (D.Z j 0), D.ψ (ptPar_STR02923 0 (D.Z j 0))) := by
      simpa only [hp0, D.zeroψ] using hSinv.mem_nhds Fp_inv_STR02916
    exact hq.eventually_mem hmem
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (Filter.eventually_all.mpr hev)
  refine ⟨min r D.radius, lt_min hr D.radius_pos, min_le_right _ _, fun h hh j => ?_⟩
  have hhball : dist h 0 < r := by
    simpa only [Real.dist_eq, sub_zero] using (hh.trans_le (min_le_left r D.radius))
  exact hball hhball j

end DGPS.Examples.ThreeSpeciesCircle
