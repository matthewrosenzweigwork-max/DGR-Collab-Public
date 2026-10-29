import LeanResearch.PeriodicAttractiveLogGas.ReferenceResidual
import LeanResearch.PeriodicAttractiveLogGas.GreenGradientOscillation

/-! The two mean-value steps in the supplied far residual proof. The square
diameter and actual closed-cell separation retain the coefficient 2 C₂. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PeriodicAttractiveLogGas.FarReferenceResidual
open MeshCells MeshAdjacentCells MeshNearbyGeometry GreenPointWeights
  RectangleDilation GreenFarOscillation GreenGradientOscillation ReferenceResidual

theorem square_diameter {Z W : PlanarSpace}
    (hZ : Z ∈ closedUnitSquare) (hW : W ∈ closedUnitSquare) :
    ‖Z - W‖ ≤ Real.sqrt 2 := by
  have h := euclidean_norm_le_sqrt_two_mul (X := Z - W) (L := 1) (by norm_num)
  simp only [mul_one] at h
  apply h
  intro k
  change |Z k - W k| ≤ 1
  exact abs_le.mpr ⟨by linarith [(hZ k (mem_univ k)).1, (hW k (mem_univ k)).2],
    by linarith [(hW k (mem_univ k)).1, (hZ k (mem_univ k)).2]⟩

theorem reference_gradient_cell_oscillation (a : PlanarSpace) {J R C₂ : ℝ}
    (hJ : 0 < J) (hR : 0 < R) (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (y : Torus)
    (hsep : ∀ Z ∈ closedUnitSquare,
      R / J ≤ torusEuclideanNorm (torusQuotient (affine a J Z) - y))
    {Z W : PlanarSpace} (hZ : Z ∈ closedUnitSquare) (hW : W ∈ closedUnitSquare) :
    ‖referenceGradient a J y Z - referenceGradient a J y W‖ ≤
      Real.sqrt 2 * C₂ * J / R ^ 2 := by
  have hd (X : PlanarSpace) (hX : X ∈ closedUnitSquare) :=
    hasFDerivAt_referenceGradient a J y (ne_zero_of_separation hJ hR (hsep X hX))
  have hn (X : PlanarSpace) (hX : X ∈ closedUnitSquare) :
      ‖fderiv ℝ (referenceGradient a J y) X‖ ≤ C₂ * J / R ^ 2 := by
    rw [(hd X hX).fderiv]
    exact norm_scaled_hessian_le hJ hR hC hk (hsep X hX)
  have h := (convex_patchClosed .cell).norm_image_sub_le_of_norm_fderiv_le
    (fun X hX ↦ (hd X hX).differentiableAt) hn hW hZ
  calc
    _ ≤ (C₂ * J / R ^ 2) * ‖Z - W‖ := h
    _ ≤ (C₂ * J / R ^ 2) * Real.sqrt 2 :=
      mul_le_mul_of_nonneg_left (square_diameter hZ hW) (by positivity)
    _ = _ := by ring

def reverseSource (x : Torus) (b : PlanarSpace) (J : ℝ) (Y : PlanarSpace) : ℝ :=
  regularGreenRepresentative (x - torusQuotient (affine b J Y))

theorem hasFDerivAt_reverseSource (x : Torus) (b : PlanarSpace) (J : ℝ)
    {Y : PlanarSpace} (hY : x - torusQuotient (affine b J Y) ≠ 0) :
    HasFDerivAt (reverseSource x b J)
      (-(J⁻¹ • greenDifferential (x - torusQuotient (affine b J Y)))) Y := by
  have hquot (V : PlanarSpace) :
      torusQuotient (centeredLift x - affine b J V) =
        x - torusQuotient (affine b J V) := by
    rw [torusQuotient_sub, torusQuotient_centeredLift]
  have hx : centeredLift x - affine b J Y ∈ offIntegerLattice := by
    change torusQuotient (centeredLift x - affine b J Y) ≠ 0
    rw [hquot]
    exact hY
  have hf : reverseSource x b J = fun V ↦ regularGreenLift (centeredLift x - affine b J V) := by
    funext V
    rw [← regularGreenRepresentative_lift]
    rw [hquot]
    rfl
  have hg : DifferentiableAt ℝ regularGreenLift (centeredLift x - affine b J Y) :=
    (contDiffOn_regularGreenLift.contDiffAt
      (isOpen_offIntegerLattice.mem_nhds hx)).differentiableAt (by simp)
  have hd := hg.hasFDerivAt.comp Y
    ((hasFDerivAt_affine b J Y).const_sub (centeredLift x))
  have hm : (fderiv ℝ regularGreenLift (centeredLift x - affine b J Y)).comp
      (-(J⁻¹ • ContinuousLinearMap.id ℝ PlanarSpace)) =
      -(J⁻¹ • greenDifferential (x - torusQuotient (affine b J Y))) := by
    rw [← greenDifferential_lift, hquot]
    ext v
    simp
  rw [hf]
  exact hd.congr_fderiv hm

theorem norm_greenDifferential_sub (z w : Torus) :
    ‖greenDifferential z - greenDifferential w‖ = ‖greenGradient z - greenGradient w‖ := by
  rw [greenGradient, greenGradient, ← map_sub]
  exact ((InnerProductSpace.toDual ℝ PlanarSpace).symm.norm_map _).symm

theorem reference_four_point_bound (a b : PlanarSpace) {J R C₂ : ℝ}
    (hJ : 0 < J) (hR : 0 < R) (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (hsep : ∀ Z ∈ closedUnitSquare, ∀ V ∈ closedUnitSquare,
      R / J ≤ torusEuclideanNorm
        (torusQuotient (affine a J Z) - torusQuotient (affine b J V)))
    {X U Y V : PlanarSpace} (hX : X ∈ closedUnitSquare) (hU : U ∈ closedUnitSquare)
    (hY : Y ∈ closedUnitSquare) (hV : V ∈ closedUnitSquare) :
    |reverseSource (torusQuotient (affine a J X)) b J Y -
      reverseSource (torusQuotient (affine a J U)) b J Y -
      reverseSource (torusQuotient (affine a J X)) b J V +
      reverseSource (torusQuotient (affine a J U)) b J V| ≤ 2 * C₂ / R ^ 2 := by
  let x := torusQuotient (affine a J X)
  let u := torusQuotient (affine a J U)
  let F := fun W => reverseSource x b J W - reverseSource u b J W
  have hd (W : PlanarSpace) (hW : W ∈ closedUnitSquare) :=
    (hasFDerivAt_reverseSource x b J (ne_zero_of_separation hJ hR (hsep X hX W hW))).sub
      (hasFDerivAt_reverseSource u b J (ne_zero_of_separation hJ hR (hsep U hU W hW)))
  have hn (W : PlanarSpace) (hW : W ∈ closedUnitSquare) :
      ‖fderiv ℝ F W‖ ≤ Real.sqrt 2 * C₂ / R ^ 2 := by
    change ‖fderiv ℝ (reverseSource x b J - reverseSource u b J) W‖ ≤ _
    rw [(hd W hW).fderiv]
    have he : -(J⁻¹ • greenDifferential (x - torusQuotient (affine b J W))) -
        -(J⁻¹ • greenDifferential (u - torusQuotient (affine b J W))) =
        -(J⁻¹ • (greenDifferential (x - torusQuotient (affine b J W)) -
          greenDifferential (u - torusQuotient (affine b J W)))) := by
      simp only [smul_sub]
      abel
    rw [he, norm_neg, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hJ.le), norm_greenDifferential_sub]
    have hg := reference_gradient_cell_oscillation a hJ hR hC hk
      (torusQuotient (affine b J W)) (fun Z hZ => hsep Z hZ W hW) hX hU
    calc
      _ ≤ J⁻¹ * (Real.sqrt 2 * C₂ * J / R ^ 2) :=
        mul_le_mul_of_nonneg_left hg (inv_nonneg.mpr hJ.le)
      _ = _ := by field_simp
  have hm := (convex_patchClosed .cell).norm_image_sub_le_of_norm_fderiv_le
    (fun W hW => (hd W hW).differentiableAt) hn hV hY
  have heq : reverseSource x b J Y - reverseSource u b J Y -
      reverseSource x b J V + reverseSource u b J V = F Y - F V := by dsimp [F]; ring
  change |reverseSource x b J Y - reverseSource u b J Y -
    reverseSource x b J V + reverseSource u b J V| ≤ _
  rw [heq, ← Real.norm_eq_abs]
  calc
    _ ≤ (Real.sqrt 2 * C₂ / R ^ 2) * ‖Y - V‖ := hm
    _ ≤ (Real.sqrt 2 * C₂ / R ^ 2) * Real.sqrt 2 :=
      mul_le_mul_of_nonneg_left (square_diameter hY hV) (by positivity)
    _ = (Real.sqrt 2) ^ 2 * (C₂ / R ^ 2) := by ring
    _ = _ := by rw [Real.sq_sqrt (by norm_num)]; ring

theorem far_closed_four_point_bound {J R : ℕ} (hJ : 0 < J) (hR : 1 ≤ R)
    {C₂ : ℝ} (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (a b : MeshIndex J) (hfar : b ∉ nearbyCells R a) {x u y v : Torus}
    (hx : x ∈ closure (meshCell J hJ a)) (hu : u ∈ closure (meshCell J hJ a))
    (hy : y ∈ closure (meshCell J hJ b)) (hv : v ∈ closure (meshCell J hJ b)) :
    |greenKernel x y - greenKernel u y - greenKernel x v + greenKernel u v| ≤
      2 * C₂ / (R : ℝ) ^ 2 := by
  rw [closure_meshCell] at hx hu hy hv
  obtain ⟨X, hX, rfl⟩ := hx
  obtain ⟨U, hU, rfl⟩ := hu
  obtain ⟨Y, hY, rfl⟩ := hy
  obtain ⟨V, hV, rfl⟩ := hv
  have hsep : ∀ Z ∈ closedUnitSquare, ∀ W ∈ closedUnitSquare,
      (R : ℝ) / J ≤ torusEuclideanNorm
        (torusQuotient (affine (meshTranslation J a) J Z) -
          torusQuotient (affine (meshTranslation J b) J W)) := by
    intro Z hZ W hW
    simpa only [torusEuclideanDist, meshChart_eq_chart, GreenPointRescaling.chart] using
      far_cell_chart_gap hJ a b hfar hZ hW
  have hh := reference_four_point_bound (meshTranslation J a) (meshTranslation J b)
    (by exact_mod_cast hJ) (show (0 : ℝ) < R by exact_mod_cast (show 0 < R by omega))
    hC hk hsep hX hU hY hV
  simpa only [reverseSource, greenKernel, meshChart_eq_chart, GreenPointRescaling.chart] using hh

theorem green_abs_le_of_gap {s : ℝ} (hs : 0 < s) {z : Torus}
    (hz : s ≤ torusEuclideanNorm z) :
    |regularGreenRepresentative z| ≤ ConditionalLawEstimates.kernelConstant - Real.log s := by
  have hn : 0 < torusEuclideanNorm z := hs.trans_le hz
  have hz0 : z ≠ 0 := by intro h; subst z; simp at hn
  have hlog := Real.log_le_log hs hz
  have hlog0 := Real.log_nonpos hn.le (torusEuclideanNorm_le_one z)
  have hb := ConditionalLawEstimates.kernel_log_bound z hz0
  have ht := abs_sub (regularGreenRepresentative z + Real.log (torusEuclideanNorm z))
    (Real.log (torusEuclideanNorm z))
  rw [add_sub_cancel_right, abs_of_nonpos hlog0] at ht
  linarith

section Far
variable {J R : ℕ} (hJ : 0 < J) (hR : 1 ≤ R) (a b : MeshIndex J)
  (hfar : b ∉ nearbyCells R a)
  (μ ν : Measure Torus) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (hμ : ∀ᵐ x ∂μ, x ∈ closure (meshCell J hJ a))
  (hν : ∀ᵐ y ∂ν, y ∈ closure (meshCell J hJ b))

include hR hfar

theorem green_abs_le_on_far_cells {x y : Torus}
    (hx : x ∈ closure (meshCell J hJ a)) (hy : y ∈ closure (meshCell J hJ b)) :
    |greenKernel x y| ≤ ConditionalLawEstimates.kernelConstant - Real.log ((R : ℝ) / J) := by
  exact green_abs_le_of_gap (div_pos (by exact_mod_cast (show 0 < R by omega))
    (by exact_mod_cast hJ)) (far_closed_cells_gap hJ a b hfar hx hy)

include hν in
theorem integrable_green_right {x : Torus} (hx : x ∈ closure (meshCell J hJ a)) :
    Integrable (greenKernel x) ν := by
  apply Integrable.of_bound
    (regularGreenRepresentative_measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    (ConditionalLawEstimates.kernelConstant - Real.log ((R : ℝ) / J))
  filter_upwards [hν] with y hy
  exact green_abs_le_on_far_cells hJ hR a b hfar hx hy

include hμ in
theorem integrable_green_left {y : Torus} (hy : y ∈ closure (meshCell J hJ b)) :
    Integrable (fun x => greenKernel x y) μ := by
  apply Integrable.of_bound
    (regularGreenRepresentative_measurable.comp (measurable_id.sub measurable_const)).aestronglyMeasurable
    (ConditionalLawEstimates.kernelConstant - Real.log ((R : ℝ) / J))
  filter_upwards [hμ] with x hx
  exact green_abs_le_on_far_cells hJ hR a b hfar hx hy

include hμ hν in
theorem integrable_green_far : Integrable (Function.uncurry greenKernel) (μ.prod ν) := by
  apply Integrable.of_bound measurable_greenKernel.aestronglyMeasurable
    (ConditionalLawEstimates.kernelConstant - Real.log ((R : ℝ) / J))
  have hx := (measurePreserving_fst (μ := μ) (ν := ν)).quasiMeasurePreserving.ae hμ
  have hy := (measurePreserving_snd (μ := μ) (ν := ν)).quasiMeasurePreserving.ae hν
  filter_upwards [hx, hy] with z hz hz'
  exact green_abs_le_on_far_cells hJ hR a b hfar hz hz'

include hμ hν in
theorem residual_eq_four_point_average {x y : Torus}
    (hx : x ∈ closure (meshCell J hJ a)) (hy : y ∈ closure (meshCell J hJ b)) :
    residual μ ν x y = ∫ u, ∫ v,
      greenKernel x y - greenKernel u y - greenKernel x v + greenKernel u v ∂ν ∂μ := by
  have hix := integrable_green_right hJ hR a b hfar ν hν hx
  have hiy := integrable_green_left hJ hR a b hfar μ hμ hy
  have hi := integrable_green_far hJ hR a b hfar μ ν hμ hν
  have hr : Integrable (fun u => ∫ v, greenKernel u v ∂ν) μ := hi.integral_prod_left
  have he : (∫ u, ∫ v,
      greenKernel x y - greenKernel u y - greenKernel x v + greenKernel u v ∂ν ∂μ) =
      ∫ u, greenKernel x y - greenKernel u y - (∫ v, greenKernel x v ∂ν) +
        (∫ v, greenKernel u v ∂ν) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hμ] with u hu
    have hiu := integrable_green_right hJ hR a b hfar ν hν hu
    have hc : Integrable (fun _ : Torus => greenKernel x y - greenKernel u y) ν := integrable_const _
    have hs : Integrable (fun v => greenKernel x y - greenKernel u y - greenKernel x v) ν := hc.sub hix
    rw [integral_add hs hiu, integral_sub hc hix]
    simp only [integral_const, probReal_univ, one_smul]
  rw [he]
  have hc : Integrable (fun _ : Torus => greenKernel x y) μ := integrable_const _
  have hs : Integrable (fun u => greenKernel x y - greenKernel u y) μ := hc.sub hiy
  have hv : Integrable (fun _ : Torus => ∫ v, greenKernel x v ∂ν) μ := integrable_const _
  have ht : Integrable (fun u => greenKernel x y - greenKernel u y - ∫ v, greenKernel x v ∂ν) μ :=
    hs.sub hv
  rw [integral_add ht hr, integral_sub hs hv, integral_sub hc hiy]
  simp only [integral_const, probReal_univ, one_smul]
  unfold ReferenceResidual.residual ResidualDoubleCentering.doubleCenter
  ring

include hμ hν in
theorem far_residual_bound {C₂ : ℝ} (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    {x y : Torus} (hx : x ∈ closure (meshCell J hJ a))
    (hy : y ∈ closure (meshCell J hJ b)) :
    |residual μ ν x y| ≤ 2 * C₂ / (R : ℝ) ^ 2 := by
  rw [residual_eq_four_point_average hJ hR a b hfar μ ν hμ hν hx hy, ← Real.norm_eq_abs]
  have hi : ∀ᵐ u ∂μ, ‖∫ v, greenKernel x y - greenKernel u y - greenKernel x v +
      greenKernel u v ∂ν‖ ≤ 2 * C₂ / (R : ℝ) ^ 2 := by
    filter_upwards [hμ] with u hu
    have hh : ∀ᵐ v ∂ν, ‖greenKernel x y - greenKernel u y - greenKernel x v +
        greenKernel u v‖ ≤ 2 * C₂ / (R : ℝ) ^ 2 := by
      filter_upwards [hν] with v hv
      exact far_closed_four_point_bound hJ hR hC hk a b hfar hx hu hy hv
    simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hh
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hi

include hμ hν in
theorem far_residual_integrable_canonical :
    Integrable (Function.uncurry (residual μ ν)) (μ.prod ν) ∧
    (∀ᵐ y ∂ν, (∫ x, residual μ ν x y ∂μ) = 0) ∧
    (∀ᵐ x ∂μ, (∫ y, residual μ ν x y ∂ν) = 0) := by
  have hi := integrable_green_far hJ hR a b hfar μ ν hμ hν
  exact ⟨ResidualDoubleCentering.integrable_doubleCenter μ ν greenKernel hi,
    ResidualDoubleCentering.ae_integral_doubleCenter_left_eq_zero μ ν greenKernel hi,
    ResidualDoubleCentering.ae_integral_doubleCenter_right_eq_zero μ ν greenKernel hi⟩

end Far

/-- The source d−1 estimate for every point of the full prescribed closures.
All support and integrability inputs are derived from the reference densities. -/
theorem far_residual_density_bound {J : ℕ} (hJ : 0 < J) (a b : MeshIndex J)
    (hd : 2 ≤ periodicIndexDistance a b) {C₂ : ℝ}
    (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (μ ν : Measure Torus) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (wa wb : Torus → ℝ≥0∞)
    (hμw : μ = (meshCellMeasure J hJ a).withDensity wa)
    (hνw : ν = (meshCellMeasure J hJ b).withDensity wb)
    (hwa : ∀ᵐ x ∂meshCellMeasure J hJ a,
      ENNReal.ofReal (Real.exp (-1)) ≤ wa x ∧ wa x ≤ ENNReal.ofReal (Real.exp 1))
    (hwb : ∀ᵐ y ∂meshCellMeasure J hJ b,
      ENNReal.ofReal (Real.exp (-1)) ≤ wb y ∧ wb y ≤ ENNReal.ofReal (Real.exp 1)) :
    Integrable (Function.uncurry greenKernel) (μ.prod ν) ∧
    Integrable (Function.uncurry (residual μ ν)) (μ.prod ν) ∧
    (∀ᵐ y ∂ν, (∫ x, residual μ ν x y ∂μ) = 0) ∧
    (∀ᵐ x ∂μ, (∫ y, residual μ ν x y ∂ν) = 0) ∧
    ∀ x ∈ closure (meshCell J hJ a), ∀ y ∈ closure (meshCell J hJ b),
      |residual μ ν x y| ≤ 2 * C₂ / ((periodicIndexDistance a b : ℝ) - 1) ^ 2 := by
  let R := periodicIndexDistance a b - 1
  have hR : 1 ≤ R := by dsimp [R]; omega
  have hfar : b ∉ nearbyCells R a := by
    rw [mem_nearbyCells]
    dsimp [R]
    omega
  have hμ' : μ ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a := by
    rw [hμw]
    exact NearLogMomentBounds.withDensity_le_exp_smul _ _ (hwa.mono fun _ h => h.2)
  have hν' : ν ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ b := by
    rw [hνw]
    exact NearLogMomentBounds.withDensity_le_exp_smul _ _ (hwb.mono fun _ h => h.2)
  have hsμ := ae_mem_closed_cell_of_domination hJ a μ hμ'
  have hsν := ae_mem_closed_cell_of_domination hJ b ν hν'
  have hcan := far_residual_integrable_canonical hJ hR a b hfar μ ν hsμ hsν
  refine ⟨integrable_green_far hJ hR a b hfar μ ν hsμ hsν, hcan.1, hcan.2.1, hcan.2.2, ?_⟩
  intro x hx y hy
  have he : (R : ℝ) = (periodicIndexDistance a b : ℝ) - 1 := by
    dsimp [R]
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  simpa only [he] using far_residual_bound hJ hR a b hfar μ ν hsμ hsν hC hk hx hy
end PeriodicAttractiveLogGas.FarReferenceResidual
