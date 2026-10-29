import LeanResearch.PeriodicAttractiveLogGas.NearCellLifts
import LeanResearch.PeriodicAttractiveLogGas.NearLogMomentBounds

/-! The actual reference residual and the near half of source
`lem:residual-kernels`. The supplied cell geometry, logarithmic integral,
single density comparison and double centering are all discharged here. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PeriodicAttractiveLogGas.ReferenceResidual

open MeshCells MeshNearbyGeometry NearCellLifts NearLogMomentBounds

def greenKernel (x y : Torus) : ℝ := regularGreenRepresentative (x - y)

theorem measurable_greenKernel : Measurable (Function.uncurry greenKernel) :=
  regularGreenRepresentative_measurable.comp (measurable_fst.sub measurable_snd)

theorem greenKernel_symm (x y : Torus) : greenKernel x y = greenKernel y x := by
  unfold greenKernel
  rw [← regularGreenRepresentative_even (y - x), neg_sub]

def potential (μ : Measure Torus) (x : Torus) : ℝ := ∫ y, greenKernel x y ∂μ
def pairAverage (μ ν : Measure Torus) : ℝ := ∫ x, potential ν x ∂μ
def residual (μ ν : Measure Torus) : Torus → Torus → ℝ :=
  ResidualDoubleCentering.doubleCenter μ ν greenKernel

theorem residual_eq_source_order (μ ν : Measure Torus) (x y : Torus) :
    residual μ ν x y = greenKernel x y - potential ν x - potential μ y + pairAverage μ ν :=
  ResidualDoubleCentering.doubleCenter_eq_source_order μ ν greenKernel greenKernel_symm x y

def nearScale (R : ℕ) : ℝ :=
  nearResidualScale (Real.log (cellReferenceRadius R) + ConditionalLawEstimates.kernelConstant)

theorem nearScale_eq_source (R : ℕ) :
    nearScale R = (42 * Real.exp 1 / 5) *
      (2 * Real.log (Real.sqrt 2 * ((R : ℝ) + 1)) +
        2 * ConditionalLawEstimates.kernelConstant + 1) := by
  unfold nearScale nearResidualScale cellReferenceRadius
  ring

theorem nearScale_nonneg (R : ℕ) : 0 ≤ nearScale R :=
  nearResidualScale_nonneg (near_shift_bound_nonneg R)

theorem ae_mem_closed_cell_of_domination {J : ℕ} (hJ : 0 < J)
    (a : MeshIndex J) (μ : Measure Torus)
    (hμ : μ ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a) :
    ∀ᵐ x ∂μ, x ∈ closure (meshCell J hJ a) := by
  apply hμ.absolutelyContinuous.ae_le
  exact Measure.ae_smul_measure ((ae_mem_meshCell J hJ a).mono fun _ hx => subset_closure hx) _

section Near
variable {J R : ℕ} (hJ : 0 < J) (hmesh : 8 * (R + 1) ≤ J)
  (a b : MeshIndex J) (hab : periodicIndexDistance a b ≤ R)
  (μ ν : Measure Torus) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (hμ : μ ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
  (hν : ν ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ b)

include hmesh hab hμ hν

/-- This conclusion concerns the literal shifted Green kernel. Both geometric
dominations are proved from actual cell support, including coincident cells. -/
theorem shifted_near_bounds {p : ℕ} (hp : 1 ≤ p) :
    let K := fun x y => greenKernel x y - Real.log (J : ℝ)
    Measurable (Function.uncurry (ResidualDoubleCentering.doubleCenter μ ν K)) ∧
    Integrable (Function.uncurry K) (μ.prod ν) ∧
    Integrable (Function.uncurry (ResidualDoubleCentering.doubleCenter μ ν K)) (μ.prod ν) ∧
    MemLp (Function.uncurry (ResidualDoubleCentering.doubleCenter μ ν K)) (p : ℝ≥0∞) (μ.prod ν) ∧
    (∀ᵐ y ∂ν, (∫ x, ResidualDoubleCentering.doubleCenter μ ν K x y ∂μ) = 0) ∧
    (∀ᵐ x ∂μ, (∫ y, ResidualDoubleCentering.doubleCenter μ ν K x y ∂ν) = 0) ∧
    essSup (CanonicalRowHolder.leftMoment μ (ResidualDoubleCentering.doubleCenter μ ν K) p) ν ≤
      ENNReal.ofReal (nearScale R ^ p * (p.factorial : ℝ)) ∧
    essSup (CanonicalRowHolder.rightMoment ν (ResidualDoubleCentering.doubleCenter μ ν K) p) μ ≤
      ENNReal.ofReal (nearScale R ^ p * (p.factorial : ℝ)) := by
  apply near_residual_kernel_bounds (meshCellMeasure J hJ a) (meshCellMeasure J hJ b)
    μ ν (meshChart J a) (meshChart J b) (fun x y => greenKernel x y - Real.log (J : ℝ))
    (measurePreserving_meshChart J hJ a) (measurePreserving_meshChart J hJ b)
    hμ hν (measurable_greenKernel.sub measurable_const) (near_shift_bound_nonneg R) ?_ ?_ hp
  · filter_upwards [ae_mem_closed_cell_of_domination hJ b ν hν] with y hy
    obtain ⟨Y, _, hY⟩ := exists_ae_shifted_green_domination hJ hmesh a b hab hy
    exact ⟨Y, hY⟩
  · filter_upwards [ae_mem_closed_cell_of_domination hJ a μ hμ] with x hx
    have hba : periodicIndexDistance b a ≤ R := by rw [periodicIndexDistance_comm]; exact hab
    obtain ⟨Y, _, hY⟩ := exists_ae_shifted_green_domination hJ hmesh b a hba hx
    refine ⟨Y, ?_⟩
    filter_upwards [hY] with Z hZ
    rw [greenKernel_symm x]
    exact hZ

/-- The actual unshifted residual has the manuscript's individual conditional
factorial bounds, with all integrability and both canonicalities established. -/
theorem near_residual_bounds {p : ℕ} (hp : 1 ≤ p) :
    Measurable (Function.uncurry (residual μ ν)) ∧
    Integrable (Function.uncurry greenKernel) (μ.prod ν) ∧
    Integrable (Function.uncurry (residual μ ν)) (μ.prod ν) ∧
    MemLp (Function.uncurry (residual μ ν)) (p : ℝ≥0∞) (μ.prod ν) ∧
    (∀ᵐ y ∂ν, (∫ x, residual μ ν x y ∂μ) = 0) ∧
    (∀ᵐ x ∂μ, (∫ y, residual μ ν x y ∂ν) = 0) ∧
    essSup (CanonicalRowHolder.leftMoment μ (residual μ ν) p) ν ≤
      ENNReal.ofReal (nearScale R ^ p * (p.factorial : ℝ)) ∧
    essSup (CanonicalRowHolder.rightMoment ν (residual μ ν) p) μ ≤
      ENNReal.ofReal (nearScale R ^ p * (p.factorial : ℝ)) := by
  obtain ⟨hsm, hsi, hsri, hsmem, _, _, hsl, hsr⟩ :=
    shifted_near_bounds hJ hmesh a b hab μ ν hμ hν hp
  have hi : Integrable (Function.uncurry greenKernel) (μ.prod ν) := by
    apply (hsi.add (integrable_const (Real.log (J : ℝ)))).congr
    exact Eventually.of_forall fun z => sub_add_cancel (greenKernel z.1 z.2) (Real.log (J : ℝ))
  have hm := ResidualDoubleCentering.measurable_doubleCenter μ ν greenKernel measurable_greenKernel
  have hae := ResidualDoubleCentering.doubleCenter_sub_const μ ν greenKernel hi (Real.log (J : ℝ))
  have har := Measure.ae_ae_of_ae_prod hae
  have hal := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae hae)
  have hml : CanonicalRowHolder.leftMoment μ
      (ResidualDoubleCentering.doubleCenter μ ν (fun x y => greenKernel x y - Real.log (J : ℝ))) p
      =ᵐ[ν] CanonicalRowHolder.leftMoment μ (residual μ ν) p := by
    filter_upwards [hal] with y hy
    exact lintegral_congr_ae (hy.mono fun x hx => congrArg (fun t : ℝ => ‖t‖ₑ ^ p) hx)
  have hmr : CanonicalRowHolder.rightMoment ν
      (ResidualDoubleCentering.doubleCenter μ ν (fun x y => greenKernel x y - Real.log (J : ℝ))) p
      =ᵐ[μ] CanonicalRowHolder.rightMoment ν (residual μ ν) p := by
    filter_upwards [har] with x hx
    exact lintegral_congr_ae (hx.mono fun y hy => congrArg (fun t : ℝ => ‖t‖ₑ ^ p) hy)
  refine ⟨hm, hi, ResidualDoubleCentering.integrable_doubleCenter μ ν greenKernel hi,
    hsmem.ae_eq hae, ResidualDoubleCentering.ae_integral_doubleCenter_left_eq_zero μ ν greenKernel hi,
    ResidualDoubleCentering.ae_integral_doubleCenter_right_eq_zero μ ν greenKernel hi, ?_, ?_⟩
  · rw [← essSup_congr_ae hml]
    exact hsl
  · rw [← essSup_congr_ae hmr]
    exact hsr

omit hμ hν in
/-- The exact source density assumption implies the measure comparison used
above; the lower bound remains part of the supplied reference hypothesis. -/
theorem near_residual_density_moments
    (wa wb : Torus → ℝ≥0∞)
    (hμw : μ = (meshCellMeasure J hJ a).withDensity wa)
    (hνw : ν = (meshCellMeasure J hJ b).withDensity wb)
    (hwa : ∀ᵐ x ∂meshCellMeasure J hJ a,
      ENNReal.ofReal (Real.exp (-1)) ≤ wa x ∧ wa x ≤ ENNReal.ofReal (Real.exp 1))
    (hwb : ∀ᵐ y ∂meshCellMeasure J hJ b,
      ENNReal.ofReal (Real.exp (-1)) ≤ wb y ∧ wb y ≤ ENNReal.ofReal (Real.exp 1))
    {p : ℕ} (hp : 1 ≤ p) :
    essSup (CanonicalRowHolder.leftMoment μ (residual μ ν) p) ν ≤
      ENNReal.ofReal (nearScale R ^ p * (p.factorial : ℝ)) ∧
    essSup (CanonicalRowHolder.rightMoment ν (residual μ ν) p) μ ≤
      ENNReal.ofReal (nearScale R ^ p * (p.factorial : ℝ)) := by
  have hμ' : μ ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a := by
    rw [hμw]
    exact withDensity_le_exp_smul _ _ (hwa.mono fun _ h => h.2)
  have hν' : ν ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ b := by
    rw [hνw]
    exact withDensity_le_exp_smul _ _ (hwb.mono fun _ h => h.2)
  exact (near_residual_bounds hJ hmesh a b hab μ ν hμ' hν' hp).2.2.2.2.2.2

end Near
end PeriodicAttractiveLogGas.ReferenceResidual
