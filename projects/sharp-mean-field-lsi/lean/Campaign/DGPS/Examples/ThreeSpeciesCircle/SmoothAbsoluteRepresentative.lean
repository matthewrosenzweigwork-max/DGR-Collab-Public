import DGPS.Examples.ThreeSpeciesCircle.OrdinaryOptimizers

/-! Store a supplied AE root representative in the original absolute-density
record. All H1/probability constraints and the original probability law are
transported. A supplied smooth positive root is retained literally. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The supplied representative is stored exactly; the original actual law,
H1 membership, nonnegativity and normalization are transported through AE equality. -/
def absoluteDensityWithRoot (ρ : AbsoluteDensity 1) (v : Torus 1 → ℝ)
    (hrep : ρ.sqrt =ᵐ[haar 1] v) : AbsoluteDensity 1 where
  sqrt := v
  sqrt_mem := mem_H1Haar_congr_ae ρ.sqrt_mem hrep
  sqrt_nonneg := by
    filter_upwards [hrep, ρ.sqrt_nonneg] with x hx hn
    rwa [← hx]
  mass_one := by
    calc
      (∫ x, v x ^ 2 ∂haar 1) = ∫ x, ρ.sqrt x ^ 2 ∂haar 1 :=
        integral_congr_ae (hrep.symm.mono fun x hx => congrArg (fun a : ℝ => a ^ 2) hx)
      _ = 1 := ρ.mass_one

@[simp] theorem absoluteDensityWithRoot_sqrt (ρ : AbsoluteDensity 1) (v : Torus 1 → ℝ)
    (hrep : ρ.sqrt =ᵐ[haar 1] v) : (absoluteDensityWithRoot ρ v hrep).sqrt = v := rfl

theorem absoluteDensityWithRoot_law (ρ : AbsoluteDensity 1) (v : Torus 1 → ℝ)
    (hrep : ρ.sqrt =ᵐ[haar 1] v) : densityMeasure (absoluteDensityWithRoot ρ v hrep) =
      densityMeasure ρ := by
  apply Subtype.ext
  apply withDensity_congr_ae
  exact hrep.symm.mono fun x hx => congrArg ENNReal.ofReal (congrArg (fun a : ℝ => a ^ 2) hx)

theorem absoluteDensityWithRoot_integral (ρ : AbsoluteDensity 1) (v : Torus 1 → ℝ)
    (hrep : ρ.sqrt =ᵐ[haar 1] v) (g : Torus 1 → ℝ) :
    (∫ x, g x ∂(densityMeasure (absoluteDensityWithRoot ρ v hrep) : Measure (Torus 1))) =
      ∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1)) := by
  rw [absoluteDensityWithRoot_law]

theorem absoluteDensityWithRoot_ordinaryEntropy (h : ℝ) (ρ : AbsoluteDensity 1)
    (v : Torus 1 → ℝ) (hrep : ρ.sqrt =ᵐ[haar 1] v) :
    ordinaryEntropy h (absoluteDensityWithRoot ρ v hrep) = ordinaryEntropy h ρ := by
  unfold ordinaryEntropy
  rw [absoluteDensityWithRoot_law]

theorem absoluteDensityWithRoot_ordinaryFisher (h : ℝ) (ρ : AbsoluteDensity 1)
    (v : Torus 1 → ℝ) (hrep : ρ.sqrt =ᵐ[haar 1] v) :
    ordinaryFisher h (absoluteDensityWithRoot ρ v hrep) = ordinaryFisher h ρ := by
  unfold ordinaryFisher
  rw [absoluteDensityWithRoot_law]

/-- Smoothness and strict positivity of the supplied root are inherited by
the genuine original-domain density record, with its original law unchanged. -/
theorem absoluteDensityWithRoot_smooth_positive (ρ : AbsoluteDensity 1) (v : Torus 1 → ℝ)
    (hrep : ρ.sqrt =ᵐ[haar 1] v) (hv : IsSmoothPeriodic v) (hp : ∀ x, 0 < v x) :
    IsSmoothPeriodic (absoluteDensityWithRoot ρ v hrep).sqrt ∧
      (∀ x, 0 < (absoluteDensityWithRoot ρ v hrep).sqrt x) ∧
      densityMeasure (absoluteDensityWithRoot ρ v hrep) = densityMeasure ρ :=
  ⟨hv, hp, absoluteDensityWithRoot_law ρ v hrep⟩

end DGPS.Examples.ThreeSpeciesCircle
