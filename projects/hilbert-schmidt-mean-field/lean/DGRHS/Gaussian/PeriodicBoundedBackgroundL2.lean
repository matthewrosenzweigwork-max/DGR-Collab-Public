import DGRHS.Gaussian.PeriodicLogKernelSections
import DGRHS.Gaussian.HoeffdingL2
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed.

Bounded-background product L2 transfer on the normalized finite-dimensional
unit torus. The real kernel representative is supplied with strong
measurability and Haar L2, not a desired product-law or centering conclusion.
The quantitative centering constant is the checked value four.

The technical measure bounds use the clipped density `ENNReal.ofReal` and do
not infer raw-density nonnegativity. The final source-shaped corollary retains
measurability and nonnegativity of the density explicitly. This is a static
L2 dependency, not a torus partition, concentration, or dynamic theorem.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The background law associated with the supplied real density. -/
def periodicCappedDensityMeasure (ρ : PeriodicTorus ι → ℝ) : Measure (PeriodicTorus ι) :=
  (periodicHaar ι).withDensity (fun x => ENNReal.ofReal (ρ x))

lemma periodicCappedDensityMeasure_le (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    periodicCappedDensityMeasure ρ ≤ ENNReal.ofReal M • periodicHaar ι := by
  have h : (fun x => ENNReal.ofReal (ρ x)) ≤ᵐ[periodicHaar ι]
      (fun _ => ENNReal.ofReal M) := hρ.mono (fun _ hx => ENNReal.ofReal_le_ofReal hx)
  simpa only [periodicCappedDensityMeasure, withDensity_const] using
    (withDensity_mono h)

lemma periodicCappedDensityMeasure_prod_le (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    (periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ) ≤
      (ENNReal.ofReal M * ENNReal.ofReal M) • ((periodicHaar ι).prod (periodicHaar ι)) := by
  letI : SFinite (periodicCappedDensityMeasure ρ) := by
    unfold periodicCappedDensityMeasure
    infer_instance
  have h := periodicCappedDensityMeasure_le ρ M hρ
  simpa only [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul] using
    (Measure.prod_mono h h)

lemma periodicPair_memLp_of_density_cap (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (g : PeriodicTorus ι → ℝ)
    (hg : MemLp g 2 (periodicHaar ι)) :
    MemLp (fun p : PeriodicTorus ι × PeriodicTorus ι => g (p.1 - p.2)) 2
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) := by
  have hp := hg.comp_measurePreserving (periodicHaar_preserving_difference (ι := ι))
  exact hp.of_measure_le_smul (by finiteness) (periodicCappedDensityMeasure_prod_le ρ M hρ)

lemma periodicPair_sq_integral_le_of_density_cap (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (g : PeriodicTorus ι → ℝ) (hgm : StronglyMeasurable g)
    (hg : MemLp g 2 (periodicHaar ι)) :
    (∫ p : PeriodicTorus ι × PeriodicTorus ι, g (p.1 - p.2) ^ 2
      ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) ≤
        M ^ 2 * ∫ x, g x ^ 2 ∂periodicHaar ι := by
  have hp := hg.comp_measurePreserving (periodicHaar_preserving_difference (ι := ι))
  have hi := hp.integrable_sq.smul_measure
    (c := ENNReal.ofReal M * ENNReal.ofReal M) (by finiteness)
  have hmono := integral_mono_measure (periodicCappedDensityMeasure_prod_le ρ M hρ)
    (Filter.Eventually.of_forall (fun p => sq_nonneg (g (p.1 - p.2)))) hi
  have hpair : (∫ p : PeriodicTorus ι × PeriodicTorus ι, g (p.1 - p.2) ^ 2
      ∂(periodicHaar ι).prod (periodicHaar ι)) = ∫ x, g x ^ 2 ∂periodicHaar ι := by
    have he := integral_map_of_stronglyMeasurable
      (μ := (periodicHaar ι).prod (periodicHaar ι))
      (periodicHaar_preserving_difference (ι := ι)).measurable (hgm.pow 2)
    rw [(periodicHaar_preserving_difference (ι := ι)).map_eq] at he
    exact he.symm
  simpa only [integral_smul_measure, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hM,
    smul_eq_mul, ← pow_two, hpair] using hmono

lemma periodicPair_norm_le_of_density_cap (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (g : PeriodicTorus ι → ℝ) (hgm : StronglyMeasurable g)
    (hg : MemLp g 2 (periodicHaar ι)) :
    ‖(periodicPair_memLp_of_density_cap ρ M hρ g hg).toLp
      (fun p : PeriodicTorus ι × PeriodicTorus ι => g (p.1 - p.2))‖ ≤ M * ‖hg.toLp g‖ := by
  have hs := periodicPair_sq_integral_le_of_density_cap ρ M hM hρ g hgm hg
  rw [← DGRHS.Kernel.norm_toLp_sq (periodicPair_memLp_of_density_cap ρ M hρ g hg),
    ← DGRHS.Kernel.norm_toLp_sq hg] at hs
  have hright : 0 ≤ M * ‖hg.toLp g‖ := mul_nonneg hM (norm_nonneg _)
  nlinarith [norm_nonneg ((periodicPair_memLp_of_density_cap ρ M hρ g hg).toLp
    (fun p : PeriodicTorus ι × PeriodicTorus ι => g (p.1 - p.2)))]

lemma periodicCenteredPair_memLp_of_density_cap (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (g : PeriodicTorus ι → ℝ)
    (hgm : StronglyMeasurable g) (hg : MemLp g 2 (periodicHaar ι)) :
    MemLp (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      DGRHS.centeredKernel (periodicCappedDensityMeasure ρ) (fun x y => g (x-y)) p.1 p.2) 2
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) := by
  exact DGRHS.Gaussian.memLp_hoeffdingCentered (periodicCappedDensityMeasure ρ)
    (fun p : PeriodicTorus ι × PeriodicTorus ι => g (p.1-p.2))
    (hgm.comp_measurable (measurable_fst.sub measurable_snd))
    (periodicPair_memLp_of_density_cap ρ M hρ g hg)

lemma periodicCenteredPair_norm_le_of_density_cap (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ)
    (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (g : PeriodicTorus ι → ℝ) (hgm : StronglyMeasurable g)
    (hg : MemLp g 2 (periodicHaar ι)) :
    ‖(periodicCenteredPair_memLp_of_density_cap ρ M hρ g hgm hg).toLp
      (fun p : PeriodicTorus ι × PeriodicTorus ι =>
        DGRHS.centeredKernel (periodicCappedDensityMeasure ρ) (fun x y => g (x-y)) p.1 p.2)‖ ≤
      4 * M * ‖hg.toLp g‖ := by
  have hc := DGRHS.Gaussian.norm_hoeffdingCentered_le (periodicCappedDensityMeasure ρ)
    (fun p : PeriodicTorus ι × PeriodicTorus ι => g (p.1-p.2))
    (hgm.comp_measurable (measurable_fst.sub measurable_snd))
    (periodicPair_memLp_of_density_cap ρ M hρ g hg)
  have hp := periodicPair_norm_le_of_density_cap ρ M hM hρ g hgm hg
  calc
    _ ≤ 4 * ‖(periodicPair_memLp_of_density_cap ρ M hρ g hg).toLp
        (fun p : PeriodicTorus ι × PeriodicTorus ι => g (p.1-p.2))‖ := hc
    _ ≤ 4 * (M * ‖hg.toLp g‖) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by ring

/-- Source-shaped bounded nonnegative density corollary. Measurability and
nonnegativity identify the intended density class; the stronger technical
measure estimates above already work for its `ofReal` law. -/
theorem periodicBoundedBackground_centeredL2 (ρ : PeriodicTorus ι → ℝ)
    (_hρm : Measurable ρ) (_hρ0 : ∀ᵐ x ∂periodicHaar ι, 0 ≤ ρ x)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ)
    (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (g : PeriodicTorus ι → ℝ) (hgm : StronglyMeasurable g)
    (hg : MemLp g 2 (periodicHaar ι)) :
    ‖(periodicCenteredPair_memLp_of_density_cap ρ M hρ g hgm hg).toLp
      (fun p : PeriodicTorus ι × PeriodicTorus ι =>
        DGRHS.centeredKernel (periodicCappedDensityMeasure ρ) (fun x y => g (x-y)) p.1 p.2)‖ ≤
      4 * M * ‖hg.toLp g‖ :=
  periodicCenteredPair_norm_le_of_density_cap ρ M hM hρ g hgm hg

end DGRHS.Periodic
