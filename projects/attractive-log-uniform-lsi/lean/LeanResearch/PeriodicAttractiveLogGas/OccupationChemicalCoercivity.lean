import LeanResearch.PeriodicAttractiveLogGas.GreenL2Coercivity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The actual chemical-potential equation and its L2 coercivity near
the uniform occupation profile, source lines 1960--1983. Discrete cell
Poincare and the subsequent root-rate comparison are separate. The
development record gives the exact checking and source-correspondence
status. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace PeriodicAttractiveLogGas.OccupationChemicalCoercivity
open MeshCells OccupationNearContraction

def neighborhood (β₀ : ℝ) : ℝ := min (1 / 8) (3 * GreenL2Coercivity.gap β₀ / 32)

theorem neighborhood_pos {β₀ : ℝ} (hsub : β₀ < 4) : 0 < neighborhood β₀ := by
  exact lt_min (by norm_num) (by have := GreenL2Coercivity.gap_pos hsub; positivity)

theorem profile_positive {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ} {β₀ : ℝ}
    (hnear : profileDeviation θ ≤ neighborhood β₀) (a : MeshIndex J) : 0 < θ a := by
  have ha := (abs_le.mp (profileDeviation_apply_le θ a)).1
  have hn : profileDeviation θ ≤ 1 / 8 := hnear.trans (min_le_left _ _)
  have hp : 0 < (J : ℝ) ^ 2 := pow_pos (by exact_mod_cast hJ) 2
  have hh : 0 < (J : ℝ) ^ 2 * θ a := by linarith
  exact (mul_pos_iff_of_pos_left hp).mp hh

/-- The literal value of a cellwise constant function on the half-open partition. -/
def cellValue {J : ℕ} (hJ : 0 < J) (c : MeshIndex J → ℝ) (x : Torus) : ℝ :=
  c (meshLabel J hJ x)

theorem cellValue_eq_sum {J : ℕ} (hJ : 0 < J) (c : MeshIndex J → ℝ) (x : Torus) :
    cellValue hJ c x = ∑ a, (meshCell J hJ a).indicator (fun _ ↦ c a) x := by
  classical
  rw [Finset.sum_eq_single (meshLabel J hJ x)]
  · rw [indicator_of_mem (show x ∈ meshCell J hJ (meshLabel J hJ x) from rfl)]
    rfl
  · intro a _ ha
    exact indicator_of_notMem (show x ∉ meshCell J hJ a from fun hx ↦ ha hx.symm)
      (fun _ : Torus ↦ c a)
  · simp

theorem cellValue_memLp {J : ℕ} (hJ : 0 < J) (c : MeshIndex J → ℝ) (p : ℝ≥0∞) :
    MemLp (cellValue hJ c) p torusMeasure := by
  have he : cellValue hJ c = fun x ↦ ∑ a, (meshCell J hJ a).indicator (fun _ ↦ c a) x :=
    funext (cellValue_eq_sum hJ c)
  rw [he]
  exact memLp_finsetSum _ fun a _ ↦ (memLp_const (c a)).indicator (measurableSet_meshCell J hJ a)

theorem cellValue_measurable {J : ℕ} (hJ : 0 < J) (c : MeshIndex J → ℝ) :
    Measurable (cellValue hJ c) := by
  have he : cellValue hJ c = fun x ↦ ∑ a, (meshCell J hJ a).indicator (fun _ ↦ c a) x :=
    funext (cellValue_eq_sum hJ c)
  rw [he]
  exact Finset.measurable_sum _ fun a _ ↦ measurable_const.indicator (measurableSet_meshCell J hJ a)

theorem integral_cellValue {J : ℕ} (hJ : 0 < J) (c : MeshIndex J → ℝ) :
    (∫ x, cellValue hJ c x ∂torusMeasure) = ((J : ℝ) ^ 2)⁻¹ * ∑ a, c a := by
  simp_rw [cellValue_eq_sum]
  rw [integral_finsetSum Finset.univ (fun a _ ↦
    (integrable_const (c a)).indicator (measurableSet_meshCell J hJ a))]
  simp only [integral_indicator (measurableSet_meshCell J hJ _), setIntegral_const,
    Measure.real, torusMeasure_meshCell, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, smul_eq_mul, Finset.mul_sum]

theorem cellValue_variance_integral {J : ℕ} (hJ : 0 < J) (c : MeshIndex J → ℝ) :
    (∫ x, (cellValue hJ c x - ∫ y, cellValue hJ c y ∂torusMeasure) ^ 2 ∂torusMeasure) =
      ((J : ℝ) ^ 2)⁻¹ * ∑ a, (c a - ∫ y, cellValue hJ c y ∂torusMeasure) ^ 2 :=
  integral_cellValue hJ (fun a ↦ (c a - ∫ y, cellValue hJ c y ∂torusMeasure) ^ 2)

def coefficient {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ)
    (β : ℝ) (f : L4) (a : MeshIndex J) : ℝ :=
  Real.log (θ a / cellIntegral hJ (scaledPotential β f) a)

def chemicalValue {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ)
    (β : ℝ) (f : L4) : Torus → ℝ := cellValue hJ (coefficient hJ θ β f)

theorem coefficient_argument_pos {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ}
    {β₀ : ℝ} (hnear : profileDeviation θ ≤ neighborhood β₀) (β : ℝ) (f : L4)
    (a : MeshIndex J) : 0 < θ a / cellIntegral hJ (scaledPotential β f) a :=
  div_pos (profile_positive hJ hnear a) (cellIntegral_pos hJ (continuous_scaledPotential β f) a)

theorem occupationMapValue_eq_chemical {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ)
    (β : ℝ) (f : L4) (x : Torus) :
    occupationMapValue hJ θ β f x =
      (θ (meshLabel J hJ x) / cellIntegral hJ (scaledPotential β f) (meshLabel J hJ x)) *
        Real.exp (scaledPotential β f x) := by
  rw [occupationMapValue_apply]
  have hh := cellDensity_haar hJ (continuous_scaledPotential β f) (meshLabel J hJ x) x
  calc
    _ = θ (meshLabel J hJ x) * ((J : ℝ) ^ 2 *
        cellDensity hJ (scaledPotential β f) (meshLabel J hJ x) x) := by ring
    _ = _ := by rw [hh]; ring

theorem occupationMapValue_log {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ}
    {β₀ : ℝ} (hnear : profileDeviation θ ≤ neighborhood β₀) (β : ℝ) (f : L4) (x : Torus) :
    Real.log (occupationMapValue hJ θ β f x) =
      scaledPotential β f x + chemicalValue hJ θ β f x := by
  rw [occupationMapValue_eq_chemical,
    Real.log_mul (coefficient_argument_pos hJ hnear β f _).ne' (Real.exp_ne_zero _), Real.log_exp]
  change coefficient hJ θ β f (meshLabel J hJ x) + scaledPotential β f x = _
  exact add_comm _ _

theorem occupationMapValue_cell_mass {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ)
    (β : ℝ) (f : L4) (a : MeshIndex J) :
    (∫ x in meshCell J hJ a, occupationMapValue hJ θ β f x ∂torusMeasure) = θ a := by
  have he : (∫ x in meshCell J hJ a, occupationMapValue hJ θ β f x ∂torusMeasure) =
      ∫ x in meshCell J hJ a, (θ a / cellIntegral hJ (scaledPotential β f) a) *
        Real.exp (scaledPotential β f x) ∂torusMeasure := by
    apply setIntegral_congr_fun (measurableSet_meshCell J hJ a)
    intro x hx
    rw [occupationMapValue_eq_chemical, (mem_meshCell J hJ a x).mp hx]
  rw [he, integral_const_mul]
  change θ a / cellIntegral hJ (scaledPotential β f) a * cellIntegral hJ (scaledPotential β f) a = θ a
  exact div_mul_cancel₀ _ (cellIntegral_pos hJ (continuous_scaledPotential β f) a).ne'

def logRemainder (r : ℝ) : ℝ := r - Real.log (1 + r)

theorem logRemainder_bound {δ r : ℝ} (_hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / 2)
    (hr : |r| ≤ δ) : |logRemainder r| ≤ 2 * δ * |r| := by
  have hlt : |-r| < 1 := by rw [abs_neg]; linarith
  have ht := Real.abs_log_sub_add_sum_range_le hlt 1
  norm_num only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_one, div_one,
    sub_neg_eq_add, abs_neg, Nat.reduceAdd] at ht
  have he : -r + Real.log (1 + r) = -logRemainder r := by unfold logRemainder; ring
  rw [he, abs_neg] at ht
  calc
    |logRemainder r| ≤ |r| ^ 2 / (1 - |r|) := ht
    _ ≤ |r| ^ 2 / (1 / 2) := div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith)
    _ = (2 * |r|) * |r| := by ring
    _ ≤ (2 * δ) * |r| := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hr (by norm_num)) (abs_nonneg r)

theorem remainder_lpNorm_le {v : Torus → ℝ} (hv : MemLp v 2 torusMeasure)
    (hR : MemLp (fun x ↦ logRemainder (v x)) 2 torusMeasure)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / 2)
    (hb : ∀ᵐ x ∂torusMeasure, |v x| ≤ δ) :
    lpNorm (fun x ↦ logRemainder (v x)) 2 torusMeasure ≤ 2 * δ * lpNorm v 2 torusMeasure := by
  have hn := ENNReal.toReal_mono (hv.const_mul (2 * δ)).eLpNorm_ne_top
    (eLpNorm_mono_ae hR.aestronglyMeasurable (show ∀ᵐ x ∂torusMeasure,
      ‖logRemainder (v x)‖ ≤ ‖2 * δ * v x‖ from by
        filter_upwards [hb] with x hx
        simpa only [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hδ] using
          logRemainder_bound hδ hsmall hx))
  change lpNorm (fun x ↦ logRemainder (v x)) 2 torusMeasure ≤
    lpNorm (fun x ↦ 2 * δ * v x) 2 torusMeasure at hn
  simpa only [DensityEntropy.lpNorm_const_mul,
    abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ)] using hn

theorem centered_lpNorm_le {g : Torus → ℝ} (hg : MemLp g 2 torusMeasure) :
    lpNorm (fun x ↦ g x - ∫ y, g y ∂torusMeasure) 2 torusMeasure ≤
      2 * lpNorm g 2 torusMeasure := by
  have ht := lpNorm_sub_le hg (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (g := fun _ ↦ ∫ y, g y ∂torusMeasure)
  have hc : lpNorm (fun _ : Torus ↦ ∫ y, g y ∂torusMeasure) 2 torusMeasure =
      |∫ y, g y ∂torusMeasure| := by
    rw [lpNorm_const' (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)]
    simp only [probReal_univ, Real.one_rpow, mul_one, Real.norm_eq_abs]
  rw [hc] at ht
  have hm := DensityMoments.norm_integral_le_lpNorm hg (by norm_num)
  change lpNorm (g - fun _ ↦ ∫ y, g y ∂torusMeasure) 2 torusMeasure ≤ _
  linarith

theorem scaledPotential_mean_zero (β : ℝ) (f : L4) :
    (∫ x, scaledPotential β f x ∂torusMeasure) = 0 := by
  change (∫ x, β * densityPotential f x ∂torusMeasure) = 0
  rw [integral_const_mul, ← GreenL2Coercivity.convolution_eq_densityPotential,
    GreenL2Coercivity.convolution_integral_zero ((Lp.memLp f).mono_exponent (by norm_num)), mul_zero]

/-- Sum of the genuine restricted Haar integrals over the half-open partition. -/
theorem sum_cell_integrals {J : ℕ} (hJ : 0 < J) {g : Torus → ℝ}
    (hg : Integrable g torusMeasure) :
    (∑ a, ∫ x in meshCell J hJ a, g x ∂torusMeasure) = ∫ x, g x ∂torusMeasure := by
  classical
  calc
    _ = ∑ a, ∫ x, (meshCell J hJ a).indicator g x ∂torusMeasure := by
      apply Finset.sum_congr rfl
      intro a _
      exact (integral_indicator (measurableSet_meshCell J hJ a)).symm
    _ = ∫ x, (∑ a, (meshCell J hJ a).indicator g x) ∂torusMeasure :=
      (integral_finsetSum Finset.univ (fun a _ ↦
        hg.indicator (measurableSet_meshCell J hJ a))).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        dsimp only
        rw [Finset.sum_eq_single (meshLabel J hJ x)]
        · exact indicator_of_mem (show x ∈ meshCell J hJ (meshLabel J hJ x) from rfl) g
        · intro a _ ha
          exact indicator_of_notMem (show x ∉ meshCell J hJ a from fun hx ↦ ha hx.symm) g
        · simp

/-- Cauchy--Schwarz with the exact Haar cell area, obtained from the actual
normalized cell probability measure. -/
theorem cell_integral_sq_le {J : ℕ} (hJ : 0 < J) {v : Torus → ℝ}
    (hv : MemLp v 2 torusMeasure) (a : MeshIndex J) :
    (J : ℝ) ^ 2 * (∫ x in meshCell J hJ a, v x ∂torusMeasure) ^ 2 ≤
      ∫ x in meshCell J hJ a, (v x) ^ 2 ∂torusMeasure := by
  have hva : MemLp v 2 (meshCellMeasure J hJ a) :=
    (hv.restrict (meshCell J hJ a)).smul_measure (by simp)
  have hm := DensityMoments.norm_integral_le_lpNorm hva (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hs := (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ lpNorm v 2 (meshCellMeasure J hJ a)
    from lpNorm_nonneg)).mpr hm
  rw [sq_abs, DensityMoments.lpNorm_two_sq hva] at hs
  simp only [Real.norm_eq_abs, sq_abs, meshCellMeasure, integral_smul_measure,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, smul_eq_mul] at hs
  have hJ2 : 0 < (J : ℝ) ^ 2 := pow_pos (by exact_mod_cast hJ) 2
  apply (mul_le_mul_iff_right₀ hJ2).mp
  convert hs using 1
  ring

theorem cellValue_variance_norm {J : ℕ} (hJ : 0 < J) (c : MeshIndex J → ℝ) :
    (∑ a, (c a - ∫ x, cellValue hJ c x ∂torusMeasure) ^ 2) =
      (J : ℝ) ^ 2 * lpNorm
        (fun x ↦ cellValue hJ c x - ∫ y, cellValue hJ c y ∂torusMeasure) 2 torusMeasure ^ 2 := by
  have hn : lpNorm (fun x ↦ cellValue hJ c x - ∫ y, cellValue hJ c y ∂torusMeasure)
      2 torusMeasure ^ 2 = ((J : ℝ) ^ 2)⁻¹ *
        ∑ a, (c a - ∫ y, cellValue hJ c y ∂torusMeasure) ^ 2 := by
    calc
      _ = ∫ x, (cellValue hJ c x - ∫ y, cellValue hJ c y ∂torusMeasure) ^ 2 ∂torusMeasure := by
        have hmem : MemLp (fun x ↦ cellValue hJ c x - ∫ y, cellValue hJ c y ∂torusMeasure)
            2 torusMeasure := (cellValue_memLp hJ c 2).sub (memLp_const _)
        simpa only [Real.norm_eq_abs, sq_abs] using DensityMoments.lpNorm_two_sq hmem
      _ = _ := cellValue_variance_integral hJ c
  rw [hn]
  have hJ0 : (J : ℝ) ^ 2 ≠ 0 := (pow_pos (by exact_mod_cast hJ) 2).ne'
  field_simp

section Near
variable {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ} {β β₀ : ℝ}
  (h : NearParameters θ β β₀) (hnear : profileDeviation θ ≤ neighborhood β₀)
local notation "fθ" => Subtype.val (nearFixedPoint hJ h)

theorem fixedPoint_value_ae :
    fθ =ᵐ[torusMeasure] occupationMapValue hJ θ β fθ := by
  have hh := occupationMap_ae hJ θ β fθ
  rw [nearFixedPoint_eq hJ h] at hh
  exact hh

include hnear in
theorem fixedPoint_positive_ae : ∀ᵐ x ∂torusMeasure, 0 < fθ x := by
  filter_upwards [fixedPoint_value_ae hJ h] with x hx
  rw [hx, occupationMapValue_eq_chemical]
  exact mul_pos (coefficient_argument_pos hJ hnear β fθ _) (Real.exp_pos _)

include hnear in
theorem fixedPoint_log_ae :
    (fun x ↦ Real.log (fθ x)) =ᵐ[torusMeasure]
      fun x ↦ scaledPotential β fθ x + chemicalValue hJ θ β fθ x := by
  filter_upwards [fixedPoint_value_ae hJ h] with x hx
  rw [hx]
  exact occupationMapValue_log hJ hnear β fθ x

include hnear in
theorem fixedPoint_log_memLp (p : ℝ≥0∞) :
    MemLp (fun x ↦ Real.log (fθ x)) p torusMeasure := by
  have hh := (memLp_continuous_torus torusMeasure (continuous_scaledPotential β fθ) p).add
    (cellValue_memLp hJ (coefficient hJ θ β fθ) p)
  exact hh.ae_eq (fixedPoint_log_ae hJ h hnear).symm

theorem fixedPoint_cell_mass (a : MeshIndex J) :
    (∫ x in meshCell J hJ a, fθ x ∂torusMeasure) = θ a := by
  rw [integral_congr_ae (ae_restrict_of_ae (fixedPoint_value_ae hJ h))]
  exact occupationMapValue_cell_mass hJ θ β fθ a

theorem fixedPoint_centered_cell_mass (a : MeshIndex J) :
    (∫ x in meshCell J hJ a, (fθ x - 1) ∂torusMeasure) = θ a - ((J : ℝ) ^ 2)⁻¹ := by
  rw [integral_sub (((Lp.memLp fθ).integrable (by norm_num)).restrict)
    (integrable_const (1 : ℝ)), fixedPoint_cell_mass hJ h a]
  simp only [setIntegral_const, Measure.real, torusMeasure_meshCell, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, smul_eq_mul, mul_one]

/-- The actual fixed point has the prescribed cell masses, so its centered L2
norm controls the Euclidean profile deviation with the exact factor J. -/
theorem fixedPoint_profile_L2_sq :
    (J : ℝ) ^ 2 * (∑ a, (θ a - ((J : ℝ) ^ 2)⁻¹) ^ 2) ≤
      lpNorm (fun x ↦ fθ x - 1) 2 torusMeasure ^ 2 := by
  have hv := GreenL2Coercivity.centered_memLp (Lp.memLp fθ)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ cell_integral_sq_le hJ hv a)
  simp_rw [fixedPoint_centered_cell_mass hJ h] at hs
  rw [← Finset.mul_sum, sum_cell_integrals hJ hv.integrable_sq] at hs
  have he : (∫ x, (fθ x - 1) ^ 2 ∂torusMeasure) =
      lpNorm (fun x ↦ fθ x - 1) 2 torusMeasure ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (DensityMoments.lpNorm_two_sq hv).symm
  exact hs.trans_eq he

theorem fixedPoint_profile_L2 :
    (J : ℝ) * ‖(WithLp.toLp 2 (fun a : MeshIndex J ↦ θ a - ((J : ℝ) ^ 2)⁻¹) :
      EuclideanSpace ℝ (MeshIndex J))‖ ≤ lpNorm (fun x ↦ fθ x - 1) 2 torusMeasure := by
  have hh := fixedPoint_profile_L2_sq hJ h
  apply (sq_le_sq₀ (mul_nonneg (Nat.cast_nonneg J) (norm_nonneg _)) lpNorm_nonneg).mp
  simpa only [mul_pow, EuclideanSpace.real_norm_sq_eq] using hh

include hnear in
theorem fixedPoint_remainder_memLp :
    MemLp (fun x ↦ logRemainder (fθ x - 1)) 2 torusMeasure := by
  have hh := (GreenL2Coercivity.centered_memLp (Lp.memLp fθ)).sub
    (fixedPoint_log_memLp hJ h hnear 2)
  convert hh using 1
  funext x
  have he : 1 + (fθ x - 1) = fθ x := by ring
  simp only [logRemainder, Pi.sub_apply, he]

theorem fixedPoint_residual_mean_zero :
    (∫ x, (fθ x - 1 - scaledPotential β fθ x) ∂torusMeasure) = 0 := by
  rw [integral_sub ((GreenL2Coercivity.centered_memLp (Lp.memLp fθ)).integrable (by norm_num))
    (integrable_continuous_torus torusMeasure (continuous_scaledPotential β fθ)),
    GreenL2Coercivity.centered_mean_zero (Lp.memLp fθ) (nearFixedPoint hJ h).property.2.1,
    scaledPotential_mean_zero, sub_self]

include hnear in
theorem fixedPoint_chemical_uncentered_ae :
    (fun x ↦ fθ x - 1 - scaledPotential β fθ x) =ᵐ[torusMeasure]
      fun x ↦ chemicalValue hJ θ β fθ x + logRemainder (fθ x - 1) := by
  filter_upwards [fixedPoint_log_ae hJ h hnear] with x hx
  have he : 1 + (fθ x - 1) = fθ x := by ring
  simp only [logRemainder, he]
  linarith

include hnear in
theorem fixedPoint_chemical_centered_ae :
    (fun x ↦ fθ x - 1 - scaledPotential β fθ x) =ᵐ[torusMeasure]
      fun x ↦ (chemicalValue hJ θ β fθ x - ∫ y, chemicalValue hJ θ β fθ y ∂torusMeasure) +
        (logRemainder (fθ x - 1) - ∫ y, logRemainder (fθ y - 1) ∂torusMeasure) := by
  have hC : Integrable (chemicalValue hJ θ β fθ) torusMeasure :=
    (cellValue_memLp hJ (coefficient hJ θ β fθ) 2).integrable (by norm_num)
  have hR := (fixedPoint_remainder_memLp hJ h hnear).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hm : (∫ y, chemicalValue hJ θ β fθ y ∂torusMeasure) +
      (∫ y, logRemainder (fθ y - 1) ∂torusMeasure) = 0 := by
    calc
      _ = ∫ x, (chemicalValue hJ θ β fθ x + logRemainder (fθ x - 1)) ∂torusMeasure :=
        (integral_add hC hR).symm
      _ = ∫ x, (fθ x - 1 - scaledPotential β fθ x) ∂torusMeasure :=
        integral_congr_ae (fixedPoint_chemical_uncentered_ae hJ h hnear).symm
      _ = 0 := fixedPoint_residual_mean_zero hJ h
  filter_upwards [fixedPoint_chemical_uncentered_ae hJ h hnear] with x hx
  linarith

include hnear in
theorem fixedPoint_centered_remainder_bound :
    lpNorm (fun x ↦ logRemainder (fθ x - 1) - ∫ y, logRemainder (fθ y - 1) ∂torusMeasure)
      2 torusMeasure ≤ (GreenL2Coercivity.gap β₀ / 2) *
        lpNorm (fun x ↦ fθ x - 1) 2 torusMeasure := by
  let δ : ℝ := (4 / 3) * profileDeviation θ
  have hd : 0 ≤ δ := mul_nonneg (by norm_num) (profileDeviation_nonneg θ)
  have hs : δ ≤ 1 / 2 := by
    have hh := hnear.trans (min_le_left (1 / 8 : ℝ) _)
    dsimp [δ]
    linarith
  have hg : 4 * δ ≤ GreenL2Coercivity.gap β₀ / 2 := by
    have hh := hnear.trans (min_le_right (1 / 8 : ℝ) _)
    dsimp [δ]
    linarith
  have hR := fixedPoint_remainder_memLp hJ h hnear
  have hr := remainder_lpNorm_le (GreenL2Coercivity.centered_memLp (Lp.memLp fθ)) hR hd hs
    (nearFixedPoint_profile_ae hJ h)
  have hc := centered_lpNorm_le hR
  have hn : 0 ≤ lpNorm (fun x ↦ fθ x - 1) 2 torusMeasure := lpNorm_nonneg
  have hp := mul_le_mul_of_nonneg_right hg hn
  linarith

include hnear in
theorem fixedPoint_chemical_norm_lower :
    (GreenL2Coercivity.gap β₀ / 2) * lpNorm (fun x ↦ fθ x - 1) 2 torusMeasure ≤
      lpNorm (fun x ↦ chemicalValue hJ θ β fθ x - ∫ y, chemicalValue hJ θ β fθ y ∂torusMeasure)
        2 torusMeasure := by
  have hC : MemLp (fun x ↦ chemicalValue hJ θ β fθ x -
      ∫ y, chemicalValue hJ θ β fθ y ∂torusMeasure) 2 torusMeasure :=
    (cellValue_memLp hJ (coefficient hJ θ β fθ) 2).sub (memLp_const _)
  have ht := lpNorm_add_le hC (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (g := fun x ↦ logRemainder (fθ x - 1) - ∫ y, logRemainder (fθ y - 1) ∂torusMeasure)
  have he := congrArg ENNReal.toReal (eLpNorm_congr_ae (p := 2)
    (fixedPoint_chemical_centered_ae hJ h hnear))
  change lpNorm (fun x ↦ fθ x - 1 - scaledPotential β fθ x) 2 torusMeasure =
    lpNorm ((fun x ↦ chemicalValue hJ θ β fθ x - ∫ y, chemicalValue hJ θ β fθ y ∂torusMeasure) +
      fun x ↦ logRemainder (fθ x - 1) - ∫ y, logRemainder (fθ y - 1) ∂torusMeasure)
      2 torusMeasure at he
  rw [← he] at ht
  have hr := fixedPoint_centered_remainder_bound hJ h hnear
  have hg := GreenL2Coercivity.centered_L4_coercivity (Lp.memLp fθ) h.beta_nonneg h.beta_le
  change GreenL2Coercivity.gap β₀ * lpNorm (fun x ↦ fθ x - 1) 2 torusMeasure ≤
    lpNorm (fun x ↦ fθ x - 1 - scaledPotential β fθ x) 2 torusMeasure at hg
  linarith

include hnear in
/-- Source finite chemical coercivity, before the discrete cell Poincare step.
Every chemical coefficient and cell mass is taken from the genuine nearby fixed
point. The only extra neighborhood restriction is the explicit scalar one. -/
theorem fixedPoint_chemical_variance_lower (hsub : β₀ < 4) :
    (GreenL2Coercivity.gap β₀) ^ 2 * (J : ℝ) ^ 4 / 4 *
        (∑ a, (θ a - ((J : ℝ) ^ 2)⁻¹) ^ 2) ≤
      ∑ a, (coefficient hJ θ β fθ a -
        ∫ x, chemicalValue hJ θ β fθ x ∂torusMeasure) ^ 2 := by
  let V : ℝ := lpNorm (fun x ↦ fθ x - 1) 2 torusMeasure
  let C : ℝ := lpNorm (fun x ↦ chemicalValue hJ θ β fθ x -
    ∫ y, chemicalValue hJ θ β fθ y ∂torusMeasure) 2 torusMeasure
  have hV : 0 ≤ V := lpNorm_nonneg
  have hC : 0 ≤ C := lpNorm_nonneg
  have hgap := (GreenL2Coercivity.gap_pos hsub).le
  have hn : GreenL2Coercivity.gap β₀ / 2 * V ≤ C :=
    fixedPoint_chemical_norm_lower hJ h hnear
  have hn2 := (sq_le_sq₀ (mul_nonneg (div_nonneg hgap (by norm_num)) hV) hC).mpr hn
  have hs : (J : ℝ) ^ 2 * (∑ a, (θ a - ((J : ℝ) ^ 2)⁻¹) ^ 2) ≤ V ^ 2 :=
    fixedPoint_profile_L2_sq hJ h
  have he : (∑ a, (coefficient hJ θ β fθ a -
      ∫ x, chemicalValue hJ θ β fθ x ∂torusMeasure) ^ 2) = (J : ℝ) ^ 2 * C ^ 2 :=
    cellValue_variance_norm hJ (coefficient hJ θ β fθ)
  rw [he]
  calc
    _ = (J : ℝ) ^ 2 * ((GreenL2Coercivity.gap β₀) ^ 2 / 4 *
        ((J : ℝ) ^ 2 * ∑ a, (θ a - ((J : ℝ) ^ 2)⁻¹) ^ 2)) := by ring
    _ ≤ (J : ℝ) ^ 2 * ((GreenL2Coercivity.gap β₀) ^ 2 / 4 * V ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (by positivity)) (sq_nonneg _)
    _ ≤ (J : ℝ) ^ 2 * C ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      nlinarith only [hn2]

end Near
end PeriodicAttractiveLogGas.OccupationChemicalCoercivity
