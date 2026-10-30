import DGPS.Examples.PolynomialSpeciesRangeChart
import DGPS.Frontier.STR029.T16

/-! The concrete interacting range map for the independent-(h,s) analytic extension.
Its zero-chart family is proved for every rate, before any implicit graph is chosen. -/

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.PolynomialSpecies

/-- The actual nonlocal differential potential, with the physical rate r. -/
def polynomialRangeEulerPotential (p : ℝ × ℝ) (r : ℝ) (u : PeriodicC2_STR02969) :
    PeriodicHolder_STR02968 :=
  let L := e0_STR02955 (polynomialRangeLogWeight p)
  let φ := e0_STR02955 (polynomialRangeFeature p)
  let B := polynomialRangeGenerator p
  let j := polynomialRangeGradientSq p
  let m := eulerMean L u φ
  let A := eulerMean L u B
  let J := eulerMean L u j
  DGPS.Circle.AngularNormalization.a0 •
    ((-2 : ℝ) • e2_STR02955 u - (2 : ℝ) •
      (e1_STR02955 (polynomialRangeLogWeight p) * e1_STR02955 u) - e1_STR02955 u * e1_STR02955 u) -
    (2 * r) • e0_STR02955 u + (2 * eta * (A + eta * m * J - r * m)) • φ +
    (2 * eta * m) • B + (eta ^ 2 * m ^ 2) • j

/-- The actual density-weighted centered Euler map of the analytic extension. -/
def polynomialRangeEuler (p : ℝ × ℝ) (r : ℝ) (u : PeriodicC2_STR02969) : PeriodicHolder_STR02968 :=
  let L := e0_STR02955 (polynomialRangeLogWeight p)
  let K := polynomialRangeEulerPotential p r u
  eulerDensity L u * (K - eulerMean L u K • (1 : PeriodicHolder_STR02968))

abbrev PolynomialEulerInput := (ℝ × ℝ) × ℝ × PeriodicC2_STR02969

private theorem potential_smooth : ContDiff ℝ ∞ (fun x : PolynomialEulerInput =>
    polynomialRangeEulerPotential x.1 x.2.1 x.2.2) := by
  obtain ⟨hL, hQ, hm, hφ, hB, hj⟩ := polynomialRange_data_smooth
  have hL0 : ContDiff ℝ ∞ (fun x : PolynomialEulerInput => e0_STR02955 (polynomialRangeLogWeight x.1)) :=
    e0_STR02955.contDiff.comp (hL.comp contDiff_fst)
  have hL1 : ContDiff ℝ ∞ (fun x : PolynomialEulerInput => e1_STR02955 (polynomialRangeLogWeight x.1)) :=
    e1_STR02955.contDiff.comp (hL.comp contDiff_fst)
  have hφ0 : ContDiff ℝ ∞ (fun x : PolynomialEulerInput => e0_STR02955 (polynomialRangeFeature x.1)) :=
    e0_STR02955.contDiff.comp (hφ.comp contDiff_fst)
  have hB0 : ContDiff ℝ ∞ (fun x : PolynomialEulerInput => polynomialRangeGenerator x.1) := hB.comp contDiff_fst
  have hj0 : ContDiff ℝ ∞ (fun x : PolynomialEulerInput => polynomialRangeGradientSq x.1) := hj.comp contDiff_fst
  have hu0 : ContDiff ℝ ∞ (fun x : PolynomialEulerInput => e0_STR02955 x.2.2) :=
    e0_STR02955.contDiff.comp (contDiff_snd.comp contDiff_snd)
  have hu1 : ContDiff ℝ ∞ (fun x : PolynomialEulerInput => e1_STR02955 x.2.2) :=
    e1_STR02955.contDiff.comp (contDiff_snd.comp contDiff_snd)
  have hu2 : ContDiff ℝ ∞ (fun x : PolynomialEulerInput => e2_STR02955 x.2.2) :=
    e2_STR02955.contDiff.comp (contDiff_snd.comp contDiff_snd)
  have hρ : ContDiff ℝ ∞ (fun x : PolynomialEulerInput =>
      eulerDensity (e0_STR02955 (polynomialRangeLogWeight x.1)) x.2.2) :=
    rho_smooth_STR02954.comp (contDiff_const.prodMk (hL0.add hu0))
  have hmeanφ : ContDiff ℝ ∞ (fun x : PolynomialEulerInput =>
      eulerMean (e0_STR02955 (polynomialRangeLogWeight x.1)) x.2.2
        (e0_STR02955 (polynomialRangeFeature x.1))) := meanCLM_STR02954.contDiff.comp (hφ0.mul hρ)
  have hmeanB : ContDiff ℝ ∞ (fun x : PolynomialEulerInput =>
      eulerMean (e0_STR02955 (polynomialRangeLogWeight x.1)) x.2.2 (polynomialRangeGenerator x.1)) :=
    meanCLM_STR02954.contDiff.comp (hB0.mul hρ)
  have hmeanj : ContDiff ℝ ∞ (fun x : PolynomialEulerInput =>
      eulerMean (e0_STR02955 (polynomialRangeLogWeight x.1)) x.2.2 (polynomialRangeGradientSq x.1)) :=
    meanCLM_STR02954.contDiff.comp (hj0.mul hρ)
  have hr : ContDiff ℝ ∞ (fun x : PolynomialEulerInput => x.2.1) := contDiff_fst.comp contDiff_snd
  have hcoeff : ContDiff ℝ ∞ (fun x : PolynomialEulerInput =>
      2 * eta * (eulerMean (e0_STR02955 (polynomialRangeLogWeight x.1)) x.2.2
        (polynomialRangeGenerator x.1) +
      eta * eulerMean (e0_STR02955 (polynomialRangeLogWeight x.1)) x.2.2
        (e0_STR02955 (polynomialRangeFeature x.1)) *
      eulerMean (e0_STR02955 (polynomialRangeLogWeight x.1)) x.2.2
        (polynomialRangeGradientSq x.1) -
      x.2.1 * eulerMean (e0_STR02955 (polynomialRangeLogWeight x.1)) x.2.2
        (e0_STR02955 (polynomialRangeFeature x.1)))) :=
    contDiff_const.mul ((hmeanB.add ((contDiff_const.mul hmeanφ).mul hmeanj)).sub (hr.mul hmeanφ))
  unfold polynomialRangeEulerPotential
  exact (((((contDiff_const (c := DGPS.Circle.AngularNormalization.a0)).smul
      (((contDiff_const (c := (-2 : ℝ))).smul hu2).sub
        ((contDiff_const (c := (2 : ℝ))).smul (hL1.mul hu1)) |>.sub (hu1.mul hu1))).sub
      ((contDiff_const.mul hr).smul hu0)).add (hcoeff.smul hφ0)).add
      ((contDiff_const.mul hmeanφ).smul hB0)).add
      ((contDiff_const.mul (hmeanφ.pow 2)).smul hj0)

/-- Joint smoothness is proved without differentiating any selected equilibrium root. -/
theorem polynomialRangeEuler_smooth : ContDiff ℝ ∞ (fun x : PolynomialEulerInput =>
    polynomialRangeEuler x.1 x.2.1 x.2.2) := by
  have hL := polynomialRange_data_smooth.1
  have hρ : ContDiff ℝ ∞ (fun x : PolynomialEulerInput =>
      eulerDensity (e0_STR02955 (polynomialRangeLogWeight x.1)) x.2.2) :=
    rho_smooth_STR02954.comp (contDiff_const.prodMk
      ((e0_STR02955.contDiff.comp (hL.comp contDiff_fst)).add
        (e0_STR02955.contDiff.comp (contDiff_snd.comp contDiff_snd))))
  have hmean : ContDiff ℝ ∞ (fun x : PolynomialEulerInput =>
      eulerMean (e0_STR02955 (polynomialRangeLogWeight x.1)) x.2.2
        (polynomialRangeEulerPotential x.1 x.2.1 x.2.2)) :=
    meanCLM_STR02954.contDiff.comp (potential_smooth.mul hρ)
  exact hρ.mul (potential_smooth.sub (hmean.smul contDiff_const))

/-- The exact zero-chart family for every independent field, tilt and physical rate. -/
theorem polynomialRangeEuler_zero (p : ℝ × ℝ) (r : ℝ) : polynomialRangeEuler p r 0 = 0 := by
  have hQ : eulerDensity (e0_STR02955 (polynomialRangeLogWeight p)) 0 = polynomialRangeReference p := by
    simp only [eulerDensity, map_zero, add_zero, polynomialRangeReference]
  have hm : eulerMean (e0_STR02955 (polynomialRangeLogWeight p)) 0
      (e0_STR02955 (polynomialRangeFeature p)) = 0 := by
    rw [eulerMean, hQ]
    exact polynomialRangeFeature_centered p
  have hA : eulerMean (e0_STR02955 (polynomialRangeLogWeight p)) 0 (polynomialRangeGenerator p) = 0 := by
    rw [eulerMean, hQ]
    exact polynomialRangeGenerator_centered p
  have hK : polynomialRangeEulerPotential p r 0 = 0 := by
    simp only [polynomialRangeEulerPotential, hm, hA, map_zero, mul_zero, zero_mul,
      zero_smul, smul_zero, sub_self, sub_zero, add_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simp [polynomialRangeEuler, hK, eulerMean]

/-- Parameters (a,b,(h,s),gamma); the reference tilt s remains independent until restriction. -/
abbrev PolynomialRangeParameters := ℝ × ℝ × (ℝ × ℝ) × ℝ

/-- The actual projected interacting range map on the existing closed Fourier complement. -/
def polynomialRangeMap (x : PolynomialRangeParameters × E_STR02969) : Y_STR02969 :=
  PY_STR02955 (polynomialRangeEuler x.1.2.2.1
    (DGPS.Circle.AngularNormalization.a0 * (1 + x.1.2.2.2))
    (x.1.1 • cosC2_STR02915 + x.1.2.1 • sinC2_STR02915 + (x.2 : PeriodicC2_STR02969)))

private def rangeInput (x : PolynomialRangeParameters × E_STR02969) : PolynomialEulerInput :=
  (x.1.2.2.1, DGPS.Circle.AngularNormalization.a0 * (1 + x.1.2.2.2),
    x.1.1 • cosC2_STR02915 + x.1.2.1 • sinC2_STR02915 + (x.2 : PeriodicC2_STR02969))

private theorem rangeInput_smooth : ContDiff ℝ ∞ rangeInput := by
  have hw : ContDiff ℝ ∞ (fun x : PolynomialRangeParameters × E_STR02969 =>
      (x.2 : PeriodicC2_STR02969)) := E_STR02969.subtypeL.contDiff.comp contDiff_snd
  have ha : ContDiff ℝ ∞ (fun x : PolynomialRangeParameters × E_STR02969 => x.1.1) :=
    contDiff_fst.comp contDiff_fst
  have hb : ContDiff ℝ ∞ (fun x : PolynomialRangeParameters × E_STR02969 => x.1.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp contDiff_fst)
  have htail : ContDiff ℝ ∞ (fun x : PolynomialRangeParameters × E_STR02969 => x.1.2.2) :=
    contDiff_snd.comp (contDiff_snd.comp contDiff_fst)
  have hp : ContDiff ℝ ∞ (fun x : PolynomialRangeParameters × E_STR02969 => x.1.2.2.1) :=
    contDiff_fst.comp htail
  have hγ : ContDiff ℝ ∞ (fun x : PolynomialRangeParameters × E_STR02969 => x.1.2.2.2) :=
    contDiff_snd.comp htail
  have hu := ((ha.smul (contDiff_const (c := cosC2_STR02915))).add
    (hb.smul (contDiff_const (c := sinC2_STR02915)))).add hw
  have hr : ContDiff ℝ ∞ (fun x : PolynomialRangeParameters × E_STR02969 =>
      DGPS.Circle.AngularNormalization.a0 * (1 + x.1.2.2.2)) :=
    contDiff_const.mul (contDiff_const.add hγ)
  exact hp.prodMk (hr.prodMk hu)

private def rangeEulerUncurried (x : PolynomialEulerInput) : PeriodicHolder_STR02968 :=
  polynomialRangeEuler x.1 x.2.1 x.2.2

private theorem rangeEulerUncurried_smooth : ContDiff ℝ ∞ rangeEulerUncurried :=
  polynomialRangeEuler_smooth

private theorem rangeMap_eq : polynomialRangeMap =
    (PY_STR02955 : PeriodicHolder_STR02968 → Y_STR02969) ∘ rangeEulerUncurried ∘ rangeInput := rfl

/-- Genuine smoothness of the concrete map to which the implicit theorem will apply. -/
theorem polynomialRangeMap_smooth : ContDiff ℝ ∞ polynomialRangeMap := by
  rw [rangeMap_eq]
  exact PY_STR02955.contDiff.comp (rangeEulerUncurried_smooth.comp rangeInput_smooth)

/-- The actual equilibrium slice vanishes for every independent (h,s,gamma), so graph
uniqueness can later identify its range correction with zero. -/
theorem polynomialRangeMap_equilibrium (h s γ : ℝ) :
    polynomialRangeMap (((0, 0, (h, s), γ) : PolynomialRangeParameters), 0) = 0 := by
  simp [polynomialRangeMap, polynomialRangeEuler_zero]

end DGPS.Examples.PolynomialSpecies
