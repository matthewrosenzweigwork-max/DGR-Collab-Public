import FullLabeledLSI.Nonvacuity.Prop82.E4_Derivatives

/-!
# Lane E, part 5: heat stationarity (core form)

The derivative at `s = 0` of the defect `fS ρ s = realDiss ρ_s - 2 R realGap ρ_s` along
`ρ_s = ρ + s ρ''` vanishes because `fS ρ ≥ 0 = fS ρ 0` near `0`. The derivative is computed from

* `fisher ρ_s`: derivative `-2 scoreEnergy ρ` (E4);
* `entropy ρ_s`: derivative `-fisher ρ` (E4);
* `firstMode ρ_s = (1 - a s)² q` (E2);
* `forceEnergy ρ_s = (a/2)(firstMode ρ_s - momNum ρ_s)` and `momNum ρ_s = (1-as)²(1-4as) N` (E2).
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82.HeatE

/-- Heat stationarity, with the aligned second moment written as the unnormalized integral
`momNum ρ = ∫ ρ ((C² - S²) c2 + 4 C S cos sin)`; `alignedSecondMoment ρ = momNum ρ / firstMode ρ`. -/
theorem heat_stationarity_momNum {rho : Torus 1 → Real} (h : SmoothOptimizer rho)
    (hQ : 0 < firstMode rho) :
    0 = -2 * scoreEnergy rho - 5 * aCos ^ 2 * firstMode rho + 3 * aCos ^ 2 * momNum rho +
      2 * realRate * (fisher rho + aCos * firstMode rho) := by
  have hrho := h.probability
  obtain ⟨m, s0, hm, hs0, -, hmrho, hlow, hsp, hQs, hf⟩ := exists_good_interval hrho hQ
  have hr := hrho.smooth
  set a := aCos with ha
  set q := firstMode rho with hq
  set N := momNum rho with hN
  set R := realRate with hR
  -- the defect as an explicit function of `s` near `0`
  let g : Real → Real := fun s =>
    fisher (rhoS rho s) + 2 * a * ((1 - a * s) ^ 2 * q) +
      a / 2 * ((1 - a * s) ^ 2 * q - (1 - a * s) ^ 2 * (1 - 4 * a * s) * N) -
      2 * R * (entropy (rhoS rho s) + (1 - a * s) ^ 2 * q / 2)
  have hEq : fS rho =ᶠ[𝓝 0] g := by
    filter_upwards [abs_le_mem_nhds hs0] with s hs
    unfold fS realDiss realGap
    rw [forceEnergy_closed (hsp s hs), firstMode_rhoS hr, momNum_rhoS hr]
  -- derivatives
  have hl : HasDerivAt (fun s : Real => 1 - a * s) (-a) 0 := by
    simpa using ((hasDerivAt_id (0 : Real)).const_mul a).const_sub 1
  have hl2 : HasDerivAt (fun s : Real => 1 - 4 * a * s) (-(4 * a)) 0 := by
    simpa using ((hasDerivAt_id (0 : Real)).const_mul (4 * a)).const_sub 1
  have hp1 : HasDerivAt (fun s : Real => (1 - a * s) ^ 2 * q) (-(2 * a) * q) 0 := by
    have := (hl.pow 2).mul_const q
    simpa using this
  have hp2 : HasDerivAt (fun s : Real => (1 - a * s) ^ 2 * (1 - 4 * a * s) * N)
      (-(6 * a) * N) 0 := by
    have := ((hl.pow 2).mul hl2).mul_const N
    convert this using 1
    simp
    ring
  have hfish := hasDerivAt_fisher_rhoS hrho hQ
  have hent := hasDerivAt_entropy_rhoS hrho hQ
  have hg : HasDerivAt g
      (-2 * scoreEnergy rho + 2 * a * (-(2 * a) * q) +
        a / 2 * (-(2 * a) * q - (-(6 * a) * N)) -
        2 * R * (-fisher rho + (-(2 * a) * q) / 2)) 0 := by
    have := ((hfish.add (hp1.const_mul (2 * a))).add
      ((hp1.sub hp2).const_mul (a / 2))).sub
      ((hent.add (hp1.div_const 2)).const_mul (2 * R))
    exact this.congr_deriv (by ring)
  have hfS : HasDerivAt (fS rho) _ 0 := hg.congr_of_eventuallyEq hEq
  have hmin : IsLocalMin (fS rho) 0 := by
    filter_upwards [abs_le_mem_nhds hs0] with s hs
    rw [fS_zero h]
    exact hf s hs
  have hzero := hmin.hasDerivAt_eq_zero hfS
  -- `hzero : (derivative) = 0`; rearrange
  have hI : fisher rho = fisher rho := rfl
  linarith [hzero]

/-- The core theorem, with the aligned second moment written out as the integral it abbreviates
(`momNum` unfolded); this is the statement of the lane E blueprint. -/
theorem heat_stationarity_core {rho : Torus 1 → Real} (h : SmoothOptimizer rho)
    (hQ : 0 < firstMode rho) :
    0 = -2 * scoreEnergy rho - 5 * aCos ^ 2 * firstMode rho +
      3 * aCos ^ 2 *
        (∫ x, rho x * (((∫ y, gCos y * rho y ∂haar 1) ^ 2 - (∫ y, sCos y * rho y ∂haar 1) ^ 2) * c2 x +
          4 * (∫ y, gCos y * rho y ∂haar 1) * (∫ y, sCos y * rho y ∂haar 1) * gCos x * sCos x) ∂haar 1) +
      2 * realRate * (fisher rho + aCos * firstMode rho) :=
  heat_stationarity_momNum h hQ

end SharpLSI.FL.Prop82.HeatE
