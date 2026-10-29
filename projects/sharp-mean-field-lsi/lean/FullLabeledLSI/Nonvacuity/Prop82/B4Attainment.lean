import FullLabeledLSI.Nonvacuity.Prop82.Compactness
import FullLabeledLSI.Nonvacuity.Prop82.B1Convergence
import FullLabeledLSI.Nonvacuity.Prop82.B2Fisher
import FullLabeledLSI.Nonvacuity.Prop82.B3Near
import SharpSymmetricLSI.Paper.AppAEvol2
import SharpSymmetricLSI.Paper.AdmFinite

/-!
# Lane B, module 4: attainment of the infimum below the threshold

The direct method.  The limit density `u²` of a Rellich-extracted minimizing
sequence is shown to be admissible (the Haar density is excluded by the sharp
near-equilibrium bound of `B3Near`, which is where `realRate < 3a/2` is used) and to
satisfy the optimizer equation by lower semicontinuity of the Fisher information.

This file does not import `Assembly.lean`.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI.FL.Prop82

attribute [local fun_prop] SharpLSI.continuous_sCos

/-! ### Primed copies of the `Model` lemmas for a not-yet-admissible limit -/

theorem entropy_fisher_finite' {rho : Torus 1 → Real} (h0 : ∀ x, 0 ≤ rho x)
    (h1 : ∫ x, rho x ∂haar 1 = 1) (hH : MemH1 (haar 1) (fun x => Real.sqrt (rho x))) :
    klDiv (densMeasure rho) (haar 1) ≠ ⊤ ∧ fisherInfo (densMeasure rho) (haar 1) ≠ ⊤ := by
  have hq := circle_quantitative_lsi_aux h0 h1 hH
  exact ⟨hq.1, hq.2.1⟩

theorem gap_eq_real' {rho : Torus 1 → Real} (h0 : ∀ x, 0 ≤ rho x)
    (h1 : ∫ x, rho x ∂haar 1 = 1) (hH : MemH1 (haar 1) (fun x => Real.sqrt (rho x))) :
    gap cosV (cosW 1) (densMeasure rho) = (realGap rho : EReal) := by
  have hkl : klDiv (densMeasure rho) (haar 1) = ENNReal.ofReal (entropy rho) :=
    (ENNReal.ofReal_toReal (entropy_fisher_finite' h0 h1 hH).1).symm
  rw [(cosine_free_energy_aux (by norm_num : (0 : Real) < 1)).2.2.2.1 rho h0 h1,
    hkl, EReal.coe_ennreal_ofReal, max_eq_left (entropy_nonneg rho), ← EReal.coe_add]
  congr 1
  unfold realGap
  ring

theorem fisher_eq_of_memH1 {rho : Torus 1 → Real} (h0 : ∀ x, 0 ≤ rho x)
    (h1 : ∫ x, rho x ∂haar 1 = 1) (hH : MemH1 (haar 1) (fun x => Real.sqrt (rho x))) :
    fisher rho = 4 * ∫ x, weakGrad (fun y => Real.sqrt (rho y)) x 0 ^ 2 ∂haar 1 := by
  unfold fisher
  rw [fisherInfo_densMeasure_eq h0 h1 hH, ENNReal.toReal_ofReal]
  exact mul_nonneg (by norm_num) (integral_nonneg fun x => sq_nonneg _)

/-! ### A uniform sup bound on the sublevel -/

/-- Constant bounding every density with `fisher < 18 a`. -/
noncomputable def supBound : Real := (1 + (Real.sqrt (9 * aCos / 2) + 9 * aCos / 2)) ^ 2

theorem ae_le_supBound {rho : Torus 1 → Real} (h : Admissible cosV (cosW 1) rho)
    (hI : fisher rho < 18 * aCos) : ∀ᵐ x ∂haar 1, rho x ≤ supBound := by
  filter_upwards [ae_abs_sqrt_sub_one_le h.1 h.2.1 h.2.2.1] with x hx
  have hf : (∫ y, weakGrad (fun x => Real.sqrt (rho x)) y 0 ^ 2 ∂haar 1) = fisher rho / 4 := by
    rw [fisher_eq_sqrt_energy h]; ring
  rw [hf] at hx
  have hW0 : 0 ≤ fisher rho / 4 := by have := fisher_nonneg rho; positivity
  have hWle : fisher rho / 4 ≤ 9 * aCos / 2 := by linarith
  have hsq : Real.sqrt (fisher rho / 4) ≤ Real.sqrt (9 * aCos / 2) := Real.sqrt_le_sqrt hWle
  have hle : Real.sqrt (rho x) ≤ 1 + (Real.sqrt (9 * aCos / 2) + 9 * aCos / 2) := by
    have := (abs_le.mp hx).2
    linarith
  unfold supBound
  calc rho x = Real.sqrt (rho x) ^ 2 := (Real.sq_sqrt (h.1 x)).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2

/-! ### The weak limit is an `H¹` square root -/

theorem limit_memH1 {u : Torus 1 → Real} {g : Torus 1 → Fin 1 → Real}
    (hu : MemLp u 2 (haar 1)) (hg : ∀ j, MemLp (fun x => g x j) 2 (haar 1))
    (hw : IsWeakGrad u g) (hu0 : ∀ᵐ x ∂haar 1, 0 ≤ u x) :
    MemH1 (haar 1) (fun x => Real.sqrt (u x ^ 2)) ∧
      (∀ᵐ x ∂haar 1, weakGrad (fun y => Real.sqrt (u y ^ 2)) x 0 = g x 0) := by
  have hae : (fun x => Real.sqrt (u x ^ 2)) =ᵐ[haar 1] u := by
    filter_upwards [hu0] with x hx
    exact Real.sqrt_sq hx
  have hgu : weakGrad u =ᵐ[haar 1] g :=
    weakGrad_ae_unique (isWeakGrad_weakGrad ⟨g, hw⟩) hw
  have hU : MemH1 (haar 1) u := by
    refine ⟨⟨g, hw⟩, hu, ?_⟩
    have h1 : MemLp (fun x => Real.sqrt (sqNorm (g x))) 2 (haar 1) := by
      have : (fun x => Real.sqrt (sqNorm (g x))) = fun x => |g x 0| := by
        funext x
        simp [sqNorm, Real.sqrt_sq_eq_abs]
      rw [this]
      exact (hg 0).abs
    refine h1.ae_eq ?_
    filter_upwards [hgu] with x hx
    rw [hx]
  have hV : MemH1 (haar 1) (fun x => Real.sqrt (u x ^ 2)) := appA_memH1_congr_ae hae.symm hU
  refine ⟨hV, ?_⟩
  have h2 := appA_weakGrad_congr_ae hae hV.1
  filter_upwards [h2, hgu] with x hx1 hx2
  rw [hx1, hx2]

/-! ### The direct method -/

theorem attainment_of_package {rho : ℕ → Torus 1 → Real}
    (ha : ∀ n, Admissible cosV (cosW 1) (rho n))
    (hb : ∀ n, fisher (rho n) < 18 * aCos)
    (hquot : Tendsto (fun n => realDiss (rho n) / (2 * realGap (rho n))) atTop (𝓝 realRate))
    (hR : realRate < aCos * (3 / 2))
    {u : Torus 1 → Real} {g : Torus 1 → Fin 1 → Real}
    (hu : MemLp u 2 (haar 1)) (hg : ∀ j, MemLp (fun x => g x j) 2 (haar 1))
    (hwg : IsWeakGrad u g)
    (hae : ∀ᵐ x ∂haar 1, Tendsto (fun n => Real.sqrt (rho n x)) atTop (𝓝 (u x)))
    (hweak : ∀ h : Torus 1 → Real, MemLp h 2 (haar 1) →
      Tendsto (fun n => ∫ x, weakGrad (fun y => Real.sqrt (rho n y)) x 0 * h x ∂haar 1)
        atTop (𝓝 (∫ x, g x 0 * h x ∂haar 1))) :
    ∃ rho : Torus 1 → Real, RawOptimizer rho := by
  set rhoInf : Torus 1 → Real := fun x => u x ^ 2 with hrhoInf
  have hu0 : ∀ᵐ x ∂haar 1, 0 ≤ u x := by
    filter_upwards [hae] with x hx
    exact ge_of_tendsto' hx fun n => Real.sqrt_nonneg _
  have hdc : DensConv rho rhoInf supBound :=
    { nonneg := fun n x => (ha n).1 x
      mass := fun n => (ha n).2.1
      bound := fun n => ae_le_supBound (ha n) (hb n)
      tendsto := by
        filter_upwards [hae] with x hx
        exact (hx.pow 2).congr fun n => Real.sq_sqrt ((ha n).1 x) }
  have h0 : ∀ x, 0 ≤ rhoInf x := fun x => sq_nonneg _
  have h1 : ∫ x, rhoInf x ∂haar 1 = 1 := hdc.mass_inf
  obtain ⟨hH1, hgrad⟩ := limit_memH1 hu hg hwg hu0
  have hfI : fisher rhoInf = 4 * ∫ x, g x 0 ^ 2 ∂haar 1 := by
    rw [fisher_eq_of_memH1 h0 h1 hH1]
    congr 1
    exact integral_congr_ae (hgrad.mono fun x hx => by simp only; rw [hx])
  have hHt := hdc.tendsto_entropy h0
  have hQt := hdc.tendsto_firstMode
  have hPt := hdc.tendsto_forceEnergy
  -- the limit is not the Haar density
  have hne : ¬ (rhoInf =ᵐ[haar 1] fun _ => 1) := by
    intro hc
    have hH0 : entropy rhoInf = 0 := by
      rw [entropy_eq_integral h0 h1]
      have : ∫ x, klFun (rhoInf x) ∂haar 1 = ∫ x, klFun (1 : Real) ∂haar 1 :=
        integral_congr_ae (hc.mono fun x hx => by simp only; rw [hx])
      simp [this, klFun_one]
    rw [hH0] at hHt
    have hev : ∀ᶠ n in atTop, realDiss (rho n) / (2 * realGap (rho n)) < aCos * (3 / 2) :=
      hquot.eventually (gt_mem_nhds hR)
    have hIn : Tendsto (fun n => fisher (rho n)) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun n => fisher_nonneg _) ?_
        (by simpa using hHt.const_mul (3 * aCos))
      filter_upwards [hev] with n hn
      exact ((subthreshold_bounds (ha n) hn).1).le
    have hη : 0 < (3 * aCos / 2 - realRate) / 2 := by linarith
    have h3 := eventually_quotient_ge ha hIn hη
    have h4 := hquot.eventually (gt_mem_nhds
      (show realRate < 3 * aCos / 2 - (3 * aCos / 2 - realRate) / 2 by linarith))
    obtain ⟨n, hn3, hn4⟩ := (h3.and h4).exists
    linarith
  have hfin := (entropy_fisher_finite' h0 h1 hH1).1
  have hHpos : 0 < entropy rhoInf := klDiv_toReal_pos h0 h1 hfin hne
  have hGpos : 0 < realGap rhoInf := by
    unfold realGap
    have := firstMode_nonneg rhoInf
    linarith
  have hadm : Admissible cosV (cosW 1) rhoInf := by
    refine ⟨h0, h1, hH1, ?_⟩
    rw [gap_eq_real' h0 h1 hH1]
    exact_mod_cast hGpos
  -- passage to the limit in the optimizer equation
  have hG : Tendsto (fun n => realGap (rho n)) atTop (𝓝 (realGap rhoInf)) := by
    unfold realGap
    exact hHt.add (hQt.div_const 2)
  have hDlim : Tendsto (fun n => realDiss (rho n)) atTop
      (𝓝 (realRate * (2 * realGap rhoInf))) := by
    refine (hquot.mul (hG.const_mul 2)).congr fun n => ?_
    have := (realGap_pos (ha n)).ne'
    field_simp
  have hIlim : Tendsto (fun n => fisher (rho n)) atTop
      (𝓝 (realRate * (2 * realGap rhoInf) - 2 * aCos * firstMode rhoInf -
        forceEnergy rhoInf)) := by
    have := (hDlim.sub (hQt.const_mul (2 * aCos))).sub hPt
    refine this.congr fun n => ?_
    unfold realDiss
    ring
  have hlsc := fisher_lsc ha (hg 0) hweak hIlim
  have hup : realDiss rhoInf ≤ 2 * realRate * realGap rhoInf := by
    unfold realDiss
    rw [hfI]
    linarith
  have hlow : realRate * (2 * realGap rhoInf) ≤ realDiss rhoInf := by
    have := realRate_le_realQuotient hadm
    rwa [le_div_iff₀ (by positivity)] at this
  exact ⟨rhoInf, hadm, (optimizer_equation_iff hadm).mpr (by linarith)⟩

/-- **Attainment below the threshold** (the content of `AttainmentBelowThreshold`). -/
theorem attainment_below_threshold_core (hR : realRate < aCos * (3 / 2)) :
    ∃ rho : Torus 1 → Real, RawOptimizer rho := by
  obtain ⟨rho0, ha0, hb0, hq0, u, g, hu, hg, hwg, hL2, hweak0⟩ :=
    exists_rellich_minimizing_sequence hR
  obtain ⟨phi, hphi, hae⟩ := exists_ae_subseq_of_L2
    (f := fun n x => Real.sqrt (rho0 n x)) (fun n => (ha0 n).2.2.1.2.1) hu hL2
  exact attainment_of_package (rho := fun n => rho0 (phi n)) (fun n => ha0 (phi n))
    (fun n => (hb0 (phi n)).2) (hq0.comp hphi.tendsto_atTop) hR hu hg hwg hae
    (fun h hh => (hweak0 0 h hh).comp hphi.tendsto_atTop)

end SharpLSI.FL.Prop82
