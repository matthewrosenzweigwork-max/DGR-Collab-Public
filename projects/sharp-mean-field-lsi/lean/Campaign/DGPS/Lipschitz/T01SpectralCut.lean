import DGPS.Lipschitz.T01HybridComparison
import DGPS.Lipschitz.T01DependencyBridge
import FullLabeledLSI.Paper.Prop23GAltB

/-!
# Uniform spectral cutoff of the current reference comparison form

The one-body LSI, reference/Haar measure comparison, spectral growth and fluctuation moment
inputs come from the same current spectral witness. The smoothing time is chosen before the
spectral level, uniformly over the particle number and the stated H1 and higher-moment bounds.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace DGPS.Lipschitz

open KernelApproximation SharpLSI SharpLSI.FL

private theorem campaign_fluct_moment {d : ℕ} (S : Spec d) (aux : Aux S) (n k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ X, (fluct S.v N n X) ^ (2 * k) ∂QN S.mu N ≤ C := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  obtain ⟨C0, hC0, hCm⟩ := Sec6.fluct_moment_bound k
  have hG := goodBasis_of_spec_aux S aux
  obtain ⟨B, hB⟩ := hG.bdd (n + 1)
  have hcent : ∫ x, S.v (n + 1) x ∂S.mu = 0 := by
    have h := hG.orth (n + 1) 0
    rw [hG.zero] at h
    simpa using h
  refine ⟨C0 * B ^ (2 * k), mul_nonneg hC0 (by rw [pow_mul]; positivity), fun N hN => ?_⟩
  exact hCm (Torus d) S.mu N hN (S.v (n + 1)) B
    (hG.meas (n + 1)) (Eventually.of_forall hB) hcent

private theorem campaign_UB_fluct {d : ℕ} (S : Spec d) (aux : Aux S)
    (hC1 : ∀ j, Gross.C1T (S.v j)) (n : ℕ) :
    UB S.mu (fun N X => fluct S.v N n X) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  intro q hq1 hq
  obtain ⟨n0, hn0⟩ := ENNReal.exists_nat_gt hq
  obtain ⟨C, hC0, hC⟩ := campaign_fluct_moment S aux n (n0 + 1)
  refine ⟨C ^ (1 / ((2 * (n0 + 1) : ℕ) : ℝ)), by positivity, fun N hN => ⟨?_, ?_⟩⟩
  · exact (schroC_Z_facts (μ := S.mu) hC1 n N).2.mono_exponent le_top
  · have hqle : q ≤ ((2 * (n0 + 1) : ℕ) : ℝ≥0∞) :=
      hn0.le.trans (by exact_mod_cast (by omega : n0 ≤ 2 * (n0 + 1)))
    refine (eLpNorm_le_eLpNorm_of_exponent_le hqle).trans ?_
    exact schroC_eLpNorm_le (schroC_Z_facts (μ := S.mu) hC1 n N).2 (n0 + 1)
      (2 * (n0 + 1)) rfl (by omega) (hC N hN)

private theorem campaign_UB_uR {d : ℕ} (S : Spec d) (aux : Aux S)
    (hC1 : ∀ j, Gross.C1T (S.v j)) {W : Torus d → Torus d → ℝ}
    (A : FiniteRankApprox W S.mu S.v) (R : ℕ) :
    UB S.mu (fun N X => uR A R (fun n => fluct S.v N n X)) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  unfold uR
  refine UB.const_mul (UB.sum _ fun i _ => UB.sum _ fun j _ => ?_) _
  exact (((campaign_UB_fluct S aux hC1 i).const_mul _).mul (campaign_UB_fluct S aux hC1 j))

private theorem campaign_UB_vR {d : ℕ} (S : Spec d) (aux : Aux S)
    (hC1 : ∀ j, Gross.C1T (S.v j)) {W : Torus d → Torus d → ℝ}
    (A : FiniteRankApprox W S.mu S.v) (R : ℕ) :
    UB S.mu (fun N X => vR A S.lam R (fun n => fluct S.v N n X)) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have hZ := campaign_UB_fluct S aux hC1
  unfold vR
  refine UB.add (UB.neg_sub (UB.const_mul (UB.sum _ fun m _ => UB.const_mul ?_ _) _)
    (UB.const _)) (UB.const_mul (UB.sum _ fun i _ => UB.sum _ fun j _ => ?_) _)
  · exact UB.sq (UB.sum _ fun j _ => (hZ j).const_mul _)
  · exact (((hZ i).mul (UB.const _)).mul (UB.const _)).mul (hZ j)

/-- Smoothing followed by a spectral cutoff changes the actual reference comparison form
by at most epsilon, uniformly over the stated particle energy and higher-moment bounds. -/
theorem campaign_J_cut {d : ℕ} (S : Spec d) (aux : Aux S)
    (he : IsRefEigenbasis S.mu S.v S.lam)
    (hC1 : ∀ j, Gross.C1T (S.v j)) (hlam0 : S.lam 0 = 0)
    {W : Torus d → Torus d → ℝ}
    (A : FiniteRankApprox W S.mu S.v) (CR : ℕ → ℕ → ℕ → ℝ) (R : ℕ)
    {p : ℝ} (hp : 1 < p) {M1 M2 : ℝ} (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) :
    ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, 0 < t ∧ ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ N : ℕ, 1 ≤ N →
      ∀ Ψ : Config N d → ℝ, MemH1C (QN S.mu N) Ψ →
        refEnergy S.mu Ψ ≤ ENNReal.ofReal M1 →
        ∫⁻ X, ENNReal.ofReal (|Ψ X| ^ (2 * p)) ∂QN S.mu N ≤
          ENNReal.ofReal M2 →
        InSpectralRange S.v S.lam L (Spectral.Fcut S.mu S.v S.lam t L Ψ) ∧
        eLpNorm (Spectral.Fcut S.mu S.v S.lam t L Ψ) 2 (QN S.mu N) ≤
          ENNReal.ofReal (M2 ^ (1 / (2 * p))) ∧
        Jexpr A S.lam (CR R) R (Spectral.Fcut S.mu S.v S.lam t L Ψ) - ε ≤
          Jexpr A S.lam (CR R) R Ψ := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  let P : BoundedPositiveReference d :=
    { density := S.w, measurable_density := S.meas, lower := S.c, upper := S.C,
      lower_pos := S.pos, lower_le := S.bound.mono fun _ hx => hx.1,
      le_upper := S.bound.mono fun _ hx => hx.2, mass_one := S.prob }
  obtain ⟨x, hx, hy⟩ := S.bound.exists
  have hupper : 0 < S.C := S.pos.trans_le (hx.trans hy)
  let a : ℝ := S.c / S.C
  have ha : 0 < a := div_pos S.pos hupper
  have hrls : ENNReal.ofReal a ≤ rLS S.mu := legacy_reference_lsi_lower_bound P
  have hpkg : ∀ (N : ℕ) {s Bs t : ℝ} (L : ℝ) (Ψ : Config N d → ℝ), 2 ≤ s → 0 < t →
      MemH1C (Spectral.Q S.mu N) Ψ → MemLp Ψ (ENNReal.ofReal s) (Spectral.Q S.mu N) →
      eLpNorm Ψ (ENNReal.ofReal s) (Spectral.Q S.mu N) ≤ ENNReal.ofReal Bs →
      Spectral.CutPackage S.mu S.v S.lam a s Bs t L Ψ (Spectral.Sfun he t Ψ)
        (Spectral.Fcut S.mu S.v S.lam t L Ψ) := by
    intro N s Bs t L Ψ hs ht hH hΨ hB
    exact Spectral.cut_package_p5 P.measure_le_smul_haar P.haar_le_smul_measure he hC1
      (fun _ => EventuallyEq.refl _ _) ha hrls hlam0 aux.hd ⟨aux.a, aux.a_pos, aux.weyl⟩
      hs ht L hH hΨ hB
  intro ε hε
  set s : ℝ := 2 * p with hs
  have hs2 : 2 ≤ s := by rw [hs]; linarith
  have hs0 : 0 < s := by linarith
  set Bs : ℝ := M2 ^ (1 / s) with hBs
  have hBs0 : 0 ≤ Bs := Real.rpow_nonneg hM2 _
  -- weights and their uniform bounds
  have hUBv := campaign_UB_vR S aux hC1 A R
  have hUBu := campaign_UB_uR S aux hC1 A R
  have hBw : ∀ {g : (N : ℕ) → Config N d → ℝ}, UB S.mu g →
      ∃ Bw : ℝ≥0∞ → ℝ, ∀ q : ℝ≥0∞, 1 ≤ q → q ≠ ⊤ → ∀ N : ℕ, 1 ≤ N →
        MemLp (g N) q (QN S.mu N) ∧
          eLpNorm (g N) q (QN S.mu N) ≤ ENNReal.ofReal (Bw q) := by
    intro g hg
    have : ∀ q : ℝ≥0∞, ∃ K : ℝ, 1 ≤ q → q ≠ ⊤ → ∀ N : ℕ, 1 ≤ N →
        MemLp (g N) q (QN S.mu N) ∧
          eLpNorm (g N) q (QN S.mu N) ≤ ENNReal.ofReal K := by
      intro q
      by_cases h : 1 ≤ q ∧ q ≠ ⊤
      · obtain ⟨K, -, hK⟩ := hg q h.1 h.2
        exact ⟨K, fun _ _ => hK⟩
      · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
    choose Bw hBw using this
    exact ⟨Bw, fun q h1 h2 => hBw q h1 h2⟩
  obtain ⟨Bv, hBv⟩ := hBw hUBv
  obtain ⟨Bu, hBu⟩ := hBw hUBu
  -- constants
  set cc : ℝ := (bRate S.mu S.lam (CR R)).toReal / 2 with hcc
  have hcc0 : 0 ≤ cc := by rw [hcc]; positivity
  set lg : ℝ := Real.log (kappaR A R) with hlg
  have hden : 0 < 2 * (1 + 2 * cc + cc * |lg|) := by positivity
  set εcut : ℝ := ε / (2 * (1 + 2 * cc + cc * |lg|)) with he'
  have he'0 : 0 < εcut := by rw [he']; positivity
  have hfin : εcut * 2 * (1 + 2 * cc + cc * |lg|) = ε := by rw [he']; field_simp
  -- step 1 moduli
  have hq1 : (2 : ℝ≥0∞) < ENNReal.ofReal s := by
    have : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [this]
    exact (ENNReal.ofReal_lt_ofReal_iff hs0).2 (by rw [hs]; linarith)
  obtain ⟨δe1, hδe1, hE1⟩ := entropy_continuity (ENNReal.ofReal s) hq1 ENNReal.ofReal_ne_top
    Bs εcut he'0
  obtain ⟨δv1, hδv1, hV1⟩ := weighted_continuity (ENNReal.ofReal s) hq1 ENNReal.ofReal_ne_top
    Bs Bv εcut he'0
  obtain ⟨δu1, hδu1, hU1⟩ := weighted_continuity (ENNReal.ofReal s) hq1 ENNReal.ofReal_ne_top
    Bs Bu εcut he'0
  set δ1 : ℝ := min δe1 (min δv1 δu1) with hδ1
  have hδ10 : 0 < δ1 := lt_min hδe1 (lt_min hδv1 hδu1)
  set t : ℝ := min 1 (δ1 ^ 2 / (M1 + 1)) with ht
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have htM : Real.sqrt (t * M1) ≤ δ1 := by
    rw [Real.sqrt_le_iff]
    refine ⟨hδ10.le, ?_⟩
    have h1 : t ≤ δ1 ^ 2 / (M1 + 1) := min_le_right _ _
    calc t * M1 ≤ δ1 ^ 2 / (M1 + 1) * M1 := mul_le_mul_of_nonneg_right h1 hM1
      _ ≤ δ1 ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg δ1]
  -- step 2 moduli
  have hq2 := ga_two_lt ha ht0
  obtain ⟨δe2, hδe2, hE2⟩ := entropy_continuity (ENNReal.ofReal (1 + Real.exp (a * t))) hq2
    ENNReal.ofReal_ne_top Bs εcut he'0
  obtain ⟨δv2, hδv2, hV2⟩ := weighted_continuity (ENNReal.ofReal (1 + Real.exp (a * t))) hq2
    ENNReal.ofReal_ne_top Bs Bv εcut he'0
  obtain ⟨δu2, hδu2, hU2⟩ := weighted_continuity (ENNReal.ofReal (1 + Real.exp (a * t))) hq2
    ENNReal.ofReal_ne_top Bs Bu εcut he'0
  set δ2 : ℝ := min δe2 (min δv2 δu2) with hδ2
  have hδ20 : 0 < δ2 := lt_min hδe2 (lt_min hδv2 hδu2)
  refine ⟨t, ht0, -Real.log (δ2 / (Bs + 1)) / t, fun L hL N hN Ψ hΨH hE hΨp => ?_⟩
  -- the cut package
  have hΨ2 : MemLp Ψ 2 (QN S.mu N) :=
    (memLp_map_measure_iff hΨH.2.1.aestronglyMeasurable measurable_flat.aemeasurable).1 hΨH.2.1
  obtain ⟨hΨs, hΨsn⟩ := ga_memLp_of_lintegral hs0 hM2 hΨ2.aestronglyMeasurable hΨp
  have hP := hpkg N L Ψ hs2 ht0 hΨH hΨs hΨsn
  have hq2r : (2 : ℝ) < 1 + Real.exp (a * t) := by
    have h1 : 1 < Real.exp (a * t) := by
      have := Real.add_one_lt_exp (ne_of_gt (mul_pos ha ht0)); have := mul_pos ha ht0; linarith
    linarith
  have hs2' : (2 : ℝ) < s := by rw [hs]; linarith
  have hF2 : eLpNorm (Spectral.Fcut S.mu S.v S.lam t L Ψ) 2
      (QN S.mu N) ≤ ENNReal.ofReal (M2 ^ (1 / (2 * p))) :=
    (eLpNorm_le_eLpNorm_of_exponent_le hq2.le).trans hP.eLpNorm_F_q_le_B
  refine ⟨hP.inRange, hF2, ?_⟩
  set Ψt := Spectral.Sfun he t Ψ with hΨt
  set F := Spectral.Fcut S.mu S.v S.lam t L Ψ with hF
  -- distances
  have hd1 : eLpNorm (Ψ - Ψt) 2 (QN S.mu N) ≤ ENNReal.ofReal δ1 := by
    refine hP.eLpNorm_sub_le.trans (ENNReal.ofReal_le_ofReal ?_)
    refine le_trans (Real.sqrt_le_sqrt ?_) htM
    have : (refEnergy S.mu Ψ).toReal ≤ M1 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hE
      rwa [ENNReal.toReal_ofReal hM1] at this
    exact mul_le_mul_of_nonneg_left this ht0.le
  have hd2 : eLpNorm (Ψt - F) 2 (QN S.mu N) ≤ ENNReal.ofReal δ2 := by
    refine hP.eLpNorm_cut_le_B.trans (ENNReal.ofReal_le_ofReal ?_)
    have hL' : -Real.log (δ2 / (Bs + 1)) ≤ t * L := by
      have := (div_le_iff₀ ht0).1 hL
      linarith
    have hex : Real.exp (-(t * L)) ≤ δ2 / (Bs + 1) := by
      calc Real.exp (-(t * L)) ≤ Real.exp (Real.log (δ2 / (Bs + 1))) :=
            Real.exp_le_exp.2 (by linarith)
        _ = δ2 / (Bs + 1) := Real.exp_log (by positivity)
    calc Real.exp (-(t * L)) * Bs ≤ δ2 / (Bs + 1) * Bs :=
          mul_le_mul_of_nonneg_right hex hBs0
      _ ≤ δ2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
  have wv : ∀ s' : ℝ≥0∞, 1 ≤ s' → s' ≠ ⊤ →
      MemLp (fun X : Config N d => vR A S.lam R (fun n => fluct S.v N n X)) s'
        (QN S.mu N) ∧
      eLpNorm (fun X : Config N d => vR A S.lam R (fun n => fluct S.v N n X)) s'
        (QN S.mu N) ≤ ENNReal.ofReal (Bv s') :=
    fun s' h1 h2 => hBv s' h1 h2 N hN
  have wu : ∀ s' : ℝ≥0∞, 1 ≤ s' → s' ≠ ⊤ →
      MemLp (fun X : Config N d => uR A R (fun n => fluct S.v N n X)) s'
        (QN S.mu N) ∧
      eLpNorm (fun X : Config N d => uR A R (fun n => fluct S.v N n X)) s'
        (QN S.mu N) ≤ ENNReal.ofReal (Bu s') :=
    fun s' h1 h2 => hBu s' h1 h2 N hN
  have wv1 : ∀ s' : ℝ≥0∞, 1 ≤ s' → s' ≠ ⊤ → MemLp
      (fun X : Config N d => vR A S.lam R (fun n => fluct S.v N n X)) s' (QN S.mu N) :=
    fun s' h1 h2 => (wv s' h1 h2).1
  have wu1 : ∀ s' : ℝ≥0∞, 1 ≤ s' → s' ≠ ⊤ → MemLp
      (fun X : Config N d => uR A R (fun n => fluct S.v N n X)) s' (QN S.mu N) :=
    fun s' h1 h2 => (wu s' h1 h2).1
  have m1 : δ1 ≤ δe1 := min_le_left _ _
  have m2 : δ1 ≤ δv1 := (min_le_right _ _).trans (min_le_left _ _)
  have m3 : δ1 ≤ δu1 := (min_le_right _ _).trans (min_le_right _ _)
  have n1 : δ2 ≤ δe2 := min_le_left _ _
  have n2 : δ2 ≤ δv2 := (min_le_right _ _).trans (min_le_left _ _)
  have n3 : δ2 ≤ δu2 := (min_le_right _ _).trans (min_le_right _ _)
  -- pair (Ψ, Ψt)
  obtain ⟨hent1, hnorm1⟩ := hE1 _ (QN S.mu N) Ψ Ψt hΨs hP.memLp_Ψt_s hΨsn
    hP.eLpNorm_Ψt_s_le (hd1.trans (ENNReal.ofReal_le_ofReal m1))
  have hv1 := hV1 _ (QN S.mu N) Ψ Ψt _ hΨs hP.memLp_Ψt_s hΨsn
    hP.eLpNorm_Ψt_s_le wv (hd1.trans (ENNReal.ofReal_le_ofReal m2))
  have hu1 := hU1 _ (QN S.mu N) Ψ Ψt _ hΨs hP.memLp_Ψt_s hΨsn
    hP.eLpNorm_Ψt_s_le wu (hd1.trans (ENNReal.ofReal_le_ofReal m3))
  -- pair (Ψt, F)
  obtain ⟨hent2, hnorm2⟩ := hE2 _ (QN S.mu N) Ψt F hP.memLp_Ψt_q hP.memLp_F_q
    hP.eLpNorm_Ψt_q_le_B hP.eLpNorm_F_q_le_B (hd2.trans (ENNReal.ofReal_le_ofReal n1))
  have hv2 := hV2 _ (QN S.mu N) Ψt F _ hP.memLp_Ψt_q hP.memLp_F_q
    hP.eLpNorm_Ψt_q_le_B hP.eLpNorm_F_q_le_B wv (hd2.trans (ENNReal.ofReal_le_ofReal n2))
  have hu2 := hU2 _ (QN S.mu N) Ψt F _ hP.memLp_Ψt_q hP.memLp_F_q
    hP.eLpNorm_Ψt_q_le_B hP.eLpNorm_F_q_le_B wu (hd2.trans (ENNReal.ofReal_le_ofReal n3))
  rw [ga_split (ν := QN S.mu N) hs2' hΨs hP.memLp_Ψt_s wv1] at hv1
  rw [ga_split (ν := QN S.mu N) hs2' hΨs hP.memLp_Ψt_s wu1] at hu1
  rw [ga_split (ν := QN S.mu N) hq2r hP.memLp_Ψt_q hP.memLp_F_q wv1] at hv2
  rw [ga_split (ν := QN S.mu N) hq2r hP.memLp_Ψt_q hP.memLp_F_q wu1] at hu2
  have hEle : (refEnergy S.mu F).toReal ≤
      (refEnergy S.mu Ψ).toReal :=
    ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hE) hP.refEnergy_le
  have key := ga_alg (EΨ := (refEnergy S.mu Ψ).toReal)
    (EF := (refEnergy S.mu F).toReal)
    (vΨ := ∫ X, Ψ X ^ 2 * vR A S.lam R (fun n => fluct S.v N n X) ∂QN S.mu N)
    (vt := ∫ X, Ψt X ^ 2 * vR A S.lam R (fun n => fluct S.v N n X) ∂QN S.mu N)
    (vF := ∫ X, F X ^ 2 * vR A S.lam R (fun n => fluct S.v N n X) ∂QN S.mu N)
    (eΨ := (ent (QN S.mu N) (fun X => Ψ X ^ 2)).toReal)
    (et := (ent (QN S.mu N) (fun X => Ψt X ^ 2)).toReal)
    (eF := (ent (QN S.mu N) (fun X => F X ^ 2)).toReal)
    (uΨ := ∫ X, Ψ X ^ 2 * URN A R N X ∂QN S.mu N)
    (ut := ∫ X, Ψt X ^ 2 * URN A R N X ∂QN S.mu N)
    (uF := ∫ X, F X ^ 2 * URN A R N X ∂QN S.mu N)
    (nΨ := ∫ X, Ψ X ^ 2 ∂QN S.mu N)
    (nt := ∫ X, Ψt X ^ 2 ∂QN S.mu N)
    (nF := ∫ X, F X ^ 2 ∂QN S.mu N)
    (cc := cc) (lg := lg) (e' := εcut) hEle hv1 hv2 hent1 hent2 hu1 hu2 hnorm1 hnorm2 hcc0
  rw [Jexpr_unfold, Jexpr_unfold, ← hcc, ← hlg]
  have : 2 * εcut * (1 + 2 * cc + cc * |lg|) = ε := by rw [← hfin]; ring
  linarith


end DGPS.Lipschitz
