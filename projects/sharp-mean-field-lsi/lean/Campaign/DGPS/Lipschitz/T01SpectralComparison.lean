import DGPS.Lipschitz.T01FiniteRankComparison
import FullLabeledLSI.Paper.Hybrid63AltO

/-!
# Spectral comparison for a campaign reference

The retained-label errors vanish on the actual campaign spectral basis. For every fixed
finite-rank approximation with positive interaction matrix, the corresponding reference
comparison form has nonnegative lower limit on each fixed spectral range. This is the
reference-product step; Gibbs transfer and the rank limit remain separate.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace DGPS.Lipschitz

open KernelApproximation SharpLSI SharpLSI.FL

private theorem campaign_joint_replace {d : ℕ} (S : Spec d) (aux : Aux S)
    (he : IsRefEigenbasis S.mu S.v S.lam)
    (hC1 : ∀ j, Gross.C1T (S.v j)) (hlam0 : S.lam 0 = 0) (hlam1 : 0 < S.lam 1)
    (J JR : ℕ) (hJ : JR ≤ J) (Φ : ℝ × (Fin JR → ℝ) → ℝ) (hΦ : Continuous Φ)
    (hgrowth : ∃ (K : ℝ) (k : ℕ), ∀ p, |Φ p| ≤ K * (1 + ‖p‖) ^ k) (L B : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ᶠ N in atTop, ∀ c : (Fin N → Fin (J + 1)) → ℝ, SpectralCoeff S.lam L c →
        ∑ j, c j ^ 2 ≤ B ^ 2 →
          |∫ X, Φ (polyEval S.v c X, fun m => Zlow S.v c δ X (Fin.castLE hJ m))
              ∂Measure.pi (fun _ : Fin N => S.mu) -
            ∫ w, Φ (hybEval S.v c δ w, fun m => Glow c δ w (Fin.castLE hJ m))
              ∂hybMeasure S.mu N J| ≤ ε := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  let P : BoundedPositiveReference d :=
    { density := S.w, measurable_density := S.meas, lower := S.c, upper := S.C,
      lower_pos := S.pos, lower_le := S.bound.mono fun _ hx => hx.1,
      le_upper := S.bound.mono fun _ hx => hx.2, mass_one := S.prob }
  have hG := goodBasis_of_spec_aux S aux
  have hmom : ∀ J, HybridPolyMoment S.mu S.v S.lam J :=
    fun J => hybrid_moments_of_campaign_reference P he hC1 hlam0 hlam1 J
  intro ε hε
  obtain ⟨δ₀, hδ₀, H⟩ := joint_replace_good hG (hmom J) hlam0 S.lam_nonneg he.mono
    hlam1 hJ hΦ hgrowth L B ε hε
  refine ⟨δ₀, hδ₀, fun δ hδ hδδ => ?_⟩
  filter_upwards [H δ hδ hδδ] with N hN c hc hB
  rw [integral_orig_eq_IP, integral_hyb_eq_IP]
  exact hN c hc hB

private theorem campaign_errS26_small {d : ℕ} (S : Spec d) (aux : Aux S)
    (he : IsRefEigenbasis S.mu S.v S.lam)
    (hC1 : ∀ j, Gross.C1T (S.v j)) (hlam0 : S.lam 0 = 0) (hlam1 : 0 < S.lam 1)
    {W : Torus d → Torus d → ℝ}
    (A : FiniteRankApprox W S.mu S.v) (R : ℕ)
    (J JR : ℕ) (hJ : JR ≤ J) (hsJR : ∀ i ∈ A.s R, i < JR) (L B τ K0 : ℝ) (hτ : 0 < τ)
    (hK0 : 0 ≤ K0) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ᶠ N in atTop, ∀ c : (Fin N → Fin (J + 1)) → ℝ, SpectralCoeff S.lam L c →
        ∑ j, c j ^ 2 ≤ B ^ 2 →
        ∫ X, polyEval S.v c X ^ 2 ∂Measure.pi (fun _ : Fin N => S.mu) ≤ B ^ 2 →
          errT2 S.mu A S.lam R S.v c δ ≤ τ ∧
          errT3 S.mu S.v c δ ≤ τ ∧
          errT4 S.mu S.v c δ ≤ τ ∧
          errT6 S.mu A R S.v c δ ≤ τ ∧
          K0 * errT7 S.mu S.v c δ ≤ τ := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  let P : BoundedPositiveReference d :=
    { density := S.w, measurable_density := S.meas, lower := S.c, upper := S.C,
      lower_pos := S.pos, lower_le := S.bound.mono fun _ hx => hx.1,
      le_upper := S.bound.mono fun _ hx => hx.2, mass_one := S.prob }
  have hG := goodBasis_of_spec_aux S aux
  have hmom : ∀ J, HybridPolyMoment S.mu S.v S.lam J :=
    fun J => hybrid_moments_of_campaign_reference P he hC1 hlam0 hlam1 J
  -- uniform continuity of `ψ`
  have huc : UniformContinuousOn Sec6.psi (Set.Icc 0 (B ^ 2 + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous Real.continuous_mul_log.continuousOn
  obtain ⟨η, hη, hηH⟩ := Metric.uniformContinuousOn_iff.mp huc τ hτ
  set ε0 : ℝ := min (min (τ / (K0 + 1)) (η / 2)) 1 with hε0
  have hε0pos : 0 < ε0 := by
    have : 0 < K0 + 1 := by linarith
    positivity
  have hε01 : ε0 ≤ τ / (K0 + 1) := (min_le_left _ _).trans (min_le_left _ _)
  have hε02 : ε0 ≤ η / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hε03 : ε0 ≤ 1 := min_le_right _ _
  -- the four tests
  obtain ⟨δ1, hδ1, H1⟩ := campaign_joint_replace S aux he hC1 hlam0 hlam1 J JR hJ (Phi1 JR)
    (continuous_Phi1 JR) (growth_Phi1 JR) L B τ hτ
  obtain ⟨δ0, hδ0, H0⟩ := campaign_joint_replace S aux he hC1 hlam0 hlam1 J JR hJ (Phi0 JR)
    (continuous_Phi0 JR) (growth_Phi0 JR) L B ε0 hε0pos
  obtain ⟨δu, hδu, Hu⟩ := campaign_joint_replace S aux he hC1 hlam0 hlam1 J JR hJ
    (PhiQuad JR (A.s R) (fun i j => A.a R i j / 2) 0)
    (continuous_PhiQuad JR _ _ _) (growth_PhiQuad JR _ _ _) L B τ hτ
  obtain ⟨δv, hδv, Hv⟩ := campaign_joint_replace S aux he hC1 hlam0 hlam1 J JR hJ
    (PhiQuad JR (A.s R) (vQ A S.lam R) (-((1 / 2) * ∑ m ∈ A.s R, A.a R m m * S.lam (m + 1))))
    (continuous_PhiQuad JR _ _ _) (growth_PhiQuad JR _ _ _) L B τ hτ
  refine ⟨min (min δ1 δ0) (min δu δv), lt_min (lt_min hδ1 hδ0) (lt_min hδu hδv),
    fun δ hδ hδlt => ?_⟩
  have d1 : δ < δ1 := hδlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have d0 : δ < δ0 := hδlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have du : δ < δu := hδlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have dv : δ < δv := hδlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  filter_upwards [H1 δ hδ d1, H0 δ hδ d0, Hu δ hδ du, Hv δ hδ dv] with N h1 h0 hu hv
  intro c hc hB hq
  have e3 := h1 c hc hB
  have e7 := h0 c hc hB
  have e6 := hu c hc hB
  have e2 := hv c hc hB
  -- identify the errors with the Lemma 7.1 differences
  have hE3 : errT3 S.mu S.v c δ ≤ τ := by
    unfold errT3; exact e3
  have hE7 : errT7 S.mu S.v c δ ≤ ε0 := by
    unfold errT7; exact e7
  have hE6 : errT6 S.mu A R S.v c δ ≤ τ := by
    unfold errT6
    simp_rw [uR_zext_castLE A R hJ hsJR]
    simpa [PhiQuad] using e6
  have hE2 : errT2 S.mu A S.lam R S.v c δ ≤ τ := by
    unfold errT2
    simp_rw [vR_zext_castLE A S.lam R hJ hsJR]
    simpa [PhiQuad] using e2
  refine ⟨hE2, hE3, ?_, hE6, ?_⟩
  · -- ψ
    set mq : ℝ := ∫ X, polyEval S.v c X ^ 2 ∂Measure.pi (fun _ : Fin N => S.mu)
      with hmq
    set mh : ℝ := ∫ w, hybEval S.v c δ w ^ 2 ∂hybMeasure S.mu N J with hmh
    have hmq0 : 0 ≤ mq := integral_nonneg fun X => sq_nonneg _
    have hmh0 : 0 ≤ mh := integral_nonneg fun w => sq_nonneg _
    have habs : |mq - mh| ≤ ε0 := by unfold errT7 at hE7; exact hE7
    have hmh1 : mh ≤ B ^ 2 + 1 := by
      have := (abs_le.1 habs).1
      linarith
    have hd' : dist mq mh < η := by
      rw [Real.dist_eq]; linarith
    have := hηH mq ⟨hmq0, by linarith⟩ mh ⟨hmh0, hmh1⟩ hd'
    rw [Real.dist_eq] at this
    unfold errT4
    exact this.le
  · calc K0 * errT7 S.mu S.v c δ ≤ K0 * ε0 :=
          mul_le_mul_of_nonneg_left hE7 hK0
      _ ≤ K0 * (τ / (K0 + 1)) := mul_le_mul_of_nonneg_left hε01 hK0
      _ ≤ τ := by
          rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
          nlinarith


private theorem campaign_errT15_small {d : ℕ} (S : Spec d) (aux : Aux S)
    (he : IsRefEigenbasis S.mu S.v S.lam)
    (hC1 : ∀ j, Gross.C1T (S.v j)) (hlam0 : S.lam 0 = 0) (hlam1 : 0 < S.lam 1)
    {W : Torus d → Torus d → ℝ}
    (A : FiniteRankApprox W S.mu S.v) (R : ℕ)
    (J : ℕ) (hJ : ∀ i ∈ A.s R, i < J) (L B τ : ℝ) (hτ : 0 < τ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N in atTop, ∀ c : (Fin N → Fin (J + 1)) → ℝ, SpectralCoeff S.lam L c → ∑ j, c j ^ 2 ≤ B ^ 2 →
      0 < lowCount c δ ∧ errT1 S.mu A S.lam R S.v c δ ≤ τ ∧
        errT5 S.mu A R S.v c δ ≤ τ := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  let P : BoundedPositiveReference d :=
    { density := S.w, measurable_density := S.meas, lower := S.c, upper := S.C,
      lower_pos := S.pos, lower_le := S.bound.mono fun _ hx => hx.1,
      le_upper := S.bound.mono fun _ hx => hx.2, mass_one := S.prob }
  have hG := goodBasis_of_spec_aux S aux
  have hmom : ∀ J, HybridPolyMoment S.mu S.v S.lam J :=
    fun J => hybrid_moments_of_campaign_reference P he hC1 hlam0 hlam1 J
  have hnn := S.lam_nonneg
  have hmono := he.mono
  have hpos := hlam1
  have hmom' := hmom J
  obtain ⟨Mq1, Kq1, hM1, hK1, H1⟩ := est721 hG hmom' hlam0 L B (A.s R) hJ (vQ A S.lam R)
  obtain ⟨Mq2, Kq2, hM2, hK2, H2⟩ := est721 hG hmom' hlam0 L B (A.s R) hJ
    (fun i j => A.a R i j / 2)
  set Cs1 : ℝ := ∑ i ∈ A.s R, ∑ j ∈ A.s R, |vQ A S.lam R i j| with hCs1
  set Cs2 : ℝ := ∑ i ∈ A.s R, ∑ j ∈ A.s R, |A.a R i j / 2| with hCs2
  have hC1 : 0 ≤ Cs1 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hC2 : 0 ≤ Cs2 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  set bmax : ℝ := max (L / S.lam 1) 0 * B ^ 2 / δ with hbmax
  obtain ⟨t1, ht1, N01, hN01⟩ := choose_t Cs1 Mq1 Kq1 bmax τ hC1 hM1 hK1 hτ
  obtain ⟨t2, ht2, N02, hN02⟩ := choose_t Cs2 Mq2 Kq2 bmax τ hC2 hM2 hK2 hτ
  refine eventually_atTop.2 ⟨max (max N01 N02) (⌈bmax⌉₊ + 1), fun N hN c hc hB => ?_⟩
  have hN1 : N01 ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : N02 ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN3 : ⌈bmax⌉₊ + 1 ≤ N := (le_max_right _ _).trans hN
  have hlow := lowCount_lower hlam0 hnn hmono hpos hc hB hδ
  have hNb : bmax < N := by
    have : (⌈bmax⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN3
    linarith [Nat.le_ceil bmax]
  have hn : 0 < lowCount c δ := by
    have : (0 : ℝ) < lowCount c δ := by linarith
    exact_mod_cast this
  have hcard : ((retained c δ).card : ℝ) ≤ bmax := by
    have hle : (retained c δ).card ≤ N := by simpa using Finset.card_le_univ (retained c δ)
    have : ((retained c δ).card : ℝ) = N - lowCount c δ := by
      unfold lowCount; rw [Nat.cast_sub hle]; ring
    linarith
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by
    have : 0 ≤ bmax := by
      rw [hbmax]
      have : (0 : ℝ) ≤ max (L / S.lam 1) 0 := le_max_right _ _
      positivity
    exact this) hNb
  have hx0 : 0 ≤ ((retained c δ).card : ℝ) / N := by positivity
  have hxb : ((retained c δ).card : ℝ) / N ≤ bmax / N :=
    div_le_div_of_nonneg_right hcard hNpos.le
  refine ⟨hn, ?_, ?_⟩
  · unfold errT1
    rw [errT_eq_integral hG A R c δ (vQ A S.lam R)
      (-((1 / 2) * ∑ m ∈ A.s R, A.a R m m * S.lam (m + 1))) (vR A S.lam R)
      (fun y => by rw [vR_eq_quad]; ring)]
    exact (H1 N c hc hB δ hn t1 ht1).trans (hN01 N hN1 _ hx0 hxb)
  · unfold errT5
    rw [errT_eq_integral hG A R c δ (fun i j => A.a R i j / 2) 0 (uR A R)
      (fun y => by rw [uR_eq_quadA]; ring)]
    exact (H2 N c hc hB δ hn t2 ht2).trans (hN02 N hN2 _ hx0 hxb)


/-- The finite-rank reference comparison has nonnegative lower limit on every fixed
spectral range. Matrix positivity is a finite-rank hypothesis, not a particle-rate premise. -/
theorem finite_rank_spectral_comparison {d : ℕ} (S : Spec d) (aux : Aux S)
    (he : IsRefEigenbasis S.mu S.v S.lam)
    (hC1 : ∀ j, Gross.C1T (S.v j)) (hlam0 : S.lam 0 = 0) (hlam1 : 0 < S.lam 1)
    {W : Torus d → Torus d → ℝ} (A : FiniteRankApprox W S.mu S.v) (R : ℕ)
    {σ : ℝ} (hσ : 0 < σ) (hpos : PosIPlus A R σ) (C : ℕ → ℕ → ℝ)
    (hC : IsInverseOfIPlus (A.a R) C) (L : ℝ) (F : (N : ℕ) → Config N d → ℝ)
    (hFr : ∀ N, InSpectralRange S.v S.lam L (F N))
    (hBex : ∃ B : ℝ, ∀ N, eLpNorm (F N) 2 (Measure.pi fun _ : Fin N => S.mu) ≤
      ENNReal.ofReal B) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, -ε ≤ Jexpr A S.lam C R (F N) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  intro ε hε
  obtain ⟨B, hB⟩ := hBex
  have hac : S.mu ≪ volume := Analysis.CompactResolvent.wMeasure_ac_haar
  have hca : volume ≪ S.mu := Analysis.CompactResolvent.haar_ac_wMeasure S.pos S.bound
  have hlamnn := S.lam_nonneg
  have hmono := he.mono
  have hlam1pos := hlam1
  have hae : ∀ j, S.v j =ᵐ[S.mu] S.v j := fun _ => Filter.EventuallyEq.refl _ _
  obtain ⟨JL, hJL⟩ := exists_JL S.lam hmono aux.hd aux.a_pos aux.weyl L
  set JR : ℕ := (A.s R).sup id + 1 with hJR
  set J : ℕ := max JR JL with hJdef
  have hsJR : ∀ i ∈ A.s R, i < JR := fun i hi => by
    have := Finset.le_sup (f := id) hi
    simp only [id] at this
    omega
  have hJ : ∀ i ∈ A.s R, i < J := fun i hi =>
    lt_of_lt_of_le (hsJR i hi) (le_max_left _ _)
  set Λ : ℝ := S.lam 1 with hΛ
  set K0 : ℝ := |Real.log (kappaR A R)| with hK0
  have hΛ0 : 0 < Λ := hlam1pos
  have hτ : 0 < ε / (3 + 3 * Λ) := by positivity
  set τ : ℝ := ε / (3 + 3 * Λ) with hτdef
  obtain ⟨δ₀, hδ₀, H26⟩ := campaign_errS26_small S aux he hC1 hlam0 hlam1 A R J JR
    (le_max_left _ _) hsJR L B τ K0 hτ (abs_nonneg _)
  have hδ : 0 < δ₀ / 2 := by positivity
  have H15 := campaign_errT15_small S aux he hC1 hlam0 hlam1 A R J hJ L B τ hτ hδ
  have hρ0 : 0 ≤ (bRate S.mu S.lam C).toReal := ENNReal.toReal_nonneg
  obtain ⟨M, hM⟩ := (hC1 1).bounded
  have hM' : ∀ x : SharpLSI.Torus d, |S.v 1 x| ≤ M := hM
  have hrl := rLS_le_lam_one_of_bdd (C := M) hac he (Filter.Eventually.of_forall hM')
  have hρΛ : (bRate S.mu S.lam C).toReal ≤ Λ := rho_le_lam_one he hrl
  filter_upwards [H26 (δ₀ / 2) hδ (by linarith), H15] with N h26 h15
  obtain ⟨T, cc, hT, hFe⟩ := hFr N
  have hTJ : ∀ k ∈ T, ∀ i, k i ≤ J := fun k hk i => by
    have h1 : S.lam (k i) ≤ ∑ i, S.lam (k i) :=
      Finset.single_le_sum (f := fun i => S.lam (k i)) (fun i _ => hlamnn _) (Finset.mem_univ i)
    exact (hJL _ (h1.trans (hT k hk))).trans (le_max_right _ _)
  set c : (Fin N → Fin (J + 1)) → ℝ := coefArr (J := J) T cc with hc
  have hcspec : SpectralCoeff S.lam L c := spectralCoeff_coefArr S.lam L T hT cc
  have hint : ∫ X, F N X ^ 2 ∂(Measure.pi fun _ : Fin N => S.mu) ≤ B ^ 2 :=
    integral_sq_le_of_eLpNorm_two (hB N)
  have hsum : ∑ j, c j ^ 2 ≤ B ^ 2 := by
    have := (Gross.torus_energy_formula hac hca he hC1 hae T cc (F := F N) hFe).1
    rw [hc, sum_sq_coefArr T hTJ cc, ← this]
    exact hint
  have hFpoly : ∀ X, F N X = polyEval S.v c X := fun X => by
    rw [hFe X, hc, polyEval_coefArr S.v T hTJ cc X]
  have hint' : ∫ X, polyEval S.v c X ^ 2
      ∂(Measure.pi fun _ : Fin N => S.mu) ≤ B ^ 2 := by
    refine le_trans (le_of_eq ?_) hint
    refine integral_congr_ae ?_
    filter_upwards [ae_pi_eq hae N] with X hX
    rw [hFpoly X, polyEval_congr c X hX]
  obtain ⟨h2, h3, h4, h6, h7⟩ := h26 c hcspec hsum hint'
  obtain ⟨hn, h1', h5⟩ := h15 c hcspec hsum
  have hmain := finite_rank_reference_comparison S aux he hC1 hlam0 hlam1 A (fun _ => C) R hσ hpos hC J hJ L T cc hT hTJ
    (F N) hFe (δ₀ / 2) hn
  set ρ := (bRate S.mu S.lam C).toReal with hρ
  have hτΛ : (3 + 3 * Λ) * τ = ε := by
    rw [hτdef]; field_simp
  have hτ0 := hτ.le
  have hmul : ρ / 2 * (errT3 S.mu S.v c (δ₀ / 2) +
      errT4 S.mu S.v c (δ₀ / 2) + errT5 S.mu A R S.v c (δ₀ / 2)
      + errT6 S.mu A R S.v c (δ₀ / 2) +
      K0 * errT7 S.mu S.v c (δ₀ / 2)) ≤ Λ / 2 * (5 * τ) := by
    apply mul_le_mul (by linarith) (by linarith) _ (by linarith)
    have := abs_nonneg (Real.log (kappaR A R))
    have e3 : 0 ≤ errT3 S.mu S.v c (δ₀ / 2) := abs_nonneg _
    have e4 : 0 ≤ errT4 S.mu S.v c (δ₀ / 2) := abs_nonneg _
    have e5 : 0 ≤ errT5 S.mu A R S.v c (δ₀ / 2) := abs_nonneg _
    have e6 : 0 ≤ errT6 S.mu A R S.v c (δ₀ / 2) := abs_nonneg _
    have e7 : 0 ≤ K0 * errT7 S.mu S.v c (δ₀ / 2) :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    linarith
  have hfin : errT1 S.mu A S.lam R S.v c (δ₀ / 2) +
      errT2 S.mu A S.lam R S.v c (δ₀ / 2) +
      ρ / 2 * (errT3 S.mu S.v c (δ₀ / 2) +
      errT4 S.mu S.v c (δ₀ / 2) + errT5 S.mu A R S.v c (δ₀ / 2)
      + errT6 S.mu A R S.v c (δ₀ / 2) +
      K0 * errT7 S.mu S.v c (δ₀ / 2)) ≤ ε := by
    nlinarith
  have hmain' : -(errT1 S.mu A S.lam R S.v c (δ₀ / 2) +
      errT2 S.mu A S.lam R S.v c (δ₀ / 2) +
      ρ / 2 * (errT3 S.mu S.v c (δ₀ / 2) +
      errT4 S.mu S.v c (δ₀ / 2) + errT5 S.mu A R S.v c (δ₀ / 2)
      + errT6 S.mu A R S.v c (δ₀ / 2) +
      K0 * errT7 S.mu S.v c (δ₀ / 2))) ≤ Jexpr A S.lam C R (F N) := hmain
  linarith


end DGPS.Lipschitz
