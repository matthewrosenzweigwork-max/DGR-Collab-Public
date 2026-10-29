import FullLabeledLSI.Nonvacuity.Prop82.E3_Variation

/-!
# Lane E, part 4: derivatives of entropy and Fisher information along `ρ_s = ρ + s ρ''`

DRAFT written in the cloud without a compiler (lane E, cloud thread).

* `hasDerivAt_entropy_rhoS : HasDerivAt (fun s => entropy (rhoS ρ s)) (-fisher ρ) 0`
* `hasDerivAt_fisher_rhoS : HasDerivAt (fun s => fisher (rhoS ρ s)) (-2 * scoreEnergy ρ) 0`
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82.HeatE

/-! ### Differentiation under the integral sign on the circle -/

theorem bdd_of_continuousOn_param {G : Real → Torus 1 → Real} {s0 : Real}
    (hG : ContinuousOn (fun p : Real × Torus 1 => G p.1 p.2) (Set.Icc (-s0) s0 ×ˢ Set.univ)) :
    ∃ L, ∀ s ∈ Set.Icc (-s0) s0, ∀ x, |G s x| ≤ L := by
  obtain ⟨L, hL⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn hG
  exact ⟨L, fun s hs x => by simpa using hL (s, x) ⟨hs, Set.mem_univ x⟩⟩

/-- Differentiation under the integral over the circle, for a family jointly continuous on
`[-s0, s0] × Torus 1`, together with its derivative. -/
theorem hasDerivAt_integral_param {F F' : Real → Torus 1 → Real} {s0 : Real} (hs0 : 0 < s0)
    (hFm : ∀ s, Measurable (F s)) (hF'm : ∀ s, Measurable (F' s))
    (hF : ContinuousOn (fun p : Real × Torus 1 => F p.1 p.2) (Set.Icc (-s0) s0 ×ˢ Set.univ))
    (hF' : ContinuousOn (fun p : Real × Torus 1 => F' p.1 p.2) (Set.Icc (-s0) s0 ×ˢ Set.univ))
    (hd : ∀ x, ∀ s ∈ Set.Ioo (-s0) s0, HasDerivAt (fun t => F t x) (F' s x) s) :
    HasDerivAt (fun s => ∫ x, F s x ∂haar 1) (∫ x, F' 0 x ∂haar 1) 0 := by
  obtain ⟨L0, hL0⟩ := bdd_of_continuousOn_param hF
  obtain ⟨L1, hL1⟩ := bdd_of_continuousOn_param hF'
  refine SharpLSI.hasDerivAt_integral_bdd (P := haar 1) (s := Set.Ioo (-s0) s0) ?_ hFm hF'm
    (L0 := L0) (L1 := L1) ?_ ?_ hd
  · exact Ioo_mem_nhds (by linarith) hs0
  · exact fun s hs w => hL0 s (Set.Ioo_subset_Icc_self hs) w
  · exact fun s hs w => hL1 s (Set.Ioo_subset_Icc_self hs) w

/-- `{s | |s| ≤ s0}` is a neighbourhood of `0`. -/
theorem abs_le_mem_nhds {s0 : Real} (hs0 : 0 < s0) : {s : Real | |s| ≤ s0} ∈ 𝓝 (0 : Real) := by
  have := Metric.closedBall_mem_nhds (0 : Real) hs0
  convert this using 1
  ext s
  simp

/-! ### Entropy -/

theorem hasDerivAt_klFun_pos {y : Real} (hy : 0 < y) :
    HasDerivAt InformationTheory.klFun (Real.log y) y := by
  have h := ((Real.hasDerivAt_mul_log hy.ne').sub (hasDerivAt_id y)).add_const 1
  have e : InformationTheory.klFun = fun x => x * Real.log x - id x + 1 := by
    funext x
    simp only [InformationTheory.klFun_apply, id]
    ring
  rw [e]
  convert h using 1
  simp

theorem entropy_eq_integral_klFun {rho : Torus 1 → Real} (h : SmoothProbability rho) :
    entropy rho = ∫ x, InformationTheory.klFun (rho x) ∂haar 1 := by
  obtain ⟨B, hB⟩ := SharpLSI.exists_bound_of_continuous (smooth_continuous h.smooth)
  exact (klDiv_densMeasure_bdd (smooth_continuous h.smooth).measurable h.nonneg h.mass
    (B := B) (fun x => (le_abs_self _).trans (hB x))).2

/-- `∫ log ρ · ρ'' = - fisher ρ`. -/
theorem integral_log_mul_dpart2 {rho : Torus 1 → Real} (h : SmoothProbability rho) :
    ∫ x, Real.log (rho x) * dpart (dpart rho 0) 0 x ∂haar 1 = -fisher rho := by
  have hlog : IsSmoothT (logD rho) := contDiff_logD h.smooth h.positive
  have h1 := integral_mul_dpart hlog (smooth_dpart h.smooth)
  have h2 : ∀ x, dpart (logD rho) 0 x * dpart rho 0 x = rho x * scoreTest rho x ^ 2 := by
    intro x
    have : dpart (logD rho) 0 x = scoreTest rho x := rfl
    rw [this, ← rho_mul_scoreTest h x]
    ring
  simp_rw [h2] at h1
  rw [fisher_eq_score_variance h]
  exact h1

theorem hasDerivAt_entropy_rhoS {rho : Torus 1 → Real} (hrho : SmoothProbability rho)
    (hQ : 0 < firstMode rho) :
    HasDerivAt (fun s => entropy (rhoS rho s)) (-fisher rho) 0 := by
  obtain ⟨m, s0, hm, hs0, -, hmrho, hlow, hsp, -, -⟩ := exists_good_interval hrho hQ
  have hlow0 : ∀ s, |s| ≤ s0 → ∀ x, 0 < rhoS rho s x :=
    fun s hs x => lt_of_lt_of_le (by positivity) (hlow s hs x)
  have hF : HasDerivAt (fun s => ∫ x, InformationTheory.klFun (rhoS rho s x) ∂haar 1)
      (∫ x, Real.log (rho x) * dpart (dpart rho 0) 0 x ∂haar 1) 0 := by
    have := hasDerivAt_integral_param (s0 := s0) (F := fun s x => InformationTheory.klFun (rhoS rho s x))
      (F' := fun s x => Real.log (rhoS rho s x) * dpart (dpart rho 0) 0 x) hs0
      (fun s => InformationTheory.continuous_klFun.measurable.comp
        (smooth_continuous (smooth_rhoS hrho.smooth s)).measurable)
      (fun s => ((smooth_continuous (smooth_rhoS hrho.smooth s)).measurable.log).mul
        (smooth_continuous (smooth_dpart2 hrho.smooth)).measurable)
      ?_ ?_ ?_
    · simpa [rhoS_zero] using this
    · -- joint continuity of `klFun (ρ x + s ρ'' x)`
      have hc : Continuous (fun p : Real × Torus 1 => rhoS rho p.1 p.2) := by
        unfold rhoS
        exact ((smooth_continuous hrho.smooth).comp continuous_snd).add
          (continuous_fst.mul ((smooth_continuous (smooth_dpart2 hrho.smooth)).comp continuous_snd))
      exact (InformationTheory.continuous_klFun.comp hc).continuousOn
    · have hc : Continuous (fun p : Real × Torus 1 => rhoS rho p.1 p.2) := by
        unfold rhoS
        exact ((smooth_continuous hrho.smooth).comp continuous_snd).add
          (continuous_fst.mul ((smooth_continuous (smooth_dpart2 hrho.smooth)).comp continuous_snd))
      refine ContinuousOn.mul ?_ ((smooth_continuous (smooth_dpart2 hrho.smooth)).comp
        continuous_snd).continuousOn
      refine hc.continuousOn.log fun p hp => ?_
      exact (hlow0 p.1 (abs_le.mpr ⟨hp.1.1, hp.1.2⟩) p.2).ne'
    · intro x s hs
      have hs' : |s| ≤ s0 := abs_le.mpr ⟨hs.1.le, hs.2.le⟩
      have hpos := hlow0 s hs' x
      have hlin : HasDerivAt (fun t : Real => rho x + t * dpart (dpart rho 0) 0 x)
          (dpart (dpart rho 0) 0 x) s := by
        simpa using ((hasDerivAt_id s).mul_const (dpart (dpart rho 0) 0 x)).const_add (rho x)
      have := (hasDerivAt_klFun_pos (show 0 < rho x + s * dpart (dpart rho 0) 0 x from hpos)).comp s hlin
      exact this
  have hEq : (fun s => entropy (rhoS rho s)) =ᶠ[𝓝 0]
      fun s => ∫ x, InformationTheory.klFun (rhoS rho s x) ∂haar 1 := by
    filter_upwards [abs_le_mem_nhds hs0] with s hs
    exact entropy_eq_integral_klFun (hsp s hs)
  rw [← integral_log_mul_dpart2 hrho]
  exact hF.congr_of_eventuallyEq hEq

/-! ### Fisher information -/

theorem fisher_eq_dpart_integral' {rho : Torus 1 → Real} (h : SmoothProbability rho) :
    fisher rho = ∫ x, dpart rho 0 x ^ 2 / rho x ∂haar 1 := by
  rw [fisher_eq_score_variance h]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    show rho x * scoreTest rho x ^ 2 = dpart rho 0 x ^ 2 / rho x
    rw [← rho_mul_scoreTest h x]
    field_simp [(h.positive x).ne']

/-- Integration by parts for the Fisher information: `∫ (2 ρ' ρ'''/ρ - ρ'² ρ''/ρ²) = -2 ∫ ρ w'²`
where `w = ρ'/ρ`. -/
theorem fisher_integrand_identity {rho : Torus 1 → Real} (hrho : SmoothProbability rho) :
    ∫ x, (2 * dpart rho 0 x * dpart (dpart (dpart rho 0) 0) 0 x * rho x -
        dpart rho 0 x ^ 2 * dpart (dpart rho 0) 0 x) / rho x ^ 2 ∂haar 1 =
      -2 * scoreEnergy rho := by
  have hr := hrho.smooth
  have hw : IsSmoothT (scoreTest rho) := scoreTest_smooth hrho
  set w := scoreTest rho with hwdef
  have hρw : ∀ x, dpart rho 0 x = rho x * w x := fun x => (rho_mul_scoreTest hrho x).symm
  have hD2 : ∀ x, dpart (dpart rho 0) 0 x = rho x * (w x ^ 2 + dpart w 0 x) := by
    intro x
    have h1 : dpart rho 0 = fun y => rho y * w y := funext hρw
    rw [h1, dpart_mul' hr hw, hρw x]
    ring
  have hpt : ∀ x, (2 * dpart rho 0 x * dpart (dpart (dpart rho 0) 0) 0 x * rho x -
        dpart rho 0 x ^ 2 * dpart (dpart rho 0) 0 x) / rho x ^ 2 =
      2 * (w x * dpart (dpart (dpart rho 0) 0) 0 x) - w x ^ 2 * dpart (dpart rho 0) 0 x := by
    intro x
    have hx := (hrho.positive x).ne'
    rw [hρw x]
    field_simp
  -- the three scalar integrals
  have hDw := smooth_dpart hw
  have hD2s := smooth_dpart2 hr
  set A := ∫ x, rho x * dpart w 0 x ^ 2 ∂haar 1 with hA
  set B := ∫ x, rho x * (w x ^ 2 * dpart w 0 x) ∂haar 1 with hB
  have e1 : ∫ x, w x * dpart (dpart (dpart rho 0) 0) 0 x ∂haar 1 = -(B + A) := by
    rw [integral_mul_dpart hw hD2s]
    have : ∀ x, dpart w 0 x * dpart (dpart rho 0) 0 x =
        rho x * (w x ^ 2 * dpart w 0 x) + rho x * dpart w 0 x ^ 2 := by
      intro x; rw [hD2 x]; ring
    simp_rw [this]
    rw [integral_add (smooth_integrable (smooth_mul hr (smooth_mul (smooth_pow hw 2) hDw)))
      (smooth_integrable (smooth_mul hr (smooth_pow hDw 2)))]
  have e3 : ∫ x, rho x * w x ^ 4 ∂haar 1 = -3 * B := by
    have h1 : ∀ x, rho x * w x ^ 4 = dpart rho 0 x * w x ^ 3 := by
      intro x; rw [hρw x]; ring
    simp_rw [h1]
    have h2 := integral_mul_dpart hr (smooth_pow hw 3)
    have h3 : ∀ x, rho x * dpart (fun y => w y ^ 3) 0 x = 3 * (rho x * (w x ^ 2 * dpart w 0 x)) := by
      intro x; rw [dpart_cube hw]; ring
    simp_rw [h3] at h2
    rw [integral_const_mul] at h2
    linarith
  have e2 : ∫ x, w x ^ 2 * dpart (dpart rho 0) 0 x ∂haar 1 = (-3 * B) + B := by
    have : ∀ x, w x ^ 2 * dpart (dpart rho 0) 0 x = rho x * w x ^ 4 + rho x * (w x ^ 2 * dpart w 0 x) := by
      intro x; rw [hD2 x]; ring
    simp_rw [this]
    rw [integral_add (smooth_integrable (smooth_mul hr (smooth_pow hw 4)))
      (smooth_integrable (smooth_mul hr (smooth_mul (smooth_pow hw 2) hDw))), e3]
  have hE : scoreEnergy rho = A := by
    unfold scoreEnergy
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Sec8.gradSq, Fin.sum_univ_one]
    rfl
  simp_rw [hpt]
  rw [integral_sub ((smooth_integrable (smooth_mul hw (smooth_dpart3 hr))).const_mul 2)
    (smooth_integrable (smooth_mul (smooth_pow hw 2) hD2s)), integral_const_mul, e1, e2, hE]
  ring

theorem hasDerivAt_fisher_rhoS {rho : Torus 1 → Real} (hrho : SmoothProbability rho)
    (hQ : 0 < firstMode rho) :
    HasDerivAt (fun s => fisher (rhoS rho s)) (-2 * scoreEnergy rho) 0 := by
  obtain ⟨m, s0, hm, hs0, -, hmrho, hlow, hsp, -, -⟩ := exists_good_interval hrho hQ
  have hpos : ∀ s, |s| ≤ s0 → ∀ x, 0 < rhoS rho s x :=
    fun s hs x => lt_of_lt_of_le (by positivity) (hlow s hs x)
  have hr := hrho.smooth
  set a0 : Torus 1 → Real := dpart rho 0 with ha0
  set d2 : Torus 1 → Real := dpart (dpart rho 0) 0 with hd2
  set d3 : Torus 1 → Real := dpart (dpart (dpart rho 0) 0) 0 with hd3
  have ca0 : Continuous a0 := smooth_continuous (smooth_dpart hr)
  have cd2 : Continuous d2 := smooth_continuous (smooth_dpart2 hr)
  have cd3 : Continuous d3 := smooth_continuous (smooth_dpart3 hr)
  have cr : Continuous rho := smooth_continuous hr
  let F : Real → Torus 1 → Real := fun s x => (a0 x + s * d3 x) ^ 2 / (rho x + s * d2 x)
  let F' : Real → Torus 1 → Real := fun s x =>
    (2 * (a0 x + s * d3 x) * d3 x * (rho x + s * d2 x) - (a0 x + s * d3 x) ^ 2 * d2 x) /
      (rho x + s * d2 x) ^ 2
  have hFeq : ∀ s, |s| ≤ s0 → fisher (rhoS rho s) = ∫ x, F s x ∂haar 1 := by
    intro s hs
    rw [fisher_eq_dpart_integral' (hsp s hs)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [F, dpart_rhoS hr s x, rhoS]
    rfl
  have hjoint : ∀ (G : Real → Torus 1 → Real), Continuous (fun p : Real × Torus 1 => G p.1 p.2) →
      ContinuousOn (fun p : Real × Torus 1 => G p.1 p.2) (Set.Icc (-s0) s0 ×ˢ Set.univ) :=
    fun G h => h.continuousOn
  have hden : ∀ p ∈ Set.Icc (-s0) s0 ×ˢ (Set.univ : Set (Torus 1)), rho p.2 + p.1 * d2 p.2 ≠ 0 := by
    intro p hp
    have := hpos p.1 (abs_le.mpr ⟨hp.1.1, hp.1.2⟩) p.2
    simp only [rhoS] at this
    exact this.ne'
  have cnum : Continuous (fun p : Real × Torus 1 => (a0 p.2 + p.1 * d3 p.2) ^ 2) :=
    ((ca0.comp continuous_snd).add (continuous_fst.mul (cd3.comp continuous_snd))).pow 2
  have cden : Continuous (fun p : Real × Torus 1 => rho p.2 + p.1 * d2 p.2) :=
    (cr.comp continuous_snd).add (continuous_fst.mul (cd2.comp continuous_snd))
  have hF : HasDerivAt (fun s => ∫ x, F s x ∂haar 1) (∫ x, F' 0 x ∂haar 1) 0 := by
    refine hasDerivAt_integral_param (s0 := s0) hs0 ?_ ?_ ?_ ?_ ?_
    · intro s
      exact ((ca0.measurable.add (measurable_const.mul cd3.measurable)).pow_const 2).div
        (cr.measurable.add (measurable_const.mul cd2.measurable))
    · intro s
      refine Measurable.div ?_ ((cr.measurable.add (measurable_const.mul cd2.measurable)).pow_const 2)
      exact (((measurable_const.mul (ca0.measurable.add (measurable_const.mul cd3.measurable))).mul
        cd3.measurable).mul (cr.measurable.add (measurable_const.mul cd2.measurable))).sub
        (((ca0.measurable.add (measurable_const.mul cd3.measurable)).pow_const 2).mul cd2.measurable)
    · exact cnum.continuousOn.div cden.continuousOn hden
    · have cnum' : Continuous (fun p : Real × Torus 1 =>
          2 * (a0 p.2 + p.1 * d3 p.2) * d3 p.2 * (rho p.2 + p.1 * d2 p.2) -
            (a0 p.2 + p.1 * d3 p.2) ^ 2 * d2 p.2) := by
        have c1 : Continuous (fun p : Real × Torus 1 => a0 p.2 + p.1 * d3 p.2) :=
          (ca0.comp continuous_snd).add (continuous_fst.mul (cd3.comp continuous_snd))
        exact ((continuous_const.mul c1).mul (cd3.comp continuous_snd)).mul cden |>.sub
          ((c1.pow 2).mul (cd2.comp continuous_snd))
      exact cnum'.continuousOn.div (cden.pow 2).continuousOn
        (fun p hp => pow_ne_zero 2 (hden p hp))
    · intro x s hs
      have hs' : |s| ≤ s0 := abs_le.mpr ⟨hs.1.le, hs.2.le⟩
      have hne : rho x + s * d2 x ≠ 0 := by
        have := hpos s hs' x
        simp only [rhoS] at this
        exact this.ne'
      have hnum : HasDerivAt (fun t : Real => (a0 x + t * d3 x) ^ 2)
          (2 * (a0 x + s * d3 x) * d3 x) s := by
        have := (((hasDerivAt_id s).mul_const (d3 x)).const_add (a0 x)).fun_pow 2
        simpa using this
      have hdn : HasDerivAt (fun t : Real => rho x + t * d2 x) (d2 x) s := by
        simpa using ((hasDerivAt_id s).mul_const (d2 x)).const_add (rho x)
      exact hnum.fun_div hdn hne
  have hEq : (fun s => fisher (rhoS rho s)) =ᶠ[𝓝 0] fun s => ∫ x, F s x ∂haar 1 := by
    filter_upwards [abs_le_mem_nhds hs0] with s hs
    exact hFeq s hs
  have hval : ∫ x, F' 0 x ∂haar 1 = -2 * scoreEnergy rho := by
    rw [← fisher_integrand_identity hrho]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [F', ha0, hd2, hd3]
  rw [← hval]
  exact hF.congr_of_eventuallyEq hEq

end SharpLSI.FL.Prop82.HeatE
