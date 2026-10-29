import DGPS.Analysis.ForceMultiplier

/-!
# Smooth force multiplier bound (H1024)

For smooth real `Q`, `ψ` and every `N ≥ 1`, with `B_i = N⁻¹ ∑_{j≠i} Q'(x_i - x_j)`, `b = ‖ψ B‖₂`,
`L = ‖Q‖_∞`, `β = ‖Q'‖₂`, `u = ‖ψ‖₂`, `v = ‖∇ψ‖₂`:
`b ≤ 2 L v + β √(u² + 2 u v/√N) ≤ (2L + β) v + β u`.

H1022 is stated with the chosen weak gradient of `Q`, H1023 with the classical derivative
`coordPartial 0 Q`; the bridge (`weakGradient Q = smoothGrad Q` a.e. for smooth `Q`, and the
Haar-preservation of the pair map `x ↦ x_i - x_j`) is proved here.
-/

open MeasureTheory

namespace DGPS.Analysis.ForceMultiplier

section smooth

variable {N : ℕ}

/-- The pair-difference map `x ↦ x_i - x_j` as an additive homomorphism `𝕋^N → 𝕋¹`. -/
noncomputable def pairDiffHom (i j : Fin N) : Torus N →+ Torus 1 where
  toFun x := fun _ => x i - x j
  map_zero' := by funext; simp
  map_add' x y := by funext; simp [sub_add_sub_comm]

/-- For `i ≠ j`, the pair map `x ↦ x_i - x_j` is Haar preserving `𝕋^N → 𝕋¹`. -/
theorem measurePreserving_pairDiff {i j : Fin N} (hij : i ≠ j) :
    MeasurePreserving (fun x : Torus N => (fun _ : Fin 1 => x i - x j : Torus 1))
      (haar N) (haar 1) := by
  have hc : Continuous (pairDiffHom i j) := by
    refine continuous_pi fun _ => ?_
    exact ((continuous_apply i).sub (continuous_apply j))
  have hs : Function.Surjective (pairDiffHom i j) := by
    intro t
    refine ⟨Pi.single i (t 0), ?_⟩
    funext k
    simp [pairDiffHom, hij.symm, Subsingleton.elim k 0]
  have : (haar N).IsAddHaarMeasure := by
    rw [DGPS.haar_eq_pi_haarAddCircle]; infer_instance
  have : (haar 1).IsAddHaarMeasure := by
    rw [DGPS.haar_eq_pi_haarAddCircle]; infer_instance
  have hmeas : Measurable (pairDiffHom i j) := hc.measurable
  have : ((haar N).map (pairDiffHom i j)).IsAddHaarMeasure :=
    MeasureTheory.Measure.isAddHaarMeasure_map (haar N) (pairDiffHom i j) hc hs (by
      rw [Filter.cocompact_eq_bot, Filter.cocompact_eq_bot]; exact Filter.tendsto_bot)
  have : IsProbabilityMeasure ((haar N).map (pairDiffHom i j)) :=
    ⟨by rw [Measure.map_apply hmeas MeasurableSet.univ]; simp⟩
  refine ⟨hmeas, ?_⟩
  exact (MeasureTheory.Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure
    (μ' := (haar N).map (pairDiffHom i j)) (μ := haar 1))

/-- For smooth `Q`, the chosen weak gradient is the classical gradient a.e. on `𝕋¹`. -/
theorem weakGradient_ae_eq_smoothGrad {Q : Torus 1 → ℝ} (hQ : IsSmoothPeriodic Q)
    (hQ' : MemH1 Q) : weakGradient Q hQ' =ᵐ[haar 1] smoothGrad Q :=
  weakGradient_ae_eq hQ.isWeakGradient

theorem norm_smoothGrad_sq_one (Q : Torus 1 → ℝ) (t : Torus 1) :
    ‖smoothGrad Q t‖ ^ 2 = coordPartial 0 Q t ^ 2 := by
  rw [tangent_norm_sq]; simp

/-- Bridge for `β`: `‖Q'‖₂` via the weak gradient equals via `coordPartial 0 Q`. -/
theorem integral_weakGradient_sq_eq {Q : Torus 1 → ℝ} (hQ : IsSmoothPeriodic Q)
    (hQ' : MemH1 Q) :
    ∫ t, ‖weakGradient Q hQ' t‖ ^ 2 ∂haar 1 = ∫ t, coordPartial 0 Q t ^ 2 ∂haar 1 := by
  refine integral_congr_ae ?_
  filter_upwards [weakGradient_ae_eq_smoothGrad hQ hQ'] with t ht
  rw [ht, norm_smoothGrad_sq_one]

/-- Bridge for the pair terms: for `i ≠ j`, the weak-gradient pullback agrees a.e. with the
classical one on `𝕋^N`. -/
theorem integral_pair_weakGradient_eq {Q : Torus 1 → ℝ} (hQ : IsSmoothPeriodic Q)
    (hQ' : MemH1 Q) {i j : Fin N} (hij : i ≠ j) (ψ : Torus N → ℝ) :
    ∫ x, ‖weakGradient Q hQ' (fun _ => x i - x j)‖ ^ 2 * ψ x ^ 2 ∂haar N =
      ∫ x, pairFun (coordPartial 0 Q) i j x ^ 2 * ψ x ^ 2 ∂haar N := by
  have h := (measurePreserving_pairDiff hij).quasiMeasurePreserving.ae_eq_comp
    (weakGradient_ae_eq_smoothGrad hQ hQ')
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  have hx' : weakGradient Q hQ' (fun _ => x i - x j) = smoothGrad Q (fun _ => x i - x j) := hx
  rw [hx', norm_smoothGrad_sq_one]
  rfl

/-- **H1024.** Smooth force multiplier bound: for smooth real `Q`, `ψ` and every `N ≥ 1`,
`‖ψ B‖₂ ≤ 2 L v + β √(u² + 2 u v/√N) ≤ (2L + β) v + β u`, where `B_i` omits `j = i`. -/
theorem smooth_force_multiplier_bound (hN : 1 ≤ N) {Q : Torus 1 → ℝ} (hQ : IsSmoothPeriodic Q)
    {ψ : Torus N → ℝ} (hψ : IsSmoothPeriodic ψ) {b β u v L : ℝ}
    (hb : b = Real.sqrt (∫ x, ∑ i, (ψ x * ((N : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i,
          pairFun (coordPartial 0 Q) i j x)) ^ 2 ∂haar N))
    (hβ : β = Real.sqrt (∫ t, coordPartial 0 Q t ^ 2 ∂haar 1))
    (hu : u = Real.sqrt (∫ x, ψ x ^ 2 ∂haar N))
    (hv : v = Real.sqrt (∫ x, ‖smoothGrad ψ x‖ ^ 2 ∂haar N))
    (hL : L = ⨆ t, |Q t|) :
    b ≤ 2 * L * v + β * Real.sqrt (u ^ 2 + 2 * (u * v) / Real.sqrt N) ∧
      2 * L * v + β * Real.sqrt (u ^ 2 + 2 * (u * v) / Real.sqrt N) ≤ (2 * L + β) * v + β * u := by
  have hL0 : 0 ≤ L := hL ▸ Real.iSup_nonneg fun t => abs_nonneg _
  have hv0 : 0 ≤ v := hv ▸ Real.sqrt_nonneg _
  have hu0 : 0 ≤ u := hu ▸ Real.sqrt_nonneg _
  have hβ0 : 0 ≤ β := hβ ▸ Real.sqrt_nonneg _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hs1 : 1 ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  have hsN : 0 < Real.sqrt N := lt_of_lt_of_le one_pos hs1
  have hq : 2 * (u * v) / Real.sqrt N ≤ 2 * (u * v) := by
    rw [div_le_iff₀ hsN]; nlinarith [mul_nonneg hu0 hv0]
  have hq0 : 0 ≤ 2 * (u * v) / Real.sqrt N := by positivity
  have hroot : Real.sqrt (u ^ 2 + 2 * (u * v) / Real.sqrt N) ≤ u + v := by
    apply Real.sqrt_le_iff.2
    exact ⟨by positivity, by nlinarith [sq_nonneg v]⟩
  refine ⟨?_, ?_⟩
  swap
  · nlinarith [mul_le_mul_of_nonneg_left hroot hβ0]
  rcases Nat.lt_or_ge N 2 with hN2 | hN2
  · -- N = 1: B vanishes
    have hN1 : N = 1 := by omega
    subst hN1
    have hb0 : b = 0 := by
      rw [hb]
      simp
    rw [hb0]
    have := Real.sqrt_nonneg (u ^ 2 + 2 * (u * v) / Real.sqrt (1 : ℕ))
    positivity
  -- N ≥ 2
  have hQ' : MemH1 Q := ⟨_, hQ.isWeakGradient⟩
  set D : ℝ := ((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j ∈ Finset.univ.erase i,
          ∫ x, pairFun (coordPartial 0 Q) i j x ^ 2 * ψ x ^ 2 ∂haar N with hD
  have hD22 : D ≤ β ^ 2 * (u ^ 2 + 2 * (u * v) / Real.sqrt N) := by
    have h := repeated_label_force_estimate N hN2 Q hQ' ψ hψ
    have e : ∀ i, ∑ j ∈ Finset.univ.erase i,
        ∫ x, ‖weakGradient Q hQ' (fun _ => x i - x j)‖ ^ 2 * ψ x ^ 2 ∂haar N =
        ∑ j ∈ Finset.univ.erase i, ∫ x, pairFun (coordPartial 0 Q) i j x ^ 2 * ψ x ^ 2 ∂haar N :=
      fun i => Finset.sum_congr rfl fun j hj =>
        integral_pair_weakGradient_eq hQ hQ' (Finset.ne_of_mem_erase hj).symm ψ
    simp_rw [e] at h
    rw [hβ, hu, hv, hD]
    rwa [integral_weakGradient_sq_eq hQ hQ'] at h
  have hD0 : 0 ≤ D := by
    rw [hD]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      integral_nonneg fun x => by positivity)
  obtain ⟨hid, h1, h2⟩ := distinct_label_integration_by_parts_identity hQ hψ hb hD hv hL
  have hb0 : 0 ≤ b := hb ▸ Real.sqrt_nonneg _
  have hsD : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
  have hdiv : 2 * L * Real.sqrt D * v / Real.sqrt N ≤ 2 * L * Real.sqrt D * v := by
    rw [div_le_iff₀ hsN]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hL0) hsD) hv0]
  have hbsq : b ^ 2 ≤ D + 2 * L * b * v + 2 * L * Real.sqrt D * v := by
    have := le_abs_self (b ^ 2 - D)
    set A := (2 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
          ∫ x, pairFun Q i j x * ((N : ℝ)⁻¹ * ∑ k ∈ Finset.univ.erase i,
            pairFun (coordPartial 0 Q) i k x) * ψ x * coordPartial j ψ x ∂haar N
    set C := (2 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
          ∫ x, pairFun Q i j x * pairFun (coordPartial 0 Q) i j x * ψ x * coordPartial j ψ x
            ∂haar N
    have hA := le_abs_self A
    have hC := neg_abs_le C
    linarith
  have hsq : (b - L * v) ^ 2 ≤ (Real.sqrt D + L * v) ^ 2 := by
    have := Real.sq_sqrt hD0
    nlinarith
  have hle := abs_le_of_sq_le_sq' hsq (by positivity)
  have hbD : b ≤ Real.sqrt D + 2 * L * v := by linarith [hle.2]
  have hsD2 : Real.sqrt D ≤ β * Real.sqrt (u ^ 2 + 2 * (u * v) / Real.sqrt N) := by
    rw [show β * Real.sqrt (u ^ 2 + 2 * (u * v) / Real.sqrt N)
      = Real.sqrt (β ^ 2 * (u ^ 2 + 2 * (u * v) / Real.sqrt N)) by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hβ0]]
    exact Real.sqrt_le_sqrt hD22
  linarith

end smooth

end DGPS.Analysis.ForceMultiplier
