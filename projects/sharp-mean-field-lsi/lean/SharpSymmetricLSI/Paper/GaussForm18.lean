import SharpSymmetricLSI.Paper.GaussForm17
import SharpSymmetricLSI.Paper.GaussForm10

/-!
# R32 (E3): Gross' inequality on `ℝⁿ` without positivity, and for bounded smooth functions

* `gross_cc`: `Ent_{γ_n}(F²) ≤ 2 ∫ |∇F|² dγ_n` for `F ∈ C^∞_c`: apply `grossProp_all` to
  `√(F²+ε) = √ε + (√(F²+ε) - √ε)` (`|∇√(F²+ε)| ≤ |∇F|`) and let `ε → 0`.
* `gross_bdd`: the same for `F ∈ C^∞` with `F` and `DF` bounded, through the cutoffs
  `χ_{m+1} F` (`Paper/GaussForm10.lean`) and dominated convergence.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ContDiff

namespace SharpLSI

/-- `|∂_v √(F²+ε)| ≤ |∂_v F|`. -/
theorem sq_fderiv_sqrt_le {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : Differentiable ℝ F) {ε : ℝ}
    (hε : 0 < ε) (x v : Fin n → ℝ) :
    fderiv ℝ (fun y => √(F y ^ 2 + ε) - √ε) x v ^ 2 ≤ fderiv ℝ F x v ^ 2 := by
  have hs : 0 < F x ^ 2 + ε := by positivity
  have h1 : HasFDerivAt (fun y => F y * F y + ε) (F x • fderiv ℝ F x + F x • fderiv ℝ F x) x :=
    ((hF x).hasFDerivAt.mul (hF x).hasFDerivAt).add_const ε
  have h2 := (h1.sqrt (by rw [← sq]; exact hs.ne')).sub_const √ε
  have e : (fun y => √(F y * F y + ε) - √ε) = fun y => √(F y ^ 2 + ε) - √ε := by
    funext y; rw [sq]
  rw [e] at h2
  rw [h2.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul, ← sq]
  have hq : 0 < √(F x ^ 2 + ε) := Real.sqrt_pos.2 hs
  have hsq : √(F x ^ 2 + ε) ^ 2 = F x ^ 2 + ε := Real.sq_sqrt hs.le
  have : (1 / (2 * √(F x ^ 2 + ε)) * (F x * fderiv ℝ F x v + F x * fderiv ℝ F x v)) ^ 2 =
      F x ^ 2 / (F x ^ 2 + ε) * fderiv ℝ F x v ^ 2 := by
    field_simp
    rw [hsq]; ring
  rw [this]
  have hle : F x ^ 2 / (F x ^ 2 + ε) ≤ 1 := by
    rw [div_le_one hs]; linarith
  calc F x ^ 2 / (F x ^ 2 + ε) * fderiv ℝ F x v ^ 2 ≤ 1 * fderiv ℝ F x v ^ 2 :=
        mul_le_mul_of_nonneg_right hle (sq_nonneg _)
    _ = _ := one_mul _

/-- **Gross' inequality on `ℝⁿ`** for `F ∈ C^∞_c`. -/
theorem gross_cc {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    entR (gpi n) (fun x => F x ^ 2) ≤
      2 * ∫ x, ∑ k, fderiv ℝ F x (Pi.single k 1) ^ 2 ∂gpi n := by
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  obtain ⟨B, hFB, hBd, hcd, -⟩ := exists_bounds_of_cc hF hc
  have hRint : Integrable (fun x => ∑ k, fderiv ℝ F x (Pi.single k 1) ^ 2) (gpi n) := by
    refine integrable_finsetSum _ fun k _ => Integrable.of_bound
      ((hcd.clm_apply continuous_const).pow 2).aestronglyMeasurable (B ^ 2)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := pow_le_pow_left₀ (abs_nonneg _) (abs_fderiv_single_le hBd x k) 2
    rwa [sq_abs] at h
  have hstep : ∀ ε : ℝ, 0 < ε → entR (gpi n) (fun x => F x ^ 2 + ε) ≤
      2 * ∫ x, ∑ k, fderiv ℝ F x (Pi.single k 1) ^ 2 ∂gpi n := by
    intro ε hε
    set ψ : (Fin n → ℝ) → ℝ := fun y => √(F y ^ 2 + ε) - √ε with hψdef
    have hψ : ContDiff ℝ ∞ ψ :=
      (((hF.pow 2).add contDiff_const).sqrt fun y => by positivity).sub contDiff_const
    have hψc : HasCompactSupport ψ := by
      refine hc.mono fun y hy => ?_
      simp only [Function.mem_support] at hy ⊢
      intro h0; apply hy; simp [hψdef, h0]
    have hpos : ∀ y, 0 < √ε + ψ y := fun y => by
      simp only [hψdef, add_sub_cancel]; exact Real.sqrt_pos.2 (by positivity)
    have h := grossProp_all n (√ε) ψ hψ hψc hpos
    have e : (fun x => (√ε + ψ x) ^ 2) = fun x => F x ^ 2 + ε := by
      funext x; simp only [hψdef, add_sub_cancel]; exact Real.sq_sqrt (by positivity)
    rw [e] at h
    refine h.trans (mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
      (Eventually.of_forall fun x => Finset.sum_nonneg fun k _ => sq_nonneg _) hRint
      (Eventually.of_forall fun x => Finset.sum_le_sum fun k _ =>
        sq_fderiv_sqrt_le hFd hε x _)) (by norm_num))
  have hlim : Tendsto (fun m : ℕ => entR (gpi n) (fun x => F x ^ 2 + 1 / ((m : ℝ) + 1))) atTop
      (𝓝 (entR (gpi n) (fun x => F x ^ 2))) := by
    refine tendsto_entR_of_bdd (B := B ^ 2 + 1) (fun m => ((hF.continuous.pow 2).add
      continuous_const).aestronglyMeasurable) (fun m x => ?_) (fun x => ?_)
    · have h1 : 1 / ((m : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
      have h2 : F x ^ 2 ≤ B ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg _) (hFB x) 2; rwa [sq_abs] at this
      rw [abs_of_nonneg (by positivity)]; linarith
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (F x ^ 2)
  exact le_of_tendsto' hlim fun m => hstep _ (by positivity)

/-- **Gross' inequality on `ℝⁿ`** for `F ∈ C^∞` with `F`, `DF` bounded. -/
theorem gross_bdd {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) {B : ℝ}
    (hFB : ∀ x, |F x| ≤ B) (hdB : ∀ x, ‖fderiv ℝ F x‖ ≤ B) :
    entR (gpi n) (fun x => F x ^ 2) ≤
      2 * ∫ x, ∑ k, fderiv ℝ F x (Pi.single k 1) ^ 2 ∂gpi n := by
  obtain ⟨M, hM0, hM⟩ := exists_fderiv_chiR_bound n
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hFB 0)
  set Fm : ℕ → (Fin n → ℝ) → ℝ := fun m y => chiR n ((m : ℝ) + 1) y * F y with hFm
  have hFmc : ∀ m, ContDiff ℝ ∞ (Fm m) := fun m => (contDiff_chiR n _).mul hF
  have hcd : Continuous fun x => fderiv ℝ F x := hF.continuous_fderiv (by simp)
  have hineq : ∀ m, entR (gpi n) (fun x => Fm m x ^ 2) ≤
      2 * ∫ x, ∑ k, fderiv ℝ (Fm m) x (Pi.single k 1) ^ 2 ∂gpi n := fun m =>
    gross_cc (hFmc m) ((hasCompactSupport_chiR (by positivity)).mul_right)
  have hev : ∀ x : Fin n → ℝ, ∀ᶠ m : ℕ in atTop, ‖x‖ < (m : ℝ) + 1 := fun x => by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with m hm
    have : (N : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  -- left-hand side
  have hL : Tendsto (fun m => entR (gpi n) (fun x => Fm m x ^ 2)) atTop
      (𝓝 (entR (gpi n) (fun x => F x ^ 2))) := by
    refine tendsto_entR_of_bdd (B := B ^ 2)
      (fun m => ((hFmc m).continuous.pow 2).aestronglyMeasurable) (fun m x => ?_) (fun x => ?_)
    · rw [abs_of_nonneg (sq_nonneg _)]
      have h1 : |Fm m x| ≤ B := by
        simp only [hFm, abs_mul]
        rw [abs_of_nonneg (chiR_nonneg _ _ _)]
        calc chiR n ((m : ℝ) + 1) x * |F x| ≤ 1 * B :=
              mul_le_mul (chiR_le_one _ _ _) (hFB x) (abs_nonneg _) zero_le_one
          _ = B := one_mul _
      have := pow_le_pow_left₀ (abs_nonneg _) h1 2; rwa [sq_abs] at this
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with m hm
      simp only [hFm, chiR_eq_one (by positivity : (0 : ℝ) < (m : ℝ) + 1) hm.le, one_mul]
  -- right-hand side
  set D := B + B * M
  have hpd : ∀ (m : ℕ) (x : Fin n → ℝ) (k : Fin n),
      |fderiv ℝ (Fm m) x (Pi.single k 1)| ≤ D := fun m x k => by
    rw [fderiv_chiR_mul hF]
    have hR : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have h1 : |fderiv ℝ F x (Pi.single k 1)| ≤ B := abs_fderiv_single_le hdB x k
    have h2 : |fderiv ℝ (chiR n ((m : ℝ) + 1)) x (Pi.single k 1)| ≤ M := by
      refine (abs_fderiv_single_le (B := M * ((m : ℝ) + 1)⁻¹) (hM _ hR) x k).trans ?_
      have : ((m : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
      nlinarith
    calc _ ≤ |chiR n ((m : ℝ) + 1) x * fderiv ℝ F x (Pi.single k 1)| +
          |F x * fderiv ℝ (chiR n ((m : ℝ) + 1)) x (Pi.single k 1)| := abs_add_le _ _
      _ ≤ 1 * B + B * M := by
        rw [abs_mul, abs_mul, abs_of_nonneg (chiR_nonneg _ _ _)]
        exact add_le_add (mul_le_mul (chiR_le_one _ _ _) h1 (abs_nonneg _) zero_le_one)
          (mul_le_mul (hFB x) h2 (abs_nonneg _) hB0)
      _ = D := by ring
  have hR : Tendsto (fun m => ∫ x, ∑ k, fderiv ℝ (Fm m) x (Pi.single k 1) ^ 2 ∂gpi n) atTop
      (𝓝 (∫ x, ∑ k, fderiv ℝ F x (Pi.single k 1) ^ 2 ∂gpi n)) := by
    refine tendsto_integral_comp_of_bdd (G := id) (B := n * D ^ 2) (fun m => ?_) (fun m x => ?_)
      (fun x => ?_) continuous_id
    · have hc' : Continuous fun x => fderiv ℝ (Fm m) x := (hFmc m).continuous_fderiv (by simp)
      exact (continuous_finsetSum _ fun k _ =>
        (hc'.clm_apply continuous_const).pow 2).aestronglyMeasurable
    · rw [abs_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)]
      calc _ ≤ ∑ _k : Fin n, D ^ 2 := Finset.sum_le_sum fun k _ => by
            have := pow_le_pow_left₀ (abs_nonneg _) (hpd m x k) 2; rwa [sq_abs] at this
        _ = n * D ^ 2 := by simp
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with m hm
      have hR' : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [fderiv_chiR_mul hF, chiR_eq_one hR' hm.le, fderiv_chiR_eq_zero hR' hm]
      simp
  exact le_of_tendsto_of_tendsto' hL (hR.const_mul 2) hineq

end SharpLSI
