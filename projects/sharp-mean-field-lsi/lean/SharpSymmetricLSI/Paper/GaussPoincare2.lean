import SharpSymmetricLSI.Paper.GaussPoincare1
import SharpSymmetricLSI.Paper.GaussForm19

/-!
# (8.10), Poincaré half (lane s42): bounded functions, and the transfer to `γ_∞`

* `poincare_bdd`: the Gaussian Poincaré inequality on `ℝⁿ` for smooth `F` with `F` and `∇F`
  bounded (cut-off `χ_R F`, `R → ∞`, as in Paper/GaussForm18 `gross_bdd`).
* `poincare_gamma_block`: for a centered Gaussian `γ` with covariance `C` and `G ∈ C_c^∞(ℝ^N)`,
  `Var_γ(G(z_0,…,z_{N-1})) ≤ ∫ ∑_{k,l<N} C_{kl} ∂_kG ∂_lG dγ` (via `z ↦ √S y`, `S` the `N×N` block
  of `C`, as in Paper/GaussForm19 `gross_gamma_block`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ContDiff MatrixOrder

namespace SharpLSI

theorem variance_eq_sub' {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    {F : α → ℝ} (hF : MemLp F 2 P) :
    variance F P = ∫ x, F x ^ 2 ∂P - (∫ x, F x ∂P) ^ 2 := by
  rw [variance_eq_sub hF]; rfl

/-- **Gaussian Poincaré on `ℝⁿ`** for smooth bounded functions with bounded gradient. -/
theorem poincare_bdd {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) {B : ℝ}
    (hFB : ∀ x, |F x| ≤ B) (hdB : ∀ x, ‖fderiv ℝ F x‖ ≤ B) :
    variance F (gpi n) ≤ ∫ x, ∑ k, fderiv ℝ F x (Pi.single k 1) ^ 2 ∂gpi n := by
  obtain ⟨M, hM0, hM⟩ := exists_fderiv_chiR_bound n
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hFB 0)
  set Fm : ℕ → (Fin n → ℝ) → ℝ := fun m y => chiR n ((m : ℝ) + 1) y * F y with hFm
  have hFmc : ∀ m, ContDiff ℝ ∞ (Fm m) := fun m => (contDiff_chiR n _).mul hF
  have hineq : ∀ m, variance (Fm m) (gpi n) ≤
      ∫ x, ∑ k, fderiv ℝ (Fm m) x (Pi.single k 1) ^ 2 ∂gpi n := fun m =>
    poincare_cc (hFmc m) ((hasCompactSupport_chiR (by positivity)).mul_right)
  have hev : ∀ x : Fin n → ℝ, ∀ᶠ m : ℕ in atTop, ‖x‖ < (m : ℝ) + 1 := fun x => by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with m hm
    have : (N : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hFmB : ∀ m x, |Fm m x| ≤ B := fun m x => by
    simp only [hFm, abs_mul]
    rw [abs_of_nonneg (chiR_nonneg _ _ _)]
    calc chiR n ((m : ℝ) + 1) x * |F x| ≤ 1 * B :=
          mul_le_mul (chiR_le_one _ _ _) (hFB x) (abs_nonneg _) zero_le_one
      _ = B := one_mul _
  have hpt : ∀ x, Tendsto (fun m => Fm m x) atTop (𝓝 (F x)) := fun x => by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev x] with m hm
    simp only [hFm, chiR_eq_one (by positivity : (0 : ℝ) < (m : ℝ) + 1) hm.le, one_mul]
  have hFmm : ∀ m, AEStronglyMeasurable (Fm m) (gpi n) := fun m =>
    (hFmc m).continuous.aestronglyMeasurable
  have hL2 : ∀ {f : (Fin n → ℝ) → ℝ}, Continuous f → (∀ x, |f x| ≤ B) → MemLp f 2 (gpi n) :=
    fun {f} hf hb => MemLp.of_bound hf.aestronglyMeasurable B
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
  -- left-hand side
  have hL : Tendsto (fun m => variance (Fm m) (gpi n)) atTop (𝓝 (variance F (gpi n))) := by
    have h1 := tendsto_integral_comp_of_bdd (P := gpi n) hFmm hFmB hpt (G := fun t => t ^ 2)
      (continuous_pow 2)
    have h2 := tendsto_integral_comp_of_bdd (P := gpi n) hFmm hFmB hpt (G := id) continuous_id
    simp only [id] at h2
    rw [variance_eq_sub' (hL2 hF.continuous hFB)]
    refine (h1.sub (h2.pow 2)).congr fun m => ?_
    rw [variance_eq_sub' (hL2 (hFmc m).continuous (hFmB m))]
  -- right-hand side
  set D := B + B * M
  have hpd : ∀ (m : ℕ) (x : Fin n → ℝ) (k : Fin n),
      |fderiv ℝ (Fm m) x (Pi.single k 1)| ≤ D := fun m x k => by
    rw [fderiv_chiR_mul hF]
    have hR : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have h1 : |fderiv ℝ F x (Pi.single k 1)| ≤ B := abs_fderiv_single_le hdB x k
    have h2 : |fderiv ℝ (chiR n ((m : ℝ) + 1)) x (Pi.single k 1)| ≤ M := by
      refine (abs_fderiv_single_le (B := M * ((m : ℝ) + 1)⁻¹) (hM _ hR) x k).trans ?_
      have : ((m : ℝ) + 1)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
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
  exact le_of_tendsto_of_tendsto' hL hR hineq

/-- **Gaussian Poincaré for `γ_∞` on cylinder functions.** -/
theorem poincare_gamma_block {γ : Measure (ℕ → ℝ)} {C : ℕ → ℕ → ℝ}
    (hγ : IsCenteredGaussianCov γ C) {N : ℕ}
    (hS : (blockMat C N).PosSemidef) {G : (Fin N → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) :
    variance (fun z => G (zBlock N z)) γ ≤
      ∫ z, ∑ k : Fin N, ∑ l : Fin N, C k l * fderiv ℝ G (zBlock N z) (Pi.single k 1) *
        fderiv ℝ G (zBlock N z) (Pi.single l 1) ∂γ := by
  have := hγ.1
  set A := CFC.sqrt (blockMat C N)
  set P := gpi N
  have hAm : Measurable fun y : Fin N → ℝ => A *ᵥ y := (matCLM A).continuous.measurable
  have hmap := map_block_eq hγ hS
  have htr : ∀ H : (Fin N → ℝ) → ℝ, Continuous H →
      ∫ z, H (zBlock N z) ∂γ = ∫ y, H (A *ᵥ y) ∂P := fun H hH => by
    rw [← integral_map (measurable_zBlock _).aemeasurable hH.aestronglyMeasurable, hmap,
      integral_map hAm.aemeasurable hH.aestronglyMeasurable]
  obtain ⟨B, hFB, hdB, -, -, hder⟩ := exists_bounds_comp hG hc (matCLM A)
  have hF : ContDiff ℝ ∞ (fun y => G (matCLM A y)) := hG.comp (matCLM A).contDiff
  have hpoin := poincare_bdd hF hFB hdB
  have hGc := hG.continuous
  obtain ⟨BG, hBG⟩ := hc.exists_bound_of_continuous hGc
  have hdc : ∀ k : Fin N, Continuous fun x => fderiv ℝ G x (Pi.single k 1) := fun k =>
    (hG.continuous_fderiv (by simp)).clm_apply continuous_const
  have hvar : variance (fun z => G (zBlock N z)) γ = variance (fun y => G (matCLM A y)) P := by
    have hL2γ : MemLp (fun z => G (zBlock N z)) 2 γ :=
      MemLp.of_bound (hGc.comp (continuous_pi fun i => continuous_apply _)).aestronglyMeasurable
        BG (Eventually.of_forall fun z => hBG _)
    have hL2P : MemLp (fun y => G (matCLM A y)) 2 P :=
      MemLp.of_bound hF.continuous.aestronglyMeasurable B
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hFB y)
    rw [variance_eq_sub' hL2γ, variance_eq_sub' hL2P, htr (fun x => G x ^ 2) (hGc.pow 2),
      htr G hGc]
    rfl
  have hgrad : ∀ y, ∑ k, fderiv ℝ (fun y => G (matCLM A y)) y (Pi.single k 1) ^ 2 =
      ∑ k : Fin N, ∑ l : Fin N, C k l * fderiv ℝ G (A *ᵥ y) (Pi.single k 1) *
        fderiv ℝ G (A *ᵥ y) (Pi.single l 1) := fun y => by
    have e1 : ∀ k, fderiv ℝ (fun y => G (matCLM A y)) y (Pi.single k 1) =
        ∑ l, A l k * fderiv ℝ G (A *ᵥ y) (Pi.single l 1) := fun k => by
      rw [hder, ContinuousLinearMap.comp_apply, matCLM_single, fderiv_apply_sum]
      rfl
    simp_rw [e1]
    rw [sum_sq_mulVec_transpose, sqrt_mul_transpose hS]
    rfl
  rw [hvar]
  refine hpoin.trans (le_of_eq ?_)
  simp_rw [hgrad]
  exact (htr _ (continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
    (continuous_const.mul (hdc k)).mul (hdc l))).symm

end SharpLSI
