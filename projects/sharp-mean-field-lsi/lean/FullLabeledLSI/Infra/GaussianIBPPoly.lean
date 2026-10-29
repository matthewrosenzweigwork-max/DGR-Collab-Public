import SharpSymmetricLSI.Paper.GaussForm1
import SharpSymmetricLSI.Paper.GaussForm10
import SharpSymmetricLSI.Paper.GaussForm17
import FullLabeledLSI.Infra.GaussianTiltA

/-!
# Gaussian integration by parts for functions of polynomial growth (plan, section 10)

* `PolyGrowth G`: `|G y| ≤ C (1 + ‖y‖)^m`.
* `integrable_W`, `PolyGrowth.integrable`: polynomial growth functions are `γ_n`-integrable.
* `gauss_ibp_poly`: `∫ y_k F dγ_n = ∫ ∂_k F dγ_n` for `C¹` `F` with `F`, `∂_k F` of polynomial growth
  (cut-off `χ_R F`, SYM's bounded `stein_pi`, dominated convergence).
* `gauss_ibp_poly_one`: the one-variable form on `gaussianReal 0 1`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal ContDiff NNReal

namespace SharpLSI.FL

open SharpLSI

/-- Polynomial growth: `|G y| ≤ C (1 + ‖y‖)^m`. -/
def PolyGrowth {n : ℕ} (G : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ, ∀ y, |G y| ≤ C * (1 + ‖y‖) ^ m

theorem memLp_coord (n m : ℕ) (i : Fin n) : MemLp (fun y : Fin n → ℝ => y i) m (gpi n) := by
  have hmp := measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i
  have h1 : MemLp id (m : ℝ≥0∞) (gaussianReal 0 1) := by
    have := memLp_id_gaussianReal (μ := 0) (v := 1) (m : ℝ≥0)
    simpa using this
  rw [← hmp.map_eq] at h1
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (measurable_pi_apply i).aemeasurable).1 h1

theorem integrable_W (n m : ℕ) : Integrable (fun y : Fin n → ℝ => (1 + ‖y‖) ^ m) (gpi n) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  set s : (Fin n → ℝ) → ℝ := fun y => 1 + ∑ i, |y i| with hs
  have hsL : MemLp s m (gpi n) := by
    refine (memLp_const (1 : ℝ)).add (memLp_finset_sum _ fun i _ => ?_)
    simpa using (memLp_coord n m i).norm
  have hs0 : ∀ y, 0 ≤ s y := fun y => by
    simp only [hs]; exact add_nonneg zero_le_one (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have hsi : Integrable (fun y => s y ^ m) (gpi n) := by
    have := hsL.integrable_norm_pow hm.ne'
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [Real.norm_eq_abs, abs_of_nonneg (hs0 y)]
  refine hsi.mono' ((continuous_const.add continuous_norm).pow m).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have hn : ‖y‖ ≤ ∑ i, |y i| := by
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun i => |y i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by positivity) _)]
  exact pow_le_pow_left₀ (by positivity) (by simp only [hs]; linarith) m

theorem PolyGrowth.integrable {n : ℕ} {G : (Fin n → ℝ) → ℝ} (hG : PolyGrowth G)
    (hm : AEStronglyMeasurable G (gpi n)) : Integrable G (gpi n) := by
  obtain ⟨C, hC, m, h⟩ := hG
  refine ((integrable_W n m).const_mul C).mono' hm (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]; exact h y

theorem fderiv_chiR_mul' {N : ℕ} {G : (Fin N → ℝ) → ℝ} (hG : Differentiable ℝ G) (R : ℝ)
    (x v : Fin N → ℝ) :
    fderiv ℝ (fun y => chiR N R y * G y) x v =
      chiR N R x * fderiv ℝ G x v + G x * fderiv ℝ (chiR N R) x v := by
  rw [fderiv_fun_mul ((contDiff_chiR N R).differentiable (by simp) x) (hG x)]
  simp [smul_eq_mul]

/-- **Gaussian integration by parts for polynomial growth**, `γ_{n+1}`. -/
theorem gauss_ibp_poly_succ {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ} (hF : Differentiable ℝ F)
    (hFc : Continuous fun y => fderiv ℝ F y) (hP : PolyGrowth F) (k : Fin (n + 1))
    (hP' : PolyGrowth fun y => fderiv ℝ F y (Pi.single k 1)) :
    ∫ y, y k * F y ∂gpi (n + 1) = ∫ y, fderiv ℝ F y (Pi.single k 1) ∂gpi (n + 1) := by
  obtain ⟨C1, hC1, m1, h1⟩ := hP
  obtain ⟨C2, hC2, m2, h2⟩ := hP'
  obtain ⟨M, hM0, hM⟩ := exists_fderiv_chiR_bound (n + 1)
  set Fm : ℕ → (Fin (n + 1) → ℝ) → ℝ := fun m y => chiR (n + 1) ((m : ℝ) + 1) y * F y with hFm
  have hpos : ∀ m : ℕ, (0 : ℝ) < (m : ℝ) + 1 := fun m => by positivity
  have hev : ∀ x : Fin (n + 1) → ℝ, ∀ᶠ m : ℕ in atTop, ‖x‖ < (m : ℝ) + 1 := fun x => by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with m hm
    have : (N : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hFmd : ∀ m, Differentiable ℝ (Fm m) := fun m =>
    ((contDiff_chiR _ _).differentiable (by simp)).mul hF
  have hFm_fd : ∀ m, (fun y => fderiv ℝ (Fm m) y) = fun y =>
      chiR (n + 1) ((m : ℝ) + 1) y • fderiv ℝ F y + F y • fderiv ℝ (chiR (n + 1) ((m : ℝ) + 1)) y :=
    fun m => funext fun y => by
      simp only [hFm]
      rw [fderiv_fun_mul ((contDiff_chiR _ _).differentiable (by simp) y) (hF y)]
  have hchic : ∀ m, Continuous fun y => fderiv ℝ (chiR (n + 1) ((m : ℝ) + 1)) y := fun m =>
    (contDiff_chiR _ _).continuous_fderiv (by simp)
  have hFmc : ∀ m, Continuous fun y => fderiv ℝ (Fm m) y := fun m => by
    rw [hFm_fd m]
    exact ((contDiff_chiR _ _).continuous.smul hFc).add (hF.continuous.smul (hchic m))
  have hcs : ∀ m, HasCompactSupport (Fm m) := fun m =>
    (hasCompactSupport_chiR (hpos m)).mul_right
  have hstein : ∀ m, ∫ y, y k * Fm m y ∂gpi (n + 1) =
      ∫ y, fderiv ℝ (Fm m) y (Pi.single k 1) ∂gpi (n + 1) := fun m => by
    obtain ⟨B1, hB1⟩ := (hcs m).exists_bound_of_continuous
      (hFmd m).continuous
    obtain ⟨B2, hB2⟩ := ((hcs m).fderiv (𝕜 := ℝ)).exists_bound_of_continuous (hFmc m)
    exact stein_pi (hFmd m) (hFmc m) (B := max B1 B2)
      (fun y => by simpa using (hB1 y).trans (le_max_left _ _))
      (fun y => (hB2 y).trans (le_max_right _ _)) k
  have hW : ∀ m, Continuous fun y : Fin (n + 1) → ℝ => (1 + ‖y‖) ^ m := fun m =>
    (continuous_const.add continuous_norm).pow m
  have hcoord : ∀ y : Fin (n + 1) → ℝ, |y k| ≤ ‖y‖ := fun y => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm y k
  -- left-hand side
  have hL : Tendsto (fun m => ∫ y, y k * Fm m y ∂gpi (n + 1)) atTop
      (𝓝 (∫ y, y k * F y ∂gpi (n + 1))) := by
    refine tendsto_integral_of_dominated_convergence (fun y => C1 * (1 + ‖y‖) ^ (m1 + 1))
      (fun m => (((continuous_apply k).mul ((contDiff_chiR _ _).continuous.mul
        hF.continuous))).aestronglyMeasurable) ((integrable_W (n + 1) (m1 + 1)).const_mul C1)
      (fun m => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
    · rw [Real.norm_eq_abs, abs_mul, hFm]
      simp only [abs_mul, abs_of_nonneg (chiR_nonneg _ _ _)]
      have hc1 := chiR_le_one (n + 1) ((m : ℝ) + 1) y
      have hc0 := chiR_nonneg (n + 1) ((m : ℝ) + 1) y
      have e1 : |y k| * (chiR (n + 1) ((m : ℝ) + 1) y * |F y|) ≤ ‖y‖ * (C1 * (1 + ‖y‖) ^ m1) := by
        refine mul_le_mul (hcoord y) ?_ (by positivity) (norm_nonneg _)
        calc chiR (n + 1) ((m : ℝ) + 1) y * |F y| ≤ 1 * |F y| :=
              mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
          _ ≤ _ := by rw [one_mul]; exact h1 y
      calc _ ≤ ‖y‖ * (C1 * (1 + ‖y‖) ^ m1) := e1
        _ ≤ (1 + ‖y‖) * (C1 * (1 + ‖y‖) ^ m1) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = C1 * (1 + ‖y‖) ^ (m1 + 1) := by ring
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev y] with m hm
      simp only [hFm, chiR_eq_one (hpos m) hm.le, one_mul]
  -- right-hand side
  have hR : Tendsto (fun m => ∫ y, fderiv ℝ (Fm m) y (Pi.single k 1) ∂gpi (n + 1)) atTop
      (𝓝 (∫ y, fderiv ℝ F y (Pi.single k 1) ∂gpi (n + 1))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => C2 * (1 + ‖y‖) ^ m2 + M * (C1 * (1 + ‖y‖) ^ m1))
      (fun m => ((hFmc m).clm_apply continuous_const).aestronglyMeasurable)
      (((integrable_W (n + 1) m2).const_mul C2).add
        (((integrable_W (n + 1) m1).const_mul C1).const_mul M))
      (fun m => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
    · have e := congrFun (hFm_fd m) y
      rw [Real.norm_eq_abs, e]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have hc1 := chiR_le_one (n + 1) ((m : ℝ) + 1) y
      have hc0 := chiR_nonneg (n + 1) ((m : ℝ) + 1) y
      have h3 : |fderiv ℝ (chiR (n + 1) ((m : ℝ) + 1)) y (Pi.single k 1)| ≤ M := by
        refine (abs_fderiv_single_le (B := M * ((m : ℝ) + 1)⁻¹) (hM _ (hpos m)) y k).trans ?_
        have : ((m : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
        nlinarith
      calc _ ≤ |chiR (n + 1) ((m : ℝ) + 1) y * fderiv ℝ F y (Pi.single k 1)| +
            |F y * fderiv ℝ (chiR (n + 1) ((m : ℝ) + 1)) y (Pi.single k 1)| := abs_add_le _ _
        _ ≤ C2 * (1 + ‖y‖) ^ m2 + M * (C1 * (1 + ‖y‖) ^ m1) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hc0]
          refine add_le_add ?_ ?_
          · calc _ ≤ 1 * |fderiv ℝ F y (Pi.single k 1)| :=
                  mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
              _ ≤ _ := by rw [one_mul]; exact h2 y
          · calc |F y| * |fderiv ℝ (chiR (n + 1) ((m : ℝ) + 1)) y (Pi.single k 1)|
                ≤ (C1 * (1 + ‖y‖) ^ m1) * M :=
                  mul_le_mul (h1 y) h3 (abs_nonneg _) (by positivity)
              _ = _ := by ring
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev y] with m hm
      have e := congrFun (hFm_fd m) y
      rw [e]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [chiR_eq_one (hpos m) hm.le, fderiv_chiR_eq_zero (hpos m) hm]
      simp
  exact tendsto_nhds_unique (hL.congr fun m => hstein m) hR

/-- **Gaussian integration by parts for polynomial growth**, `γ_n`. -/
theorem gauss_ibp_poly {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : Differentiable ℝ F)
    (hFc : Continuous fun y => fderiv ℝ F y) (hP : PolyGrowth F) (k : Fin n)
    (hP' : PolyGrowth fun y => fderiv ℝ F y (Pi.single k 1)) :
    ∫ y, y k * F y ∂gpi n = ∫ y, fderiv ℝ F y (Pi.single k 1) ∂gpi n := by
  cases n with
  | zero => exact k.elim0
  | succ n => exact gauss_ibp_poly_succ hF hFc hP k hP'

/-- **One-variable form**: `∫ x φ(x) dN(0,1) = ∫ φ'(x) dN(0,1)` for `C¹` `φ` with `φ`, `φ'` of
polynomial growth. -/
theorem gauss_ibp_poly_one {φ φ' : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ'c : Continuous φ') {C1 C2 : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) {m1 m2 : ℕ}
    (h1 : ∀ x, |φ x| ≤ C1 * (1 + |x|) ^ m1) (h2 : ∀ x, |φ' x| ≤ C2 * (1 + |x|) ^ m2) :
    ∫ x, x * φ x ∂gaussianReal 0 1 = ∫ x, φ' x ∂gaussianReal 0 1 := by
  set F : (Fin 1 → ℝ) → ℝ := fun y => φ (y 0) with hFdef
  have hder : ∀ y, HasFDerivAt F (φ' (y 0) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)) y := by
    intro y
    have := (hφ (y 0)).hasFDerivAt.comp y
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
    have e : (φ' (y 0) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)) =
        ContinuousLinearMap.toSpanSingleton ℝ (φ' (y 0)) ∘SL
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) := by
      ext v
      simp [mul_comm]
    rw [e]
    exact this
  have hFd : Differentiable ℝ F := fun y => (hder y).differentiableAt
  have hfd : ∀ y, fderiv ℝ F y =
      φ' (y 0) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) :=
    fun y => (hder y).fderiv
  have hFc : Continuous fun y => fderiv ℝ F y := by
    simp_rw [hfd]
    exact (hφ'c.comp (continuous_apply 0)).smul continuous_const
  have hnorm : ∀ y : Fin 1 → ℝ, |y 0| ≤ ‖y‖ := fun y => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm y 0
  have hP : PolyGrowth F := ⟨C1, hC1, m1, fun y => (h1 (y 0)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (by linarith [hnorm y]) m1) hC1)⟩
  have hP' : PolyGrowth fun y => fderiv ℝ F y (Pi.single 0 1) :=
    ⟨C2, hC2, m2, fun y => by
      show |fderiv ℝ F y (Pi.single 0 1)| ≤ _
      rw [hfd]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, Pi.single_eq_same,
        smul_eq_mul, mul_one]
      exact (h2 (y 0)).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by linarith [hnorm y]) m2) hC2)⟩
  have key := gauss_ibp_poly hFd hFc hP 0 hP'
  have hmap : (gpi 1).map (fun y : Fin 1 → ℝ => y 0) = gaussianReal 0 1 :=
    (measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) 0).map_eq
  have hm0 : Measurable fun y : Fin 1 → ℝ => y 0 := measurable_pi_apply 0
  have hφcont : Continuous φ := continuous_iff_continuousAt.2 fun x => (hφ x).continuousAt
  rw [← hmap, integral_map (φ := fun y : Fin 1 → ℝ => y 0) (f := fun x : ℝ => x * φ x) hm0.aemeasurable
      (continuous_id.mul hφcont).aestronglyMeasurable,
    integral_map hm0.aemeasurable hφ'c.aestronglyMeasurable]
  simp_rw [hfd] at key
  simpa [hFdef] using key

section nested
variable {N J : ℕ}

/-- The flat-to-nested linear map (`reshape.symm` as a continuous linear map). -/
noncomputable def unflat (N J : ℕ) : (Fin (N * J) → ℝ) →L[ℝ] (Fin N → Fin J → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun m =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (N * J) => ℝ) (finProdFinEquiv (i, m))

theorem unflat_apply (z : Fin (N * J) → ℝ) (i : Fin N) (m : Fin J) :
    unflat N J z i m = z (finProdFinEquiv (i, m)) := rfl

theorem unflat_eq_symm (z : Fin (N * J) → ℝ) : unflat N J z = (reshape N J).symm z := by
  funext i m; rw [unflat_apply, reshape_symm_apply]

theorem norm_unflat_le (z : Fin (N * J) → ℝ) : ‖unflat N J z‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun m => ?_
  rw [unflat_apply]
  exact norm_le_pi_norm z _

theorem unflat_single (i : Fin N) (m : Fin J) :
    unflat N J (Pi.single (finProdFinEquiv (i, m)) 1) = Pi.single i (Pi.single m 1) := by
  funext i' m'
  rw [unflat_apply]
  by_cases h : i' = i
  · subst h
    by_cases h2 : m' = m
    · subst h2; simp
    · have : finProdFinEquiv (i', m') ≠ finProdFinEquiv (i', m) := by
        intro hh; exact h2 (by simpa using finProdFinEquiv.injective hh)
      simp [Pi.single_apply, this, h2]
  · have : finProdFinEquiv (i', m') ≠ finProdFinEquiv (i, m) := by
      intro hh; exact h (by simpa using congrArg Prod.fst (finProdFinEquiv.injective hh))
    simp [Pi.single_apply, this, h]

/-- **Gaussian integration by parts for polynomial growth on `Fin N → Fin J → ℝ`**
(iterated product Gaussian). -/
theorem gauss_ibp_poly_nested {F : (Fin N → Fin J → ℝ) → ℝ} (hF : Differentiable ℝ F)
    (hFc : Continuous fun y => fderiv ℝ F y) (i : Fin N) (m : Fin J)
    {C1 C2 : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) {p1 p2 : ℕ}
    (h1 : ∀ y, |F y| ≤ C1 * (1 + ‖y‖) ^ p1)
    (h2 : ∀ y, |fderiv ℝ F y (Pi.single i (Pi.single m 1))| ≤ C2 * (1 + ‖y‖) ^ p2) :
    ∫ y, y i m * F y ∂(Measure.pi fun _ : Fin N =>
        Measure.pi fun _ : Fin J => ProbabilityTheory.gaussianReal 0 1) =
      ∫ y, fderiv ℝ F y (Pi.single i (Pi.single m 1)) ∂(Measure.pi fun _ : Fin N =>
        Measure.pi fun _ : Fin J => ProbabilityTheory.gaussianReal 0 1) := by
  set G : (Fin (N * J) → ℝ) → ℝ := fun z => F (unflat N J z) with hG
  have hGd : Differentiable ℝ G := hF.comp (unflat N J).differentiable
  have hGder : ∀ z, fderiv ℝ G z = (fderiv ℝ F (unflat N J z)).comp (unflat N J) := fun z =>
    ((hF (unflat N J z)).hasFDerivAt.comp z (unflat N J).hasFDerivAt).fderiv
  have hGc : Continuous fun z => fderiv ℝ G z := by
    simp_rw [hGder]
    exact (hFc.comp (unflat N J).continuous).clm_comp continuous_const
  set k := finProdFinEquiv (i, m)
  have hGk : ∀ z, fderiv ℝ G z (Pi.single k 1) =
      fderiv ℝ F (unflat N J z) (Pi.single i (Pi.single m 1)) := fun z => by
    rw [hGder, ContinuousLinearMap.comp_apply, unflat_single]
  have hP : PolyGrowth G := ⟨C1, hC1, p1, fun z => (h1 _).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (by linarith [norm_unflat_le z]) p1) hC1)⟩
  have hP' : PolyGrowth fun z => fderiv ℝ G z (Pi.single k 1) :=
    ⟨C2, hC2, p2, fun z => by
      show |fderiv ℝ G z (Pi.single k 1)| ≤ _
      rw [hGk]
      exact (h2 _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by linarith [norm_unflat_le z]) p2) hC2)⟩
  have key := gauss_ibp_poly hGd hGc hP k hP'
  have hmp := (reshape_measurePreserving N J).symm
  have e1 := hmp.integral_comp' (g := fun y : Fin N → Fin J → ℝ => y i m * F y)
  have e2 := hmp.integral_comp' (g := fun y : Fin N → Fin J → ℝ =>
    fderiv ℝ F y (Pi.single i (Pi.single m 1)))
  rw [← e1, ← e2]
  simp only [hGk] at key
  simp only [hG] at key
  simp_rw [unflat_eq_symm] at key
  simpa [reshape_symm_apply, k] using key

end nested

end SharpLSI.FL
