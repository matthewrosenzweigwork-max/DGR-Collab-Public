import SharpSymmetricLSI.Paper.GaussFormClause2

/-!
# R32 form clause (lane s42), step 3: the truncations `G_n = F ∘ A_n`

`A_n x = (∑_{i<n} v_{ji} x_i)_{j<J}` and `G_n = F ∘ A_n`, so `G_n(z_{<n}) = F(ξ^{(n)}(z))` with the
truncated row variables `ξ^{(n)}_j = ∑_{i<n} v_{ji} z_i`. For `F ∈ C^∞_c(ℝ^J)`: `G_n` is smooth,
bounded with bounded derivative, `∂_i G_n = ∑_j v_{ji} ∂_j F ∘ A_n` (`pd_trunc`), and
`formG(G_n) = ∫ ∑_{j,k} ∂_jF ∂_kF(ξ^{(n)}) M^n_{jk}` with `M^n_{jk} = ∑_{i<n} λ'_i v_{ji} v_{ki}`
(`formG_trunc_integrand`). Along a subsequence with `ξ^{(n)} → ξ` a.e., `M^n → ν δ` (`hvΛ`) and
dominated convergence give `formG(G_n) → ∫ ∑_j ν_j (∂_jF(ξ))² dγ` (`tendsto_formG_trunc`).
-/

noncomputable section
open MeasureTheory Filter Topology Finset
open scoped ENNReal ContDiff

namespace SharpLSI

/-- `A_n x = (∑_{i<n} v_{ji} x_i)_j`. -/
def linA (v : ℕ → ℕ → ℝ) (J n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin J → ℝ) :=
  ContinuousLinearMap.pi fun j : Fin J =>
    ∑ i : Fin n, v j i • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)

theorem linA_apply (v : ℕ → ℕ → ℝ) (J n : ℕ) (x : Fin n → ℝ) (j : Fin J) :
    linA v J n x j = ∑ i : Fin n, v j i * x i := by
  simp [linA]

theorem linA_zBlock (v : ℕ → ℕ → ℝ) (J n : ℕ) (z : ℕ → ℝ) (j : Fin J) :
    linA v J n (zBlock n z) j = ∑ i ∈ Finset.range n, v j i * z i := by
  rw [linA_apply]
  exact Fin.sum_univ_eq_sum_range (fun i => v j i * z i) n

theorem linA_single (v : ℕ → ℕ → ℝ) (J n : ℕ) (i : Fin n) :
    linA v J n (Pi.single i 1) = fun j : Fin J => v j i := by
  funext j
  rw [linA_apply, Finset.sum_eq_single i (fun b _ hb => by simp [Pi.single_apply, hb])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

/-- A linear functional on `ℝ^J` in coordinates. -/
theorem clm_apply_eq_sum_fin {J : ℕ} (L : (Fin J → ℝ) →L[ℝ] ℝ) (w : Fin J → ℝ) :
    L w = ∑ j, w j * L (Pi.single j 1) := by
  conv_lhs => rw [show w = ∑ j, w j • (Pi.single j 1 : Fin J → ℝ) by
    funext k; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]

section trunc
variable {J : ℕ} {F : (Fin J → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (v : ℕ → ℕ → ℝ)
include hF

theorem contDiff_trunc (n : ℕ) : ContDiff ℝ ∞ (fun x => F (linA v J n x)) :=
  hF.comp (linA v J n).contDiff

theorem fderiv_trunc (n : ℕ) (x : Fin n → ℝ) :
    fderiv ℝ (fun x => F (linA v J n x)) x = (fderiv ℝ F (linA v J n x)).comp (linA v J n) := by
  have hd : DifferentiableAt ℝ F (linA v J n x) := (hF.differentiable (by simp)) _
  exact (hd.hasFDerivAt.comp x (linA v J n).hasFDerivAt).fderiv

/-- `∂_i G_n = ∑_j v_{ji} ∂_jF ∘ A_n`. -/
theorem pd_trunc (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (fun x => F (linA v J n x)) x (Pi.single i 1) =
      ∑ j : Fin J, v j i * fderiv ℝ F (linA v J n x) (Pi.single j 1) := by
  rw [fderiv_trunc hF v n x, ContinuousLinearMap.comp_apply, linA_single, clm_apply_eq_sum_fin]

theorem trunc_bounds (hFc : HasCompactSupport F) (n : ℕ) :
    ∃ B, (∀ x, |F (linA v J n x)| ≤ B) ∧
      ∀ x, ‖fderiv ℝ (fun x => F (linA v J n x)) x‖ ≤ B := by
  obtain ⟨B, hB1, hB2, -, -⟩ := exists_bounds_of_cc hF hFc
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB1 0)
  refine ⟨B * (1 + ‖linA v J n‖), fun x => ?_, fun x => ?_⟩
  · exact (hB1 _).trans (le_mul_of_one_le_right hB0 (by linarith [norm_nonneg (linA v J n)]))
  · rw [fderiv_trunc hF v n x]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_mul (hB2 _) (by linarith) (norm_nonneg _) hB0

/-- The integrand of `formG(G_n)` as a quadratic form in `∇F`. -/
theorem formG_trunc_integrand (lam' : ℕ → ℝ) (n : ℕ) (x : Fin n → ℝ) :
    ∑ i : Fin n, lam' i * (fderiv ℝ (fun x => F (linA v J n x)) x (Pi.single i 1)) ^ 2 =
      ∑ j : Fin J, ∑ k : Fin J, fderiv ℝ F (linA v J n x) (Pi.single j 1) *
        fderiv ℝ F (linA v J n x) (Pi.single k 1) *
          ∑ i ∈ Finset.range n, lam' i * v j i * v k i := by
  simp only [pd_trunc hF v n x]
  set d : Fin J → ℝ := fun j => fderiv ℝ F (linA v J n x) (Pi.single j 1)
  have e : ∀ j k : Fin J, ∑ i ∈ Finset.range n, lam' i * v j i * v k i =
      ∑ i : Fin n, lam' i * v j i * v k i := fun j k =>
    (Fin.sum_univ_eq_sum_range (fun i => lam' i * v j i * v k i) n).symm
  simp only [e]
  simp_rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end trunc

section conv
variable {J : ℕ} {F : (Fin J → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
  {v : ℕ → ℕ → ℝ} {lam' : ℕ → ℝ} {ν : ℕ → ℝ}
  (hv2 : ∀ j, Summable fun i => v j i ^ 2) (hvl : ∀ j, Summable fun i => (lam' i * v j i) ^ 2)
  (hvΛ : ∀ i j, ∑' a, lam' a * v i a * v j a = if i = j then ν i else 0)
  {γ : Measure (ℕ → ℝ)} [IsProbabilityMeasure γ] {ξ : ℕ → (ℕ → ℝ) → ℝ}
include hF hFc hv2 hvl hvΛ

/-- **`formG(G_n) → ∫ ∑_j ν_j (∂_jF(ξ))² dγ`** along a subsequence with `ξ^{(n)} → ξ` a.e. -/
theorem tendsto_formG_trunc {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hae : ∀ᵐ z ∂γ, ∀ j : Fin J, Tendsto (fun k => ∑ i ∈ Finset.range (φ k), v j i * z i) atTop
      (𝓝 (ξ j z))) :
    Tendsto (fun k => formG lam' γ (φ k) (fun x => F (linA v J (φ k) x))) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (∑ j : Fin J, ν j *
        (fderiv ℝ F (fun i => ξ i z) (Pi.single j 1)) ^ 2) ∂γ)) := by
  obtain ⟨B, hB1, hB2, hdc, -⟩ := exists_bounds_of_cc hF hFc
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB1 0)
  -- the matrices `M^n`
  have hsum : ∀ j k : ℕ, Summable fun i => lam' i * v j i * v k i := fun j k => by
    refine Summable.of_norm_bounded (((hvl j).add (hv2 k)).div_const 2) fun i => ?_
    rw [Real.norm_eq_abs, show lam' i * v j i * v k i = (lam' i * v j i) * v k i by ring, abs_mul]
    nlinarith [sq_nonneg (|lam' i * v j i| - |v k i|), sq_abs (lam' i * v j i), sq_abs (v k i)]
  set Mb : ℕ → ℕ → ℝ := fun j k => ∑' i, |lam' i * v j i * v k i|
  have hMb : ∀ (j k : ℕ) (n : ℕ), |∑ i ∈ Finset.range n, lam' i * v j i * v k i| ≤ Mb j k :=
    fun j k n => (Finset.abs_sum_le_sum_abs _ _).trans
      ((hsum j k).abs.sum_le_tsum _ fun _ _ => abs_nonneg _)
  have hM : ∀ j k : ℕ, Tendsto (fun m => ∑ i ∈ Finset.range (φ m), lam' i * v j i * v k i) atTop
      (𝓝 (if j = k then ν j else 0)) := fun j k => by
    rw [← hvΛ j k]
    exact (hsum j k).hasSum.tendsto_sum_nat.comp hφ.tendsto_atTop
  -- the integrands
  set d : (Fin J → ℝ) → Fin J → ℝ := fun y j => fderiv ℝ F y (Pi.single j 1)
  have hdB : ∀ y j, |d y j| ≤ B := fun y j => by
    have := (fderiv ℝ F y).le_opNorm (Pi.single j 1)
    rw [Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs] at this
    exact this.trans (hB2 y)
  have hdcont : ∀ j, Continuous fun y => d y j := fun j => hdc.clm_apply continuous_const
  have hint : ∀ k z, (∑ i : Fin (φ k), lam' i * (fderiv ℝ (fun x => F (linA v J (φ k) x))
      (zBlock (φ k) z) (Pi.single i 1)) ^ 2) =
      ∑ j : Fin J, ∑ l : Fin J, d (linA v J (φ k) (zBlock (φ k) z)) j *
        d (linA v J (φ k) (zBlock (φ k) z)) l *
          ∑ i ∈ Finset.range (φ k), lam' i * v j i * v l i := fun k z =>
    formG_trunc_integrand hF v lam' (φ k) (zBlock (φ k) z)
  unfold formG
  simp_rw [hint]
  set bound : ℝ := ∑ j : Fin J, ∑ l : Fin J, B * B * Mb j l
  refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal bound) (fun k => ?_)
    (fun k => Eventually.of_forall fun z => ?_) (by simp) ?_
  · -- measurability
    refine ENNReal.measurable_ofReal.comp ?_
    refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun l _ => ?_
    have hz : Continuous fun z : ℕ → ℝ => linA v J (φ k) (zBlock (φ k) z) :=
      (linA v J (φ k)).continuous.comp (continuous_pi fun i => continuous_apply _)
    exact ((((hdcont j).comp hz).mul ((hdcont l).comp hz)).mul continuous_const).measurable
  · refine ENNReal.ofReal_le_ofReal ?_
    refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => ?_
    refine (le_abs_self _).trans ?_
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hdB _ _) (hdB _ _) (abs_nonneg _) hB0) (hMb j l _)
      (abs_nonneg _) (mul_nonneg hB0 hB0)
  · filter_upwards [hae] with z hz
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    have hA : Tendsto (fun k => linA v J (φ k) (zBlock (φ k) z)) atTop (𝓝 (fun i => ξ i z)) :=
      tendsto_pi_nhds.2 fun j => by simpa only [linA_zBlock] using hz j
    have hlim : Tendsto (fun k => ∑ j : Fin J, ∑ l : Fin J, d (linA v J (φ k) (zBlock (φ k) z)) j *
        d (linA v J (φ k) (zBlock (φ k) z)) l *
          ∑ i ∈ Finset.range (φ k), lam' i * v j i * v l i) atTop
        (𝓝 (∑ j : Fin J, ∑ l : Fin J, d (fun i => ξ i z) j * d (fun i => ξ i z) l *
          (if (j : ℕ) = l then ν j else 0))) :=
      tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun l _ =>
        ((((hdcont j).tendsto _).comp hA).mul (((hdcont l).tendsto _).comp hA)).mul (hM j l)
    convert hlim using 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j (fun l _ hl => by
      rw [if_neg (fun h => hl (Fin.ext h).symm), mul_zero]) (fun h => absurd (Finset.mem_univ j) h),
      if_pos rfl]
    simp only [d]
    ring

end conv

end SharpLSI
