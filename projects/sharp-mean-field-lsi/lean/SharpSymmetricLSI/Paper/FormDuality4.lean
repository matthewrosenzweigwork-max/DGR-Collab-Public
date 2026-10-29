import SharpSymmetricLSI.Paper.FormDuality3

/-!
# R32 (8.8), part 4: smooth compactly supported functions of `ξ`

For `p ∈ C_c^∞(ℝ^m)`, `(p(ξ), L_ξ p(ξ)) ∈ CylApprox`, where
`L_ξ p = ∑_j ν_j (∂_j² p - y_j ∂_j p)` (`cylApprox_comp_xi`). The approximants are the
cylinder functions `p(ξ^N)` with `ξ^N_j = ∑_{q<N} v_{jq} z_q` (then cut off, Level 1); the limit
`N → ∞` uses `ξ^N → ξ` (row variables), `∑_{i<N} λ'_i v_{ji} v_{ki} → δ_{jk} ν_j` and the drift
clause `∑_{i<N} λ'_i v_{ji} (z_i + Y_i) → ν_j ξ_j` in `L²` (hypothesis `hLξ`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ContDiff

namespace SharpLSI

/-! ### Linear algebra of the truncation map -/

/-- The truncated diagonal map `x ↦ (∑_{q<N} v_{jq} x_q)_{j<m}`. -/
noncomputable def truncMap (v : ℕ → ℕ → ℝ) (m N : ℕ) : (Fin N → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi fun j : Fin m => ∑ q : Fin N, v j q • ContinuousLinearMap.proj q

theorem truncMap_apply (v : ℕ → ℕ → ℝ) {m N : ℕ} (x : Fin N → ℝ) (j : Fin m) :
    truncMap v m N x j = ∑ q : Fin N, v j q * x q := by
  simp [truncMap]

theorem truncMap_single (v : ℕ → ℕ → ℝ) {m N : ℕ} (i : Fin N) :
    truncMap v m N (Pi.single i 1) = fun j : Fin m => v j i := by
  funext j
  rw [truncMap_apply]
  simp [Pi.single_apply]

theorem truncMap_zBlock (v : ℕ → ℕ → ℝ) {m N : ℕ} (z : ℕ → ℝ) :
    truncMap v m N (zBlock N z) = fun j : Fin m => ∑ q ∈ Finset.range N, v j q * z q := by
  funext j
  rw [truncMap_apply]
  exact Fin.sum_univ_eq_sum_range (fun q => v j q * z q) N

theorem clm_apply_eq_sum_single {m : ℕ} (L : (Fin m → ℝ) →L[ℝ] ℝ) (w : Fin m → ℝ) :
    L w = ∑ j, w j * L (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (Pi.single j (w j) : Fin m → ℝ) = w j • (Pi.single j (1 : ℝ) : Fin m → ℝ) := by
    ext k; by_cases h : k = j <;> simp [h]
  rw [e, map_smul, smul_eq_mul]

theorem pd_comp_clm {m N : ℕ} {p : (Fin m → ℝ) → ℝ} (hp : Differentiable ℝ p)
    (A : (Fin N → ℝ) →L[ℝ] (Fin m → ℝ)) (i : Fin N) (x : Fin N → ℝ) :
    pd (fun x => p (A x)) i x = ∑ j, A (Pi.single i 1) j * pd p j (A x) := by
  unfold pd
  rw [fderiv_fun_comp x (hp (A x)) A.differentiableAt, A.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  exact clm_apply_eq_sum_single _ _

theorem pd_sum_mul {m : ℕ} {g : Fin m → (Fin m → ℝ) → ℝ} (hg : ∀ j, Differentiable ℝ (g j))
    (c : Fin m → ℝ) (k : Fin m) (y : Fin m → ℝ) :
    pd (fun y => ∑ j, c j * g j y) k y = ∑ j, c j * pd (g j) k y := by
  unfold pd
  rw [fderiv_fun_sum fun j _ => ((hg j y).const_mul (c j))]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_const_mul (hg j y), ContinuousLinearMap.smul_apply, smul_eq_mul]

section trunc
variable (v : ℕ → ℕ → ℝ) {m N : ℕ} {p : (Fin m → ℝ) → ℝ}

theorem pd_comp_truncMap (hp : Differentiable ℝ p) (i : Fin N) (x : Fin N → ℝ) :
    pd (fun x => p (truncMap v m N x)) i x = ∑ j : Fin m, v j i * pd p j (truncMap v m N x) := by
  rw [pd_comp_clm hp, truncMap_single]

theorem d2_comp_truncMap (hp : ContDiff ℝ ∞ p) (i : Fin N) (x : Fin N → ℝ) :
    d2 (fun x => p (truncMap v m N x)) i x =
      ∑ k : Fin m, v k i * ∑ j : Fin m, v j i * pd (pd p j) k (truncMap v m N x) := by
  have hd : ∀ j, Differentiable ℝ (pd p j) := fun j =>
    (contDiff_pd hp j).differentiable (by simp)
  have e : pd (fun x => p (truncMap v m N x)) i =
      fun x => (fun y => ∑ j : Fin m, v j i * pd p j y) (truncMap v m N x) := by
    funext x; exact pd_comp_truncMap v (hp.differentiable (by simp)) i x
  show pd (pd (fun x => p (truncMap v m N x)) i) i x = _
  rw [e, pd_comp_clm (Differentiable.fun_sum fun j _ => (hd j).const_mul _), truncMap_single]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pd_sum_mul hd]

/-- The generator on `p(ξ^N)`. -/
theorem genG_comp_truncMap (hp : ContDiff ℝ ∞ p) (lam' : ℕ → ℝ) (Y : ℕ → (ℕ → ℝ) → ℝ)
    (z : ℕ → ℝ) :
    genG lam' Y N (fun x => p (truncMap v m N x)) z =
      ∑ j : Fin m, ∑ k : Fin m, (∑ i ∈ Finset.range N, lam' i * v j i * v k i) *
          pd (pd p j) k (fun j => ∑ q ∈ Finset.range N, v j q * z q) -
        ∑ j : Fin m, pd p j (fun j => ∑ q ∈ Finset.range N, v j q * z q) *
          ∑ i ∈ Finset.range N, lam' i * v j i * (z i + Y i z) := by
  unfold genG
  simp_rw [d2_comp_truncMap v hp, pd_comp_truncMap v (hp.differentiable (by simp)),
    truncMap_zBlock]
  set P : Fin m → Fin m → ℝ := fun j k => pd (pd p j) k (fun j => ∑ q ∈ Finset.range N, v j q * z q)
  set D : Fin m → ℝ := fun j => pd p j (fun j => ∑ q ∈ Finset.range N, v j q * z q)
  show ∑ i : Fin N, lam' i * (∑ k : Fin m, v k i * ∑ j : Fin m, v j i * P j k -
      (z i + Y i z) * ∑ j : Fin m, v j i * D j) =
    ∑ j : Fin m, ∑ k : Fin m, (∑ i ∈ Finset.range N, lam' i * v j i * v k i) * P j k -
      ∑ j : Fin m, D j * ∑ i ∈ Finset.range N, lam' i * v j i * (z i + Y i z)
  simp_rw [← Fin.sum_univ_eq_sum_range (fun i => lam' i * v _ i * v _ i) N,
    ← Fin.sum_univ_eq_sum_range (fun i => lam' i * v _ i * (z i + Y i z)) N]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
    refine Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring

end trunc

/-! ### `L²` convergence of bounded continuous compositions -/

variable {γ : Measure (ℕ → ℝ)}

theorem aestronglyMeasurable_vec {m : ℕ} {X : Fin m → (ℕ → ℝ) → ℝ}
    (hX : ∀ j, AEStronglyMeasurable (X j) γ) :
    AEStronglyMeasurable (fun z => fun j => X j z) γ :=
  (AEMeasurable.of_eval fun j => (hX j).aemeasurable).aestronglyMeasurable

theorem tendsto_eLpNorm_comp_bdd [IsFiniteMeasure γ] {m : ℕ} {h : (Fin m → ℝ) → ℝ}
    (hh : Continuous h) {K : ℝ} (hK : ∀ y, |h y| ≤ K) {X : ℕ → Fin m → (ℕ → ℝ) → ℝ}
    {X₀ : Fin m → (ℕ → ℝ) → ℝ} (hXm : ∀ N j, AEStronglyMeasurable (X N j) γ)
    (hX₀m : ∀ j, AEStronglyMeasurable (X₀ j) γ)
    (hX : ∀ j, Tendsto (fun N => eLpNorm (fun z => X N j z - X₀ j z) 2 γ) atTop (𝓝 0)) :
    Tendsto (fun N => eLpNorm (fun z => h (fun j => X N j z) - h (fun j => X₀ j z)) 2 γ) atTop
      (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  set e : ℕ → (ℕ → ℝ) → ℝ := fun n z => ∑ j, |X (ns n) j z - X₀ j z|
  have he : Tendsto (fun n => eLpNorm (e n - 0) 2 γ) atTop (𝓝 0) := by
    have hle : ∀ n, eLpNorm (e n - 0) 2 γ ≤
        ∑ j, eLpNorm (fun z => X (ns n) j z - X₀ j z) 2 γ := fun n => by
      rw [sub_zero]
      have : e n = ∑ j, fun z => |X (ns n) j z - X₀ j z| := by
        funext z; simp [e, Finset.sum_apply]
      rw [this]
      refine (eLpNorm_sum_le (by norm_num)).trans (Finset.sum_le_sum fun j _ => ?_)
      have := eLpNorm_norm (p := 2) (μ := γ) (fun z => X (ns n) j z - X₀ j z)
        ((hXm _ j).sub (hX₀m j))
      simp only [Real.norm_eq_abs] at this
      exact this.le
    have h0 : Tendsto (fun n => ∑ j, eLpNorm (fun z => X (ns n) j z - X₀ j z) 2 γ) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun j _ => (hX j).comp hns
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => bot_le) hle
  obtain ⟨ms, -, hms⟩ := (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero he).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  refine tendsto_eLpNorm_two_of_dom_ae (g := fun _ => 2 * K)
    (fun n => (hh.comp_aestronglyMeasurable (aestronglyMeasurable_vec (hXm _))).sub
      (hh.comp_aestronglyMeasurable (aestronglyMeasurable_vec hX₀m)))
    (memLp_const _) (fun n => Eventually.of_forall fun z => ?_) (hms.mono fun z hz => ?_)
  · have := hK (fun j => X (ns (ms n)) j z); have := hK (fun j => X₀ j z)
    refine (abs_sub _ _).trans ?_; linarith
  · have hv : Tendsto (fun n => fun j => X (ns (ms n)) j z) atTop (𝓝 fun j => X₀ j z) := by
      refine tendsto_pi_nhds.2 fun j => ?_
      have h1 : Tendsto (fun n => X (ns (ms n)) j z - X₀ j z) atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun n => ?_) hz
        rw [Real.norm_eq_abs]
        exact Finset.single_le_sum (f := fun j => |X (ns (ms n)) j z - X₀ j z|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      simpa using h1.add_const (X₀ j z)
    have := ((hh.tendsto _).comp hv).sub_const (h fun j => X₀ j z)
    simpa [Function.comp_def] using this

/-- Finite sums of `L²`-convergent sequences. -/
theorem tendsto_eLpNorm_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℕ → (ℕ → ℝ) → ℝ}
    {g : ι → (ℕ → ℝ) → ℝ}
    (h : ∀ i ∈ s, Tendsto (fun N => eLpNorm (fun z => f i N z - g i z) 2 γ) atTop (𝓝 0)) :
    Tendsto (fun N => eLpNorm (fun z => ∑ i ∈ s, f i N z - ∑ i ∈ s, g i z) 2 γ) atTop (𝓝 0) := by
  have hle : ∀ N, eLpNorm (fun z => ∑ i ∈ s, f i N z - ∑ i ∈ s, g i z) 2 γ ≤
      ∑ i ∈ s, eLpNorm (fun z => f i N z - g i z) 2 γ := fun N => by
    have e : (fun z => ∑ i ∈ s, f i N z - ∑ i ∈ s, g i z) = ∑ i ∈ s, fun z => f i N z - g i z := by
      funext z; simp [Finset.sum_apply, Finset.sum_sub_distrib]
    rw [e]; exact eLpNorm_sum_le (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => bot_le) hle
  simpa using tendsto_finsetSum s h

theorem tendsto_eLpNorm_sub_sub {a b : ℕ → (ℕ → ℝ) → ℝ} {a₀ b₀ : (ℕ → ℝ) → ℝ}
    (ha : Tendsto (fun N => eLpNorm (fun z => a N z - a₀ z) 2 γ) atTop (𝓝 0))
    (hb : Tendsto (fun N => eLpNorm (fun z => b N z - b₀ z) 2 γ) atTop (𝓝 0)) :
    Tendsto (fun N => eLpNorm (fun z => (a N z - b N z) - (a₀ z - b₀ z)) 2 γ) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using ha.add hb)
    (fun _ => bot_le) fun N => ?_
  have e : (fun z => (a N z - b N z) - (a₀ z - b₀ z)) =
      (fun z => a N z - a₀ z) - (fun z => b N z - b₀ z) := by funext z; simp; ring
  rw [e]; exact eLpNorm_sub_le (by norm_num)

theorem tendsto_eLpNorm_const [IsProbabilityMeasure γ] {c : ℕ → ℝ} {c₀ : ℝ}
    (hc : Tendsto c atTop (𝓝 c₀)) :
    Tendsto (fun N => eLpNorm (fun _ : ℕ → ℝ => c N - c₀) 2 γ) atTop (𝓝 0) := by
  simp_rw [eLpNorm_const _ two_ne_zero (IsProbabilityMeasure.ne_zero γ), measure_univ,
    ENNReal.one_rpow, mul_one]
  have : Tendsto (fun N => c N - c₀) atTop (𝓝 0) := by simpa using hc.sub_const c₀
  simpa [Function.comp_def] using (continuous_enorm.tendsto 0).comp this

/-! ### Level 2 -/

section level2
variable [IsProbabilityMeasure γ] {lam' : ℕ → ℝ} {Y : ℕ → (ℕ → ℝ) → ℝ}
  {v : ℕ → ℕ → ℝ} {ν : ℕ → ℝ} {ξ : ℕ → (ℕ → ℝ) → ℝ}
  (hz : ∀ i, MemLp (fun z : ℕ → ℝ => z i) 2 γ) (hY : ∀ i, MemLp (Y i) 2 γ)
  (hξ : ∀ j, IsRowVariable v γ j (ξ j))
  (hW : ∀ j k, Tendsto (fun N => ∑ i ∈ Finset.range N, lam' i * v j i * v k i) atTop
    (𝓝 (if j = k then ν j else 0)))
  (hLξ : ∀ j, Tendsto (fun N => eLpNorm (fun z => ∑ i ∈ Finset.range N,
    lam' i * v j i * (z i + Y i z) - ν j * ξ j z) 2 γ) atTop (𝓝 0))
include hz hY hξ hW hLξ

theorem exists_bound_cc {m : ℕ} {p : (Fin m → ℝ) → ℝ} (hp : ContDiff ℝ ∞ p)
    (hpc : HasCompactSupport p) : ∃ K, ∀ y, |p y| ≤ K := by
  obtain ⟨K, hK⟩ := hpc.exists_bound_of_continuous hp.continuous
  exact ⟨K, fun y => by simpa [Real.norm_eq_abs] using hK y⟩

omit hz hY hξ hW hLξ in
theorem exists_iteratedFDeriv_bound_cc {m : ℕ} {p : (Fin m → ℝ) → ℝ} (hp : ContDiff ℝ ∞ p)
    (hpc : HasCompactSupport p) : ∃ B, ∀ k ≤ 2, ∀ y, ‖iteratedFDeriv ℝ k p y‖ ≤ B := by
  have hb : ∀ k : ℕ, ∃ B, ∀ y, ‖iteratedFDeriv ℝ k p y‖ ≤ B := fun k =>
    (hpc.iteratedFDeriv k).exists_bound_of_continuous
      (hp.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  obtain ⟨B0, h0⟩ := hb 0; obtain ⟨B1, h1⟩ := hb 1; obtain ⟨B2, h2⟩ := hb 2
  refine ⟨max B0 (max B1 B2), fun k hk y => ?_⟩
  interval_cases k
  · exact (h0 y).trans (le_max_left _ _)
  · exact (h1 y).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h2 y).trans ((le_max_right _ _).trans (le_max_right _ _))

omit hz hY hξ hW hLξ in
theorem bdd_iteratedFDeriv_comp_truncMap {m N : ℕ} {p : (Fin m → ℝ) → ℝ} (hp : ContDiff ℝ ∞ p)
    (hpc : HasCompactSupport p) : ∃ B, ∀ k ≤ 2, ∀ x,
      ‖iteratedFDeriv ℝ k (fun x => p (truncMap v m N x)) x‖ ≤ B := by
  obtain ⟨B, hB⟩ := exists_iteratedFDeriv_bound_cc hp hpc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by norm_num) 0)
  set A := truncMap v m N
  refine ⟨B * (1 + ‖A‖) ^ 2, fun k hk x => ?_⟩
  have e : (fun x => p (A x)) = p ∘ A := rfl
  rw [e, A.iteratedFDeriv_comp_right hp x (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h1 : ‖A‖ ^ k ≤ (1 + ‖A‖) ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_nonneg A]) k).trans
      (pow_le_pow_right₀ (by linarith [norm_nonneg A]) hk)
  exact mul_le_mul (hB k hk _) h1 (by positivity) hB0

/-- **Level 2**: `(p(ξ), L_ξ p(ξ))` is approximated by cylinders, for `p ∈ C_c^∞(ℝ^m)`. -/
theorem cylApprox_comp_xi {m : ℕ} {p : (Fin m → ℝ) → ℝ} (hp : ContDiff ℝ ∞ p)
    (hpc : HasCompactSupport p) :
    CylApprox lam' Y γ (fun z => p (fun j => ξ j z))
      (fun z => ∑ j : Fin m, ν j * (pd (pd p j) j (fun i => ξ i z) -
        ξ j z * pd p j (fun i => ξ i z))) := by
  have hYm : ∀ i, AEStronglyMeasurable (Y i) γ := fun i => (hY i).aestronglyMeasurable
  have hξm : ∀ j, AEStronglyMeasurable (ξ j) γ := fun j => (hξ j).1.aestronglyMeasurable
  have hpd : ∀ j, ContDiff ℝ ∞ (pd p j) := fun j => contDiff_pd hp j
  have hpdc : ∀ j, HasCompactSupport (pd p j) := fun j => hasCompactSupport_pd hpc j
  have hpdd : ∀ j k, ContDiff ℝ ∞ (pd (pd p j) k) := fun j k => contDiff_pd (hpd j) k
  have hpddc : ∀ j k, HasCompactSupport (pd (pd p j) k) := fun j k =>
    hasCompactSupport_pd (hpdc j) k
  -- truncated variables
  set XN : ℕ → Fin m → (ℕ → ℝ) → ℝ := fun N j z => ∑ q ∈ Finset.range N, v j q * z q
  have hXNm : ∀ N j, AEStronglyMeasurable (XN N j) γ := fun N j =>
    (Finset.measurable_fun_sum _ fun q _ =>
      measurable_const.mul (measurable_pi_apply q)).aestronglyMeasurable
  have hXN : ∀ j : Fin m, Tendsto (fun N => eLpNorm (fun z => XN N j z - ξ j z) 2 γ) atTop
      (𝓝 0) := fun j => (hξ j).2
  have hGs : ∀ N, ContDiff ℝ ∞ (fun x => p (truncMap v m N x)) := fun N =>
    hp.comp (truncMap v m N).contDiff
  refine CylApprox.of_tendsto hYm (Fk := fun N z => p (truncMap v m N (zBlock N z)))
    (Gk := fun N => genG lam' Y N (fun x => p (truncMap v m N x))) (fun N => ?_) (fun N => ?_)
    (fun N => aestronglyMeasurable_genG hYm lam' (hGs N)) ?_ ?_ ?_ ?_
  · obtain ⟨B, hB⟩ := bdd_iteratedFDeriv_comp_truncMap (v := v) (N := N) hp hpc
    exact cylApprox_of_bdd (hGs N) hB hz hY lam'
  · exact ((hGs N).continuous.measurable.comp (measurable_zBlock N)).aestronglyMeasurable
  · exact hp.continuous.comp_aestronglyMeasurable (aestronglyMeasurable_vec fun j => hξm j)
  · refine Finset.aestronglyMeasurable_fun_sum _ fun j _ => aestronglyMeasurable_const.mul
      (((hpdd j j).continuous.comp_aestronglyMeasurable (aestronglyMeasurable_vec fun i => hξm i)).sub
      ((hξm j).mul ((hpd j).continuous.comp_aestronglyMeasurable
        (aestronglyMeasurable_vec fun i => hξm i))))
  · -- `p(ξ^N) → p(ξ)`
    obtain ⟨K, hK⟩ := exists_bound_cc hz hY hξ hW hLξ hp hpc
    have := tendsto_eLpNorm_comp_bdd hp.continuous hK hXNm (fun j => hξm j) hXN
    refine this.congr fun N => ?_
    congr 1; funext z; rw [truncMap_zBlock]
  · -- the generator
    have e : ∀ N, (fun z => genG lam' Y N (fun x => p (truncMap v m N x)) z -
        ∑ j : Fin m, ν j * (pd (pd p j) j (fun i => ξ i z) - ξ j z * pd p j (fun i => ξ i z))) =
        fun z => (∑ j : Fin m, ∑ k : Fin m, (∑ i ∈ Finset.range N, lam' i * v j i * v k i) *
          pd (pd p j) k (fun j => XN N j z) -
          ∑ j : Fin m, pd p j (fun j => XN N j z) *
            ∑ i ∈ Finset.range N, lam' i * v j i * (z i + Y i z)) -
          (∑ j : Fin m, ∑ k : Fin m, (if (j : ℕ) = k then ν j else 0) *
            pd (pd p j) k (fun i => ξ i z) -
          ∑ j : Fin m, pd p j (fun i => ξ i z) * (ν j * ξ j z)) := fun N => by
      funext z
      rw [genG_comp_truncMap v hp]
      congr 1
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_eq_single j (fun k _ hk => by
        rw [if_neg (fun h => hk (Fin.ext h).symm), zero_mul]) (by simp), if_pos rfl]
      ring
    simp_rw [e]
    refine tendsto_eLpNorm_sub_sub ?_ ?_
    · refine tendsto_eLpNorm_finset_sum _ fun j _ => tendsto_eLpNorm_finset_sum _ fun k _ => ?_
      obtain ⟨K, hK⟩ := exists_bound_cc hz hY hξ hW hLξ (hpdd j k) (hpddc j k)
      have h1 := tendsto_eLpNorm_comp_bdd (hpdd j k).continuous hK hXNm (fun j => hξm j) hXN
      have h2 := tendsto_eLpNorm_mul_bdd' (b := fun N _ => ∑ i ∈ Finset.range N,
          lam' i * v j i * v k i) (b₀ := fun _ => if (j : ℕ) = k then ν j else 0)
        (fun N => (hpdd j k).continuous.comp_aestronglyMeasurable (aestronglyMeasurable_vec (hXNm N)))
        ((hpdd j k).continuous.comp_aestronglyMeasurable (aestronglyMeasurable_vec fun i => hξm i))
        (fun N => aestronglyMeasurable_const) (fun N z => hK _) (fun z => hK _) h1 (memLp_const _)
        (tendsto_eLpNorm_const (hW j k))
      refine h2.congr fun N => ?_
      congr 1; funext z; ring
    · refine tendsto_eLpNorm_finset_sum _ fun j _ => ?_
      obtain ⟨K, hK⟩ := exists_bound_cc hz hY hξ hW hLξ (hpd j) (hpdc j)
      have h1 := tendsto_eLpNorm_comp_bdd (hpd j).continuous hK hXNm (fun j => hξm j) hXN
      have hDm : ∀ N, AEStronglyMeasurable (fun z => ∑ i ∈ Finset.range N,
          lam' i * v j i * (z i + Y i z)) γ := fun N =>
        Finset.aestronglyMeasurable_fun_sum _ fun i _ => aestronglyMeasurable_const.mul
          ((measurable_pi_apply i).aestronglyMeasurable.add (hYm i))
      exact tendsto_eLpNorm_mul_bdd'
        (fun N => (hpd j).continuous.comp_aestronglyMeasurable (aestronglyMeasurable_vec (hXNm N)))
        ((hpd j).continuous.comp_aestronglyMeasurable (aestronglyMeasurable_vec fun i => hξm i))
        hDm (fun N z => hK _) (fun z => hK _) h1 ((hξ j).1.const_mul _) (hLξ j)

end level2

end SharpLSI
