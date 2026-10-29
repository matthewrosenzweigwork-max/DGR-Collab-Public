import SharpSymmetricLSI.Paper.GaussPoincare2
import SharpSymmetricLSI.Paper.LamSym8

/-!
# (8.10), Poincaré half (lane s42): `Var_γ f ≤ ℰ_∞(f)/λ_G`

* `quad_mul_lamG_le`: for finitely supported `a`, `⟨a, C a⟩ λ_G ≤ ∑ λ'_k a_k²` (definition (8.9)).
* `lamG_pos`, `lamG_lt_top`: `0 < λ_G < ∞`.
* `var_mul_lamG_le_form`: on cylinder functions, `Var_γ(φ) λ_G ≤ ℰ_∞(φ)` (Paper/GaussPoincare2
  and the pointwise bound).
* `gaussian_poincare`: for every `f ∈ L²(γ)`, `Var_γ f ≤ ℰ_∞(f)/λ_G` (`ℰ_∞` is the relaxation
  `gaussForm`; the variance is continuous in `L²(γ)`).
* `lamSym_tendsto_of''`: (2.8) with the compactness property as the only hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal ContDiff MatrixOrder

namespace SharpLSI

/-- Extension of `a : Fin J → ℝ` by zero. -/
def extFin {J : ℕ} (a : Fin J → ℝ) : ℕ → ℝ := fun i => if h : i < J then a ⟨i, h⟩ else 0

theorem extFin_eq_zero {J : ℕ} (a : Fin J → ℝ) {i : ℕ} (hi : i ∉ range J) : extFin a i = 0 := by
  rw [mem_range] at hi
  simp [extFin, hi]

theorem extFin_coe {J : ℕ} (a : Fin J → ℝ) (k : Fin J) : extFin a k = a k := by
  simp [extFin, k.2]

section quad
variable {C : ℕ → ℕ → ℝ}

theorem quad_range_extFin {J : ℕ} (a : Fin J → ℝ) :
    ∑ i ∈ range J, ∑ j ∈ range J, extFin a i * C i j * extFin a j =
      ∑ k : Fin J, ∑ l : Fin J, C k l * a k * a l := by
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [extFin_coe, extFin_coe]; ring

theorem tsum_quad_extFin {J : ℕ} (a : Fin J → ℝ) :
    ∑' i, extFin a i * ∑' j, C i j * extFin a j =
      ∑ k : Fin J, ∑ l : Fin J, C k l * a k * a l := by
  rw [← quad_range_extFin, tsum_eq_sum (s := range J) fun i hi => by
    rw [extFin_eq_zero a hi, zero_mul]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tsum_eq_sum (s := range J) fun j hj => by rw [extFin_eq_zero a hj, mul_zero],
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem tsum_lam_extFin {J : ℕ} (lam' : ℕ → ℝ) (a : Fin J → ℝ) :
    ∑' i, lam' i * extFin a i ^ 2 = ∑ k : Fin J, lam' k * a k ^ 2 := by
  rw [tsum_eq_sum (s := range J) fun i hi => by rw [extFin_eq_zero a hi]; ring, Finset.sum_range]
  exact Finset.sum_congr rfl fun k _ => by rw [extFin_coe]

/-- **The pointwise bound from the definition of `λ_G`.** -/
theorem quad_mul_lamG_le {lam' : ℕ → ℝ} {J : ℕ} (a : Fin J → ℝ) :
    ENNReal.ofReal (∑ k : Fin J, ∑ l : Fin J, C k l * a k * a l) * lamG lam' C ≤
      ENNReal.ofReal (∑ k : Fin J, lam' k * a k ^ 2) := by
  set Q := ∑ k : Fin J, ∑ l : Fin J, C k l * a k * a l
  rcases le_or_gt Q 0 with hQ | hQ
  · rw [ENNReal.ofReal_of_nonpos hQ, zero_mul]; exact zero_le
  have hv0 : extFin a ≠ 0 := fun h => by
    have : Q = 0 := by
      have e : Q = ∑' i, extFin a i * ∑' j, C i j * extFin a j := (tsum_quad_extFin a).symm
      rw [e, h]; simp
    linarith
  have hmem : extFin a ∈ {v : ℕ → ℝ | Summable (fun i => v i ^ 2) ∧
      Summable (fun i => lam' i * v i ^ 2) ∧ v ≠ 0} :=
    ⟨summable_of_ne_finset_zero (s := range J) fun i hi => by rw [extFin_eq_zero a hi]; ring,
      summable_of_ne_finset_zero (s := range J) fun i hi => by rw [extFin_eq_zero a hi]; ring,
      hv0⟩
  have h : lamG lam' C ≤ ENNReal.ofReal (∑' i, lam' i * extFin a i ^ 2) /
      ENNReal.ofReal (∑' i, extFin a i * ∑' j, C i j * extFin a j) := by
    unfold lamG
    exact iInf₂_le (f := fun v (_ : v ∈ {v : ℕ → ℝ | Summable (fun i => v i ^ 2) ∧
      Summable (fun i => lam' i * v i ^ 2) ∧ v ≠ 0}) =>
        ENNReal.ofReal (∑' i, lam' i * v i ^ 2) /
          ENNReal.ofReal (∑' i, v i * ∑' j, C i j * v j)) (extFin a) hmem
  rw [tsum_quad_extFin, tsum_lam_extFin] at h
  rw [mul_comm]
  exact (ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hQ)) (Or.inl ENNReal.ofReal_ne_top)).mp h

variable {σ : ℝ} (hσ0 : 0 < σ) (hCs : ∀ i j, C i j = C j i)
  (hnn : ∀ (s : Finset ℕ) (v : ℕ → ℝ), 0 ≤ ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j)
  (hup : ∀ (s : Finset ℕ) (v : ℕ → ℝ),
    ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j ≤ (∑ i ∈ s, v i ^ 2) / σ)
  (hcol : ∀ j, Summable fun k => C k j ^ 2)

include hσ0 hCs hnn hup hcol in
/-- **`λ_G > 0`.** -/
theorem lamG_pos {lam' : ℕ → ℝ} {c : ℝ} (hc : 0 < c) (hlam : ∀ i, c ≤ lam' i) :
    0 < lamG lam' C := by
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (mul_pos hc hσ0)) ?_
  unfold lamG
  refine le_iInf₂ fun v hv => ?_
  obtain ⟨hv2, hvl, hv0⟩ := hv
  set Vs := ∑' i, v i ^ 2
  have hV : 0 < Vs := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h; push_neg at h; exact hv0 (funext h)
    exact hv2.tsum_pos (fun _ => sq_nonneg _) i (by positivity)
  set L := ∑' i, lam' i * v i ^ 2
  have hL : c * Vs ≤ L := by
    rw [← tsum_mul_left]
    exact (hv2.mul_left c).tsum_le_tsum (fun i => mul_le_mul_of_nonneg_right (hlam i)
      (sq_nonneg _)) hvl
  set Q := ∑' i, v i * ∑' j, C i j * v j
  have hQe : Q = ∑' i, v i * Cvec C v i := rfl
  obtain ⟨hCv, hCvle⟩ := Cv_sq_le hσ0 hCs hnn hup hcol hv2
  have hQ : Q ≤ Vs / σ := by
    obtain ⟨-, hcs⟩ := tsum_mul_sq_le hv2 hCv
    rw [← hQe] at hcs
    have h2 : Q ^ 2 ≤ (Vs / σ) ^ 2 := by
      calc Q ^ 2 ≤ Vs * ∑' i, Cvec C v i ^ 2 := hcs
        _ ≤ Vs * (Vs / σ ^ 2) := mul_le_mul_of_nonneg_left hCvle hV.le
        _ = (Vs / σ) ^ 2 := by ring
    exact (abs_le_of_sq_le_sq' h2 (by positivity)).2
  rcases le_or_gt Q 0 with hQ0 | hQ0
  · rw [ENNReal.ofReal_of_nonpos hQ0, ENNReal.div_zero (by simpa using
      (lt_of_lt_of_le (mul_pos hc hV) hL))]
    exact le_top
  rw [← ENNReal.ofReal_div_of_pos hQ0]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hQ0]
  calc c * σ * Q ≤ c * σ * (Vs / σ) := mul_le_mul_of_nonneg_left hQ (by positivity)
    _ = c * Vs := by field_simp
    _ ≤ L := hL

include hCs hnn in
/-- **`λ_G < ∞`.** -/
theorem lamG_lt_top {T : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus T C) (lam' : ℕ → ℝ) :
    lamG lam' C < ⊤ := by
  set v : ℕ → ℝ := fun i => if i = 0 then 1 else 0
  have hv : ∀ i, i ≠ 0 → v i = 0 := fun i hi => by simp [v, hi]
  -- `C₀₀ > 0`
  have hC00 : 0 < C 0 0 := by
    have h0 : 0 ≤ C 0 0 := by
      have := hnn {0} v
      simpa [v] using this
    refine lt_of_le_of_ne h0 fun hz => ?_
    have hrow : ∀ k, C 0 k = 0 := fun k => by
      set w : ℕ → ℝ := fun i => if i = k then 1 else 0
      have hcs := quad_cs hCs hnn (range (k + 1)) v w
      have e1 : ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1), v i * C i j * w j = C 0 k := by
        rw [Finset.sum_eq_single 0 (fun i _ hi => by simp [v, hi]) (by simp)]
        rw [Finset.sum_eq_single k (fun j _ hj => by simp [w, hj]) (by simp)]
        simp [v, w]
      have e2 : ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1), v i * C i j * v j = C 0 0 := by
        rw [Finset.sum_eq_single 0 (fun i _ hi => by simp [v, hi]) (by simp)]
        rw [Finset.sum_eq_single 0 (fun j _ hj => by simp [v, hj]) (by simp)]
        simp [v]
      rw [e1, e2, ← hz, zero_mul] at hcs
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm hcs (sq_nonneg _))
    have h := ((hC 0).2 0).2
    simp only [if_true] at h
    have : ∀ k, ((if 0 = k then (1 : ℝ) else 0) + T 0 k) * C k 0 = 0 := fun k => by
      rw [hCs k 0, hrow k, mul_zero]
    simp only [this, tsum_zero] at h
    exact zero_ne_one h
  have hmem : v ∈ {v : ℕ → ℝ | Summable (fun i => v i ^ 2) ∧
      Summable (fun i => lam' i * v i ^ 2) ∧ v ≠ 0} := by
    refine ⟨summable_of_ne_finset_zero (s := {0}) fun i hi => ?_,
      summable_of_ne_finset_zero (s := {0}) fun i hi => ?_, fun h => ?_⟩
    · rw [hv i (by simpa using hi)]; ring
    · rw [hv i (by simpa using hi)]; ring
    · have := congrFun h 0; simp [v] at this
  have hQ : ∑' i, v i * ∑' j, C i j * v j = C 0 0 := by
    rw [tsum_eq_single 0 fun i hi => by rw [hv i hi, zero_mul],
      tsum_eq_single 0 fun j hj => by rw [hv j hj, mul_zero]]
    simp [v]
  refine lt_of_le_of_lt (iInf₂_le (f := fun v (_ : v ∈ {v : ℕ → ℝ | Summable (fun i => v i ^ 2) ∧
      Summable (fun i => lam' i * v i ^ 2) ∧ v ≠ 0}) =>
        ENNReal.ofReal (∑' i, lam' i * v i ^ 2) /
          ENNReal.ofReal (∑' i, v i * ∑' j, C i j * v j)) v hmem) ?_
  rw [hQ]
  exact ENNReal.div_lt_top ENNReal.ofReal_ne_top (by simpa using hC00)

end quad

section relax
variable {γ : Measure (ℕ → ℝ)} {C : ℕ → ℕ → ℝ} (hγ : IsCenteredGaussianCov γ C)
  (hS : ∀ N, (blockMat C N).PosSemidef) {lam' : ℕ → ℝ}
include hγ hS

omit hS in
theorem memLp_cyl (c : Cyl) : MemLp c.eval 2 γ := by
  have := hγ.1
  obtain ⟨B, hB⟩ := c.compact.exists_bound_of_continuous c.smooth.continuous
  exact MemLp.of_bound (c.smooth.continuous.comp (continuous_pi fun i =>
    continuous_apply _)).aestronglyMeasurable B (Eventually.of_forall fun z => hB _)

/-- **Poincaré on cylinder functions**: `Var_γ(φ) λ_G ≤ ℰ_∞(φ)`. -/
theorem var_mul_lamG_le_form (hnn : ∀ (s : Finset ℕ) (v : ℕ → ℝ),
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j) (c : Cyl) :
    var γ c.eval * lamG lam' C ≤ c.form lam' γ := by
  have := hγ.1
  set d : (ℕ → ℝ) → Fin c.J → ℝ := fun z k => fderiv ℝ c.φ (zBlock c.J z) (Pi.single k 1)
  have hdc : ∀ k : Fin c.J, Continuous fun x => fderiv ℝ c.φ x (Pi.single k 1) := fun k =>
    (c.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hzc : Continuous (zBlock c.J) := continuous_pi fun i => continuous_apply _
  set Qz : (ℕ → ℝ) → ℝ := fun z => ∑ k : Fin c.J, ∑ l : Fin c.J, C k l * d z k * d z l
  have hQc : Continuous Qz := continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
    (continuous_const.mul ((hdc k).comp hzc)).mul ((hdc l).comp hzc)
  have hQ0 : ∀ z, 0 ≤ Qz z := fun z => by
    have := hnn (range c.J) (extFin (d z))
    rwa [quad_range_extFin] at this
  -- `Qz` is bounded
  have hQb : ∃ K, ∀ z, |Qz z| ≤ K := by
    have hb : ∀ k : Fin c.J, ∃ K, ∀ x, ‖fderiv ℝ c.φ x (Pi.single k 1)‖ ≤ K := fun k =>
      ((c.compact.fderiv (𝕜 := ℝ)).comp_left (g := fun L : (Fin c.J → ℝ) →L[ℝ] ℝ =>
        L (Pi.single k 1)) (by simp)).exists_bound_of_continuous (hdc k)
    choose K hK using hb
    refine ⟨∑ k : Fin c.J, ∑ l : Fin c.J, |C k l| * (|K k| * |K l|), fun z => ?_⟩
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ =>
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_))
    rw [abs_mul, abs_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ ?_ (abs_nonneg _) (abs_nonneg _))
      (abs_nonneg _)
    · exact ((hK k _).trans (le_abs_self _)) |> fun h => by rw [← Real.norm_eq_abs]; exact h
    · exact ((hK l _).trans (le_abs_self _)) |> fun h => by rw [← Real.norm_eq_abs]; exact h
  obtain ⟨K, hK⟩ := hQb
  have hQi : Integrable Qz γ := Integrable.of_bound hQc.aestronglyMeasurable K
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hK z)
  have hP := poincare_gamma_block hγ (hS c.J) c.smooth c.compact
  have hvar : var γ c.eval = ENNReal.ofReal (variance c.eval γ) :=
    ((memLp_cyl hγ c).ofReal_variance_eq).symm
  calc var γ c.eval * lamG lam' C = ENNReal.ofReal (variance c.eval γ) * lamG lam' C := by
        rw [hvar]
    _ ≤ ENNReal.ofReal (∫ z, Qz z ∂γ) * lamG lam' C := by
        gcongr
        exact hP
    _ = (∫⁻ z, ENNReal.ofReal (Qz z) ∂γ) * lamG lam' C := by
        rw [ofReal_integral_eq_lintegral_ofReal hQi (Eventually.of_forall hQ0)]
    _ = ∫⁻ z, ENNReal.ofReal (Qz z) * lamG lam' C ∂γ :=
        (lintegral_mul_const _ (ENNReal.measurable_ofReal.comp hQc.measurable)).symm
    _ ≤ ∫⁻ z, ENNReal.ofReal (∑ i : Fin c.J, lam' i * (fderiv ℝ c.φ (fun j => z j)
          (Pi.single i 1)) ^ 2) ∂γ :=
        lintegral_mono fun z => quad_mul_lamG_le (C := C) (d z)
    _ = c.form lam' γ := rfl

omit hγ hS in
theorem L2_inner_eq_integral_gen (f g : Lp ℝ 2 γ) : @inner ℝ _ _ f g = ∫ x, f x * g x ∂γ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [RCLike.inner_apply, conj_trivial]
  ring

omit hγ hS in
/-- The variance in terms of the `L²` inner product. -/
theorem var_eq_inner [IsProbabilityMeasure γ] {g : (ℕ → ℝ) → ℝ} (hg : MemLp g 2 γ) :
    var γ g = ENNReal.ofReal (@inner ℝ _ _ (hg.toLp g) (hg.toLp g) -
      (@inner ℝ _ _ ((memLp_const (1 : ℝ)).toLp (fun _ => (1 : ℝ)) : Lp ℝ 2 γ) (hg.toLp g)) ^ 2) := by
  show evariance g γ = _
  rw [← hg.ofReal_variance_eq, variance_eq_sub hg, L2_inner_eq_integral_gen,
    L2_inner_eq_integral_gen]
  congr 2
  · refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp] with x hx
    simp only [Pi.pow_apply, hx, sq]
  · congr 1
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp, (memLp_const (1 : ℝ)).coeFn_toLp (μ := γ) (p := 2)]
      with x hx h1
    rw [hx, h1, one_mul]

/-- **Gaussian Poincaré inequality** for `γ_∞`: `Var_γ f ≤ ℰ_∞(f)/λ_G` on `L²(γ)`. -/
theorem gaussian_poincare (hnn : ∀ (s : Finset ℕ) (v : ℕ → ℝ),
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j)
    (hpos : 0 < lamG lam' C) (htop : lamG lam' C < ⊤) :
    ∀ f : (ℕ → ℝ) → ℝ, MemLp f 2 γ → var γ f ≤ gaussForm lam' γ f / lamG lam' C := by
  have := hγ.1
  intro f hf
  rw [ENNReal.le_div_iff_mul_le (Or.inl hpos.ne') (Or.inl htop.ne)]
  unfold gaussForm
  refine le_iInf₂ fun u hu => ?_
  set one : Lp ℝ 2 γ := (memLp_const (1 : ℝ)).toLp (fun _ => (1 : ℝ))
  have hL : Tendsto (fun n => (memLp_cyl hγ (u n)).toLp (u n).eval) atTop (𝓝 (hf.toLp f)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => (u n).eval) (fun n => memLp_cyl hγ (u n)) f hf).2
      hu
  have hcont : Continuous fun x : Lp ℝ 2 γ => ENNReal.ofReal (@inner ℝ _ _ x x -
      (@inner ℝ _ _ one x) ^ 2) :=
    ENNReal.continuous_ofReal.comp ((continuous_id.inner continuous_id).sub
      ((continuous_const.inner continuous_id).pow 2))
  have hvar : Tendsto (fun n => var γ (u n).eval) atTop (𝓝 (var γ f)) := by
    rw [var_eq_inner hf]
    refine ((hcont.tendsto _).comp hL).congr fun n => ?_
    exact (var_eq_inner (memLp_cyl hγ (u n))).symm
  have hT : Tendsto (fun n => var γ (u n).eval * lamG lam' C) atTop
      (𝓝 (var γ f * lamG lam' C)) := ENNReal.Tendsto.mul_const hvar (Or.inr htop.ne)
  rw [← hT.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun n => var_mul_lamG_le_form hγ hS hnn (u n))

end relax

section main
variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **(8.10), Poincaré half**, for the concrete `γ_∞`, `ℰ_∞`, `λ_G` of Sections 6 and 8. -/
theorem gaussian_poincare_of_prop21 (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C) :
    ∀ f : (ℕ → ℝ) → ℝ, MemLp f 2 γ →
      var γ f ≤ gaussForm (lamShift lam) γ f / lamG (lamShift lam) C := by
  have h21 := prop21Conclusion_of_equilibrium (prop_equilibrium hd hyp hr) hμ
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  have hT := Tmat_symm hyp hμ he
  have hS' := (hasSum_Tmat_sq hyp hμ he).summable
  have hCs : ∀ i j, C i j = C j i := fun i j => C_symm_of_secOp hT hS' hσ0 hσ hC i j
  have hnn := quadC_nonneg hT hS' hσ0 hσ hC
  have hup := quadC_le hT hS' hσ0 hσ hC
  have hcol : ∀ j, Summable fun k => C k j ^ 2 := fun j => (hC j).1
  have hlam0 : 0 < lamShift lam 0 := ((ref_spectrum hd hyp hr hμ).2 e lam he).1 1 le_rfl
  have hmono : ∀ i, lamShift lam 0 ≤ lamShift lam i := fun i =>
    he.mono (by simp [lamShift] : 0 + 1 ≤ i + 1)
  exact gaussian_poincare hγ (fun N => blockMat_posSemidef_of_prop21 hyp hμ he h21 hC N) hnn
    (lamG_pos hσ0 hCs hnn hup hcol hlam0 hmono) (lamG_lt_top hCs hnn hC _)

/-- **(2.8): `λ_N^sym → λ_G`**, with the compactness property (2.5)–(2.7) as the only
hypothesis. -/
theorem lamSym_tendsto_of'' (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    (hcomp : CompactnessProperty' V W γ (gaussForm (lamShift lam) γ)) :
    lamG (lamShift lam) C ≤ liminf (fun N => lamSym V W N) atTop ∧
    limsup (fun N => lamSym V W N) atTop ≤ lamG (lamShift lam) C ∧
    Tendsto (fun N => lamSym V W N) atTop (𝓝 (lamG (lamShift lam) C)) :=
  lamSym_tendsto_of' hd hyp hr hμ he hC hγ hcomp
    (gaussian_poincare_of_prop21 hd hyp hr hμ he hC hγ)

end main

end SharpLSI
