import SharpSymmetricLSI.Paper.GaussLaw4
import SharpSymmetricLSI.Defs.D18_GaussianForm

/-!
# (2.8) (lane s42): the constant `λ_G` is an infimum over finitely supported vectors

Abstract `ℓ²` facts about an infinite matrix `C` that is symmetric, with finite blocks
`0 ≤ ⟨v, C v⟩_s ≤ |v|²_s / σ` (Paper/GaussForm15 `quadC_nonneg`, `quadC_le`) and columns in `ℓ²`:
* Cauchy–Schwarz for the finite blocks (`quad_cs`);
* `‖C v‖_{ℓ²} ≤ ‖v‖_{ℓ²}/σ` (`Cv_sq_le`);
* `⟨v^{(n)}, C v^{(n)}⟩ → ⟨v, C v⟩` for the truncations `v^{(n)} = v 1_{[0,n)}` (`tendsto_Qv_vtr`);
* hence (`le_lamG_of_trunc`) a lower bound for every finite ratio
  `∑_{i<n} λ_i v_i² / ∑_{i,j<n} v_i C_{ij} v_j` is a lower bound for `λ_G = lamG` (8.9). The
  cases `⟨v, Cv⟩ = 0` (ratio `⊤`, as `∑ λ_i v_i² > 0` for `v ≠ 0`, `λ_i > 0`) are explicit.
-/

noncomputable section
open Filter Topology Finset
open scoped ENNReal

namespace SharpLSI

/-- The truncation `v 1_{[0,n)}`. -/
def vtr (v : ℕ → ℝ) (n : ℕ) : ℕ → ℝ := fun i => if i < n then v i else 0

/-- `(C v)_i = ∑_j C_{ij} v_j`. -/
def Cvec (C : ℕ → ℕ → ℝ) (v : ℕ → ℝ) (i : ℕ) : ℝ := ∑' j, C i j * v j

theorem vtr_eq_zero {v : ℕ → ℝ} {n i : ℕ} (hi : i ∉ range n) : vtr v n i = 0 := by
  simp only [vtr, mem_range] at hi ⊢; simp [hi]

theorem summable_sq_vtr {v : ℕ → ℝ} (n : ℕ) : Summable fun i => vtr v n i ^ 2 :=
  summable_of_ne_finset_zero (s := range n) fun i hi => by rw [vtr_eq_zero hi]; ring

theorem tendsto_tail_vtr {v : ℕ → ℝ} (hv : Summable fun i => v i ^ 2) :
    Tendsto (fun n => ∑' i, (v i - vtr v n i) ^ 2) atTop (𝓝 0) := by
  have e : ∀ n, ∑' i, (v i - vtr v n i) ^ 2 = ∑' k, v (k + n) ^ 2 := fun n => by
    have hs : Summable fun i => (v i - vtr v n i) ^ 2 := by
      refine hv.of_nonneg_of_le (fun _ => sq_nonneg _) fun i => ?_
      simp only [vtr]; split_ifs <;> simp [sq_nonneg]
    rw [← hs.sum_add_tsum_nat_add n]
    have h0 : ∑ i ∈ range n, (v i - vtr v n i) ^ 2 = 0 :=
      Finset.sum_eq_zero fun i hi => by
        simp only [vtr, mem_range] at hi ⊢; simp [hi]
    rw [h0, zero_add]
    refine tsum_congr fun k => ?_
    simp only [vtr]; rw [if_neg (by omega)]; ring
  simp_rw [e]
  exact tendsto_sum_nat_add fun k => v k ^ 2

section quad
variable {C : ℕ → ℕ → ℝ} {σ : ℝ} (hσ0 : 0 < σ) (hCs : ∀ i j, C i j = C j i)
  (hnn : ∀ (s : Finset ℕ) (v : ℕ → ℝ), 0 ≤ ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j)
  (hup : ∀ (s : Finset ℕ) (v : ℕ → ℝ),
    ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j ≤ (∑ i ∈ s, v i ^ 2) / σ)
  (hcol : ∀ j, Summable fun k => C k j ^ 2)

include hCs hnn in
/-- Cauchy–Schwarz for the finite blocks of `C`. -/
theorem quad_cs (s : Finset ℕ) (u w : ℕ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, u i * C i j * w j) ^ 2 ≤
      (∑ i ∈ s, ∑ j ∈ s, u i * C i j * u j) * ∑ i ∈ s, ∑ j ∈ s, w i * C i j * w j := by
  have hsym : ∑ i ∈ s, ∑ j ∈ s, w i * C i j * u j = ∑ i ∈ s, ∑ j ∈ s, u i * C i j * w j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hCs j i]; ring
  have key : ∀ t : ℝ, 0 ≤ (∑ i ∈ s, ∑ j ∈ s, w i * C i j * w j) * (t * t) +
      2 * (∑ i ∈ s, ∑ j ∈ s, u i * C i j * w j) * t + ∑ i ∈ s, ∑ j ∈ s, u i * C i j * u j := by
    intro t
    have h := hnn s (fun i => u i + t * w i)
    have e : ∀ i j, (u i + t * w i) * C i j * (u j + t * w j) =
        u i * C i j * u j + t * (u i * C i j * w j) + t * (w i * C i j * u j) +
          (t * t) * (w i * C i j * w j) := fun i j => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum] at h
    rw [hsym] at h
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith [this]

include hσ0 hCs hnn hup in
theorem quad_sq_le (s : Finset ℕ) (u w : ℕ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, u i * C i j * w j) ^ 2 ≤
      (∑ i ∈ s, u i ^ 2) * (∑ i ∈ s, w i ^ 2) / σ ^ 2 := by
  refine (quad_cs hCs hnn s u w).trans ?_
  have h1 := hup s u
  have h2 := hup s w
  have h3 : 0 ≤ (∑ i ∈ s, u i ^ 2) / σ := div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) hσ0.le
  calc (∑ i ∈ s, ∑ j ∈ s, u i * C i j * u j) * ∑ i ∈ s, ∑ j ∈ s, w i * C i j * w j
      ≤ (∑ i ∈ s, u i ^ 2) / σ * ((∑ i ∈ s, w i ^ 2) / σ) :=
        mul_le_mul h1 h2 (hnn s w) h3
    _ = _ := by field_simp

include hCs hcol in
theorem summable_row (i : ℕ) : Summable fun j => C i j ^ 2 :=
  (hcol i).congr fun k => by rw [hCs]

include hCs hcol in
theorem summable_Cvec_term {v : ℕ → ℝ} (hv : Summable fun i => v i ^ 2) (i : ℕ) :
    Summable fun j => C i j * v j :=
  (tsum_mul_sq_le (summable_row hCs hcol i) hv).1

omit hσ0 in
theorem Cvec_fin {x : ℕ → ℝ} {s : Finset ℕ} (hx : ∀ i ∉ s, x i = 0) (j : ℕ) :
    Cvec C x j = ∑ i ∈ s, C j i * x i :=
  tsum_eq_sum fun i hi => by rw [hx i hi, mul_zero]

include hσ0 hCs hnn hup in
/-- `‖C x‖² ≤ |x|²/σ²` for finitely supported `x`. -/
theorem Cvec_fin_sq_le {x : ℕ → ℝ} {s : Finset ℕ} (hx : ∀ i ∉ s, x i = 0) :
    Summable (fun j => Cvec C x j ^ 2) ∧
      ∑' j, Cvec C x j ^ 2 ≤ (∑ i ∈ s, x i ^ 2) / σ ^ 2 := by
  set X := ∑ i ∈ s, x i ^ 2
  have hN : ∀ N, ∑ j ∈ range N, Cvec C x j ^ 2 ≤ X / σ ^ 2 := by
    intro N
    set S := ∑ j ∈ range N, Cvec C x j ^ 2
    set U := range N ∪ s
    set y : ℕ → ℝ := fun j => if j ∈ range N then Cvec C x j else 0
    have hy : ∀ j ∉ range N, y j = 0 := fun j hj => if_neg hj
    have hxU : ∀ j, ∑ i ∈ U, C j i * x i = Cvec C x j := fun j => by
      rw [Cvec_fin hx j]
      exact (Finset.sum_subset Finset.subset_union_right fun i _ hi => by
        rw [hx i hi, mul_zero]).symm
    have hQ : ∑ i ∈ U, ∑ j ∈ U, y i * C i j * x j = S := by
      have e1 : ∀ i, ∑ j ∈ U, y i * C i j * x j = y i * Cvec C x i := fun i => by
        rw [← hxU i, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      simp_rw [e1]
      rw [← Finset.sum_subset Finset.subset_union_left fun i _ hi => by rw [hy i hi, zero_mul]]
      exact Finset.sum_congr rfl fun i hi => by rw [show y i = Cvec C x i from if_pos hi, sq]
    have hYU : ∑ i ∈ U, y i ^ 2 = S := by
      rw [← Finset.sum_subset Finset.subset_union_left fun i _ hi => by rw [hy i hi]; ring]
      exact Finset.sum_congr rfl fun i hi => by rw [show y i = Cvec C x i from if_pos hi]
    have hXU : ∑ i ∈ U, x i ^ 2 = X :=
      (Finset.sum_subset Finset.subset_union_right fun i _ hi => by rw [hx i hi]; ring).symm
    have h := quad_sq_le hσ0 hCs hnn hup U y x
    rw [hQ, hYU, hXU] at h
    have hS0 : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
    rcases hS0.eq_or_lt with h0 | h0
    · rw [← h0]; exact div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
    · have : S * S ≤ S * (X / σ ^ 2) := by rw [mul_div_assoc'] ; nlinarith [h]
      exact le_of_mul_le_mul_left this h0
  have hs : Summable fun j => Cvec C x j ^ 2 :=
    summable_of_sum_range_le (fun _ => sq_nonneg _) hN
  exact ⟨hs, Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _) hN⟩

include hσ0 hCs hnn hup hcol in
/-- **`‖C v‖² ≤ ‖v‖²/σ²`** for `v ∈ ℓ²`. -/
theorem Cv_sq_le {v : ℕ → ℝ} (hv : Summable fun i => v i ^ 2) :
    Summable (fun i => Cvec C v i ^ 2) ∧
      ∑' i, Cvec C v i ^ 2 ≤ (∑' i, v i ^ 2) / σ ^ 2 := by
  set Vs := ∑' i, v i ^ 2
  have hN : ∀ N, ∑ i ∈ range N, Cvec C v i ^ 2 ≤ Vs / σ ^ 2 := by
    intro N
    set B := ∑ i ∈ range N, Cvec C v i ^ 2
    set x : ℕ → ℝ := fun i => if i ∈ range N then Cvec C v i else 0
    have hx : ∀ i ∉ range N, x i = 0 := fun i hi => if_neg hi
    have hXB : ∑ i ∈ range N, x i ^ 2 = B := Finset.sum_congr rfl fun i hi => by
      rw [show x i = Cvec C v i from if_pos hi]
    obtain ⟨hCx, hCxle⟩ := Cvec_fin_sq_le hσ0 hCs hnn hup hx
    rw [hXB] at hCxle
    -- `B = ∑' j, (C x)_j v_j`
    have hB : B = ∑' j, Cvec C x j * v j := by
      have e1 : B = ∑ i ∈ range N, x i * Cvec C v i :=
        Finset.sum_congr rfl fun i hi => by rw [show x i = Cvec C v i from if_pos hi, sq]
      rw [e1]
      have e2 : ∀ i ∈ range N, x i * Cvec C v i = ∑' j, x i * (C i j * v j) := fun i _ => by
        unfold Cvec; rw [tsum_mul_left]
      rw [Finset.sum_congr rfl e2, ← Summable.tsum_finsetSum fun i _ =>
        (summable_Cvec_term hCs hcol hv i).mul_left (x i)]
      refine tsum_congr fun j => ?_
      rw [Cvec_fin hx j, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hCs i j]; ring
    obtain ⟨-, hcs⟩ := tsum_mul_sq_le hCx hv
    rw [← hB] at hcs
    have hB0 : 0 ≤ B := sum_nonneg fun _ _ => sq_nonneg _
    have h2 : B ^ 2 ≤ B / σ ^ 2 * Vs :=
      hcs.trans (mul_le_mul_of_nonneg_right hCxle (tsum_nonneg fun _ => sq_nonneg _))
    rcases hB0.eq_or_lt with h0 | h0
    · rw [← h0]; exact div_nonneg (tsum_nonneg fun _ => sq_nonneg _) (sq_nonneg _)
    · have : B * B ≤ B * (Vs / σ ^ 2) := by
        have e : B / σ ^ 2 * Vs = B * (Vs / σ ^ 2) := by ring
        nlinarith [h2, e]
      exact le_of_mul_le_mul_left this h0
  exact ⟨summable_of_sum_range_le (fun _ => sq_nonneg _) hN,
    Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _) hN⟩

include hCs hcol in
theorem Cvec_sub {v w : ℕ → ℝ} (hv : Summable fun i => v i ^ 2)
    (hw : Summable fun i => w i ^ 2) (i : ℕ) :
    Cvec C (fun j => v j - w j) i = Cvec C v i - Cvec C w i := by
  unfold Cvec
  rw [← (summable_Cvec_term hCs hcol hv i).tsum_sub (summable_Cvec_term hCs hcol hw i)]
  exact tsum_congr fun j => by ring

theorem summable_sq_sub {v w : ℕ → ℝ} (hv : Summable fun i => v i ^ 2)
    (hw : Summable fun i => w i ^ 2) : Summable fun i => (v i - w i) ^ 2 := by
  refine ((hv.add hw).mul_left 2).of_nonneg_of_le (fun _ => sq_nonneg _) fun i => ?_
  nlinarith [sq_nonneg (v i + w i)]

include hσ0 hCs hnn hup hcol in
/-- **`⟨v^{(n)}, C v^{(n)}⟩ → ⟨v, C v⟩`.** -/
theorem tendsto_Qv_vtr {v : ℕ → ℝ} (hv : Summable fun i => v i ^ 2) :
    Tendsto (fun n => ∑' i, vtr v n i * Cvec C (vtr v n) i) atTop
      (𝓝 (∑' i, v i * Cvec C v i)) := by
  obtain ⟨hCv, -⟩ := Cv_sq_le hσ0 hCs hnn hup hcol hv
  set Vs := ∑' i, v i ^ 2
  set K := Real.sqrt (∑' i, Cvec C v i ^ 2) + Real.sqrt Vs / σ
  set Tn : ℕ → ℝ := fun n => ∑' i, (v i - vtr v n i) ^ 2
  have hT := tendsto_tail_vtr hv
  have hbound : ∀ n, |∑' i, v i * Cvec C v i - ∑' i, vtr v n i * Cvec C (vtr v n) i| ≤
      K * Real.sqrt (Tn n) := by
    intro n
    have hvt := summable_sq_vtr (v := v) n
    have hd := summable_sq_sub hv hvt
    obtain ⟨hCvt, -⟩ := Cv_sq_le hσ0 hCs hnn hup hcol hvt
    obtain ⟨hCd, hCdle⟩ := Cv_sq_le hσ0 hCs hnn hup hcol hd
    obtain ⟨s1, cs1⟩ := tsum_mul_sq_le hd hCv
    obtain ⟨s2, cs2⟩ := tsum_mul_sq_le hvt hCd
    obtain ⟨s3, -⟩ := tsum_mul_sq_le hv hCv
    obtain ⟨s4, -⟩ := tsum_mul_sq_le hvt hCvt
    have hsplit : ∑' i, v i * Cvec C v i - ∑' i, vtr v n i * Cvec C (vtr v n) i =
        ∑' i, (v i - vtr v n i) * Cvec C v i +
          ∑' i, vtr v n i * Cvec C (fun j => v j - vtr v n j) i := by
      rw [← s3.tsum_sub s4, ← s1.tsum_add s2]
      refine tsum_congr fun i => ?_
      rw [Cvec_sub hCs hcol hv hvt]; ring
    rw [hsplit]
    have hvtle : ∑' i, vtr v n i ^ 2 ≤ Vs :=
      hvt.tsum_le_tsum (fun i => by simp only [vtr]; split_ifs <;> simp [sq_nonneg]) hv
    have e1 : |∑' i, (v i - vtr v n i) * Cvec C v i| ≤
        Real.sqrt (Tn n) * Real.sqrt (∑' i, Cvec C v i ^ 2) := by
      rw [← Real.sqrt_mul (tsum_nonneg fun _ => sq_nonneg _)]
      exact Real.abs_le_sqrt cs1
    have e2 : |∑' i, vtr v n i * Cvec C (fun j => v j - vtr v n j) i| ≤
        Real.sqrt (Tn n) * (Real.sqrt Vs / σ) := by
      have h3 : (∑' i, vtr v n i * Cvec C (fun j => v j - vtr v n j) i) ^ 2 ≤
          Vs * (Tn n / σ ^ 2) :=
        cs2.trans (mul_le_mul hvtle hCdle (tsum_nonneg fun _ => sq_nonneg _)
          (tsum_nonneg fun _ => sq_nonneg _))
      refine (Real.abs_le_sqrt h3).trans (le_of_eq ?_)
      rw [Real.sqrt_mul (tsum_nonneg fun _ => sq_nonneg _), Real.sqrt_div' _ (sq_nonneg σ),
        Real.sqrt_sq hσ0.le]
      ring
    calc _ ≤ |∑' i, (v i - vtr v n i) * Cvec C v i| +
          |∑' i, vtr v n i * Cvec C (fun j => v j - vtr v n j) i| := abs_add_le _ _
      _ ≤ _ := by
        have := add_le_add e1 e2
        linarith [this, show K * Real.sqrt (Tn n) = Real.sqrt (Tn n) * Real.sqrt
          (∑' i, Cvec C v i ^ 2) + Real.sqrt (Tn n) * (Real.sqrt Vs / σ) by ring]
  have hlim : Tendsto (fun n => K * Real.sqrt (Tn n)) atTop (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp hT).const_mul K
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact hbound n

omit hσ0 in
theorem Qv_vtr_eq (v : ℕ → ℝ) (n : ℕ) :
    ∑' i, vtr v n i * Cvec C (vtr v n) i =
      ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j := by
  rw [tsum_eq_sum (s := range n) fun i hi => by rw [vtr_eq_zero hi, zero_mul]]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Cvec_fin (fun j hj => vtr_eq_zero hj), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [vtr, mem_range] at hi hj ⊢
  rw [if_pos hi, if_pos hj]; ring

include hσ0 hCs hnn hup hcol in
/-- **A lower bound for all finite ratios is a lower bound for `λ_G`.** -/
theorem le_lamG_of_trunc {lam' : ℕ → ℝ} (hlam : ∀ i, 0 < lam' i) {x : ℝ≥0∞}
    (hx : ∀ (n : ℕ) (v : ℕ → ℝ), 0 < ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j →
      x ≤ ENNReal.ofReal (∑ i ∈ range n, lam' i * v i ^ 2) /
        ENNReal.ofReal (∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j)) :
    x ≤ lamG lam' C := by
  unfold lamG
  refine le_iInf₂ fun v hv => ?_
  obtain ⟨hv2, hvl, hv0⟩ := hv
  set L := ∑' i, lam' i * v i ^ 2
  set Q := ∑' i, v i * ∑' j, C i j * v j
  have hQe : Q = ∑' i, v i * Cvec C v i := rfl
  -- `L > 0`
  have hL : 0 < L := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h; push_neg at h; exact hv0 (funext h)
    exact hvl.tsum_pos (fun j => mul_nonneg (hlam j).le (sq_nonneg _)) i
      (mul_pos (hlam i) (by positivity))
  rcases le_or_gt Q 0 with hQ | hQ
  · rw [ENNReal.ofReal_of_nonpos hQ, ENNReal.div_zero (by simpa using hL)]
    exact le_top
  -- truncations
  have hQn := tendsto_Qv_vtr hσ0 hCs hnn hup hcol hv2
  rw [← hQe] at hQn
  simp_rw [Qv_vtr_eq] at hQn
  have hLn : Tendsto (fun n => ∑ i ∈ range n, lam' i * v i ^ 2) atTop (𝓝 L) :=
    hvl.hasSum.tendsto_sum_nat
  have hpos : ∀ᶠ n in atTop, 0 < ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j :=
    hQn.eventually (lt_mem_nhds hQ)
  have hratio : Tendsto (fun n => ENNReal.ofReal ((∑ i ∈ range n, lam' i * v i ^ 2) /
      ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j)) atTop (𝓝 (ENNReal.ofReal (L / Q))) :=
    ENNReal.tendsto_ofReal (hLn.div hQn hQ.ne')
  rw [← ENNReal.ofReal_div_of_pos hQ]
  refine ge_of_tendsto hratio ?_
  filter_upwards [hpos] with n hn
  rw [ENNReal.ofReal_div_of_pos hn]
  exact hx n v hn

end quad

end SharpLSI
