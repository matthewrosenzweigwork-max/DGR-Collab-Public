import DGPS.Foundations.SobolevFourier

/-!
# FOU005: Compact torus form embedding

On the unit torus `𝕋^d` (Haar probability `m`):

* every `H¹`-bounded sequence (`‖uₙ‖₂² + ‖∇uₙ‖₂² ≤ M`, with `∇uₙ` the weak gradient) has an
  `L²`-strongly convergent subsequence;
* the omitted `L²` mass of a Euclidean Fourier cutoff is at most `‖∇u‖₂²/(4π²R²)`;
* for a measurable weight `0 < c ≤ w ≤ C < ∞` the same compactness holds for the weighted norms
  `∫ u² w dm + ∫ ‖∇u‖² w dm`, with convergence in `L²(w m)`.

Route (05_LEMMA_LEVEL_DAG FOU005): Fourier coefficients of a bounded sequence are bounded, so a
subsequence converges coefficientwise (Tychonoff on `∏ₖ closedBall 0 √M`, a first countable
space); the explicit tail bound `∑_{k ∉ box N} |ûₙ|² ≤ M/(4π²N²)` (from FOU004) upgrades this to
an `L²`-Cauchy subsequence; completeness of `L²` gives the limit.

Main results:
* `DGPS.exists_subseq_tendsto_sq_of_h1_bounded`: unweighted compactness.
* `DGPS.integral_sq_fourierCutoff_sub_le`: tail bound for the Euclidean cutoff.
* `DGPS.exists_subseq_tendsto_weighted_of_h1_bounded`: weighted compactness.
* `DGPS.Analysis.compact_torus_form_embedding`: the FOU005 bundle.
-/

open MeasureTheory Filter Topology
open scoped Real

namespace DGPS

variable {d : ℕ}

/-! ### Frequency boxes -/

/-- The finite cube of frequencies `|kⱼ| ≤ N`. -/
def freqBox (d N : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

theorem mem_freqBox {N : ℕ} {k : Fin d → ℤ} : k ∈ freqBox d N ↔ ∀ j, |k j| ≤ N := by
  simp [freqBox, Fintype.mem_piFinset, abs_le]

theorem four_pi_sq_mul_le_gradWeight {N : ℕ} {k : Fin d → ℤ} (hk : k ∉ freqBox d N) :
    4 * π ^ 2 * (N : ℝ) ^ 2 ≤ gradWeight k := by
  rw [mem_freqBox] at hk
  push Not at hk
  obtain ⟨j, hj⟩ := hk
  have h1 : (N : ℝ) ≤ |((k j : ℤ) : ℝ)| := by
    have : (N : ℤ) ≤ |k j| := hj.le
    have h := (Int.cast_le (R := ℝ)).mpr this
    simpa using h
  have h2 : (N : ℝ) ^ 2 ≤ ((k j : ℤ) : ℝ) ^ 2 := by
    rw [← sq_abs ((k j : ℤ) : ℝ)]
    exact pow_le_pow_left₀ (by positivity) h1 2
  have h3 : ((k j : ℤ) : ℝ) ^ 2 ≤ ∑ i, ((k i : ℤ) : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun i => ((k i : ℤ) : ℝ) ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
  unfold gradWeight
  have : 0 ≤ 4 * π ^ 2 := by positivity
  nlinarith

/-! ### Basic coefficient estimates -/

theorem norm_sq_fourierCoeff_le {u : Torus d → ℝ} (hu : MemLp u 2 (haar d)) (k : Fin d → ℤ) :
    ‖fourierCoeff u k‖ ^ 2 ≤ ∫ x, u x ^ 2 ∂haar d :=
  le_hasSum (hasSum_sq_fourierCoeff hu) k fun _ _ => by positivity

theorem fourierCoeff_sub' {u v : Torus d → ℝ} (hu : MemLp u 2 (haar d)) (hv : MemLp v 2 (haar d))
    (k : Fin d → ℤ) :
    fourierCoeff (fun x => u x - v x) k = fourierCoeff u k - fourierCoeff v k :=
  SharpLSI.cf_sub (hu.integrable one_le_two) (hv.integrable one_le_two) k

/-- Two `H¹` functions are `L²`-close up to a finite number of low modes and an explicit tail. -/
theorem integral_sq_sub_le {u v : Torus d → ℝ} {g h : Torus d → Tangent d}
    (hu : IsWeakGradient u g) (hv : IsWeakGradient v h) {N : ℕ} (hN : 0 < N) :
    ∫ x, (u x - v x) ^ 2 ∂haar d ≤
      ∑ k ∈ freqBox d N, ‖fourierCoeff u k - fourierCoeff v k‖ ^ 2 +
        2 / (4 * π ^ 2 * (N : ℝ) ^ 2) *
          (∫ x, ‖g x‖ ^ 2 ∂haar d + ∫ x, ‖h x‖ ^ 2 ∂haar d) := by
  have hc : 0 < 4 * π ^ 2 * (N : ℝ) ^ 2 := by positivity
  have hP := hasSum_sq_fourierCoeff (hu.memLp.sub hv.memLp)
  have hA := hasSum_gradWeight_weakGradient hu
  have hB := hasSum_gradWeight_weakGradient hv
  have hF1 : HasSum (fun k : Fin d → ℤ => if k ∈ freqBox d N then
      ‖fourierCoeff u k - fourierCoeff v k‖ ^ 2 else 0)
      (∑ k ∈ freqBox d N, ‖fourierCoeff u k - fourierCoeff v k‖ ^ 2) := by
    have := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _) (f := fun k : Fin d → ℤ => if k ∈ freqBox d N then
      ‖fourierCoeff u k - fourierCoeff v k‖ ^ 2 else 0) (s := freqBox d N)
      (fun k hk => by simp [hk])
    convert this using 1
    exact Finset.sum_congr rfl fun k hk => by simp [hk]
  have hF2 := (hA.add hB).mul_left (2 / (4 * π ^ 2 * (N : ℝ) ^ 2))
  have hF := hF1.add hF2
  refine hasSum_le (fun k => ?_) hP hF
  show ‖fourierCoeff (fun x => u x - v x) k‖ ^ 2 ≤ _
  rw [fourierCoeff_sub' hu.memLp hv.memLp]
  have hgw : 0 ≤ gradWeight k := by unfold gradWeight; positivity
  by_cases hk : k ∈ freqBox d N
  · simp only [hk, ite_true]
    have : 0 ≤ 2 / (4 * π ^ 2 * (N : ℝ) ^ 2) *
        (gradWeight k * ‖fourierCoeff u k‖ ^ 2 + gradWeight k * ‖fourierCoeff v k‖ ^ 2) := by
      positivity
    linarith
  · simp only [hk, ite_false, zero_add]
    have hge := four_pi_sq_mul_le_gradWeight hk
    set p := ‖fourierCoeff u k‖ ^ 2
    set q := ‖fourierCoeff v k‖ ^ 2
    have hp : 0 ≤ p := by positivity
    have hq : 0 ≤ q := by positivity
    have h1 : ‖fourierCoeff u k - fourierCoeff v k‖ ^ 2 ≤ 2 * (p + q) := by
      have := norm_sub_le (fourierCoeff u k) (fourierCoeff v k)
      have h0 := norm_nonneg (fourierCoeff u k - fourierCoeff v k)
      have : ‖fourierCoeff u k - fourierCoeff v k‖ ^ 2 ≤
          (‖fourierCoeff u k‖ + ‖fourierCoeff v k‖) ^ 2 := pow_le_pow_left₀ h0 this 2
      nlinarith [sq_nonneg (‖fourierCoeff u k‖ - ‖fourierCoeff v k‖)]
    have h2 : 2 * (p + q) ≤ 2 / (4 * π ^ 2 * (N : ℝ) ^ 2) * (gradWeight k * p + gradWeight k * q) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      nlinarith
    linarith

/-! ### Compactness of the unweighted `H¹` ball in `L²` -/

theorem norm_sq_toLp_sub {f g : Torus d → ℝ} (hf : MemLp f 2 (haar d)) (hg : MemLp g 2 (haar d)) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, (f x - g x) ^ 2 ∂haar d := by
  rw [← MemLp.toLp_sub, ← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(hf.sub hg).coeFn_toLp] with x hx
  simp [hx, sq]

/-- FOU005 (unweighted): an `H¹`-bounded sequence has an `L²`-convergent subsequence. -/
theorem exists_subseq_tendsto_sq_of_h1_bounded (u : ℕ → Torus d → ℝ) (g : ℕ → Torus d → Tangent d)
    (M : ℝ) (hg : ∀ n, IsWeakGradient (u n) (g n))
    (hM : ∀ n, ∫ x, u n x ^ 2 ∂haar d + ∫ x, ‖g n x‖ ^ 2 ∂haar d ≤ M) :
    ∃ (φ : ℕ → ℕ) (v : Torus d → ℝ), StrictMono φ ∧ MemLp v 2 (haar d) ∧
      Tendsto (fun n => ∫ x, (u (φ n) x - v x) ^ 2 ∂haar d) atTop (𝓝 0) := by
  have hu0 : ∀ n, 0 ≤ ∫ x, u n x ^ 2 ∂haar d := fun n => integral_nonneg fun _ => sq_nonneg _
  have hg0 : ∀ n, 0 ≤ ∫ x, ‖g n x‖ ^ 2 ∂haar d := fun n => integral_nonneg fun _ => by positivity
  have hM0 : 0 ≤ M := (add_nonneg (hu0 0) (hg0 0)).trans (hM 0)
  have hEn : ∀ n, ∫ x, ‖g n x‖ ^ 2 ∂haar d ≤ M := fun n => by linarith [hM n, hu0 n]
  -- coefficientwise convergent subsequence
  let K : Set ((Fin d → ℤ) → ℂ) := Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) (Real.sqrt M)
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hx : ∀ n, (fun k => fourierCoeff (u n) k) ∈ K := by
    intro n k _
    rw [mem_closedBall_zero_iff]
    refine Real.le_sqrt_of_sq_le ?_
    exact (norm_sq_fourierCoeff_le (hg n).memLp k).trans (by linarith [hM n, hg0 n])
  obtain ⟨c, -, φ, hφ, hc⟩ := hK.tendsto_subseq hx
  have hck : ∀ k, Tendsto (fun n => fourierCoeff (u (φ n)) k) atTop (𝓝 (c k)) :=
    fun k => tendsto_pi_nhds.mp hc k
  -- Cauchy in `L²`
  let U : ℕ → Lp ℝ 2 (haar d) := fun n => (hg (φ n)).memLp.toLp (u (φ n))
  have hcauchy : ∀ ε > 0, ∃ N0, ∀ n ≥ N0, ∀ m ≥ N0,
      ∫ x, (u (φ n) x - u (φ m) x) ^ 2 ∂haar d < ε := by
    intro ε hε
    obtain ⟨N', hN'⟩ := exists_nat_gt (2 * M / (π ^ 2 * ε))
    set N : ℕ := N' + 1 with hNdef
    have hNpos : 0 < N := Nat.succ_pos _
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
    have hNgt : 2 * M / (π ^ 2 * ε) < N := by
      have : (N' : ℝ) < N := by simp [hNdef]
      linarith
    have hpe : 0 < π ^ 2 * ε := by positivity
    have htail : 2 / (4 * π ^ 2 * (N : ℝ) ^ 2) * (M + M) < ε / 2 := by
      have h1 : 2 * M < N * (π ^ 2 * ε) := (div_lt_iff₀ hpe).mp hNgt
      have h2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      have hc : 0 < 4 * π ^ 2 * (N : ℝ) ^ 2 := by positivity
      rw [div_mul_eq_mul_div, div_lt_iff₀ hc]
      have h3 : (N : ℝ) * (π ^ 2 * ε) ≤ (N : ℝ) ^ 2 * (π ^ 2 * ε) :=
        mul_le_mul_of_nonneg_right h2 hpe.le
      nlinarith
    have hT : Tendsto (fun p : ℕ × ℕ => ∑ k ∈ freqBox d N,
        ‖fourierCoeff (u (φ p.1)) k - fourierCoeff (u (φ p.2)) k‖ ^ 2) atTop (𝓝 0) := by
      rw [← Filter.prod_atTop_atTop_eq]
      have hk : ∀ k ∈ freqBox d N, Tendsto (fun p : ℕ × ℕ =>
          ‖fourierCoeff (u (φ p.1)) k - fourierCoeff (u (φ p.2)) k‖ ^ 2)
          (atTop ×ˢ atTop) (𝓝 0) := by
        intro k _
        have h1 := (hck k).comp (tendsto_fst (f := (atTop : Filter ℕ)) (g := (atTop : Filter ℕ)))
        have h2 := (hck k).comp (tendsto_snd (f := (atTop : Filter ℕ)) (g := (atTop : Filter ℕ)))
        have := ((h1.sub h2).norm).pow 2
        simpa using this
      simpa using tendsto_finsetSum (freqBox d N) hk
    have hev := (hT.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity)))
    rw [Filter.eventually_atTop] at hev
    obtain ⟨⟨a, b⟩, hab⟩ := hev
    refine ⟨max a b, fun n hn m hm => ?_⟩
    have hlow := hab (n, m) ⟨(le_max_left a b).trans hn, (le_max_right a b).trans hm⟩
    have := integral_sq_sub_le (hg (φ n)) (hg (φ m)) hNpos
    have hs : ∫ x, ‖g (φ n) x‖ ^ 2 ∂haar d + ∫ x, ‖g (φ m) x‖ ^ 2 ∂haar d ≤ M + M :=
      add_le_add (hEn _) (hEn _)
    have hcpos : 0 ≤ 2 / (4 * π ^ 2 * (N : ℝ) ^ 2) := by positivity
    have := mul_le_mul_of_nonneg_left hs hcpos
    simp only at hlow
    linarith
  have hUc : CauchySeq U := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N0, hN0⟩ := hcauchy (ε ^ 2) (by positivity)
    refine ⟨N0, fun n hn m hm => ?_⟩
    rw [dist_eq_norm]
    have h := norm_sq_toLp_sub (hg (φ n)).memLp (hg (φ m)).memLp
    have h2 := hN0 n hn m hm
    have : ‖U n - U m‖ ^ 2 < ε ^ 2 := by
      show ‖(hg (φ n)).memLp.toLp (u (φ n)) - (hg (φ m)).memLp.toLp (u (φ m))‖ ^ 2 < _
      rw [h]; exact h2
    exact lt_of_pow_lt_pow_left₀ 2 hε.le this
  obtain ⟨V, hV⟩ := cauchySeq_tendsto_of_complete hUc
  refine ⟨φ, (V : Torus d → ℝ), hφ, Lp.memLp V, ?_⟩
  have hnorm : Tendsto (fun n => ‖U n - V‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hV)
  have hsq := hnorm.pow 2
  rw [zero_pow two_ne_zero] at hsq
  refine hsq.congr fun n => ?_
  have h := norm_sq_toLp_sub (hg (φ n)).memLp (Lp.memLp V)
  rw [Lp.toLp_coeFn] at h
  exact h

/-! ### The tail of the Euclidean cutoff -/

/-- The omitted `L²` mass of the Fourier cutoff retaining `|k| ≤ R` is at most
`‖∇u‖₂²/(4π²R²)`. -/
theorem integral_sq_fourierCutoff_sub_le {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hg : IsWeakGradient u g) {R : ℝ} (hR : 0 < R) :
    ∫ y, (fourierCutoff u R y - u y) ^ 2 ∂haar d ≤
      (∫ x, ‖g x‖ ^ 2 ∂haar d) / (4 * π ^ 2 * R ^ 2) := by
  have hc : 0 < 4 * π ^ 2 * R ^ 2 := by positivity
  rw [integral_sq_fourierCutoff_sub hg.memLp]
  have hB := (hasSum_gradWeight_weakGradient hg).div_const (4 * π ^ 2 * R ^ 2)
  have hle : ∀ k : Fin d → ℤ, (if InFreqBall R k then 0 else ‖fourierCoeff u k‖ ^ 2) ≤
      gradWeight k * ‖fourierCoeff u k‖ ^ 2 / (4 * π ^ 2 * R ^ 2) := by
    intro k
    by_cases hk : InFreqBall R k
    · simp only [hk, ite_true]
      have : 0 ≤ gradWeight k := by unfold gradWeight; positivity
      positivity
    · simp only [hk, ite_false]
      have h1 : R < Real.sqrt (∑ j, ((k j : ℤ) : ℝ) ^ 2) := not_le.mp hk
      have h2 : R ^ 2 < ∑ j, ((k j : ℤ) : ℝ) ^ 2 :=
        (Real.lt_sqrt hR.le).mp h1
      have h3 : 4 * π ^ 2 * R ^ 2 ≤ gradWeight k := by
        unfold gradWeight
        have : 0 ≤ 4 * π ^ 2 := by positivity
        nlinarith
      rw [le_div_iff₀ hc]
      nlinarith [sq_nonneg ‖fourierCoeff u k‖]
  have hsum : Summable fun k : Fin d → ℤ =>
      (if InFreqBall R k then 0 else ‖fourierCoeff u k‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) hle hB.summable
  exact hasSum_le hle hsum.hasSum hB

/-! ### Weighted version -/

section Weighted

variable {w : Torus d → ℝ} {c C : ℝ}

theorem integrable_mul_weight {ψ : Torus d → ℝ} (hψ : Integrable ψ (haar d))
    (hw : Measurable w) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) (hc : 0 < c) :
    Integrable (fun x => ψ x * w x) (haar d) := by
  refine Integrable.mono' (hψ.norm.const_mul C) (hψ.aestronglyMeasurable.mul hw.aestronglyMeasurable) ?_
  filter_upwards [hwb] with x hx
  have hw0 : 0 ≤ w x := hc.le.trans hx.1
  rw [norm_mul, Real.norm_of_nonneg hw0]
  exact (mul_le_mul_of_nonneg_left hx.2 (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem mul_integral_le_integral_mul_weight {ψ : Torus d → ℝ} (hψ : Integrable ψ (haar d))
    (hψ0 : ∀ x, 0 ≤ ψ x) (hw : Measurable w) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (hc : 0 < c) : c * ∫ x, ψ x ∂haar d ≤ ∫ x, ψ x * w x ∂haar d := by
  rw [← integral_const_mul]
  refine integral_mono_ae (hψ.const_mul c) (integrable_mul_weight hψ hw hwb hc) ?_
  filter_upwards [hwb] with x hx
  have := mul_le_mul_of_nonneg_left hx.1 (hψ0 x)
  linarith

theorem integral_mul_weight_le {ψ : Torus d → ℝ} (hψ : Integrable ψ (haar d))
    (hψ0 : ∀ x, 0 ≤ ψ x) (hw : Measurable w) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (hc : 0 < c) : ∫ x, ψ x * w x ∂haar d ≤ C * ∫ x, ψ x ∂haar d := by
  rw [← integral_const_mul]
  refine integral_mono_ae (integrable_mul_weight hψ hw hwb hc) (hψ.const_mul C) ?_
  filter_upwards [hwb] with x hx
  have := mul_le_mul_of_nonneg_left hx.2 (hψ0 x)
  linarith

/-- FOU005 (weighted): for a measurable weight `0 < c ≤ w ≤ C` (a.e.), a sequence with
`∫ u² w + ∫ ‖∇u‖² w` bounded has a subsequence converging in `L²(w m)`. -/
theorem exists_subseq_tendsto_weighted_of_h1_bounded (u : ℕ → Torus d → ℝ)
    (g : ℕ → Torus d → Tangent d) (M : ℝ) (hw : Measurable w)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) (hc : 0 < c)
    (hg : ∀ n, IsWeakGradient (u n) (g n))
    (hM : ∀ n, ∫ x, u n x ^ 2 * w x ∂haar d + ∫ x, ‖g n x‖ ^ 2 * w x ∂haar d ≤ M) :
    ∃ (φ : ℕ → ℕ) (v : Torus d → ℝ), StrictMono φ ∧ MemLp v 2 (haar d) ∧
      Tendsto (fun n => ∫ x, (u (φ n) x - v x) ^ 2 * w x ∂haar d) atTop (𝓝 0) := by
  have hint : ∀ n, Integrable (fun x => u n x ^ 2) (haar d) := fun n => (hg n).memLp.integrable_sq
  have hintg : ∀ n, Integrable (fun x => ‖g n x‖ ^ 2) (haar d) := fun n =>
    (memLp_two_iff_integrable_sq_norm (hg n).memLp_grad.aestronglyMeasurable).mp (hg n).memLp_grad
  have hbound : ∀ n, ∫ x, u n x ^ 2 ∂haar d + ∫ x, ‖g n x‖ ^ 2 ∂haar d ≤ M / c := by
    intro n
    rw [le_div_iff₀ hc]
    have h1 := mul_integral_le_integral_mul_weight (hint n) (fun x => sq_nonneg _) hw hwb hc
    have h2 := mul_integral_le_integral_mul_weight (hintg n) (fun x => by positivity) hw hwb hc
    have := hM n
    linarith
  obtain ⟨φ, v, hφ, hv, hT⟩ := exists_subseq_tendsto_sq_of_h1_bounded u g (M / c) hg hbound
  refine ⟨φ, v, hφ, hv, ?_⟩
  have hT' : Tendsto (fun n => C * ∫ x, (u (φ n) x - v x) ^ 2 ∂haar d) atTop (𝓝 0) := by
    simpa using hT.const_mul C
  refine squeeze_zero (fun n => integral_nonneg_of_ae ?_) (fun n => ?_) hT'
  · filter_upwards [hwb] with x hx
    have hw0 : 0 ≤ w x := hc.le.trans hx.1
    positivity
  · exact integral_mul_weight_le (((hg (φ n)).memLp.sub hv).integrable_sq)
      (fun x => sq_nonneg _) hw hwb hc

end Weighted

end DGPS

namespace DGPS.Analysis

open DGPS

/-- FOU005: compact torus form embedding. On the unit torus `𝕋^d`:
(1) every `H¹`-bounded sequence has an `L²`-strongly convergent subsequence;
(2) the omitted `L²` mass of the Fourier cutoff retaining `|k| ≤ R` is at most
`‖∇u‖₂²/(4π²R²)`;
(3) for a measurable weight `0 < c ≤ w ≤ C < ∞` the same compactness holds for the weighted
`H¹`/`L²` norms, with convergence in `L²(w m)`. -/
theorem compact_torus_form_embedding (d : ℕ) :
    -- (1) unweighted compact embedding
    (∀ (u : ℕ → Torus d → ℝ) (g : ℕ → Torus d → Tangent d) (M : ℝ),
      (∀ n, IsWeakGradient (u n) (g n)) →
      (∀ n, ∫ x, u n x ^ 2 ∂haar d + ∫ x, ‖g n x‖ ^ 2 ∂haar d ≤ M) →
      ∃ (φ : ℕ → ℕ) (v : Torus d → ℝ), StrictMono φ ∧ MemLp v 2 (haar d) ∧
        Tendsto (fun n => ∫ x, (u (φ n) x - v x) ^ 2 ∂haar d) atTop (𝓝 0)) ∧
    -- (2) explicit cutoff tail bound
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g → ∀ R : ℝ, 0 < R →
      ∫ y, (fourierCutoff u R y - u y) ^ 2 ∂haar d ≤
        (∫ x, ‖g x‖ ^ 2 ∂haar d) / (4 * π ^ 2 * R ^ 2)) ∧
    -- (3) weighted compact embedding for a fixed density `0 < c ≤ w ≤ C`
    (∀ (w : Torus d → ℝ) (c C : ℝ), Measurable w → 0 < c → (∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) →
      ∀ (u : ℕ → Torus d → ℝ) (g : ℕ → Torus d → Tangent d) (M : ℝ),
      (∀ n, IsWeakGradient (u n) (g n)) →
      (∀ n, ∫ x, u n x ^ 2 * w x ∂haar d + ∫ x, ‖g n x‖ ^ 2 * w x ∂haar d ≤ M) →
      ∃ (φ : ℕ → ℕ) (v : Torus d → ℝ), StrictMono φ ∧ MemLp v 2 (haar d) ∧
        Tendsto (fun n => ∫ x, (u (φ n) x - v x) ^ 2 * w x ∂haar d) atTop (𝓝 0)) :=
  ⟨fun u g M hg hM => exists_subseq_tendsto_sq_of_h1_bounded u g M hg hM,
    fun _ _ hg _ hR => integral_sq_fourierCutoff_sub_le hg hR,
    fun _ _ _ hw hc hwb u g M hg hM =>
      exists_subseq_tendsto_weighted_of_h1_bounded u g M hw hwb hc hg hM⟩

end DGPS.Analysis
