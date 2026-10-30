import DGPS.Lipschitz.T01RankRateConvergence
import DGPS.Lipschitz.T01CenteredDualGenerator
import SharpSymmetricLSI.Paper.FormLiminfS14c
import SharpSymmetricLSI.Paper.FormLiminfS4

/-!
# Centered cylinder-generator limits on the actual spectral witness

The Gaussian row passage uses the genuine covariance and the same finite-rank coefficients.
Particle mobility, residual force and joint-law estimates are kept tied to that witness.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction

namespace DGPS.Lipschitz
open KernelApproximation SharpLSI

set_option maxHeartbeats 1000000 in
/-- The actual covariance bound and matrix Hilbert--Schmidt convergence control Gaussian rows. -/
theorem t01_gaussian_row_approx {T C : ℕ → ℕ → ℝ} {σ : ℝ}
    (P : SharpLSI.FL.Rank3.SymPkg T C σ)
    (a : ℕ → ℕ → ℕ → ℝ)
    (hsum : ∀ R, Summable (fun p : ℕ × ℕ => (a R p.1 p.2 - T p.1 p.2) ^ 2))
    (hHS : Tendsto (fun R => ∑' p : ℕ × ℕ, (a R p.1 p.2 - T p.1 p.2) ^ 2)
      atTop (𝓝 0))
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable T γ i (Y i)) (i : ℕ) :
    Tendsto (fun R => limsup (fun n => ∫ z,
      (∑ q ∈ Finset.range n, a R i q * z q - Y i z) ^ 2 ∂γ) atTop) atTop (𝓝 0) := by
  haveI := hγ.1
  have hσ0 := P.pos
  have hnn := P.nn
  have hup := P.up
  set HS : ℕ → ℝ := fun R =>
    ∑' p : ℕ × ℕ, (a R p.1 p.2 - T p.1 p.2) ^ 2
  set w : ℕ → ℕ → ℝ := fun R q => a R i q - T i q
  -- the row is bounded by the Hilbert–Schmidt sum
  have hrow : ∀ R n, ∑ q ∈ range n, w R q ^ 2 ≤ HS R := fun R n => by
    set G : ℕ × ℕ → ℝ := fun p => (a R p.1 p.2 - T p.1 p.2) ^ 2 with hG
    set ι : ℕ → ℕ × ℕ := fun q => (i, q) with hι
    have hinj : Function.Injective ι := fun a b h => (Prod.mk.inj h).2
    have hg0 : ∀ p, 0 ≤ G p := fun _ => sq_nonneg _
    have hGs : Summable G := hsum R
    have hrs : Summable (G ∘ ι) := hGs.comp_injective hinj
    have hw : ∀ q, w R q ^ 2 = (G ∘ ι) q := fun q => rfl
    have h1 : ∑ q ∈ range n, (G ∘ ι) q ≤ ∑' q, (G ∘ ι) q :=
      hrs.sum_le_tsum _ fun q _ => hg0 (ι q)
    have h2 : ∑' q, (G ∘ ι) q ≤ ∑' p, G p := tsum_comp_le_tsum_of_inj hGs hg0 hinj
    simp only [hw]
    exact h1.trans h2
  -- the row-variable error
  obtain ⟨hYm, hYt⟩ := hY i
  set b : ℕ → (ℕ → ℝ) → ℝ := fun n z => (∑ q ∈ range n, T i q * z q) - Y i z
  have hbm : ∀ n, MemLp (b n) 2 γ := fun n => (memLp_linSum_gamma hγ (range n) _).sub hYm
  have hb : Tendsto (fun n => ∫ z, b n z ^ 2 ∂γ) atTop (𝓝 0) := by
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hYt
    have h2 := h1.pow 2
    simp only [Function.comp_def, ENNReal.toReal_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow] at h2
    exact h2.congr fun n => (integral_sq_eq_eLpNorm_sq (hbm n)).symm
  -- the bound for each `R, n`
  set f : ℕ → ℕ → ℝ := fun R n =>
    ∫ z, (∑ q ∈ range n, a R i q * z q - Y i z) ^ 2 ∂γ
  have hf0 : ∀ R n, 0 ≤ f R n := fun R n => integral_nonneg fun _ => sq_nonneg _
  have hfle : ∀ R n, f R n ≤ 2 * HS R / σ + 2 * ∫ z, b n z ^ 2 ∂γ := fun R n => by
    have hA := memLp_linSum_gamma hγ (range n) (w R)
    have hsplit : ∀ z, ∑ q ∈ range n, a R i q * z q - Y i z =
        ∑ q ∈ range n, w R q * z q + b n z := fun z => by
      simp only [w, b, sub_mul, Finset.sum_sub_distrib]; ring
    have hi1 : Integrable (fun z => (∑ q ∈ range n, w R q * z q + b n z) ^ 2) γ :=
      (hA.add (hbm n)).integrable_sq
    have hi2 : Integrable (fun z => 2 * (∑ q ∈ range n, w R q * z q) ^ 2 + 2 * b n z ^ 2) γ :=
      (hA.integrable_sq.const_mul 2).add ((hbm n).integrable_sq.const_mul 2)
    calc f R n = ∫ z, (∑ q ∈ range n, w R q * z q + b n z) ^ 2 ∂γ := by
          simp only [f]; congr 1; funext z; rw [hsplit]
      _ ≤ ∫ z, 2 * (∑ q ∈ range n, w R q * z q) ^ 2 + 2 * b n z ^ 2 ∂γ :=
          integral_mono hi1 hi2 fun z => by
            nlinarith [sq_nonneg (∑ q ∈ range n, w R q * z q - b n z)]
      _ = 2 * (∑ q ∈ range n, ∑ q' ∈ range n, w R q * C q q' * w R q') +
            2 * ∫ z, b n z ^ 2 ∂γ := by
          rw [integral_add (hA.integrable_sq.const_mul 2) ((hbm n).integrable_sq.const_mul 2),
            integral_const_mul, integral_const_mul,
            integral_linSum_sq_gamma hγ (range n) (w R) (hnn _ _)]
      _ ≤ 2 * HS R / σ + 2 * ∫ z, b n z ^ 2 ∂γ := by
          have h1 := hup (range n) (w R)
          have h2 : (∑ q ∈ range n, w R q ^ 2) / σ ≤ HS R / σ :=
            div_le_div_of_nonneg_right (hrow R n) hσ0.le
          have : 2 * (∑ q ∈ range n, ∑ q' ∈ range n, w R q * C q q' * w R q') ≤ 2 * HS R / σ := by
            rw [mul_div_assoc]; linarith
          linarith
  -- `limsup_n`
  have hlim : ∀ R, 0 ≤ limsup (f R) atTop ∧ limsup (f R) atTop ≤ 2 * HS R / σ := fun R => by
    have hg : Tendsto (fun n => 2 * HS R / σ + 2 * ∫ z, b n z ^ 2 ∂γ) atTop
        (𝓝 (2 * HS R / σ)) := by
      simpa using tendsto_const_nhds.add (hb.const_mul 2)
    have hbdd : IsBoundedUnder (· ≤ ·) atTop (f R) :=
      hg.isBoundedUnder_le.mono_le (Eventually.of_forall (hfle R))
    have hcob : IsCoboundedUnder (· ≤ ·) atTop (f R) :=
      isCoboundedUnder_le_of_le atTop (hf0 R)
    refine ⟨le_limsup_of_frequently_le (Frequently.of_forall (hf0 R)) hbdd, ?_⟩
    rw [← hg.limsup_eq]
    exact limsup_le_limsup (Eventually.of_forall (hfle R)) hcob hg.isBoundedUnder_le
  have hHS0 : Tendsto (fun R => 2 * HS R / σ) atTop (𝓝 0) := by
    simpa using (hHS.const_mul 2).div_const σ
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hHS0
    (fun R => (hlim R).1) fun R => (hlim R).2


/-- Bounded finite cylinder coefficients may be paired with the actual Gaussian row limit. -/
theorem t01_gaussian_row_pairing_tendsto {T C : ℕ → ℕ → ℝ} {σ : ℝ}
    (P : SharpLSI.FL.Rank3.SymPkg T C σ)
    (s : ℕ → Finset ℕ) (a : ℕ → ℕ → ℕ → ℝ)
    (hsupport : ∀ R i j, i ∉ s R ∨ j ∉ s R → a R i j = 0)
    (hsum : ∀ R, Summable (fun p : ℕ × ℕ => (a R p.1 p.2 - T p.1 p.2) ^ 2))
    (hHS : Tendsto (fun R => ∑' p : ℕ × ℕ, (a R p.1 p.2 - T p.1 p.2) ^ 2)
      atTop (𝓝 0))
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable T γ i (Y i))
    {F : (ℕ → ℝ) → ℝ} (hF : MemLp F 2 γ)
    {J : ℕ} (ψ : Fin J → (ℕ → ℝ) → ℝ) (hψm : ∀ i, Measurable (ψ i))
    {K : ℝ} (hψ : ∀ i z, |ψ i z| ≤ K) :
    Tendsto (fun R => ∫ z, F z * ∑ i : Fin J, ψ i z * ∑ p ∈ s R, ∑ q ∈ s R,
        a R p q * z q * (if p = (i : ℕ) then 1 else 0) ∂γ) atTop
      (𝓝 (∫ z, F z * ∑ i : Fin J, ψ i z * Y i z ∂γ)) := by
  haveI := hγ.1
  -- the finite rows
  set N : ℕ → ℕ := fun R => (s R).sup id + 1
  have hsN : ∀ R, s R ⊆ Finset.range (N R) := fun R q hq => by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hq)
  set S : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun R i z =>
    ∑ q ∈ Finset.range (N R), a R i q * z q
  -- the inner sum is the finite row, for every `n ≥ N R`
  have hrow : ∀ R (i : ℕ) n, N R ≤ n → ∀ z : ℕ → ℝ, ∑ q ∈ Finset.range n, a R i q * z q =
      ∑ p ∈ s R, ∑ q ∈ s R, a R p q * z q * (if p = i then 1 else 0) := fun R i n hn z => by
    have hsub : s R ⊆ Finset.range n := (hsN R).trans (Finset.range_subset_range.2 hn)
    rw [← Finset.sum_subset hsub (fun q _ hq => by rw [hsupport R i q (Or.inr hq), zero_mul])]
    by_cases hi : i ∈ s R
    · rw [Finset.sum_eq_single i (fun p _ hp => Finset.sum_eq_zero fun q _ => by
        rw [if_neg hp, mul_zero]) (fun h => absurd hi h)]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [if_pos rfl, mul_one]
    · rw [Finset.sum_eq_zero fun q hq => by rw [hsupport R i q (Or.inl hi), zero_mul]]
      exact (Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q _ => by
        rw [if_neg (fun (h : p = i) => hi (h ▸ hp)), mul_zero]).symm
  -- `L²` convergence of the rows
  have hconv : ∀ i : ℕ, Tendsto (fun R => ∫ z, (S R i z - Y i z) ^ 2 ∂γ) atTop (𝓝 0) := fun i => by
    have h := t01_gaussian_row_approx P a hsum hHS hγ hY i
    refine h.congr fun R => ?_
    have hev : (fun n => ∫ z, (∑ q ∈ Finset.range n, a R i q * z q - Y i z) ^ 2 ∂γ)
        =ᶠ[atTop] fun _ => ∫ z, (S R i z - Y i z) ^ 2 ∂γ := by
      filter_upwards [eventually_ge_atTop (N R)] with n hn
      congr 1; funext z
      simp only [S]
      rw [hrow R i n hn z, hrow R i (N R) le_rfl z]
    rw [limsup_congr hev, limsup_const]
  -- the bound for each `i`
  have hFψ : ∀ i : Fin J, MemLp (fun z => F z * ψ i z) 2 γ := fun i => by
    refine (hF.norm.const_mul K).of_le (hF.aestronglyMeasurable.mul (hψm i).aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (hψ i z)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤
      K * ‖F z‖), Real.norm_eq_abs, mul_comm K]
    exact mul_le_mul_of_nonneg_left (hψ i z) (abs_nonneg _)
  have hSm : ∀ R i, MemLp (S R i) 2 γ := fun R i => memLp_linSum_gamma hγ _ _
  have hDm : ∀ R (i : ℕ), MemLp (fun z => S R i z - Y i z) 2 γ := fun R i =>
    (hSm R i).sub (hY i).1
  have hint : ∀ (G : ℕ → (ℕ → ℝ) → ℝ), (∀ i, MemLp (G i) 2 γ) →
      ∫ z, F z * ∑ i : Fin J, ψ i z * G i z ∂γ = ∑ i : Fin J, ∫ z, (F z * ψ i z) * G i z ∂γ :=
    fun G hG => by
      rw [← integral_finsetSum (f := fun (i : Fin J) z => (F z * ψ i z) * G i z) _ fun i _ =>
        (hFψ i).integrable_mul (hG i)]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  -- rewrite the sequence
  have hseq : ∀ R, ∫ z, F z * ∑ i : Fin J, ψ i z * ∑ p ∈ s R, ∑ q ∈ s R,
      a R p q * z q * (if p = (i : ℕ) then 1 else 0) ∂γ =
        ∑ i : Fin J, ∫ z, (F z * ψ i z) * S R i z ∂γ := fun R => by
    rw [← hint (fun i => S R i) (hSm R)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [S]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrow R i (N R) le_rfl z]
  simp only [hseq]
  rw [hint Y fun i => (hY i).1]
  refine tendsto_finsetSum _ fun i _ => ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbd : ∀ R, ‖∫ z, (F z * ψ i z) * S R i z ∂γ - ∫ z, (F z * ψ i z) * Y i z ∂γ‖ ≤
      (eLpNorm (fun z => F z * ψ i z) 2 γ).toReal * √(∫ z, (S R i z - Y i z) ^ 2 ∂γ) := fun R => by
    rw [← integral_sub (f := fun z => (F z * ψ i z) * S R i z) (g := fun z => (F z * ψ i z) * Y i z)
      ((hFψ i).integrable_mul (hSm R i)) ((hFψ i).integrable_mul (hY i).1), Real.norm_eq_abs]
    have e1 : (fun z => F z * ψ i z * S R i z - F z * ψ i z * Y i z) =
        fun z => (F z * ψ i z) * (S R i z - Y i z) := by funext z; ring
    rw [e1]
    refine (abs_integral_mul_le_L2 (hFψ i) (hDm R i)).trans (le_of_eq ?_)
    rw [eLpNorm_two_eq_sqrt_gamma (hDm R i), ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  refine squeeze_zero (fun _ => norm_nonneg _) hbd ?_
  have := ((hconv i).sqrt).const_mul (eLpNorm (fun z => F z * ψ i z) 2 γ).toReal
  simpa using this


/-- The Gaussian finite-rank cylinder generators converge under the actual covariance bound. -/
theorem t01_gaussian_crossH_tendsto {T C : ℕ → ℕ → ℝ} {σ : ℝ}
    (P : SharpLSI.FL.Rank3.SymPkg T C σ) (lam : ℕ → ℝ)
    (s : ℕ → Finset ℕ) (a : ℕ → ℕ → ℕ → ℝ)
    (hsupport : ∀ R i j, i ∉ s R ∨ j ∉ s R → a R i j = 0)
    (hsum : ∀ R, Summable (fun p : ℕ × ℕ => (a R p.1 p.2 - T p.1 p.2) ^ 2))
    (hHS : Tendsto (fun R => ∑' p : ℕ × ℕ, (a R p.1 p.2 - T p.1 p.2) ^ 2)
      atTop (𝓝 0))
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable T γ i (Y i))
    {F : (ℕ → ℝ) → ℝ} (hF : MemLp F 2 γ)
    (c : Cyl) {J' : ℕ → ℕ} (hJ : ∀ R, c.J ≤ J' R)
    (hsJ : ∀ R, ∀ q ∈ s R, q < J' R) :
    Tendsto (fun R => ∫ z, F z * crossH lam c (s R) (a R) (hJ R)
      (fun n : Fin (J' R) => z n) ∂γ) atTop
      (𝓝 (∫ z, F z * (-(c.gen (lamShift lam) Y z)) ∂γ)) := by
  haveI := hγ.1
  set ψ' : Fin c.J → (ℕ → ℝ) → ℝ := fun i z => lamShift lam i * cylD c i (fun j => z j)
  have hψK : ∀ i : Fin c.J, ∃ K, 0 ≤ K ∧ ∀ w, |cylD c i w| ≤ K := fun i =>
    exists_bound_of_compact (contDiff_cylD c i).continuous (hasCompactSupport_cylD c i)
  choose Kc hKc0 hKc using hψK
  set K : ℝ := ∑ i : Fin c.J, |lamShift lam i| * Kc i
  have hψb : ∀ i z, |ψ' i z| ≤ K := fun i z => by
    simp only [ψ', abs_mul]
    exact (mul_le_mul_of_nonneg_left (hKc i _) (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun i : Fin c.J => |lamShift lam i| * Kc i)
        (fun i _ => mul_nonneg (abs_nonneg _) (hKc0 i)) (Finset.mem_univ i))
  have hψm : ∀ i, Measurable (ψ' i) := fun i =>
    measurable_const.mul ((contDiff_cylD c i).continuous.measurable.comp
      (measurable_pi_iff.2 fun j => measurable_pi_apply _))
  have hrow := t01_gaussian_row_pairing_tendsto P s a hsupport hsum hHS hγ hY hF ψ' hψm hψb
  set G : ℕ → (ℕ → ℝ) → ℝ := fun R z => ∑ i : Fin c.J, ψ' i z * ∑ p ∈ s R, ∑ q ∈ s R,
    a R p q * z q * (if p = (i : ℕ) then 1 else 0)
  -- pointwise splitting
  have hpt : ∀ R z, crossH lam c (s R) (a R) (hJ R) (fun n : Fin (J' R) => z n) =
      crossH1 lam c (fun j => z j) + G R z := fun R z => by
    unfold crossH crossH2
    rw [projJ_coe]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ψ', Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
    rw [extN_coe z (hsJ R q hq)]
    split_ifs <;> ring
  have hH1 := memLp_crossH1 hγ lam c
  have hGL : ∀ R, MemLp (G R) 2 γ := fun R =>
    memLp_finsetSum (ε' := ℝ) _ fun i _ => by
      refine MemLp.of_le (g := fun z => K * ∑ p ∈ s R, ∑ q ∈ s R,
          a R p q * z q * (if p = (i : ℕ) then 1 else 0)) ?_
        ((hψm i).aestronglyMeasurable.mul ?_) (Eventually.of_forall fun z => ?_)
      · exact (memLp_finsetSum (ε' := ℝ) _ fun p _ => memLp_finsetSum (ε' := ℝ) _ fun q _ =>
          ((memLp_coord_gamma hγ q).const_mul (a R p q)).mul_const _).const_mul K
      · exact (Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun q _ =>
          ((measurable_pi_apply q).const_mul _).mul_const _).aestronglyMeasurable
      · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul (ψ' i z), abs_mul K]
        exact mul_le_mul_of_nonneg_right ((hψb i z).trans (le_abs_self K)) (abs_nonneg _)
  have hYL : MemLp (fun z => ∑ i : Fin c.J, ψ' i z * Y i z) 2 γ :=
    memLp_finsetSum (ε' := ℝ) _ fun i _ => by
      refine MemLp.of_le ((hY i).1.const_mul K) ((hψm i).aestronglyMeasurable.mul
        (hY i).1.aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul (ψ' i z), abs_mul K]
      exact mul_le_mul_of_nonneg_right ((hψb i z).trans (le_abs_self K)) (abs_nonneg _)
  -- the integrals
  have hsplit : ∀ R, ∫ z, F z * crossH lam c (s R) (a R) (hJ R) (fun n : Fin (J' R) => z n) ∂γ =
      ∫ z, F z * crossH1 lam c (fun j => z j) ∂γ + ∫ z, F z * G R z ∂γ := fun R => by
    rw [← integral_add (f := fun z => F z * crossH1 lam c (fun j => z j)) (g := fun z => F z * G R z)
      (hF.integrable_mul hH1) (hF.integrable_mul (hGL R))]
    exact integral_congr_ae (Eventually.of_forall fun z => by simp only [hpt, mul_add])
  have hlim : ∫ z, F z * (-(c.gen (lamShift lam) Y z)) ∂γ =
      ∫ z, F z * crossH1 lam c (fun j => z j) ∂γ + ∫ z, F z * ∑ i : Fin c.J, ψ' i z * Y i z ∂γ := by
    rw [← integral_add (f := fun z => F z * crossH1 lam c (fun j => z j))
      (g := fun z => F z * ∑ i : Fin c.J, ψ' i z * Y i z) (hF.integrable_mul hH1)
      (hF.integrable_mul hYL)]
    exact integral_congr_ae (Eventually.of_forall fun z => by
      simp only [neg_gen_eq, mul_add, ψ'])
  simp_rw [hsplit]
  rw [hlim]
  exact tendsto_const_nhds.add hrow

/-- Hilbert--Schmidt convergence of the actual retained smoothing coefficients. -/
theorem t01_actual_coefficient_HS {d : ℕ} (S : Spec d)
    (A : InteractionData d) (D : KData d) (hD : D.K = centeredKernel A S.mu)
    (t : ℕ → ℝ) (m : ℕ → ℕ) (ht : ∀ R, 0 ≤ t R)
    (htlim : Tendsto t atTop (𝓝 0)) (hm : StrictMono m)
    (F : SharpLSI.FL.FiniteRankApprox A.W S.mu S.v)
    (ha : ∀ R i j, F.a R i j = positiveKernelCoefficient S D (t R) (m R) i j) :
    (∀ R, Summable (fun p : ℕ × ℕ =>
      (F.a R p.1 p.2 - SharpLSI.Tmat A.W S.mu S.v p.1 p.2) ^ 2)) ∧
    Tendsto (fun R => ∑' p : ℕ × ℕ,
      (F.a R p.1 p.2 - SharpLSI.Tmat A.W S.mu S.v p.1 p.2) ^ 2) atTop (𝓝 0) := by
  let T := SharpLSI.Tmat A.W S.mu S.v
  let q (R : ℕ) (p : ℕ × ℕ) := (F.a R p.1 p.2 - T p.1 p.2) ^ 2
  have hsT := t01_shifted_pair_summable (fun p : ℕ × ℕ => TK S D.K p.1 p.2 ^ 2)
    (hasSum_prod_sq S D).summable
  have hqeq : ∀ R p, q R p =
      (kernelCoefficient_LIP016 S D (t R) (m R) (p.1 + 1) (p.2 + 1) -
        TK S D.K (p.1 + 1) (p.2 + 1)) ^ 2 := by
    intro R p
    dsimp only [q, T]
    rw [t01_Tmat_eq_TK S D A hD, ha, positiveKernelCoefficient_eq_shift]
  have hqbound : ∀ R p, q R p ≤ TK S D.K (p.1 + 1) (p.2 + 1) ^ 2 := by
    intro R p
    rw [hqeq]
    exact kernelCoefficient_error_le_LIP016 S D (ht R) (m R) (p.1 + 1) (p.2 + 1)
  have hqs : ∀ R, Summable (q R) := fun R =>
    Summable.of_nonneg_of_le (fun p => sq_nonneg _) (hqbound R) hsT
  have hq : Tendsto (fun R => ∑' p, q R p) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence hsT (f := q) (g := fun _ => (0 : ℝ))
      (fun p => by
        simp_rw [hqeq]
        simpa only [sub_self, zero_pow (by norm_num : 2 ≠ 0)] using
          ((kernelCoefficient_tendsto_LIP016 S D t m htlim hm (p.1 + 1) (p.2 + 1)).sub_const
            (TK S D.K (p.1 + 1) (p.2 + 1))).pow 2)
      (Eventually.of_forall fun R p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hqbound R p)
    simpa only [tsum_zero] using h
  exact ⟨hqs, hq⟩

/-- The Gaussian rank limit for the same actual interaction, covariance and spectral smoothing. -/
theorem t01_actual_gaussian_crossH_tendsto {d : ℕ} (S : Spec d) (aux : Aux S)
    (A : InteractionData d) (D : KData d) (hD : D.K = centeredKernel A S.mu)
    {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ inner ℝ g (DGPS.densityHessian A (specProbability_LIP016 S) g))
    (t : ℕ → ℝ) (m : ℕ → ℕ) (ht : ∀ R, 0 ≤ t R)
    (htlim : Tendsto t atTop (𝓝 0)) (hm : StrictMono m)
    (F : SharpLSI.FL.FiniteRankApprox A.W S.mu S.v)
    (ha : ∀ R i j, F.a R i j = positiveKernelCoefficient S D (t R) (m R) i j)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ (t01CovarianceMatrix S A))
    {Y : ℕ → (ℕ → ℝ) → ℝ}
    (hY : ∀ i, IsRowVariable (SharpLSI.Tmat A.W S.mu S.v) γ i (Y i))
    {f : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 γ)
    (c : Cyl) {J' : ℕ → ℕ} (hJ : ∀ R, c.J ≤ J' R)
    (hsJ : ∀ R, ∀ q ∈ F.s R, q < J' R) :
    Tendsto (fun R => ∫ z, f z * crossH S.lam c (F.s R) (F.a R) (hJ R)
      (fun n : Fin (J' R) => z n) ∂γ) atTop
      (𝓝 (∫ z, f z * (-(c.gen (lamShift S.lam) Y z)) ∂γ)) := by
  obtain ⟨hsum, hHS⟩ := t01_actual_coefficient_HS S A D hD t m ht htlim hm F ha
  exact t01_gaussian_crossH_tendsto (t01CovarianceMatrix_symPkg S aux A D hD hσ hH)
    S.lam F.s F.a F.supp hsum hHS hγ hY hf c hJ hsJ

/-- Actual joint convergence permits linear-growth cylinder pairings for bounded particle tests. -/
theorem t01_bounded_joint_pairing_limit {d J : ℕ} (A : InteractionData d)
    (e : ℕ → Torus d → ℝ) (hem : ∀ i, Measurable (e i))
    (Ns : ℕ → ℕ+) (f : (k : ℕ) → ParticleSpace d (Ns k) → ℝ)
    (hfm : ∀ k, AEStronglyMeasurable (f k) (particleLaw A (Ns k)))
    {B : ℝ} (hB0 : 0 ≤ B) (hfb : ∀ k X, |f k X| ≤ B)
    {C : ℕ → ℕ → ℝ} {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    {F : (ℕ → ℝ) → ℝ} (hF : MemLp F 2 γ)
    (hlaw : ∀ g : ℝ × (Fin J → ℝ) →ᵇ ℝ,
      Tendsto (fun k => ∫ X, g (f k X, fun i => fluct e (Ns k) i X)
        ∂particleLaw A (Ns k)) atTop (𝓝 (∫ z, g (F z, fun i => z i) ∂γ)))
    {K : ℝ} (hZ4 : ∀ k (i : Fin J),
      Integrable (fun X => fluct e (Ns k) i X ^ 4) (particleLaw A (Ns k)) ∧
        ∫ X, fluct e (Ns k) i X ^ 4 ∂particleLaw A (Ns k) ≤ K)
    {H : (Fin J → ℝ) → ℝ} (hH : Continuous H) {a : ℝ}
    (hHb : ∀ z, |H z| ≤ a * (1 + ∑ j, |z j|)) :
    Tendsto (fun k => ∫ X, f k X * H (fun i => fluct e (Ns k) i X)
      ∂particleLaw A (Ns k)) atTop (𝓝 (∫ z, F z * H (fun i => z i) ∂γ)) := by
  haveI := hγ.1
  have hZm : ∀ k, AEStronglyMeasurable
      (fun X => fun i : Fin J => fluct e (Ns k) i X) (particleLaw A (Ns k)) := by
    intro k
    refine (measurable_pi_iff.mpr fun i => ?_).aestronglyMeasurable
    exact measurable_const.mul (Finset.measurable_sum _ fun l _ =>
      (hem (i + 1)).comp (measurable_pi_apply l))
  have hfsq : ∀ k X, f k X ^ 2 ≤ B ^ 2 := fun k X => by
    rw [← sq_abs (f k X)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hfb k X) 2
  have hUI : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ k,
      ∫⁻ X in {X | M < f k X ^ 2}, ENNReal.ofReal (f k X ^ 2)
        ∂particleLaw A (Ns k) ≤ ENNReal.ofReal ε := by
    intro ε hε
    refine ⟨B ^ 2, fun k => ?_⟩
    have hempty : {X | B ^ 2 < f k X ^ 2} = ∅ := by
      ext X
      simp [not_lt_of_ge (hfsq k X)]
    rw [hempty]
    simp
  have hf2 : ∀ k, ∫ X, f k X ^ 2 ∂particleLaw A (Ns k) ≤ max (B ^ 2) K := by
    intro k
    refine (integral_mono_of_nonneg (Eventually.of_forall fun X => sq_nonneg _)
      (integrable_const (B ^ 2)) (Eventually.of_forall (hfsq k))).trans ?_
    simpa using (le_max_left (B ^ 2) K)
  have hz4 : ∀ j : Fin J, MemLp (fun z : ℕ → ℝ => z j) 4 γ := by
    intro j
    have hmap : γ.map (fun z : ℕ → ℝ => z j) = gaussianReal 0 (C j j).toNNReal := by
      have h := hγ.2 {(j : ℕ)} (fun _ => 1)
      simpa using h
    have hg : MemLp id (4 : ℝ≥0) (γ.map (fun z : ℕ → ℝ => z j)) := by
      rw [hmap]
      exact memLp_id_gaussianReal 4
    exact (memLp_map_measure_iff aestronglyMeasurable_id
      (measurable_pi_apply (j : ℕ)).aemeasurable).1 hg
  exact tendsto_integral_mul_of_law (fun k => particleLaw A (Ns k)) f
    (fun k X i => fluct e (Ns k) i X) hfm hZm hF hlaw hUI hf2
    (fun k i => ⟨(hZ4 k i).1, (hZ4 k i).2.trans (le_max_right _ _)⟩) hz4 hH hHb

/-- The finite-rank cross term converges under the actual bounded-test joint law. -/
theorem t01_bounded_crossH_pairing_limit {d : ℕ} (A : InteractionData d)
    (e : ℕ → Torus d → ℝ) (hem : ∀ i, Measurable (e i))
    (Ns : ℕ → ℕ+) (f : (k : ℕ) → ParticleSpace d (Ns k) → ℝ)
    (hfm : ∀ k, AEStronglyMeasurable (f k) (particleLaw A (Ns k)))
    {B : ℝ} (hB0 : 0 ≤ B) (hfb : ∀ k X, |f k X| ≤ B)
    {C : ℕ → ℕ → ℝ} {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    {F : (ℕ → ℝ) → ℝ} (hF : MemLp F 2 γ)
    (hlaw : ∀ J (g : ℝ × (Fin J → ℝ) →ᵇ ℝ),
      Tendsto (fun k => ∫ X, g (f k X, fun i => fluct e (Ns k) i X)
        ∂particleLaw A (Ns k)) atTop (𝓝 (∫ z, g (F z, fun i => z i) ∂γ)))
    (hZ4 : ∀ J, ∃ K : ℝ, ∀ k (i : Fin J),
      Integrable (fun X => fluct e (Ns k) i X ^ 4) (particleLaw A (Ns k)) ∧
        ∫ X, fluct e (Ns k) i X ^ 4 ∂particleLaw A (Ns k) ≤ K)
    (lam : ℕ → ℝ) (c : Cyl) (s : Finset ℕ) (a : ℕ → ℕ → ℝ)
    {J' : ℕ} (hJ : c.J ≤ J') :
    Tendsto (fun k => ∫ X, f k X * crossH lam c s a hJ
      (fun i : Fin J' => fluct e (Ns k) i X) ∂particleLaw A (Ns k)) atTop
      (𝓝 (∫ z, F z * crossH lam c s a hJ (fun i : Fin J' => z i) ∂γ)) := by
  obtain ⟨K, hK⟩ := hZ4 J'
  obtain ⟨aH, hHb⟩ := crossH_growth lam c s a hJ
  exact t01_bounded_joint_pairing_limit A e hem Ns f hfm hB0 hfb hγ hF (hlaw J') hK
    (continuous_crossH lam c s a hJ) hHb

end DGPS.Lipschitz
