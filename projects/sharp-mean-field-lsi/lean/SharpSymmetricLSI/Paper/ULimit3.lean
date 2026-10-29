import SharpSymmetricLSI.Paper.ULimit2

/-!
# The second chaos `Q_T` (6.8) (Phase 3, lane D; R26)

`E_γ |∑_{i,j<n} B_{ij}(z_i z_j - δ_{ij})|² = 2 ∑_{i,j<n} B_{ij}²` for symmetric `B`, hence the
truncations of `Q_T` are Cauchy in `L²(γ)` when `∑ T_{ij}² < ∞`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

/-- Expansion of the square of an orthogonal sum. -/
theorem integral_sq_sum_orth {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} (S : Finset ι)
    (c : ι → ℝ) (F : ι → Ω → ℝ) (hF : ∀ a, MemLp (F a) 2 P)
    (horth : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∫ ω, F a ω * F b ω ∂P = 0) :
    ∫ ω, (∑ a ∈ S, c a * F a ω) ^ 2 ∂P = ∑ a ∈ S, c a ^ 2 * ∫ ω, F a ω ^ 2 ∂P := by
  have hexp : ∀ ω, (∑ a ∈ S, c a * F a ω) ^ 2 = ∑ a ∈ S, ∑ b ∈ S, c a * c b * (F a ω * F b ω) := by
    intro ω; rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hint : ∀ a b, Integrable (fun ω => c a * c b * (F a ω * F b ω)) P := fun a b =>
    ((hF a).integrable_mul (hF b)).const_mul _
  simp_rw [hexp]
  rw [integral_finset_sum (f := fun a ω => ∑ b ∈ S, c a * c b * (F a ω * F b ω)) _
    fun a _ => integrable_finset_sum _ fun b _ => hint a b]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [integral_finset_sum (f := fun b ω => c a * c b * (F a ω * F b ω)) _ fun b _ => hint a b,
    Finset.sum_eq_single a]
  · rw [integral_const_mul]; simp only [← sq]
  · intro b hb hba
    rw [integral_const_mul, horth a ha b hb (Ne.symm hba), mul_zero]
  · intro h; exact absurd ha h

/-- **The `L²(γ)` norm of a quadratic chaos.** -/
theorem integral_quad_chaos_sq {n : ℕ} {B : ℕ → ℕ → ℝ} (hB : ∀ i j, B i j = B j i) :
    ∫ ω, (∑ i : Fin n, ∑ j : Fin n, B i j * chaosH i j ω) ^ 2 ∂gammaRef =
      2 * ∑ i : Fin n, ∑ j : Fin n, B i j ^ 2 := by
  set S := (Finset.univ : Finset (Fin n × Fin n)).filter fun p => p.1 ≤ p.2
  set c : Fin n × Fin n → ℝ := fun p => if p.1 < p.2 then 2 * B p.1 p.2 else B p.1 p.2
  set F : Fin n × Fin n → (ℕ → ℝ) → ℝ := fun p => chaosH p.1 p.2
  have hsymm : ∀ ω, ∀ i j : Fin n, B i j * chaosH i j ω = B j i * chaosH j i ω := fun ω i j => by
    rw [hB, chaosH_symm]
  have hrw : ∀ ω, (∑ i : Fin n, ∑ j : Fin n, B i j * chaosH i j ω) = ∑ p ∈ S, c p * F p ω := by
    intro ω
    rw [sum_sum_symm_eq (f := fun i j : Fin n => B i j * chaosH i j ω) (hsymm ω),
      Finset.sum_filter, Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hd : B i i * chaosH i i ω = ∑ j : Fin n, if i = j then B i j * chaosH i j ω else 0 := by
      simp
    rw [Finset.mul_sum, hd, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [c, F]
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.le, h.ne, h.ne']; ring
    · subst h; simp
    · simp [h, h.ne, h.ne', not_le.mpr h, not_lt.mpr h.le]
  simp_rw [hrw]
  rw [integral_sq_sum_orth S c F (fun p => memLp_chaosH _ _) ?_]
  · simp only [F, integral_chaosH_sq]
    calc ∑ p ∈ S, c p ^ 2 * (if (p.1 : ℕ) = p.2 then (2 : ℝ) else 1)
        = ∑ i : Fin n, ∑ j : Fin n, if i ≤ j then c (i, j) ^ 2 *
            (if (i : ℕ) = j then (2 : ℝ) else 1) else 0 := by
          rw [Finset.sum_filter, Fintype.sum_prod_type]
      _ = ∑ i : Fin n, ∑ j : Fin n, (4 * (if i < j then B i j ^ 2 else 0) +
            2 * (if i = j then B i j ^ 2 else 0)) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          simp only [c]
          rcases lt_trichotomy i j with h | h | h
          · have : (i : ℕ) ≠ j := fun h' => h.ne (Fin.ext h')
            simp [h, h.le, h.ne, this]; ring
          · subst h; simp; ring
          · simp [h, h.ne', not_le.mpr h, not_lt.mpr h.le]
      _ = 2 * (2 * (∑ i : Fin n, ∑ j : Fin n, if i < j then B i j ^ 2 else 0) +
            ∑ i : Fin n, B i i ^ 2) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ,
            if_true]
          ring
      _ = _ := by rw [sum_sum_symm_eq (f := fun i j : Fin n => B i j ^ 2) fun i j => by rw [hB]]
  · intro p hp q hq hpq
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    refine integral_chaosH_orth (p := ((p.1 : ℕ), (p.2 : ℕ))) (q := ((q.1 : ℕ), (q.2 : ℕ)))
      hp hq ?_
    intro h
    simp only [Prod.mk.injEq] at h
    exact hpq (Prod.ext (Fin.ext h.1) (Fin.ext h.2))


/-! ### Truncations and the existence of `Q_T` -/

/-- `∑_{i,j<n} T_{ij}(z_i z_j - δ_{ij})`. -/
def quadTrunc (T : ℕ → ℕ → ℝ) (n : ℕ) (z : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, T i j * (z i * z j - if i = j then 1 else 0)

/-- `∑_{i,j<n} T_{ij}²`. -/
def sqSum (T : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, T i j ^ 2

theorem sum_range_restrict {m n : ℕ} (hmn : m ≤ n) (g : ℕ → ℕ → ℝ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (if i < m ∧ j < m then g i j else 0) =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, g i j := by
  have hf : (Finset.range n).filter (· < m) = Finset.range m := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  simp_rw [ite_and]
  rw [← hf, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [Finset.sum_filter]
  · simp

theorem quadTrunc_eq_fin (T : ℕ → ℕ → ℝ) (n : ℕ) (z : ℕ → ℝ) :
    quadTrunc T n z = ∑ i : Fin n, ∑ j : Fin n, T i j * chaosH i j z := by
  unfold quadTrunc chaosH
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun j => T i j * (z i * z j - if (i : ℕ) = j then 1 else 0))]

theorem memLp_quadTrunc (T : ℕ → ℕ → ℝ) (n : ℕ) : MemLp (quadTrunc T n) 2 gammaRef := by
  have : quadTrunc T n = fun z => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      T i j * chaosH i j z := rfl
  rw [this]
  exact memLp_finsetSum _ fun i _ => memLp_finsetSum (f := fun j z => T i j * chaosH i j z) _
    fun j _ => (memLp_chaosH i j).const_mul _

theorem integral_quadTrunc_sub_sq {T : ℕ → ℕ → ℝ} (hT : ∀ i j, T i j = T j i) {m n : ℕ}
    (hmn : m ≤ n) :
    ∫ z, (quadTrunc T n z - quadTrunc T m z) ^ 2 ∂gammaRef = 2 * (sqSum T n - sqSum T m) := by
  set B : ℕ → ℕ → ℝ := fun i j => if i < m ∧ j < m then 0 else T i j
  have hB : ∀ i j, B i j = B j i := fun i j => by simp only [B, and_comm, hT i j]
  have hdiff : ∀ z, quadTrunc T n z - quadTrunc T m z =
      ∑ i : Fin n, ∑ j : Fin n, B i j * chaosH i j z := by
    intro z
    have hm : quadTrunc T m z = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (if i < m ∧ j < m then T i j * chaosH i j z else 0) := by
      rw [sum_range_restrict hmn]; rfl
    rw [hm, quadTrunc, ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun j => T i j * (z i * z j - if (i : ℕ) = j then 1 else 0)),
      ← Fin.sum_univ_eq_sum_range (fun j => if (i : ℕ) < m ∧ j < m then T i j * chaosH i j z else 0),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [B, chaosH]
    split_ifs <;> ring
  simp_rw [hdiff]
  rw [integral_quad_chaos_sq hB]
  congr 1
  have hm : sqSum T m = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (if i < m ∧ j < m then T i j ^ 2 else 0) := by rw [sum_range_restrict hmn]; rfl
  rw [hm, sqSum, ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun j => T i j ^ 2),
    ← Fin.sum_univ_eq_sum_range (fun j => if (i : ℕ) < m ∧ j < m then T i j ^ 2 else 0),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [B]
  split_ifs <;> ring

theorem tendsto_sqSum {T : ℕ → ℕ → ℝ} (hs : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2) :
    Tendsto (sqSum T) atTop (𝓝 (∑' p : ℕ × ℕ, T p.1 p.2 ^ 2)) := by
  have hmono : Monotone fun n : ℕ => Finset.range n ×ˢ Finset.range n := fun a b hab =>
    Finset.product_subset_product (Finset.range_mono hab) (Finset.range_mono hab)
  have hcov : ∀ p : ℕ × ℕ, ∃ n, p ∈ Finset.range n ×ˢ Finset.range n := fun p =>
    ⟨max p.1 p.2 + 1, by simp only [Finset.mem_product, Finset.mem_range]; omega⟩
  have h := hs.hasSum.comp (tendsto_atTop_finset_of_monotone hmono hcov)
  refine h.congr fun n => ?_
  simp only [Function.comp, sqSum, Finset.sum_product]

/-- `‖f - g‖²_{L²(γ)}` through `toLp`. -/
theorem norm_toLp_sub_sq_gamma {f g : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 gammaRef)
    (hg : MemLp g 2 gammaRef) :
    ‖hf.toLp - hg.toLp‖ ^ 2 = ∫ z, (f z - g z) ^ 2 ∂gammaRef := by
  rw [← MemLp.toLp_sub, ← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(hf.sub hg).coeFn_toLp] with z h
  rw [h, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
  simp [sq]

/-- **(6.8): existence of the second chaos.** -/
theorem exists_secondChaos {T : ℕ → ℕ → ℝ} (hT : ∀ i j, T i j = T j i)
    (hs : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2) : ∃ Q, IsSecondChaos T Q := by
  set F : ℕ → Lp ℝ 2 gammaRef := fun n => (memLp_quadTrunc T n).toLp
  have hdist : ∀ m n, m ≤ n → dist (F n) (F m) ^ 2 = 2 * (sqSum T n - sqSum T m) := by
    intro m n hmn
    rw [dist_eq_norm, norm_toLp_sub_sq_gamma, integral_quadTrunc_sub_sq hT hmn]
  have hS := (tendsto_sqSum hs).cauchySeq
  have hcauchy : CauchySeq F := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hS (ε ^ 2 / 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hdist N n hn
    have h2 := hN n hn
    rw [Real.dist_eq] at h2
    have h3 : dist (F n) (F N) ^ 2 < ε ^ 2 := by
      rw [h1]; have := (abs_lt.mp h2).2; linarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h3
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨L, Lp.memLp L, ?_⟩
  have hL' : Tendsto (fun n => F n - L) atTop (𝓝 0) := by simpa using hL.sub_const L
  have h := (continuous_enorm.tendsto (0 : Lp ℝ 2 gammaRef)).comp hL'
  rw [enorm_zero] at h
  refine h.congr fun n => ?_
  simp only [Function.comp, Lp.enorm_def]
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (F n) L, (memLp_quadTrunc T n).coeFn_toLp] with z h1 h2
  rw [h1, Pi.sub_apply, h2]
  rfl


/-- The truncation error of any second chaos. -/
theorem integral_secondChaos_sub_trunc_sq {T : ℕ → ℕ → ℝ} (hT : ∀ i j, T i j = T j i)
    (hs : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2) {Q : (ℕ → ℝ) → ℝ} (hQ : IsSecondChaos T Q)
    (R : ℕ) :
    ∫ z, (Q z - quadTrunc T R z) ^ 2 ∂gammaRef = 2 * ((∑' p : ℕ × ℕ, T p.1 p.2 ^ 2) - sqSum T R) := by
  set F : ℕ → Lp ℝ 2 gammaRef := fun n => (memLp_quadTrunc T n).toLp
  set G := hQ.1.toLp
  have hFG : Tendsto F atTop (𝓝 G) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hQ.2
    refine h.congr fun n => ?_
    simp only [Function.comp, F, G]
    rw [← MemLp.toLp_sub, Lp.norm_toLp]
    rfl
  have h1 : Tendsto (fun n => ‖F n - F R‖ ^ 2) atTop (𝓝 (‖G - F R‖ ^ 2)) :=
    ((hFG.sub_const (F R)).norm).pow 2
  have h2 : Tendsto (fun n => ‖F n - F R‖ ^ 2) atTop
      (𝓝 (2 * ((∑' p : ℕ × ℕ, T p.1 p.2 ^ 2) - sqSum T R))) := by
    have h := ((tendsto_sqSum hs).sub_const (sqSum T R)).const_mul 2
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop R] with n hn
    rw [norm_toLp_sub_sq_gamma, integral_quadTrunc_sub_sq hT hn]
  rw [← norm_toLp_sub_sq_gamma hQ.1 (memLp_quadTrunc T R)]
  exact tendsto_nhds_unique h1 h2

end SharpLSI
