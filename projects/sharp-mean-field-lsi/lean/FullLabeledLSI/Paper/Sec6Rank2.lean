import FullLabeledLSI.Paper.Sec6Rank1
import SharpSymmetricLSI.Paper.GaussLaw9
import SharpSymmetricLSI.Paper.ULimit10

/-!
# Lemma 6.1, second conclusion: `κ_R → K_∞` (item M4)

`κ_R = ∫ e^{-u_R} dγ` (`kappaR`), `K_∞ = ∫ e^{-U_∞} dγ` (`Kinf`), with
`u_R = ½ zᵀ a^R z = ½ Q_{a^R} + ½ tr a^R` and `U_∞ = ½ Q + ½ d_K`.

Route.
* (i) Bessel in `L²(μ ⊗ μ)` for the orthonormal family `e'_{i+1} ⊗ e'_{j+1}`:
  `∑_{i,j<n} (T_ij - a^R_ij)² ≤ ‖K - K_R'‖²_{L²(μ⊗μ)} ≤ ‖K - K_R‖²_∞ → 0`
  (`e'` a Borel version of `e`, `K_R'` the finite-rank kernel built from it; `Rank1.Dk`).
* (ii) `tr a^R = ∫ K_R(x,x) dμ → ∫ K(x,x) dμ = d_K`, from the diagonal conjunct of `IsKernelApprox`.
  Hence `u_R → U_∞` in `L²(γ)` (the chaos isometry `E Q_B² = 2‖B‖²_HS`, `integral_quad_chaos_sq`).
* (iii) `I + T ≥ σ` (Proposition 2.1) and `|⟨y,(T - a^R)y⟩| ≤ ‖T - a^R‖_HS ‖y‖²` give
  `I + a^R ≥ σ/2` for large `R`; the explicit Gaussian integral (`GaussLaw2`/`GaussLaw3`) then bounds
  `∫ e^{-q u_R} dγ` uniformly, for `q = 1 + σ/4`.
* (iv) Vitali (`tendsto_integral_of_ae_of_rpow_le`) along a.e.-convergent subsequences.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace SharpLSI.FL

namespace Rank2

/-! ### A generic Bessel inequality on a product space -/

section Bessel

variable {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
  {E : ℕ → α → ℝ}

lemma memLp_prod_E (hEm : ∀ i, Measurable (E i)) (hE : ∀ i, MemLp (E i) 2 ν) (i j : ℕ) :
    MemLp (fun p : α × α => E i p.1 * E j p.2) 2 (ν.prod ν) := by
  refine (memLp_two_iff_integrable_sq ((hEm i).comp measurable_fst |>.mul
    ((hEm j).comp measurable_snd)).aestronglyMeasurable).mpr ?_
  exact ((hE i).integrable_sq.mul_prod (hE j).integrable_sq).congr
    (Eventually.of_forall fun p => by simp [mul_pow])

lemma integral_prod_E (horth : ∀ i j, ∫ x, E i x * E j x ∂ν = if i = j then 1 else 0)
    (a b c d : ℕ) :
    ∫ p : α × α, (E a p.1 * E b p.2) * (E c p.1 * E d p.2) ∂(ν.prod ν) =
      (if a = c then 1 else 0) * (if b = d then 1 else 0) := by
  have : (fun p : α × α => (E a p.1 * E b p.2) * (E c p.1 * E d p.2)) =
      fun p => (E a p.1 * E c p.1) * (E b p.2 * E d p.2) := by
    funext p; ring
  rw [this, integral_prod_mul (f := fun x => E a x * E c x) (g := fun y => E b y * E d y),
    horth, horth]

theorem bessel_prod (hEm : ∀ i, Measurable (E i)) (hE : ∀ i, MemLp (E i) 2 ν)
    (horth : ∀ i j, ∫ x, E i x * E j x ∂ν = if i = j then 1 else 0)
    {f : α × α → ℝ} (hf : MemLp f 2 (ν.prod ν)) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (∫ p, f p * (E i p.1 * E j p.2) ∂(ν.prod ν)) ^ 2 ≤ ∫ p, f p ^ 2 ∂(ν.prod ν) := by
  set S := Finset.range n ×ˢ Finset.range n with hS
  set F : ℕ × ℕ → α × α → ℝ := fun q p => E q.1 p.1 * E q.2 p.2 with hFdef
  set c : ℕ × ℕ → ℝ := fun q => ∫ p, f p * F q p ∂(ν.prod ν) with hcdef
  have hF : ∀ q, MemLp (F q) 2 (ν.prod ν) := fun q => memLp_prod_E hEm hE q.1 q.2
  set g : α × α → ℝ := fun p => ∑ q ∈ S, c q * F q p with hgdef
  have hg : MemLp g 2 (ν.prod ν) :=
    memLp_finsetSum (f := fun q p => c q * F q p) _ fun q _ => (hF q).const_mul _
  have hFF : ∀ q q' : ℕ × ℕ, ∫ p, F q p * F q' p ∂(ν.prod ν) =
      (if q.1 = q'.1 then 1 else 0) * (if q.2 = q'.2 then 1 else 0) :=
    fun q q' => integral_prod_E horth _ _ _ _
  have horthF : ∀ q ∈ S, ∀ q' ∈ S, q ≠ q' → ∫ p, F q p * F q' p ∂(ν.prod ν) = 0 := by
    intro q _ q' _ hqq'
    rw [hFF]
    rcases q with ⟨a, b⟩; rcases q' with ⟨a', b'⟩
    by_cases h1 : a = a'
    · subst h1
      have : b ≠ b' := fun h => hqq' (by rw [h])
      simp [this]
    · simp [h1]
  have hgsq : ∫ p, g p ^ 2 ∂(ν.prod ν) = ∑ q ∈ S, c q ^ 2 := by
    simp only [hgdef]
    rw [integral_sq_sum_orth S c F hF horthF]
    refine Finset.sum_congr rfl fun q _ => ?_
    have h1 : ∫ p, F q p ^ 2 ∂(ν.prod ν) = 1 := by
      simp_rw [sq]; rw [hFF]; simp
    rw [h1, mul_one]
  have hfg : ∫ p, f p * g p ∂(ν.prod ν) = ∑ q ∈ S, c q ^ 2 := by
    simp only [hgdef, Finset.mul_sum]
    have hint : ∀ q ∈ S, Integrable (fun p => f p * (c q * F q p)) (ν.prod ν) := fun q _ =>
      hf.integrable_mul ((hF q).const_mul (c q))
    rw [integral_finsetSum S hint]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : (fun p => f p * (c q * F q p)) = fun p => c q * (f p * F q p) := by
      funext p; ring
    rw [this, integral_const_mul, sq]
  have e1 : ∀ p : α × α, (f p - g p) ^ 2 = f p ^ 2 - 2 * (f p * g p) + g p ^ 2 :=
    fun p => by ring
  have hsq : ∫ p, (f p - g p) ^ 2 ∂(ν.prod ν) =
      ∫ p, f p ^ 2 ∂(ν.prod ν) - 2 * ∑ q ∈ S, c q ^ 2 + ∑ q ∈ S, c q ^ 2 := by
    simp_rw [e1]
    have i1 : Integrable (fun p => f p ^ 2) (ν.prod ν) := hf.integrable_sq
    have i2 : Integrable (fun p => 2 * (f p * g p)) (ν.prod ν) :=
      (hf.integrable_mul hg).const_mul 2
    have i3 : Integrable (fun p => g p ^ 2) (ν.prod ν) := hg.integrable_sq
    have i4 : Integrable (fun p => f p ^ 2 - 2 * (f p * g p)) (ν.prod ν) := i1.sub i2
    rw [integral_add i4 i3, integral_sub i1 i2, integral_const_mul, hfg, hgsq]
  have h0 : 0 ≤ ∫ p, (f p - g p) ^ 2 ∂(ν.prod ν) := integral_nonneg fun _ => sq_nonneg _
  have hprod : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (∫ p, f p * (E i p.1 * E j p.2) ∂(ν.prod ν)) ^ 2 = ∑ q ∈ S, c q ^ 2 := by
    rw [hS, Finset.sum_product]
  rw [hprod]
  linarith

/-- `∬ K_R F_ij = a_ij` for the finite-rank kernel `K_R = ∑ a_kl E_k ⊗ E_l` supported on `s × s`. -/
lemma integrable_kerE_mul (hEm : ∀ i, Measurable (E i)) (hE : ∀ i, MemLp (E i) 2 ν)
    (s : Finset ℕ) (a : ℕ → ℕ → ℝ) (i j : ℕ) :
    Integrable (fun p : α × α => (∑ k ∈ s, ∑ l ∈ s, a k l * E k p.1 * E l p.2) *
      (E i p.1 * E j p.2)) (ν.prod ν) := by
  have hexp : ∀ p : α × α, (∑ k ∈ s, ∑ l ∈ s, a k l * E k p.1 * E l p.2) *
      (E i p.1 * E j p.2) =
      ∑ k ∈ s, ∑ l ∈ s, a k l * ((E k p.1 * E l p.2) * (E i p.1 * E j p.2)) := by
    intro p
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [hexp]
  exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    ((memLp_prod_E hEm hE k l).integrable_mul (memLp_prod_E hEm hE i j)).const_mul _

lemma integral_kerE_mul (hEm : ∀ i, Measurable (E i)) (hE : ∀ i, MemLp (E i) 2 ν)
    (horth : ∀ i j, ∫ x, E i x * E j x ∂ν = if i = j then 1 else 0)
    {s : Finset ℕ} {a : ℕ → ℕ → ℝ} (ha : ∀ i j, (i ∉ s ∨ j ∉ s) → a i j = 0) (i j : ℕ) :
    ∫ p : α × α, (∑ k ∈ s, ∑ l ∈ s, a k l * E k p.1 * E l p.2) * (E i p.1 * E j p.2)
      ∂(ν.prod ν) = a i j := by
  have hterm : ∀ k l, Integrable (fun p : α × α =>
      a k l * ((E k p.1 * E l p.2) * (E i p.1 * E j p.2))) (ν.prod ν) := fun k l =>
    ((memLp_prod_E hEm hE k l).integrable_mul (memLp_prod_E hEm hE i j)).const_mul _
  have hexp : ∀ p : α × α, (∑ k ∈ s, ∑ l ∈ s, a k l * E k p.1 * E l p.2) *
      (E i p.1 * E j p.2) =
      ∑ k ∈ s, ∑ l ∈ s, a k l * ((E k p.1 * E l p.2) * (E i p.1 * E j p.2)) := by
    intro p
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hterm k l]
  have h1 : ∀ k ∈ s, ∫ p : α × α, ∑ l ∈ s, a k l * ((E k p.1 * E l p.2) * (E i p.1 * E j p.2))
      ∂(ν.prod ν) = ∑ l ∈ s, a k l * ((if k = i then 1 else 0) * (if l = j then 1 else 0)) := by
    intro k _
    rw [integral_finsetSum _ fun l _ => hterm k l]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, integral_prod_E horth]
  rw [Finset.sum_congr rfl h1]
  by_cases hi : i ∈ s
  · by_cases hj : j ∈ s
    · simp [mul_ite, hi, hj]
    · rw [ha i j (Or.inr hj)]
      simp [mul_ite, hj]
  · rw [ha i j (Or.inl hi)]
    simp [mul_ite, hi]

omit [IsProbabilityMeasure ν] in
lemma integrable_diag_kerE (hE : ∀ i, MemLp (E i) 2 ν) (s : Finset ℕ) (a : ℕ → ℕ → ℝ) :
    Integrable (fun x => ∑ k ∈ s, ∑ l ∈ s, a k l * E k x * E l x) ν := by
  refine integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => ?_
  have := ((hE k).integrable_mul (hE l)).const_mul (a k l)
  refine this.congr (Eventually.of_forall fun x => ?_)
  show a k l * (E k x * E l x) = a k l * E k x * E l x
  ring

omit [IsProbabilityMeasure ν] in
lemma integral_diag_kerE (hE : ∀ i, MemLp (E i) 2 ν)
    (horth : ∀ i j, ∫ x, E i x * E j x ∂ν = if i = j then 1 else 0) (s : Finset ℕ)
    (a : ℕ → ℕ → ℝ) :
    ∫ x, ∑ k ∈ s, ∑ l ∈ s, a k l * E k x * E l x ∂ν = ∑ k ∈ s, a k k := by
  have hint : ∀ k l, Integrable (fun x => a k l * (E k x * E l x)) ν := fun k l =>
    ((hE k).integrable_mul (hE l)).const_mul _
  have hexp : ∀ x, ∑ k ∈ s, ∑ l ∈ s, a k l * E k x * E l x =
      ∑ k ∈ s, ∑ l ∈ s, a k l * (E k x * E l x) := fun x =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_finsetSum _ fun l _ => hint k l]
  simp_rw [integral_const_mul, horth]
  simp [mul_ite, Finset.sum_ite_eq, hk]

end Bessel

/-! ### Elementary algebra -/

section Alg

variable {s : Finset ℕ} {a : ℕ → ℕ → ℝ}

lemma sum_range_eq_sum_supp {n : ℕ} (hs : ∀ i ∈ s, i < n)
    (ha : ∀ i j, (i ∉ s ∨ j ∉ s) → a i j = 0) (g : ℕ → ℕ → ℝ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, a i j * g i j =
      ∑ i ∈ s, ∑ j ∈ s, a i j * g i j := by
  have hsub : s ⊆ Finset.range n := fun i hi => Finset.mem_range.2 (hs i hi)
  rw [← Finset.sum_subset hsub (f := fun i => ∑ j ∈ Finset.range n, a i j * g i j) ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact (Finset.sum_subset hsub fun j _ hj => by rw [ha i j (Or.inr hj), zero_mul]).symm
  · intro i _ hi
    exact Finset.sum_eq_zero fun j _ => by rw [ha i j (Or.inl hi), zero_mul]

lemma sum_fin_eq_range (M : ℕ → ℕ → ℝ) (n : ℕ) :
    ∑ i : Fin n, ∑ j : Fin n, M i j = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, M i j := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range n, M i j) n]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Fin.sum_univ_eq_sum_range (fun j => M i j) n

variable {d : ℕ} {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}

lemma quadTrunc_eq_supp' {n : ℕ} (hs : ∀ i ∈ s, i < n)
    (ha : ∀ i j, (i ∉ s ∨ j ∉ s) → a i j = 0) (z : ℕ → ℝ) :
    quadTrunc a n z = ∑ i ∈ s, ∑ j ∈ s, a i j * (z i * z j - if i = j then 1 else 0) :=
  sum_range_eq_sum_supp hs ha (fun i j => z i * z j - if i = j then 1 else 0)

lemma quadTrunc_eq_supp (R n : ℕ) (A : FiniteRankApprox W μ e) (hs : ∀ i ∈ A.s R, i < n)
    (z : ℕ → ℝ) :
    quadTrunc (A.a R) n z = ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j *
      (z i * z j - if i = j then 1 else 0) :=
  quadTrunc_eq_supp' hs (A.supp R) z

lemma uR_eq_quad (A : FiniteRankApprox W μ e) (R n : ℕ) (hs : ∀ i ∈ A.s R, i < n)
    (z : ℕ → ℝ) :
    uR A R z = quadTrunc (A.a R) n z / 2 + (∑ i ∈ A.s R, A.a R i i) / 2 := by
  rw [quadTrunc_eq_supp R n A hs z]
  have h2 : ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * (z i * z j - if i = j then 1 else 0) =
      ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * z i * z j - ∑ i ∈ A.s R, A.a R i i := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    · refine Finset.sum_congr rfl fun i hi => ?_
      simp [mul_ite, Finset.sum_ite_eq, hi]
  rw [h2]
  unfold uR
  ring

lemma abs_quad_le {n : ℕ} (M : ℕ → ℕ → ℝ) (y : EuclideanSpace ℝ (Fin n)) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∑ i : Fin n, ∑ j : Fin n, M i j ^ 2 ≤ b ^ 2) :
    |∑ i : Fin n, ∑ j : Fin n, M i j * (y i * y j)| ≤ b * ‖y‖ ^ 2 := by
  have hy : ‖y‖ ^ 2 = ∑ i : Fin n, y i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [sq_abs]
  have h2 : ∑ i : Fin n, ∑ j : Fin n, (y i * y j) ^ 2 = (‖y‖ ^ 2) ^ 2 := by
    rw [hy, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_pow _ _ _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
    (fun p => M p.1 p.2) (fun p => y p.1 * y p.2)
  simp only [Fintype.sum_prod_type] at hcs
  rw [h2] at hcs
  have h3 : (∑ i : Fin n, ∑ j : Fin n, M i j * (y i * y j)) ^ 2 ≤ (b * ‖y‖ ^ 2) ^ 2 := by
    refine hcs.trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  exact abs_le_of_sq_le_sq h3 (by positivity)

/-- `I + T ≥ σ` and `‖T - a‖_HS ≤ b` give `I + a ≥ σ - b`. -/
lemma secOp_ge_of_close {T a : ℕ → ℕ → ℝ} {σ b : ℝ} (hb0 : 0 ≤ b)
    (hσ : ∀ n (y : EuclideanSpace ℝ (Fin n)), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp T n y⟫_ℝ)
    (hb : ∀ n, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (T i j - a i j) ^ 2 ≤ b ^ 2)
    (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    (σ - b) * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp a n y⟫_ℝ := by
  have h1 := abs_quad_le (fun i j => T i j - a i j) y hb0
    (by rw [sum_fin_eq_range (fun i j => (T i j - a i j) ^ 2) n]; exact hb n)
  have h2 := hσ n y
  rw [inner_secOp_self] at h2 ⊢
  have h3 : ∑ i : Fin n, ∑ j : Fin n, (T i j - a i j) * (y i * y j) =
      ∑ i : Fin n, ∑ j : Fin n, T i j * (y i * y j) -
        ∑ i : Fin n, ∑ j : Fin n, a i j * (y i * y j) := by
    simp only [← Finset.sum_sub_distrib, sub_mul]
  rw [h3] at h1
  have h4 := (abs_le.1 h1).2
  nlinarith

end Alg

/-! ### `L²` bound for second chaoses -/

section Chaos

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma eLpNorm_two_le_of_sq {f : Ω → ℝ} (hf : MemLp f 2 P) {c : ℝ}
    (h : ∫ x, f x ^ 2 ∂P ≤ c) : eLpNorm f 2 P ≤ ENNReal.ofReal (Real.sqrt c) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : ∫ x, ‖f x‖ ^ (2 : ℝ≥0∞).toReal ∂P = ∫ x, f x ^ 2 ∂P := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have h2 : (∫ x, f x ^ 2 ∂P) ^ ((2 : ℝ)⁻¹) = Real.sqrt (∫ x, f x ^ 2 ∂P) := by
    rw [Real.sqrt_eq_rpow, one_div]
  rw [h1, ENNReal.toReal_ofNat, h2]
  exact Real.sqrt_le_sqrt h

/-- `quadTrunc` is linear in the matrix. -/
lemma quadTrunc_sub (T a : ℕ → ℕ → ℝ) (n : ℕ) (z : ℕ → ℝ) :
    quadTrunc T n z - quadTrunc a n z = quadTrunc (fun i j => T i j - a i j) n z := by
  unfold quadTrunc
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The `L²(γ)` distance between a finite chaos and the second chaos of `T`. -/
theorem eLpNorm_quadTrunc_sub_le {T a : ℕ → ℕ → ℝ} (hTs : ∀ i j, T i j = T j i)
    (has : ∀ i j, a i j = a j i) {Q : (ℕ → ℝ) → ℝ} (hQ : IsSecondChaos T Q)
    {s : Finset ℕ} (hsupp : ∀ i j, (i ∉ s ∨ j ∉ s) → a i j = 0) {m : ℕ}
    (hm : ∀ i ∈ s, i < m) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ n, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (T i j - a i j) ^ 2 ≤ b ^ 2) :
    eLpNorm (fun z => quadTrunc a m z - Q z) 2 gammaRef ≤ ENNReal.ofReal (Real.sqrt 2 * b) := by
  set c := ENNReal.ofReal (Real.sqrt 2 * b) with hc
  have he_n : Tendsto (fun n => eLpNorm (fun z => quadTrunc T n z - Q z) 2 gammaRef) atTop
      (𝓝 0) := hQ.2
  have hlim : Tendsto (fun n => c + eLpNorm (fun z => quadTrunc T n z - Q z) 2 gammaRef) atTop
      (𝓝 (c + 0)) := tendsto_const_nhds.add he_n
  rw [add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop m] with n hn
  have hsn : ∀ i ∈ s, i < n := fun i hi => (hm i hi).trans_le hn
  have hqa : quadTrunc a n = quadTrunc a m := by
    funext z
    rw [quadTrunc_eq_supp' hsn hsupp, quadTrunc_eq_supp' hm hsupp]
  have hB : ∀ i j, (fun i j => T i j - a i j) i j = (fun i j => T i j - a i j) j i := by
    intro i j; simp only [hTs i j, has i j]
  have hmem : MemLp (fun z => quadTrunc a m z - quadTrunc T n z) 2 gammaRef :=
    (memLp_quadTrunc a m).sub (memLp_quadTrunc T n)
  have hsq : ∫ z, (quadTrunc a m z - quadTrunc T n z) ^ 2 ∂gammaRef ≤ 2 * b ^ 2 := by
    have h1 : ∀ z, (quadTrunc a m z - quadTrunc T n z) ^ 2 =
        (∑ i : Fin n, ∑ j : Fin n, (T i j - a i j) * chaosH i j z) ^ 2 := by
      intro z
      rw [← quadTrunc_eq_fin (fun i j => T i j - a i j) n z, ← quadTrunc_sub T a n z, ← hqa,
        ← neg_sub, neg_sq]
    simp_rw [h1]
    rw [integral_quad_chaos_sq (B := fun i j => T i j - a i j) hB,
      sum_fin_eq_range (fun i j => (T i j - a i j) ^ 2) n]
    linarith [hb n]
  have h2 := eLpNorm_two_le_of_sq hmem hsq
  have h3 : Real.sqrt (2 * b ^ 2) = Real.sqrt 2 * b := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hb0]
  rw [h3] at h2
  have htri : eLpNorm (fun z => quadTrunc a m z - Q z) 2 gammaRef ≤
      eLpNorm (fun z => quadTrunc a m z - quadTrunc T n z) 2 gammaRef +
        eLpNorm (fun z => quadTrunc T n z - Q z) 2 gammaRef := by
    have : (fun z => quadTrunc a m z - Q z) = (fun z => quadTrunc a m z - quadTrunc T n z) +
        (fun z => quadTrunc T n z - Q z) := by
      funext z; simp
    rw [this]
    exact eLpNorm_add_le one_le_two
  exact htri.trans (add_le_add h2 le_rfl)

end Chaos

/-! ### The explicit Gaussian integral for `e^{-q u_R}` -/

section Gauss

variable {d : ℕ} {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}

theorem integral_exp_uR_le (A : FiniteRankApprox W μ e) (R n : ℕ) (hs : ∀ i ∈ A.s R, i < n)
    {q δ : ℝ} (hδ : 0 < δ) (hpos : ∀ k, δ ≤ 1 + q * secEig (A.symm R) n k) :
    Integrable (fun z => Real.exp (-(q * uR A R z))) gammaRef ∧
    ∫ z, Real.exp (-(q * uR A R z)) ∂gammaRef ≤
      Real.exp (-(q * ∑ i ∈ A.s R, A.a R i i) / 2) *
        Real.exp (q ^ 2 * (∑ i : Fin n, ∑ j : Fin n, A.a R i j ^ 2) / (2 * δ)) := by
  have hA := A.symm R
  have hp : ∀ k, 0 < 1 + q * secEig hA n k := fun k => hδ.trans_le (hpos k)
  have hpt : (fun z => Real.exp (-(q * uR A R z))) = fun z =>
      Real.exp (-(q * ∑ i ∈ A.s R, A.a R i i) / 2) *
        Real.exp ((0 : ℝ) * ∑ i ∈ (∅ : Finset ℕ), (fun _ => (0 : ℝ)) i * z i -
          q * quadTrunc (A.a R) n z / 2) := by
    funext z
    rw [← Real.exp_add, uR_eq_quad A R n hs z]
    congr 1
    simp only [zero_mul, zero_sub]
    ring
  have hint := integrable_gammaRef_exp_quad hA (∅ : Finset ℕ) (by simp) (fun _ => (0 : ℝ)) 0 q hp
  have hval := integral_gammaRef_exp_quad hA (∅ : Finset ℕ) (by simp) (fun _ => (0 : ℝ)) 0 q hp
  rw [hpt]
  refine ⟨hint.const_mul _, ?_⟩
  rw [integral_const_mul, hval]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  refine (gaussProd_le hA hδ _ hpos).trans ?_
  simp

end Gauss

/-! ### The rates -/

section Rates

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The `L^∞` error `‖K_R - K‖_{L^∞(μ⊗μ)}` of `IsKernelApprox`. -/
noncomputable def epsR (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (e : ℕ → Torus d → ℝ) (A : FiniteRankApprox W μ e) (R : ℕ) : ℝ≥0∞ :=
  eLpNorm (fun X : Config 2 d => kerC (Rank1.kerFR (A.s R) (A.a R) e) X -
    kerC (centeredKernel W μ) X) ⊤ (Measure.pi fun _ : Fin 2 => μ)

/-- The diagonal error `‖K_R(x,x) - K(x,x)‖_{L^∞(μ)}` of `IsKernelApprox`. -/
noncomputable def deltaR (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (e : ℕ → Torus d → ℝ) (A : FiniteRankApprox W μ e) (R : ℕ) : ℝ≥0∞ :=
  eLpNorm (fun x => Rank1.kerFR (A.s R) (A.a R) e x x - centeredKernel W μ x x) ⊤ μ

/-- (i) Bessel: `∑_{i,j<n} (T_ij - a^R_ij)² ≤ ‖K_R - K‖²_∞`, and (ii) `|tr a^R - d_K| ≤
‖K_R(x,x) - K(x,x)‖_∞`, for a Borel version `e'` of `e` with `KerData` for `T`. -/
theorem rank_data_aux (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {T : ℕ → ℕ → ℝ}
    {e e' : ℕ → Torus d → ℝ} (hD : KerData μ (centeredKernel W μ) e' T)
    (hee' : ∀ᵐ x ∂μ, ∀ j, e j x = e' j x) (A : FiniteRankApprox W μ e) (R : ℕ)
    (hε : epsR W μ e A R ≠ ⊤) (hδ : deltaR W μ e A R ≠ ⊤) :
    (∀ n, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (T i j - A.a R i j) ^ 2 ≤ ((epsR W μ e A R).toReal) ^ 2) ∧
    |∑ i ∈ A.s R, A.a R i i - diagMean W μ| ≤ (deltaR W μ e A R).toReal := by
  have hEm : ∀ i, Measurable (fun x => e' (i + 1) x) := fun i => hD.emeas (i + 1)
  have hE : ∀ i, MemLp (fun x => e' (i + 1) x) 2 μ := fun i => hD.eL2 (i + 1)
  have horth : ∀ i j, ∫ x, e' (i + 1) x * e' (j + 1) x ∂μ = if i = j then 1 else 0 := by
    intro i j
    have := hD.orth (i + 1) (j + 1)
    simpa using this
  have hmeas := Rank1.measurable_Dk hyp μ (s := A.s R) (a := A.a R) hD.emeas
  have hbound := Rank1.ae_abs_Dk_le (W := W) μ (A.s R) (A.a R) e e' hee' (epsR W μ e A R) hε
    le_rfl
  have hbound2 := Rank1.ae_abs_Dk_diag_le (W := W) μ (A.s R) (A.a R) e e' hee'
    (deltaR W μ e A R) hδ le_rfl
  constructor
  · intro n
    have hf : MemLp (fun p : Torus d × Torus d => Rank1.Dk W μ (A.s R) (A.a R) e' p.1 p.2) 2
        (μ.prod μ) :=
      MemLp.of_bound hmeas.aestronglyMeasurable (epsR W μ e A R).toReal
        (hbound.mono fun p hp => by rw [Real.norm_eq_abs]; exact hp)
    have hbes := bessel_prod (E := fun i => e' (i + 1)) hEm hE horth hf n
    have hc : ∀ i j, ∫ p : Torus d × Torus d, Rank1.Dk W μ (A.s R) (A.a R) e' p.1 p.2 *
        (e' (i + 1) p.1 * e' (j + 1) p.2) ∂(μ.prod μ) = T i j - A.a R i j := by
      intro i j
      have h1 := hD.integrable_kappa_mul (i + 1) (j + 1)
      have h2 := integrable_kerE_mul (E := fun i => e' (i + 1)) hEm hE (A.s R) (A.a R) i j
      have h3 := integral_kerE_mul (E := fun i => e' (i + 1)) hEm hE horth (A.supp R) i j
      have h4 := hD.T_eq_prod i j
      unfold Rank1.Dk Rank1.kerFR
      simp_rw [sub_mul]
      rw [integral_sub h1 h2, ← h4, h3]
    simp_rw [hc] at hbes
    refine hbes.trans ?_
    calc ∫ p : Torus d × Torus d, Rank1.Dk W μ (A.s R) (A.a R) e' p.1 p.2 ^ 2 ∂(μ.prod μ)
        ≤ ∫ _p : Torus d × Torus d, ((epsR W μ e A R).toReal) ^ 2 ∂(μ.prod μ) :=
          integral_mono_ae hf.integrable_sq (integrable_const _)
            (hbound.mono fun p hp => by
              have h := pow_le_pow_left₀ (abs_nonneg _) hp 2
              rw [sq_abs] at h
              exact h)
      _ = ((epsR W μ e A R).toReal) ^ 2 := by simp
  · have hKd : Integrable (fun x => centeredKernel W μ x x) μ := by
      obtain ⟨B, hB⟩ := centeredKernel_bdd hyp μ
      exact Integrable.of_bound
        (((measurable_centeredKernel hyp μ).comp
          (measurable_id.prodMk measurable_id)).aestronglyMeasurable) B
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x x)
    have hRd := integrable_diag_kerE (E := fun i => e' (i + 1)) hE (A.s R) (A.a R)
    have htr := integral_diag_kerE (E := fun i => e' (i + 1)) hE horth (A.s R) (A.a R)
    have hint : ∫ x, Rank1.Dk W μ (A.s R) (A.a R) e' x x ∂μ =
        diagMean W μ - ∑ i ∈ A.s R, A.a R i i := by
      unfold Rank1.Dk Rank1.kerFR diagMean
      rw [integral_sub hKd hRd, htr]
    have := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun x => Rank1.Dk W μ (A.s R) (A.a R) e' x x) (C := (deltaR W μ e A R).toReal)
      (hbound2.mono fun x hx => by rw [Real.norm_eq_abs]; exact hx)
    rw [hint, Real.norm_eq_abs] at this
    simpa [abs_sub_comm] using this

end Rates

/-! ### `L²(γ)` convergence of `u_R` -/

section L2

variable {d : ℕ} {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}

theorem eLpNorm_uR_sub_Uinf_le {T : ℕ → ℕ → ℝ} (hTs : ∀ i j, T i j = T j i)
    {Q : (ℕ → ℝ) → ℝ} (hQ : IsSecondChaos T Q) (A : FiniteRankApprox W μ e) (R : ℕ)
    {b dd : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ n, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (T i j - A.a R i j) ^ 2 ≤ b ^ 2)
    (hd : |∑ i ∈ A.s R, A.a R i i - diagMean W μ| ≤ dd) :
    eLpNorm (fun z => uR A R z - Uinf W μ Q z) 2 gammaRef ≤
      ENNReal.ofReal (Real.sqrt 2 * b) + ENNReal.ofReal dd := by
  set m := (A.s R).sup id + 1 with hm_def
  have hm : ∀ i ∈ A.s R, i < m := fun i hi => by
    have := Finset.le_sup (f := id) hi
    simp only [id] at this
    omega
  have h1 := eLpNorm_quadTrunc_sub_le hTs (A.symm R) hQ (A.supp R) hm hb0 hb
  have heq : (fun z => uR A R z - Uinf W μ Q z) =
      (fun z => (1 / 2 : ℝ) * (quadTrunc (A.a R) m z - Q z)) +
        (fun _ => ((∑ i ∈ A.s R, A.a R i i) - diagMean W μ) / 2) := by
    funext z
    simp only [Pi.add_apply]
    rw [uR_eq_quad A R m hm z]
    unfold Uinf
    ring
  rw [heq]
  refine (eLpNorm_add_le one_le_two).trans (add_le_add ?_ ?_)
  · have h2 : (fun z => (1 / 2 : ℝ) * (quadTrunc (A.a R) m z - Q z)) =
        (1 / 2 : ℝ) • (fun z => quadTrunc (A.a R) m z - Q z) := by
      funext z; simp [smul_eq_mul]
    rw [h2, eLpNorm_const_smul]
    have hhalf : ‖(1 / 2 : ℝ)‖ₑ ≤ 1 := by
      rw [Real.enorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_one.2 ?_
      rw [abs_of_pos (by norm_num)]
      norm_num
    calc ‖(1 / 2 : ℝ)‖ₑ * eLpNorm (fun z => quadTrunc (A.a R) m z - Q z) 2 gammaRef
        ≤ 1 * eLpNorm (fun z => quadTrunc (A.a R) m z - Q z) 2 gammaRef := by gcongr
      _ ≤ _ := by rw [one_mul]; exact h1
  · rw [eLpNorm_const _ two_ne_zero (IsProbabilityMeasure.ne_zero _)]
    simp only [measure_univ, ENNReal.one_rpow, mul_one]
    rw [Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [abs_div, abs_two]
    have := abs_nonneg (∑ i ∈ A.s R, A.a R i i - diagMean W μ)
    linarith

end L2

/-! ### Conclusion -/

section Main

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem tendsto_kappaR_of (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (h21 : Prop21Conclusion V W μ) {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {Q : (ℕ → ℝ) → ℝ} (hQ : IsSecondChaos (Tmat W μ e) Q)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) :
    Tendsto (fun R => kappaR A R) atTop (𝓝 (Kinf W μ Q)) := by
  have hμ := h21.minimizer
  have : IsProbabilityMeasure (μ : Measure (Torus d)) := inferInstance
  have hT := Tmat_symm hyp hμ he
  have hS := (hasSum_Tmat_sq hyp hμ he).summable
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  have hD := kerData_mk hyp hμ he
  have hee' : ∀ᵐ x ∂(μ : Measure (Torus d)), ∀ j, e j x =
      (fun i => (he.memLp i).aestronglyMeasurable.mk (e i)) j x := by
    rw [ae_all_iff]; exact fun j => (he.memLp j).aestronglyMeasurable.ae_eq_mk
  -- the rates
  have hε : Tendsto (fun R => epsR W μ e A R) atTop (𝓝 0) := A.approx.2.1
  have hδ : Tendsto (fun R => deltaR W μ e A R) atTop (𝓝 0) := A.approx.2.2.2.2.1
  have hb : Tendsto (fun R => (epsR W μ e A R).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hε
    rw [ENNReal.toReal_zero] at h
    exact h
  have hd : Tendsto (fun R => (deltaR W μ e A R).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hδ
    rw [ENNReal.toReal_zero] at h
    exact h
  have hσ1 : 0 < σ / 2 := by positivity
  have hgood : ∀ᶠ R in atTop, epsR W μ e A R < 1 ∧ deltaR W μ e A R < 1 ∧
      (epsR W μ e A R).toReal < min (σ / 2) 1 ∧ (deltaR W μ e A R).toReal < 1 := by
    have h0 : (0 : ℝ) < min (σ / 2) 1 := lt_min hσ1 one_pos
    exact (hε.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ≥0∞) < 1))).and
      ((hδ.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ≥0∞) < 1))).and
        ((hb.eventually (gt_mem_nhds h0)).and (hd.eventually (gt_mem_nhds one_pos))))
  -- `L²(γ)` convergence
  have hL2 : Tendsto (fun R => eLpNorm (fun z => uR A R z - Uinf W μ Q z) 2 gammaRef) atTop
      (𝓝 0) := by
    have hc : Tendsto (fun R => ENNReal.ofReal (Real.sqrt 2 * (epsR W μ e A R).toReal) +
        ENNReal.ofReal (deltaR W μ e A R).toReal) atTop (𝓝 0) := by
      have h1 := ENNReal.tendsto_ofReal (hb.const_mul (Real.sqrt 2))
      have h2 := ENNReal.tendsto_ofReal hd
      simpa using h1.add h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hgood] with R hR
    obtain ⟨hε1, hδ1, -, -⟩ := hR
    obtain ⟨hr1, hr2⟩ := rank_data_aux hyp hD hee' A R (hε1.trans ENNReal.one_lt_top).ne
      (hδ1.trans ENNReal.one_lt_top).ne
    exact eLpNorm_uR_sub_Uinf_le hT hQ A R ENNReal.toReal_nonneg hr1 hr2
  have hmeasure : TendstoInMeasure gammaRef (fun R => uR A R) atTop (Uinf W μ Q) :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero hL2
  -- uniform exponential bounds
  set σ1 : ℝ := σ / 2 with hσ1def
  set q : ℝ := 1 + σ1 / 2 with hq
  set δq : ℝ := σ1 * (1 + σ1) / 2 with hδq
  have hq1 : 1 < q := by simp only [hq]; linarith
  have hq0 : 0 < q := by linarith
  have hδq0 : 0 < δq := by positivity
  set ST : ℝ := ∑' p : ℕ × ℕ, Tmat W μ e p.1 p.2 ^ 2 with hST
  set dK : ℝ := diagMean W μ with hdK
  set B : ℝ := Real.exp (q * (|dK| + 1) / 2) *
    Real.exp (q ^ 2 * (2 * ST + 2) / (2 * δq)) with hB
  obtain ⟨R0, hR0⟩ := eventually_atTop.1 hgood
  have hkey : ∀ R ≥ R0, Integrable (fun z => Real.exp (-uR A R z)) gammaRef ∧
      Integrable (fun z => Real.exp (-uR A R z) ^ q) gammaRef ∧
      ∫ z, Real.exp (-uR A R z) ^ q ∂gammaRef ≤ B := by
    intro R hR
    obtain ⟨hε1, hδ1, hb1, hd1⟩ := hR0 R hR
    obtain ⟨hr1, hr2⟩ := rank_data_aux hyp hD hee' A R (hε1.trans ENNReal.one_lt_top).ne
      (hδ1.trans ENNReal.one_lt_top).ne
    have hbR0 : 0 ≤ (epsR W μ e A R).toReal := ENNReal.toReal_nonneg
    have hbR1 : (epsR W μ e A R).toReal < σ1 := lt_of_lt_of_le hb1 (min_le_left _ _)
    have hbR2 : (epsR W μ e A R).toReal < 1 := lt_of_lt_of_le hb1 (min_le_right _ _)
    set n := (A.s R).sup id + 1 with hn_def
    have hn : ∀ i ∈ A.s R, i < n := fun i hi => by
      have := Finset.le_sup (f := id) hi
      simp only [id] at this
      omega
    have hσR : ∀ y : EuclideanSpace ℝ (Fin n),
        σ1 * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp (A.a R) n y⟫_ℝ := by
      intro y
      have h := secOp_ge_of_close hbR0 hσ hr1 n y
      have hy0 : 0 ≤ ‖y‖ ^ 2 := sq_nonneg _
      nlinarith
    have hlam : ∀ k, σ1 - 1 ≤ secEig (A.symm R) n k := fun k => secEig_ge (A.symm R) hσR k
    have hpos1 : ∀ k, σ1 ≤ 1 + 1 * secEig (A.symm R) n k := fun k => by
      have := hlam k; linarith
    have hposq : ∀ k, δq ≤ 1 + q * secEig (A.symm R) n k := fun k => by
      have h := mul_le_mul_of_nonneg_left (hlam k) hq0.le
      have : δq = 1 + q * (σ1 - 1) := by simp only [hδq, hq]; ring
      linarith
    obtain ⟨hint1, -⟩ := integral_exp_uR_le A R n hn hσ1 hpos1
    obtain ⟨hintq, hboundq⟩ := integral_exp_uR_le A R n hn hδq0 hposq
    have hpow : ∀ z, Real.exp (-uR A R z) ^ q = Real.exp (-(q * uR A R z)) := fun z => by
      rw [← Real.exp_mul]; congr 1; ring
    refine ⟨by simpa only [one_mul] using hint1, by simpa only [hpow] using hintq, ?_⟩
    simp_rw [hpow]
    refine hboundq.trans ?_
    -- bound the trace and the Hilbert-Schmidt norm
    have htr : -(∑ i ∈ A.s R, A.a R i i) ≤ |dK| + 1 := by
      have h1 := (abs_le.1 hr2).1
      have h2 : (deltaR W μ e A R).toReal < 1 := hd1
      have h3 := neg_abs_le dK
      linarith
    have hSa : ∑ i : Fin n, ∑ j : Fin n, A.a R i j ^ 2 ≤ 2 * ST + 2 := by
      have h1 : ∀ i j : ℕ, A.a R i j ^ 2 ≤
          2 * Tmat W μ e i j ^ 2 + 2 * (Tmat W μ e i j - A.a R i j) ^ 2 := fun i j => by
        nlinarith [sq_nonneg (2 * Tmat W μ e i j - A.a R i j)]
      have h2 : ∑ i : Fin n, ∑ j : Fin n, (Tmat W μ e i j - A.a R i j) ^ 2 ≤ 1 := by
        rw [sum_fin_eq_range (fun i j => (Tmat W μ e i j - A.a R i j) ^ 2) n]
        refine (hr1 n).trans ?_
        nlinarith
      calc ∑ i : Fin n, ∑ j : Fin n, A.a R i j ^ 2
          ≤ ∑ i : Fin n, ∑ j : Fin n, (2 * Tmat W μ e i j ^ 2 +
              2 * (Tmat W μ e i j - A.a R i j) ^ 2) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 _ _
        _ = 2 * ∑ i : Fin n, ∑ j : Fin n, Tmat W μ e i j ^ 2 +
              2 * ∑ i : Fin n, ∑ j : Fin n, (Tmat W μ e i j - A.a R i j) ^ 2 := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ ≤ 2 * ST + 2 * 1 := by
            have := sum_fin_sq_le_tsum hS n
            nlinarith
        _ = 2 * ST + 2 := by ring
    have e1 : -(q * ∑ i ∈ A.s R, A.a R i i) / 2 ≤ q * (|dK| + 1) / 2 := by
      have := mul_le_mul_of_nonneg_left htr hq0.le
      linarith
    have e2 : q ^ 2 * (∑ i : Fin n, ∑ j : Fin n, A.a R i j ^ 2) / (2 * δq) ≤
        q ^ 2 * (2 * ST + 2) / (2 * δq) := by
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hSa (sq_nonneg _)
    exact mul_le_mul (Real.exp_le_exp.2 e1) (Real.exp_le_exp.2 e2) (Real.exp_pos _).le
      (Real.exp_pos _).le
  -- Vitali along a.e.-convergent subsequences
  have key : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ,
      Integrable (fun z => Real.exp (-Uinf W μ Q z)) gammaRef ∧
      Tendsto (fun k => ∫ z, Real.exp (-uR A (ns (ms k) + R0) z) ∂gammaRef) atTop
        (𝓝 (∫ z, Real.exp (-Uinf W μ Q z) ∂gammaRef)) := by
    intro ns hns
    have hm' := hmeasure.comp ((tendsto_add_atTop_nat R0).comp hns)
    obtain ⟨ms, -, hms⟩ := hm'.exists_seq_tendsto_ae
    refine ⟨ms, tendsto_integral_of_ae_of_rpow_le
      (f := fun k z => Real.exp (-uR A (ns (ms k) + R0) z))
      (fun _ _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
      (fun k => (hkey _ (Nat.le_add_left _ _)).1) hq1
      (fun k => (hkey _ (Nat.le_add_left _ _)).2.1)
      (fun k => (hkey _ (Nat.le_add_left _ _)).2.2) ?_⟩
    filter_upwards [hms] with z hz
    exact (Real.continuous_exp.tendsto _).comp hz.neg
  have hlim : Tendsto (fun R => ∫ z, Real.exp (-uR A R z) ∂gammaRef) atTop
      (𝓝 (∫ z, Real.exp (-Uinf W μ Q z) ∂gammaRef)) := by
    refine (tendsto_add_atTop_iff_nat R0).1 (tendsto_of_subseq_tendsto fun ns hns => ?_)
    obtain ⟨ms, -, h⟩ := key ns hns
    exact ⟨ms, h⟩
  exact hlim

end Main

end Rank2

/-- **Lemma 6.1, second conclusion** (`rank_errors`, part 2): `κ_R → K_∞`. -/
theorem rank_errors_part2 {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (Q : (ℕ → ℝ) → ℝ) (hQ : IsSecondChaos (Tmat W μ e) Q)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) :
    Tendsto (fun R => kappaR A R) atTop (𝓝 (Kinf W μ Q)) :=
  Rank2.tendsto_kappaR_of hyp (prop21Conclusion_of_equilibrium (prop_equilibrium hd hyp hr) hμ)
    he hQ A

end SharpLSI.FL
