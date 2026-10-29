import Mathlib.Analysis.InnerProductSpace.Calculus
import DGPS.Examples.RoughBoundary.ThreeState

/-!
# Order-parameter potential of the rough counterexample (RUF018)

Source `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 2.8. With `κ = 11/6`, `β₀ = 3κ/2 = 11/4`
and the unit vectors `vᵢ` of `ThreeState`, set `Λ∞(t) = log (1/3 ∑ᵢ exp ⟨t, vᵢ⟩)`,
`Ψ∞(t) = ‖t‖² / (2κ) - Λ∞(t)` and `pᵢ(t) = exp ⟨t, vᵢ⟩ / ∑ⱼ exp ⟨t, vⱼ⟩`.

Main result: `DGPS.Examples.RoughBoundary.Landscape.order_parameter_chart_and_exact_potential_identity`.
-/

namespace DGPS.Examples.RoughBoundary.Landscape

open DGPS.Examples.RoughBoundary.ThreeState Real
open scoped ContDiff

/-- The coupling `κ = 11/6`. -/
noncomputable def kappa0 : ℝ := 11 / 6

/-- The reduced coupling `β₀ = 3κ/2 = 11/4`. -/
noncomputable def beta0 : ℝ := 11 / 4

/-- `Λ∞(t) = log ((1/3) ∑ᵢ exp (t · vᵢ))`. -/
noncomputable def logPartition (t : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Real.log (1 / 3 * ∑ i, Real.exp (inner ℝ t (vertex i)))

/-- `Ψ∞(t) = ‖t‖² / (2κ) - Λ∞(t)`. -/
noncomputable def orderPotential (t : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ‖t‖ ^ 2 / (2 * kappa0) - logPartition t

/-- The chart `t ↦ p(t)`, `pᵢ(t) = exp (t · vᵢ) / ∑ⱼ exp (t · vⱼ)`. -/
noncomputable def orderChart (t : EuclideanSpace ℝ (Fin 2)) : Fin 3 → ℝ :=
  fun i => Real.exp (inner ℝ t (vertex i)) / ∑ j, Real.exp (inner ℝ t (vertex j))

/-- The relative interior of the simplex: all coordinates positive, sum one. -/
def positiveSimplex : Set (Fin 3 → ℝ) := {p | (∀ i, 0 < p i) ∧ ∑ i, p i = 1}

lemma sum_vertex : ∑ i, vertex i = 0 := by
  ext k
  fin_cases k <;> norm_num [Fin.sum_univ_three, vertex_zero, vertex_one, vertex_two]

lemma inner_vertex_self (i : Fin 3) : inner ℝ (vertex i) (vertex i) = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_vertex]; norm_num

lemma inner_vertex_ne {i j : Fin 3} (h : i ≠ j) : inner ℝ (vertex i) (vertex j) = -1 / 2 :=
  three_state_simplex_normalization.2.2.1 i j h

lemma eq_zero_of_inner_vertex {w : EuclideanSpace ℝ (Fin 2)} (h0 : inner ℝ w (vertex 0) = 0)
    (h1 : inner ℝ w (vertex 1) = 0) : w = 0 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp [vertex_zero, vertex_one, inner, Fin.sum_univ_two] at h0 h1
  ext k
  fin_cases k
  · simpa using h0
  · simp
    have : √3 ≠ 0 := by positivity
    nlinarith [Real.sqrt_pos.2 (show (0:ℝ) < 3 by norm_num)]

lemma sum_inner_vertex (t : EuclideanSpace ℝ (Fin 2)) : ∑ i, inner ℝ t (vertex i) = 0 := by
  rw [← inner_sum, sum_vertex, inner_zero_right]


lemma gibbsSum_pos (t : EuclideanSpace ℝ (Fin 2)) : 0 < ∑ j, Real.exp (inner ℝ t (vertex j)) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

lemma orderChart_pos (t : EuclideanSpace ℝ (Fin 2)) (i : Fin 3) : 0 < orderChart t i :=
  div_pos (Real.exp_pos _) (gibbsSum_pos t)

lemma sum_orderChart (t : EuclideanSpace ℝ (Fin 2)) : ∑ i, orderChart t i = 1 := by
  unfold orderChart
  rw [← Finset.sum_div]
  exact div_self (gibbsSum_pos t).ne'

lemma orderChart_mem (t : EuclideanSpace ℝ (Fin 2)) : orderChart t ∈ positiveSimplex :=
  ⟨orderChart_pos t, sum_orderChart t⟩

lemma orderChart_mem_simplex (t : EuclideanSpace ℝ (Fin 2)) : orderChart t ∈ simplex :=
  ⟨fun i => (orderChart_pos t i).le, sum_orderChart t⟩

lemma log_three_mul_orderChart (t : EuclideanSpace ℝ (Fin 2)) (i : Fin 3) :
    Real.log (3 * orderChart t i) = inner ℝ t (vertex i) - logPartition t := by
  have hZ := gibbsSum_pos t
  unfold orderChart logPartition
  have : 3 * (Real.exp (inner ℝ t (vertex i)) / ∑ j, Real.exp (inner ℝ t (vertex j))) =
      Real.exp (inner ℝ t (vertex i)) / (1 / 3 * ∑ j, Real.exp (inner ℝ t (vertex j))) := by
    field_simp
  rw [this, Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp]

lemma inner_vertex_meanVector {p : Fin 3 → ℝ} (hp : ∑ i, p i = 1) (i : Fin 3) :
    inner ℝ (vertex i) (meanVector p) = 3 / 2 * p i - 1 / 2 := by
  unfold meanVector
  rw [inner_sum]
  simp_rw [inner_smul_right]
  have : ∀ j, p j * inner ℝ (vertex i) (vertex j) =
      if j = i then p j else -1 / 2 * p j := by
    intro j
    by_cases h : j = i
    · subst h; rw [inner_vertex_self]; simp
    · simp [h, inner_vertex_ne (Ne.symm h)]; ring
  simp_rw [this]
  rw [Fin.sum_univ_three] at hp ⊢
  fin_cases i <;> simp <;> linarith

lemma inner_meanVector_eq (t : EuclideanSpace ℝ (Fin 2)) (p : Fin 3 → ℝ) :
    inner ℝ t (meanVector p) = ∑ i, p i * inner ℝ t (vertex i) := by
  unfold meanVector
  rw [inner_sum]
  simp_rw [inner_smul_right]

lemma entropy_orderChart (t : EuclideanSpace ℝ (Fin 2)) :
    entropy (orderChart t) = inner ℝ t (meanVector (orderChart t)) - logPartition t := by
  rw [inner_meanVector_eq]
  unfold entropy
  simp_rw [log_three_mul_orderChart, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_orderChart]
  ring

lemma orderPotential_eq (t : EuclideanSpace ℝ (Fin 2)) :
    orderPotential t = freeEnergy beta0 (orderChart t) +
      ‖t - kappa0 • meanVector (orderChart t)‖ ^ 2 / (2 * kappa0) := by
  have hF := three_state_simplex_normalization.2.2.2.2.1 kappa0 beta0
    (by unfold kappa0 beta0; norm_num) _ (orderChart_mem_simplex t)
  rw [← hF, entropy_orderChart, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, real_inner_comm]
  unfold orderPotential
  have : (0:ℝ) < kappa0 := by unfold kappa0; norm_num
  field_simp
  ring


lemma orderChart_injective : Function.Injective orderChart := by
  intro t s h
  have key : ∀ i, inner ℝ (t - s) (vertex i) = logPartition t - logPartition s := by
    intro i
    have := log_three_mul_orderChart t i
    have h2 := log_three_mul_orderChart s i
    rw [h] at this
    rw [inner_sub_left]
    linarith
  have hc : logPartition t - logPartition s = 0 := by
    have := sum_inner_vertex (t - s)
    simp_rw [key] at this
    simp at this
    linarith
  have := sub_eq_zero.1 (eq_zero_of_inner_vertex (by rw [key, hc]) (by rw [key, hc]))
  exact this

lemma exists_orderChart_eq {q : Fin 3 → ℝ} (hq : q ∈ positiveSimplex) :
    ∃ t, orderChart t = q := by
  obtain ⟨hpos, hsum⟩ := hq
  set m : ℝ := (1 / 3) * ∑ i, Real.log (q i) with hm
  set a : Fin 3 → ℝ := fun i => Real.log (q i) - m with ha
  have hasum : ∑ i, a i = 0 := by
    simp only [ha, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hm]
    push_cast; ring
  rw [Fin.sum_univ_three] at hasum
  refine ⟨(2 / 3 : ℝ) • ∑ i, a i • vertex i, ?_⟩
  have hin : ∀ j, inner ℝ ((2 / 3 : ℝ) • ∑ i, a i • vertex i) (vertex j) = a j := by
    intro j
    rw [inner_smul_left, sum_inner]
    simp_rw [inner_smul_left]
    simp only [Fin.sum_univ_three, conj_trivial]
    fin_cases j
    · simp only [Fin.zero_eta, inner_vertex_self, inner_vertex_ne (show (1 : Fin 3) ≠ 0 by decide),
        inner_vertex_ne (show (2 : Fin 3) ≠ 0 by decide)]
      simp; linarith
    · simp only [Fin.mk_one, inner_vertex_self, inner_vertex_ne (show (0 : Fin 3) ≠ 1 by decide),
        inner_vertex_ne (show (2 : Fin 3) ≠ 1 by decide)]
      simp; linarith
    · simp only [Fin.reduceFinMk, inner_vertex_self,
        inner_vertex_ne (show (0 : Fin 3) ≠ 2 by decide),
        inner_vertex_ne (show (1 : Fin 3) ≠ 2 by decide)]
      simp; linarith
  funext i
  unfold orderChart
  simp_rw [hin]
  have hexp : ∀ j, Real.exp (a j) = q j * Real.exp (-m) := by
    intro j
    simp only [ha, sub_eq_add_neg, Real.exp_add, Real.exp_log (hpos j)]
  simp_rw [hexp]
  rw [← Finset.sum_mul, hsum, one_mul]
  have := Real.exp_pos (-m)
  field_simp

lemma orderChart_contDiff : ContDiff ℝ ∞ orderChart := by
  refine contDiff_pi.2 fun i => ?_
  have hc : ∀ j : Fin 3, ContDiff ℝ ∞ (fun t : EuclideanSpace ℝ (Fin 2) =>
      Real.exp (inner ℝ t (vertex j))) := fun j =>
    Real.contDiff_exp.comp ((contDiff_id (𝕜 := ℝ)).inner ℝ contDiff_const)
  exact (hc i).div (ContDiff.sum fun j _ => hc j) fun t => (gibbsSum_pos t).ne'


lemma hasFDerivAt_orderPotential (t : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt orderPotential
      (innerSL ℝ (kappa0⁻¹ • t - meanVector (orderChart t))) t := by
  have hA : ∀ i : Fin 3, HasFDerivAt (fun t : EuclideanSpace ℝ (Fin 2) => inner ℝ t (vertex i))
      (innerSL ℝ (vertex i)) t := by
    intro i
    have : (fun t : EuclideanSpace ℝ (Fin 2) => inner ℝ t (vertex i)) =
        fun t => innerSL ℝ (vertex i) t := by
      funext x; simp [real_inner_comm]
    rw [this]
    exact (innerSL ℝ (vertex i)).hasFDerivAt
  have hE : ∀ i : Fin 3, HasFDerivAt
      (fun t : EuclideanSpace ℝ (Fin 2) => Real.exp (inner ℝ t (vertex i)))
      (Real.exp (inner ℝ t (vertex i)) • innerSL ℝ (vertex i)) t := fun i => (hA i).exp
  have hS := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hE i)
  have hL := ((hS.const_mul (1 / 3 : ℝ)).log (by
    have := gibbsSum_pos t
    positivity))
  have hN0 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ ^ 2) (2 • innerSL ℝ t) t :=
    (hasStrictFDerivAt_norm_sq t).hasFDerivAt
  have hN := hN0.const_mul (1 / (2 * kappa0))
  have := hN.sub hL
  have hfun : orderPotential = fun x : EuclideanSpace ℝ (Fin 2) =>
      1 / (2 * kappa0) * ‖x‖ ^ 2 - Real.log (1 / 3 * ∑ i, Real.exp (inner ℝ x (vertex i))) := by
    funext x; unfold orderPotential logPartition; ring
  rw [hfun]
  refine this.congr_fderiv ?_
  ext h
  have hZ := gibbsSum_pos t
  have hM : inner ℝ (meanVector (orderChart t)) h =
      ∑ i, (Real.exp (inner ℝ t (vertex i)) / ∑ j, Real.exp (inner ℝ t (vertex j))) *
        inner ℝ (vertex i) h := by
    unfold meanVector
    rw [sum_inner]
    simp_rw [inner_smul_left]
    rfl
  simp only [sub_apply, smul_apply,
    sum_apply, innerSL_apply_apply, smul_eq_mul,
    inner_sub_left, inner_smul_left, hM]
  simp only [conj_trivial, nsmul_eq_mul, Nat.cast_ofNat, div_eq_mul_inv]
  have hk : (0:ℝ) < kappa0 := by unfold kappa0; norm_num
  have hR : ∑ x, Real.exp (inner ℝ t (vertex x)) * (∑ i, Real.exp (inner ℝ t (vertex i)))⁻¹ *
      inner ℝ (vertex x) h = (∑ x, Real.exp (inner ℝ t (vertex x)) * inner ℝ (vertex x) h) *
        (∑ i, Real.exp (inner ℝ t (vertex i)))⁻¹ := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hR]
  generalize (∑ i, Real.exp (inner ℝ t (vertex i))) = Z at hZ ⊢
  generalize (∑ i, Real.exp (inner ℝ t (vertex i)) * inner ℝ (vertex i) h) = S
  field_simp


lemma fderiv_orderPotential (t : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ orderPotential t = innerSL ℝ (kappa0⁻¹ • t - meanVector (orderChart t)) :=
  (hasFDerivAt_orderPotential t).fderiv

lemma kappa0_pos : (0 : ℝ) < kappa0 := by unfold kappa0; norm_num

lemma fderiv_eq_zero_iff (t : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ orderPotential t = 0 ↔ t = kappa0 • meanVector (orderChart t) := by
  rw [fderiv_orderPotential]
  constructor
  · intro h
    have h0 : kappa0⁻¹ • t - meanVector (orderChart t) = 0 := by
      generalize kappa0⁻¹ • t - meanVector (orderChart t) = x at h ⊢
      have := congrArg (fun L => L x) h
      simp only [innerSL_apply_apply, zero_apply] at this
      exact inner_self_eq_zero.1 this
    have h1 : kappa0⁻¹ • t = meanVector (orderChart t) := sub_eq_zero.1 h0
    rw [← h1, smul_smul, mul_inv_cancel₀ kappa0_pos.ne', one_smul]
  · intro h
    have h0 : kappa0⁻¹ • t - meanVector (orderChart t) = 0 := by
      have h' : kappa0⁻¹ • t = kappa0⁻¹ • (kappa0 • meanVector (orderChart t)) := by rw [← h]
      rw [h', smul_smul, inv_mul_cancel₀ kappa0_pos.ne', one_smul, sub_self]
    rw [h0]; simp

lemma freeDeriv_orderChart (t : EuclideanSpace ℝ (Fin 2)) (i : Fin 3) :
    Real.log (3 * orderChart t i) + 1 - beta0 * orderChart t i =
      inner ℝ (t - kappa0 • meanVector (orderChart t)) (vertex i) + (1 - logPartition t - kappa0 / 2) := by
  have hM : inner ℝ (meanVector (orderChart t)) (vertex i) = 3 / 2 * orderChart t i - 1 / 2 := by
    rw [real_inner_comm]; exact inner_vertex_meanVector (sum_orderChart t) i
  rw [log_three_mul_orderChart, inner_sub_left, inner_smul_left, hM]
  simp only [conj_trivial]
  unfold beta0 kappa0
  ring

lemma isInteriorCriticalPoint_iff (t : EuclideanSpace ℝ (Fin 2)) :
    IsInteriorCriticalPoint beta0 (orderChart t) ↔ t = kappa0 • meanVector (orderChart t) := by
  constructor
  · intro hc
    set w := t - kappa0 • meanVector (orderChart t) with hw
    have key : ∀ h : Fin 3 → ℝ, ∑ i, h i = 0 → ∑ i, h i * inner ℝ w (vertex i) = 0 := by
      intro h hh
      have := freeDeriv_eq_zero_of_crit hc h hh
      unfold freeDeriv at this
      simp_rw [freeDeriv_orderChart, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hh,
        zero_mul, add_zero] at this
      exact this
    have e1 := key ![1, -1, 0] (by simp [Fin.sum_univ_three])
    have e2 := key ![1, 0, -1] (by simp [Fin.sum_univ_three])
    have e3 := sum_inner_vertex w
    simp [Fin.sum_univ_three] at e1 e2 e3
    have h0 : inner ℝ w (vertex 0) = 0 := by linarith
    have h1 : inner ℝ w (vertex 1) = 0 := by linarith
    have := eq_zero_of_inner_vertex h0 h1
    exact sub_eq_zero.1 this
  · intro h
    refine isInteriorCriticalPoint_of_freeDeriv (orderChart_mem_simplex t)
      (orderChart_pos t) fun k hk => ?_
    unfold freeDeriv
    simp_rw [freeDeriv_orderChart]
    rw [← h]
    simp [sub_self, ← Finset.sum_mul, hk]

lemma orderChart_zero : orderChart 0 = fun _ => 1 / 3 := by
  funext i
  simp [orderChart]

lemma orderPotential_zero : orderPotential 0 = 0 := by
  simp [orderPotential, logPartition]

lemma freeEnergy_beta0_nonneg_and_eq {p : Fin 3 → ℝ} (hp : p ∈ simplex) :
    0 ≤ freeEnergy beta0 p ∧ (freeEnergy beta0 p = 0 → p = fun _ => 1 / 3) := by
  obtain ⟨hl1, -, hl3, -, -, -⟩ := exact_logarithmic_inequalities
  obtain ⟨-, -, -, -, -, -, -, -, -, hlow⟩ := coexistence_parameter_and_global_positivity
  have hb : beta0 < 4 * Real.log 2 := by unfold beta0; linarith
  have hmin := (hlow beta0 hb _ uniform_mem_simplex).2 rfl
  have h0 := freeEnergy_uniform beta0
  refine ⟨?_, fun hz => ?_⟩
  · have := hmin hp
    simp only [Set.mem_ofPred_eq] at this
    linarith
  · exact ((hlow beta0 hb p hp).1 (fun q hq => by
      have := hmin hq
      simp only [Set.mem_ofPred_eq] at this ⊢
      linarith))

/-- **RUF018, order-parameter chart and exact potential identity.** `t ↦ p(t)` is a smooth
bijection of `ℝ²` onto the positive simplex; `v_i · M = (3/2) pᵢ - 1/2` for `M = ∑ pᵢ vᵢ`;
`Ψ∞(t) = F_{β₀}(p(t)) + ‖t - κ M(t)‖² / (2κ)`; `Ψ∞` has a critical point at `t` iff `t = κ M(t)`
iff `p(t)` is an interior critical point of `F_{β₀}`, `p` maps the critical points of `Ψ∞`
bijectively onto the interior critical points of `F_{β₀}`, with equal values; and `Ψ∞ ≥ 0` with
unique zero `t = 0`. -/
theorem order_parameter_chart_and_exact_potential_identity :
    (ContDiff ℝ ∞ orderChart ∧ Set.BijOn orderChart Set.univ positiveSimplex) ∧
    (∀ t i, inner ℝ (vertex i) (meanVector (orderChart t)) = 3 / 2 * orderChart t i - 1 / 2) ∧
    (∀ t, orderPotential t = freeEnergy beta0 (orderChart t) +
      ‖t - kappa0 • meanVector (orderChart t)‖ ^ 2 / (2 * kappa0)) ∧
    (∀ t, (fderiv ℝ orderPotential t = 0 ↔ t = kappa0 • meanVector (orderChart t)) ∧
      (t = kappa0 • meanVector (orderChart t) ↔
        IsInteriorCriticalPoint beta0 (orderChart t))) ∧
    Set.BijOn orderChart {t | fderiv ℝ orderPotential t = 0}
      {p | IsInteriorCriticalPoint beta0 p} ∧
    (∀ t, fderiv ℝ orderPotential t = 0 → orderPotential t = freeEnergy beta0 (orderChart t)) ∧
    (∀ t, 0 ≤ orderPotential t) ∧ (∀ t, orderPotential t = 0 ↔ t = 0) := by
  have hcrit : ∀ t, fderiv ℝ orderPotential t = 0 ↔
      IsInteriorCriticalPoint beta0 (orderChart t) := fun t =>
    (fderiv_eq_zero_iff t).trans (isInteriorCriticalPoint_iff t).symm
  have hnn : ∀ t, 0 ≤ orderPotential t := fun t => by
    rw [orderPotential_eq t]
    have := (freeEnergy_beta0_nonneg_and_eq (orderChart_mem_simplex t)).1
    have := kappa0_pos
    positivity
  refine ⟨⟨orderChart_contDiff, fun t _ => orderChart_mem t,
    fun _ _ _ _ h => orderChart_injective h, ?_⟩, fun t i =>
    inner_vertex_meanVector (sum_orderChart t) i, orderPotential_eq,
    fun t => ⟨fderiv_eq_zero_iff t, (isInteriorCriticalPoint_iff t).symm⟩, ?_, ?_, hnn, ?_⟩
  · intro q hq; obtain ⟨t, ht⟩ := exists_orderChart_eq hq; exact ⟨t, trivial, ht⟩
  · refine ⟨fun t ht => (hcrit t).1 ht, fun _ _ _ _ h => orderChart_injective h, ?_⟩
    intro p hp
    obtain ⟨t, ht⟩ := exists_orderChart_eq (show p ∈ positiveSimplex from ⟨hp.2.1, hp.1.2⟩)
    exact ⟨t, (hcrit t).2 (ht ▸ hp), ht⟩
  · intro t ht
    have h := (fderiv_eq_zero_iff t).1 ht
    rw [orderPotential_eq t, ← h, sub_self]
    simp
  · intro t
    refine ⟨fun h0 => ?_, fun h => by rw [h]; exact orderPotential_zero⟩
    have hF := (freeEnergy_beta0_nonneg_and_eq (orderChart_mem_simplex t))
    have hk := kappa0_pos
    have hsq : 0 ≤ ‖t - kappa0 • meanVector (orderChart t)‖ ^ 2 / (2 * kappa0) := by positivity
    rw [orderPotential_eq t] at h0
    have hz : freeEnergy beta0 (orderChart t) = 0 := by linarith [hF.1]
    have := hF.2 hz
    rw [← orderChart_zero] at this
    exact orderChart_injective this

/-! ### RUF019: Hessians, coercive tail and the axis barrier -/

/-- The covariance form `Cov_p(v)(h,k) = E_p[⟨v,h⟩⟨v,k⟩] - E_p⟨v,h⟩ E_p⟨v,k⟩` of the three
vertices under the Gibbs probabilities `p(t)`. -/
noncomputable def orderCov (t h k : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ∑ i, orderChart t i * inner ℝ (vertex i) h * inner ℝ (vertex i) k -
    (∑ i, orderChart t i * inner ℝ (vertex i) h) * (∑ i, orderChart t i * inner ℝ (vertex i) k)

lemma inner_meanVector_left (p : Fin 3 → ℝ) (h : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (meanVector p) h = ∑ i, p i * inner ℝ (vertex i) h := by
  unfold meanVector
  rw [sum_inner]
  simp_rw [inner_smul_left]
  rfl

lemma hasFDerivAt_logPartition (t : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt logPartition (innerSL ℝ (meanVector (orderChart t))) t := by
  have hN0 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ ^ 2) (2 • innerSL ℝ t) t :=
    (hasStrictFDerivAt_norm_sq t).hasFDerivAt
  have hN := hN0.const_mul (1 / (2 * kappa0))
  have := hN.sub (hasFDerivAt_orderPotential t)
  have hfun : logPartition = fun x : EuclideanSpace ℝ (Fin 2) =>
      1 / (2 * kappa0) * ‖x‖ ^ 2 - orderPotential x := by
    funext x; unfold orderPotential; ring
  rw [hfun]
  refine this.congr_fderiv ?_
  ext h
  have hk := kappa0_pos
  simp only [sub_apply, smul_apply, innerSL_apply_apply,
    smul_eq_mul, inner_sub_left, inner_smul_left, nsmul_eq_mul, Nat.cast_ofNat, conj_trivial]
  field_simp
  ring

lemma hasFDerivAt_orderChart_apply (t : EuclideanSpace ℝ (Fin 2)) (i : Fin 3) :
    HasFDerivAt (fun s : EuclideanSpace ℝ (Fin 2) => orderChart s i)
      (orderChart t i • (innerSL ℝ (vertex i) - innerSL ℝ (meanVector (orderChart t)))) t := by
  have hA : HasFDerivAt (fun s : EuclideanSpace ℝ (Fin 2) => inner ℝ s (vertex i))
      (innerSL ℝ (vertex i)) t := by
    have : (fun s : EuclideanSpace ℝ (Fin 2) => inner ℝ s (vertex i)) =
        fun s => innerSL ℝ (vertex i) s := by
      funext x; simp [real_inner_comm]
    rw [this]
    exact (innerSL ℝ (vertex i)).hasFDerivAt
  have h := (((hA.sub (hasFDerivAt_logPartition t)).exp).const_mul (1 / 3 : ℝ))
  have hfun : (fun s : EuclideanSpace ℝ (Fin 2) => orderChart s i) =
      fun s => 1 / 3 * Real.exp (inner ℝ s (vertex i) - logPartition s) := by
    funext s
    have := log_three_mul_orderChart s i
    have h3 : Real.exp (inner ℝ s (vertex i) - logPartition s) = 3 * orderChart s i := by
      rw [← this, Real.exp_log (by have := orderChart_pos s i; positivity)]
    rw [h3]; ring
  rw [hfun]
  refine h.congr_fderiv ?_
  have h3 : Real.exp (inner ℝ t (vertex i) - logPartition t) = 3 * orderChart t i := by
    rw [← log_three_mul_orderChart, Real.exp_log (by have := orderChart_pos t i; positivity)]
  simp only [Pi.sub_apply]
  rw [h3]
  ext h
  simp
  ring

lemma hasFDerivAt_meanVector_chart (t : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (fun s => meanVector (orderChart s))
      (∑ i, (orderChart t i • (innerSL ℝ (vertex i) -
        innerSL ℝ (meanVector (orderChart t)))).smulRight (vertex i)) t := by
  have := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (hasFDerivAt_orderChart_apply t i).smul_const (vertex i))
  exact this

lemma fderiv_fderiv_orderPotential (t : EuclideanSpace ℝ (Fin 2)) :
    DifferentiableAt ℝ (fderiv ℝ orderPotential) t ∧
    ∀ h k, fderiv ℝ (fderiv ℝ orderPotential) t h k = inner ℝ h k / kappa0 - orderCov t h k := by
  have hg : HasFDerivAt (fun s : EuclideanSpace ℝ (Fin 2) => kappa0⁻¹ • s - meanVector (orderChart s))
      (kappa0⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) -
        ∑ i, (orderChart t i • (innerSL ℝ (vertex i) -
          innerSL ℝ (meanVector (orderChart t)))).smulRight (vertex i)) t :=
    ((hasFDerivAt_id t).const_smul kappa0⁻¹).sub (hasFDerivAt_meanVector_chart t)
  set Lc : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 2))).toContinuousLinearMap
    with hLc
  have hLc_apply : ∀ x y, Lc x y = inner ℝ x y := fun x y => rfl
  have hL := Lc.hasFDerivAt (x := kappa0⁻¹ • t - meanVector (orderChart t))
  have hc := hL.comp t hg
  have hfun : fderiv ℝ orderPotential =
      ⇑Lc ∘
        fun s : EuclideanSpace ℝ (Fin 2) => kappa0⁻¹ • s - meanVector (orderChart s) := by
    funext s
    rw [fderiv_orderPotential s]
    ext y
    simp [hLc_apply]
  rw [← hfun] at hc
  refine ⟨hc.differentiableAt, fun h k => ?_⟩
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply, sum_apply,
    ContinuousLinearMap.smulRight_apply, hLc_apply, innerSL_apply_apply, inner_sub_left, sum_inner,
    inner_smul_left, conj_trivial, smul_eq_mul]
  unfold orderCov
  rw [inner_meanVector_left]
  have key : ∀ A : ℝ, ∑ x, orderChart t x * (inner ℝ (vertex x) h - A) * inner ℝ (vertex x) k =
      ∑ x, orderChart t x * inner ℝ (vertex x) h * inner ℝ (vertex x) k -
        A * ∑ x, orderChart t x * inner ℝ (vertex x) k := by
    intro A
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [key]
  have hk := kappa0_pos
  field_simp

/-- The unit vector `(0, 1)`, orthogonal to the distinguished vertex `v₁ = (1, 0)`. -/
noncomputable def tangentDirection : EuclideanSpace ℝ (Fin 2) := !₂[0, 1]

/-- The axis `t(r) = (2/3) (log r) v₁`. -/
noncomputable def axisPoint (r : ℝ) : EuclideanSpace ℝ (Fin 2) := ((2 / 3 : ℝ) * Real.log r) • vertex 0

lemma inner_vertex_zero_left (k : EuclideanSpace ℝ (Fin 2)) : inner ℝ (vertex 0) k = k 0 := by
  simp [vertex_zero, inner, Fin.sum_univ_two]

lemma inner_vertex_one_left (k : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (vertex 1) k = -(1 / 2) * k 0 + √3 / 2 * k 1 := by
  simp [vertex_one, inner, Fin.sum_univ_two]; ring

lemma inner_vertex_two_left (k : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (vertex 2) k = -(1 / 2) * k 0 - √3 / 2 * k 1 := by
  simp [vertex_two, inner, Fin.sum_univ_two]; ring

lemma inner_eq_coord (h k : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ h k = h 0 * k 0 + h 1 * k 1 := by
  simp [inner, Fin.sum_univ_two]; ring

lemma tangentDirection_zero : tangentDirection 0 = 0 := by simp [tangentDirection]
lemma tangentDirection_one : tangentDirection 1 = 1 := by simp [tangentDirection]

lemma orderChart_axisPoint {r : ℝ} (hr : 0 < r) : orderChart (axisPoint r) = pointR r := by
  have h0 : Real.exp (inner ℝ (axisPoint r) (vertex 0)) = r * Real.exp (-(1 / 3 * Real.log r)) := by
    have : inner ℝ (axisPoint r) (vertex 0) = Real.log r + -(1 / 3 * Real.log r) := by
      unfold axisPoint
      rw [inner_smul_left, inner_vertex_self]; simp; ring
    rw [this, Real.exp_add, Real.exp_log hr]
  have h1 : ∀ j : Fin 3, j ≠ 0 → Real.exp (inner ℝ (axisPoint r) (vertex j)) =
      Real.exp (-(1 / 3 * Real.log r)) := by
    intro j hj
    have : inner ℝ (axisPoint r) (vertex j) = -(1 / 3 * Real.log r) := by
      unfold axisPoint
      rw [inner_smul_left, inner_vertex_ne (Ne.symm hj)]; simp; ring
    rw [this]
  have hE := Real.exp_pos (-(1 / 3 * Real.log r))
  have h2 : r + 2 ≠ 0 := by positivity
  funext i
  unfold orderChart
  rw [Fin.sum_univ_three, h0, h1 1 (by decide), h1 2 (by decide)]
  fin_cases i
  · simp [h0, pointR]
    field_simp
    ring
  · simp [h1 1 (by decide), pointR]
    field_simp
    ring
  · simp [h1 2 (by decide), pointR]
    field_simp
    ring

lemma orderCov_zero (h k : EuclideanSpace ℝ (Fin 2)) :
    orderCov 0 h k = 1 / 2 * inner ℝ h k := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold orderCov
  rw [orderChart_zero]
  simp only [Fin.sum_univ_three, inner_vertex_zero_left, inner_vertex_one_left,
    inner_vertex_two_left]
  rw [inner_eq_coord]
  linear_combination (1 / 6 * h 1 * k 1) * h3

lemma hessian_zero (h k : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fderiv ℝ orderPotential) 0 h k = 1 / 22 * inner ℝ h k := by
  rw [(fderiv_fderiv_orderPotential 0).2, orderCov_zero]
  unfold kappa0
  ring

lemma orderCov_radial {t : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r)
    (ht : orderChart t = pointR r) (k : EuclideanSpace ℝ (Fin 2)) :
    orderCov t (vertex 0) k = 9 * r / (2 * (r + 2) ^ 2) * inner ℝ (vertex 0) k := by
  have h2 : r + 2 ≠ 0 := by positivity
  unfold orderCov
  rw [ht]
  simp only [Fin.sum_univ_three, pointR, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, inner_vertex_self,
    inner_vertex_ne (show (1 : Fin 3) ≠ 0 by decide), inner_vertex_ne (show (2 : Fin 3) ≠ 0 by decide),
    inner_vertex_zero_left, inner_vertex_one_left, inner_vertex_two_left]
  field_simp
  ring

lemma orderCov_tangent {t : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r)
    (ht : orderChart t = pointR r) (k : EuclideanSpace ℝ (Fin 2)) :
    orderCov t tangentDirection k = 3 / (2 * (r + 2)) * inner ℝ tangentDirection k := by
  have h2 : r + 2 ≠ 0 := by positivity
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold orderCov
  rw [ht]
  simp only [Fin.sum_univ_three, pointR, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, inner_vertex_zero_left,
    inner_vertex_one_left, inner_vertex_two_left, tangentDirection_zero, tangentDirection_one,
    inner_eq_coord tangentDirection k]
  field_simp
  linear_combination ((2 * r + 4) * k 1) * h3

lemma deriv_criticalFunction_eq {r : ℝ} (hr : 0 < r) :
    deriv (criticalFunction beta0) r = 1 / r - 3 * beta0 / (r + 2) ^ 2 := by
  rw [(hasDerivAt_criticalFunction beta0 hr).deriv]
  have h2 : r + 2 ≠ 0 := by positivity
  field_simp
  ring


lemma beta0_eq : beta0 = 11 / 4 := rfl

lemma hessian_radial {t : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r)
    (ht : orderChart t = pointR r) (k : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fderiv ℝ orderPotential) t (vertex 0) k =
      3 * r / (2 * beta0) * deriv (criticalFunction beta0) r * inner ℝ (vertex 0) k := by
  rw [(fderiv_fderiv_orderPotential t).2, orderCov_radial hr ht, deriv_criticalFunction_eq hr]
  have h2 : r + 2 ≠ 0 := by positivity
  unfold kappa0 beta0
  field_simp
  ring

lemma hessian_tangent {t : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r)
    (ht : orderChart t = pointR r) (k : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fderiv ℝ orderPotential) t tangentDirection k =
      3 * (r + 2 - beta0) / (2 * beta0 * (r + 2)) * inner ℝ tangentDirection k := by
  rw [(fderiv_fderiv_orderPotential t).2, orderCov_tangent hr ht]
  have h2 : r + 2 ≠ 0 := by positivity
  unfold kappa0 beta0
  field_simp
  ring

lemma hessian_radial_link {r : ℝ} (hr : 0 < r) :
    3 * r / (2 * beta0) * deriv (criticalFunction beta0) r =
      3 * r / (4 * beta0 * (r + 2) ^ 2) * hessianForm beta0 (pointR r) tangentW := by
  rw [hessianForm_pointR_w beta0 r hr]
  have h2 : r + 2 ≠ 0 := by positivity
  have hb : beta0 ≠ 0 := by unfold beta0; norm_num
  field_simp
  ring

lemma hessian_tangent_link {r : ℝ} (hr : 0 < r) :
    3 * (r + 2 - beta0) / (2 * beta0 * (r + 2)) =
      3 / (4 * beta0 * (r + 2)) * hessianForm beta0 (pointR r) tangentV := by
  rw [hessianForm_pointR_v beta0 r hr]
  have h2 : r + 2 ≠ 0 := by positivity
  have hb : beta0 ≠ 0 := by unfold beta0; norm_num
  field_simp
  ring

lemma frame_orthonormal :
    inner ℝ (vertex 0) (vertex 0) = 1 ∧ inner ℝ tangentDirection tangentDirection = 1 ∧
      inner ℝ (vertex 0) tangentDirection = 0 := by
  refine ⟨inner_vertex_self 0, ?_, ?_⟩
  · rw [inner_eq_coord, tangentDirection_zero, tangentDirection_one]; norm_num
  · rw [inner_vertex_zero_left, tangentDirection_zero]

lemma logPartition_le (t : EuclideanSpace ℝ (Fin 2)) : logPartition t ≤ ‖t‖ := by
  unfold logPartition
  have hpos : 0 < 1 / 3 * ∑ i, Real.exp (inner ℝ t (vertex i)) := by
    have := gibbsSum_pos t; positivity
  rw [Real.log_le_iff_le_exp hpos]
  have hle : ∀ i, Real.exp (inner ℝ t (vertex i)) ≤ Real.exp ‖t‖ := fun i => by
    apply Real.exp_le_exp.2
    calc inner ℝ t (vertex i) ≤ ‖t‖ * ‖vertex i‖ := real_inner_le_norm _ _
      _ = ‖t‖ := by rw [norm_vertex, mul_one]
  have h1 : ∑ i, Real.exp (inner ℝ t (vertex i)) ≤ ∑ _i : Fin 3, Real.exp ‖t‖ :=
    Finset.sum_le_sum fun i _ => hle i
  have h3 : ∑ _i : Fin 3, Real.exp ‖t‖ = 3 * Real.exp ‖t‖ := by simp
  linarith

lemma orderPotential_ge (t : EuclideanSpace ℝ (Fin 2)) :
    ‖t‖ ^ 2 / (2 * kappa0) - ‖t‖ ≤ orderPotential t := by
  unfold orderPotential
  linarith [logPartition_le t]

lemma tendsto_quadratic_tail :
    Filter.Tendsto (fun x : ℝ => x ^ 2 / (2 * kappa0) - x) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨max (4 * kappa0) b, fun a ha => ?_⟩
  have h1 : 4 * kappa0 ≤ a := le_trans (le_max_left _ _) ha
  have h2 : b ≤ a := le_trans (le_max_right _ _) ha
  have hk := kappa0_pos
  have ha0 : 0 ≤ a := by linarith
  have : a ≤ a ^ 2 / (2 * kappa0) - a := by
    rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha0]
  linarith

lemma tendsto_coercive_lower :
    Filter.Tendsto (fun t : EuclideanSpace ℝ (Fin 2) => ‖t‖ ^ 2 / (2 * kappa0) - ‖t‖)
      (Filter.cocompact _) Filter.atTop :=
  tendsto_quadratic_tail.comp tendsto_norm_cocompact_atTop

lemma tendsto_orderPotential :
    Filter.Tendsto orderPotential (Filter.cocompact (EuclideanSpace ℝ (Fin 2))) Filter.atTop :=
  Filter.tendsto_atTop_mono orderPotential_ge tendsto_coercive_lower

lemma meanVector_pointR {r : ℝ} (hr : 0 < r) :
    meanVector (pointR r) = ((r - 1) / (r + 2)) • vertex 0 := by
  have h2 : r + 2 ≠ 0 := by positivity
  ext j
  fin_cases j
  · simp [meanVector, Fin.sum_univ_three, pointR, vertex_zero, vertex_one, vertex_two]
    field_simp
    ring
  · simp [meanVector, Fin.sum_univ_three, pointR, vertex_zero, vertex_one, vertex_two]

lemma hasDerivAt_axisPoint {r : ℝ} (hr : 0 < r) :
    HasDerivAt axisPoint ((2 / 3 * r⁻¹) • vertex 0) r :=
  ((Real.hasDerivAt_log hr.ne').const_mul (2 / 3 : ℝ)).smul_const (vertex 0)

lemma hasDerivAt_orderPotential_axis {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun x => orderPotential (axisPoint x))
      (2 * criticalFunction beta0 r / (3 * beta0 * r)) r := by
  have h := (hasFDerivAt_orderPotential (axisPoint r)).comp_hasDerivAt r (hasDerivAt_axisPoint hr)
  refine h.congr_deriv ?_
  rw [orderChart_axisPoint hr, meanVector_pointR hr]
  have hw : kappa0⁻¹ • axisPoint r - ((r - 1) / (r + 2)) • vertex 0 =
      (kappa0⁻¹ * (2 / 3 * Real.log r) - (r - 1) / (r + 2)) • vertex 0 := by
    unfold axisPoint
    rw [smul_smul, ← sub_smul]
  rw [hw, innerSL_apply_apply, inner_smul_left, inner_smul_right, inner_vertex_self]
  have h2 : r + 2 ≠ 0 := by positivity
  have hr0 : r ≠ 0 := hr.ne'
  unfold criticalFunction kappa0 beta0
  simp only [conj_trivial]
  field_simp
  ring

lemma orderPotential_axisPoint {r : ℝ} (hr : 0 < r) :
    orderPotential (axisPoint r) =
      freeEnergy beta0 (pointR r) + (2 / 3 * criticalFunction beta0 r) ^ 2 / (2 * kappa0) := by
  rw [orderPotential_eq, orderChart_axisPoint hr, meanVector_pointR hr]
  have h2 : r + 2 ≠ 0 := by positivity
  have hv : axisPoint r - kappa0 • (((r - 1) / (r + 2)) • vertex 0) =
      (2 / 3 * criticalFunction beta0 r) • vertex 0 := by
    unfold axisPoint criticalFunction kappa0 beta0
    rw [smul_smul, ← sub_smul]
    congr 1
    field_simp
    ring
  rw [hv, norm_smul, norm_vertex, mul_one, Real.norm_eq_abs, sq_abs]

lemma axis_max {rs rm : ℝ} (h2rs : 2 < rs) (hrs3 : rs < 3) (h3rm : 3 < rm)
    (hroots : ∀ r : ℝ, 0 < r → (criticalFunction (11 / 4) r = 0 ↔ r = 1 ∨ r = rs ∨ r = rm)) :
    ∀ r ∈ Set.Icc 1 rm, orderPotential (axisPoint r) ≤ orderPotential (axisPoint rs) := by
  obtain ⟨hs1, hs2⟩ := criticalFunction_sign_between h2rs hrs3 h3rm hroots
  have hd : ∀ r : ℝ, 0 < r → HasDerivAt (fun x => orderPotential (axisPoint x))
      (2 * criticalFunction beta0 r / (3 * beta0 * r)) r := fun r hr =>
    hasDerivAt_orderPotential_axis hr
  have hb : 0 < beta0 := by unfold beta0; norm_num
  have hcont : ∀ a b : ℝ, 0 < a → ContinuousOn (fun x => orderPotential (axisPoint x))
      (Set.Icc a b) := fun a b ha x hx =>
    (hd x (lt_of_lt_of_le ha hx.1)).continuousAt.continuousWithinAt
  have hmono : MonotoneOn (fun x => orderPotential (axisPoint x)) (Set.Icc 1 rs) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 1 rs) (hcont 1 rs one_pos) ?_ ?_
    · rw [interior_Icc]
      intro x hx
      exact (hd x (by linarith [hx.1])).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      rw [(hd x hx0).deriv]
      have := hs1 x hx.1 hx.2
      positivity
  have hanti : AntitoneOn (fun x => orderPotential (axisPoint x)) (Set.Icc rs rm) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc rs rm) (hcont rs rm (by linarith)) ?_ ?_
    · rw [interior_Icc]
      intro x hx
      exact (hd x (by linarith [hx.1])).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      rw [(hd x hx0).deriv]
      have h5 : criticalFunction beta0 x < 0 := hs2 x hx.1 hx.2
      have : 2 * criticalFunction beta0 x < 0 := by linarith
      exact (div_neg_of_neg_of_pos this (by positivity)).le
  intro r hr
  rcases le_or_gt r rs with h | h
  · exact hmono ⟨hr.1, h⟩ ⟨by linarith, le_refl _⟩ h
  · exact hanti ⟨le_refl _, by linarith⟩ ⟨h.le, hr.2⟩ h.le

lemma barrier_lower {rs rm : ℝ}
    (hbar : ∀ p ∈ pointROrbit rm,
      IsLeast {c : ℝ | ∃ γ : ℝ → Fin 3 → ℝ, IsSimplexPath p (fun _ => 1 / 3) γ ∧
        ∃ s ∈ Set.Icc (0 : ℝ) 1, IsMaxOn (fun t => freeEnergy (11 / 4) (γ t)) (Set.Icc 0 1) s ∧
          c = freeEnergy (11 / 4) (γ s)} (freeEnergy (11 / 4) (pointR rs)))
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)} (hc : ContinuousOn γ (Set.Icc 0 1))
    (h0 : orderChart (γ 0) ∈ pointROrbit rm) (h1 : γ 1 = 0) {s : ℝ}
    (hmax : IsMaxOn (fun τ => orderPotential (γ τ)) (Set.Icc 0 1) s) :
    freeEnergy (11 / 4) (pointR rs) ≤ orderPotential (γ s) := by
  have hqc : ContinuousOn (fun τ => orderChart (γ τ)) (Set.Icc 0 1) :=
    orderChart_contDiff.continuous.comp_continuousOn hc
  have hq : IsSimplexPath (orderChart (γ 0)) (fun _ => 1 / 3) (fun τ => orderChart (γ τ)) :=
    ⟨hqc, fun τ _ => orderChart_mem_simplex _, rfl, by
      show orderChart (γ 1) = _
      rw [h1, orderChart_zero]⟩
  have hFc : ContinuousOn (fun τ => freeEnergy (11 / 4) (orderChart (γ τ))) (Set.Icc 0 1) :=
    (continuous_freeEnergy _).comp_continuousOn hqc
  obtain ⟨s', hs', hmax'⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
    (Set.nonempty_Icc.2 zero_le_one) hFc
  have hB := (hbar _ h0).2 ⟨_, hq, s', hs', hmax', rfl⟩
  have key : freeEnergy (11 / 4) (orderChart (γ s')) ≤ orderPotential (γ s') := by
    have e : freeEnergy beta0 (orderChart (γ s')) ≤ orderPotential (γ s') := by
      rw [orderPotential_eq (γ s')]
      have := kappa0_pos
      have : 0 ≤ ‖γ s' - kappa0 • meanVector (orderChart (γ s'))‖ ^ 2 / (2 * kappa0) := by
        positivity
      linarith
    exact e
  have hle : orderPotential (γ s') ≤ orderPotential (γ s) := isMaxOn_iff.1 hmax s' hs'
  linarith


/-- **RUF019, order-parameter Hessians and coercive tail.**  (1) `D²Ψ∞ = κ⁻¹ I - Cov_p(v)`
(`orderCov`).  (2) at any `t` with chart `p(t) = p(r)`, in the orthonormal frame `v₁ = vertex 0`,
`(0,1)` the covariance and Hessian act diagonally, with covariance eigenvalues
`9r/[2(r+2)²]`, `3/[2(r+2)]` and Hessian eigenvalues `(3r/(2β₀)) f'(r)`,
`3(r+2-β₀)/[2β₀(r+2)]` (also expressed through the RUF016 forms).  (3) `D²Ψ∞(0) = I/22`.
(4) `Ψ∞(t) ≥ ‖t‖²/(2κ) - ‖t‖ → ∞` along `cocompact`.  (5) the axis `t(r) = (2/3)(log r) v₁`
has chart `p(r)`, `d/dr Ψ∞(t(r)) = 2 f(r)/(3β₀ r)`, `Ψ∞(t(r)) = F(p(r)) + ((2/3) f(r))²/(2κ)`, and
with the RUF017 radii `rs < rm` the minimax value of `Ψ∞` over continuous parameter paths from
the minimum chart orbit to `0` is at least `B∞ = F(p(rs))`, attained exactly by the axis path. -/
theorem order_parameter_hessians_and_coercive_tail :
    (∀ t : EuclideanSpace ℝ (Fin 2), DifferentiableAt ℝ (fderiv ℝ orderPotential) t ∧
      ∀ h k, fderiv ℝ (fderiv ℝ orderPotential) t h k =
        inner ℝ h k / kappa0 - orderCov t h k) ∧
    (inner ℝ (vertex 0) (vertex 0) = 1 ∧ inner ℝ tangentDirection tangentDirection = 1 ∧
      inner ℝ (vertex 0) tangentDirection = 0) ∧
    (∀ (r : ℝ) (t : EuclideanSpace ℝ (Fin 2)), 0 < r → orderChart t = pointR r →
      (∀ k, orderCov t (vertex 0) k = 9 * r / (2 * (r + 2) ^ 2) * inner ℝ (vertex 0) k) ∧
      (∀ k, orderCov t tangentDirection k = 3 / (2 * (r + 2)) * inner ℝ tangentDirection k) ∧
      (∀ k, fderiv ℝ (fderiv ℝ orderPotential) t (vertex 0) k =
        3 * r / (2 * beta0) * deriv (criticalFunction beta0) r * inner ℝ (vertex 0) k) ∧
      (∀ k, fderiv ℝ (fderiv ℝ orderPotential) t tangentDirection k =
        3 * (r + 2 - beta0) / (2 * beta0 * (r + 2)) * inner ℝ tangentDirection k) ∧
      3 * r / (2 * beta0) * deriv (criticalFunction beta0) r =
        3 * r / (4 * beta0 * (r + 2) ^ 2) * hessianForm beta0 (pointR r) tangentW ∧
      3 * (r + 2 - beta0) / (2 * beta0 * (r + 2)) =
        3 / (4 * beta0 * (r + 2)) * hessianForm beta0 (pointR r) tangentV) ∧
    (∀ h k, fderiv ℝ (fderiv ℝ orderPotential) 0 h k = 1 / 22 * inner ℝ h k) ∧
    (∀ t : EuclideanSpace ℝ (Fin 2), ‖t‖ ^ 2 / (2 * kappa0) - ‖t‖ ≤ orderPotential t) ∧
    Filter.Tendsto (fun t : EuclideanSpace ℝ (Fin 2) => ‖t‖ ^ 2 / (2 * kappa0) - ‖t‖)
      (Filter.cocompact _) Filter.atTop ∧
    Filter.Tendsto orderPotential (Filter.cocompact (EuclideanSpace ℝ (Fin 2))) Filter.atTop ∧
    (∀ r : ℝ, 0 < r → orderChart (axisPoint r) = pointR r ∧
      HasDerivAt (fun x => orderPotential (axisPoint x))
        (2 * criticalFunction beta0 r / (3 * beta0 * r)) r ∧
      orderPotential (axisPoint r) = freeEnergy beta0 (pointR r) +
        (2 / 3 * criticalFunction beta0 r) ^ 2 / (2 * kappa0)) ∧
    ∃ rs rm : ℝ, 2 < rs ∧ rs < rm ∧ 3 < rm ∧ rm < 4 ∧
      (∀ r : ℝ, 0 < r → (criticalFunction (11 / 4) r = 0 ↔ r = 1 ∨ r = rs ∨ r = rm)) ∧
      (∀ p ∈ pointROrbit rm,
        IsLeast {c : ℝ | ∃ γ : ℝ → Fin 3 → ℝ, IsSimplexPath p (fun _ => 1 / 3) γ ∧
          ∃ s ∈ Set.Icc (0 : ℝ) 1, IsMaxOn (fun t => freeEnergy (11 / 4) (γ t)) (Set.Icc 0 1) s ∧
            c = freeEnergy (11 / 4) (γ s)} (freeEnergy (11 / 4) (pointR rs))) ∧
      (∀ γ : ℝ → EuclideanSpace ℝ (Fin 2), ContinuousOn γ (Set.Icc 0 1) →
        orderChart (γ 0) ∈ pointROrbit rm → γ 1 = 0 → ∀ s ∈ Set.Icc (0 : ℝ) 1,
          IsMaxOn (fun τ => orderPotential (γ τ)) (Set.Icc 0 1) s →
          freeEnergy (11 / 4) (pointR rs) ≤ orderPotential (γ s)) ∧
      IsLeast {c : ℝ | ∃ γ : ℝ → EuclideanSpace ℝ (Fin 2), ContinuousOn γ (Set.Icc 0 1) ∧
          γ 0 = axisPoint rm ∧ γ 1 = 0 ∧ ∃ s ∈ Set.Icc (0 : ℝ) 1,
            IsMaxOn (fun τ => orderPotential (γ τ)) (Set.Icc 0 1) s ∧
              c = orderPotential (γ s)} (freeEnergy (11 / 4) (pointR rs)) := by
  obtain ⟨rs, rm, h2rs, hrsrm, h3rm, hrm4, hroots, -, -, -, hbar, -⟩ := exact_discrete_path_barrier
  obtain ⟨f2, f3, -⟩ := criticalFunction_eleven_quarters_signs
  have hrs3 : rs < 3 := by
    have hcont : ContinuousOn (criticalFunction (11 / 4)) (Set.Icc 2 3) :=
      criticalFunction_continuousOn_pos (fun z hz => by
        have := hz.1
        exact lt_of_lt_of_le (by norm_num) this) _
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' (by norm_num : (2 : ℝ) ≤ 3) hcont
      ⟨f3.le, f2.le⟩
    rcases (hroots c (by linarith [hc.1])).1 hc0 with h | h | h
    · linarith [hc.1]
    · rcases lt_or_eq_of_le (h ▸ hc.2 : rs ≤ 3) with h' | h'
      · exact h'
      · exfalso
        have := (hroots 3 (by norm_num)).2 (Or.inr (Or.inl h'.symm))
        linarith
    · linarith [hc.2]
  have hlow := fun γ hc h0 h1 s hmax => barrier_lower (rs := rs) (rm := rm) hbar
    (γ := γ) hc h0 h1 (s := s) hmax
  have hlogrm : 0 < Real.log rm := Real.log_pos (by linarith)
  have hlogrs : 0 < Real.log rs := Real.log_pos (by linarith)
  have hlogle : Real.log rs ≤ Real.log rm := Real.log_le_log (by linarith) (by linarith)
  -- the axis path `τ ↦ t(rm^(1-τ))`
  set γa : ℝ → EuclideanSpace ℝ (Fin 2) :=
    fun τ => ((1 - τ) * ((2 / 3 : ℝ) * Real.log rm)) • vertex 0 with hγa
  have hγa_axis : ∀ τ, γa τ = axisPoint (Real.exp ((1 - τ) * Real.log rm)) := by
    intro τ
    simp only [hγa, axisPoint, Real.log_exp]
    congr 1
    ring
  have hγa_cont : ContinuousOn γa (Set.Icc 0 1) :=
    Continuous.continuousOn (by simp only [hγa]; fun_prop)
  have hγa0 : γa 0 = axisPoint rm := by
    rw [hγa_axis]; simp [Real.exp_log (show 0 < rm by linarith)]
  have hγa1 : γa 1 = 0 := by simp [hγa]
  refine ⟨fun t => ⟨(fderiv_fderiv_orderPotential t).1, (fderiv_fderiv_orderPotential t).2⟩,
    frame_orthonormal, fun r t hr ht => ⟨orderCov_radial hr ht, orderCov_tangent hr ht,
      hessian_radial hr ht, hessian_tangent hr ht, hessian_radial_link hr,
      hessian_tangent_link hr⟩, hessian_zero, orderPotential_ge, tendsto_coercive_lower,
    tendsto_orderPotential, fun r hr => ⟨orderChart_axisPoint hr, hasDerivAt_orderPotential_axis hr,
      orderPotential_axisPoint hr⟩, rs, rm, h2rs, hrsrm, h3rm, hrm4, hroots, hbar,
    fun γ hc h0 h1 s hs hmax => hlow γ hc h0 h1 s hmax, ?_, ?_⟩
  · -- the axis path attains `B∞`
    have hrs0 : 0 < rs := by linarith
    have hrm0 : 0 < rm := by linarith
    set s0 : ℝ := 1 - Real.log rs / Real.log rm with hs0
    have hdiv0 : 0 ≤ Real.log rs / Real.log rm := div_nonneg hlogrs.le hlogrm.le
    have hdiv1 : Real.log rs / Real.log rm ≤ 1 := (div_le_one hlogrm).2 hlogle
    have hs0mem : s0 ∈ Set.Icc (0 : ℝ) 1 := ⟨by rw [hs0]; linarith, by rw [hs0]; linarith⟩
    have hexp : Real.exp ((1 - s0) * Real.log rm) = rs := by
      have : (1 - s0) * Real.log rm = Real.log rs := by
        rw [hs0]; field_simp; ring
      rw [this, Real.exp_log hrs0]
    have hval : orderPotential (γa s0) = freeEnergy (11 / 4) (pointR rs) := by
      rw [hγa_axis, hexp, orderPotential_axisPoint hrs0]
      have hf : criticalFunction beta0 rs = 0 := (hroots rs hrs0).2 (Or.inr (Or.inl rfl))
      rw [hf]
      show freeEnergy (11 / 4) (pointR rs) + (2 / 3 * 0) ^ 2 / (2 * kappa0) = _
      ring
    refine ⟨γa, hγa_cont, hγa0, hγa1, s0, hs0mem, ?_, hval.symm⟩
    intro τ hτ
    show orderPotential (γa τ) ≤ orderPotential (γa s0)
    rw [hγa_axis τ, hγa_axis s0, hexp]
    refine axis_max h2rs hrs3 h3rm hroots _ ⟨?_, ?_⟩
    · exact Real.one_le_exp (mul_nonneg (by linarith [hτ.2]) hlogrm.le)
    · calc Real.exp ((1 - τ) * Real.log rm) ≤ Real.exp (Real.log rm) :=
            Real.exp_le_exp.2 (by nlinarith [hτ.1])
        _ = rm := Real.exp_log hrm0
  · rintro c ⟨γ, hc, h0, h1, s, hs, hmax, rfl⟩
    refine hlow γ hc ?_ h1 s hmax
    rw [h0, orderChart_axisPoint (by linarith)]
    exact ⟨1, by funext i; simp⟩

end DGPS.Examples.RoughBoundary.Landscape
