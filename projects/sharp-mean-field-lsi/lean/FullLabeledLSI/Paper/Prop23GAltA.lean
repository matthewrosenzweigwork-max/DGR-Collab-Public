import FullLabeledLSI.Paper.Prop23FAltA

/-!
# Proposition 2.3, WP-G (alt), part A: uniform moments of the weights `u_R(Z_N)`, `v_R(Z_N)`

`UB μ g` says that the family `g N : Config N d → ℝ` is bounded in every finite `L^q(Q_N)` uniformly
in `N ≥ 1`.  It is closed under sums, products and constants, contains `Z_N = fluct eC`, and hence
contains `u_R(Z_N)` and `v_R(Z_N)` (computed with `e`, by the a.e. transfer).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- Uniform `L^q` bounds for all finite `q ≥ 1`, for `N ≥ 1`. -/
def UB (μ : Measure (Torus d)) (g : (N : ℕ) → Config N d → ℝ) : Prop :=
  ∀ q : ℝ≥0∞, 1 ≤ q → q ≠ ⊤ → ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
    MemLp (g N) q (QN μ N) ∧ eLpNorm (g N) q (QN μ N) ≤ ENNReal.ofReal K

section UBLemmas

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

theorem UB.const (c : ℝ) : UB μ (fun _ _ => c) := by
  intro q hq1 hq
  refine ⟨|c|, abs_nonneg _, fun N _ => ⟨memLp_const c, ?_⟩⟩
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq1).ne'
  rw [eLpNorm_const' c hq0 hq]
  simp [Real.enorm_eq_ofReal_abs]

theorem UB.add {g h : (N : ℕ) → Config N d → ℝ} (hg : UB μ g) (hh : UB μ h) :
    UB μ (fun N X => g N X + h N X) := by
  intro q hq1 hq
  obtain ⟨K1, hK1, h1⟩ := hg q hq1 hq
  obtain ⟨K2, hK2, h2⟩ := hh q hq1 hq
  refine ⟨K1 + K2, add_nonneg hK1 hK2, fun N hN => ⟨(h1 N hN).1.add (h2 N hN).1, ?_⟩⟩
  beta_reduce
  have := eLpNorm_add_le (p := q) (μ := QN μ N) (f := g N) (g := h N) hq1
  rw [ENNReal.ofReal_add hK1 hK2]
  exact this.trans (add_le_add (h1 N hN).2 (h2 N hN).2)

theorem UB.const_mul {g : (N : ℕ) → Config N d → ℝ} (hg : UB μ g) (c : ℝ) :
    UB μ (fun N X => c * g N X) := by
  intro q hq1 hq
  obtain ⟨K, hK, h1⟩ := hg q hq1 hq
  refine ⟨|c| * K, mul_nonneg (abs_nonneg _) hK, fun N hN => ⟨(h1 N hN).1.const_mul c, ?_⟩⟩
  rw [schroC_eLpNorm_const_mul, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_mul (abs_nonneg _)]
  exact mul_le_mul_right (h1 N hN).2 _

theorem UB.neg_sub {g h : (N : ℕ) → Config N d → ℝ} (hg : UB μ g) (hh : UB μ h) :
    UB μ (fun N X => g N X - h N X) := by
  have := hg.add (hh.const_mul (-1))
  refine fun q hq1 hq => ?_
  obtain ⟨K, hK, h1⟩ := this q hq1 hq
  refine ⟨K, hK, fun N hN => ?_⟩
  have e : (fun X => g N X - h N X) = fun X => g N X + -1 * h N X := by
    funext X; ring
  have h1N := h1 N hN
  beta_reduce at h1N ⊢
  rw [e]
  exact h1N

instance ud_holder (q : ℝ≥0∞) : ENNReal.HolderTriple (2 * q) (2 * q) q where
  inv_add_inv_eq_inv := by
    rw [ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
    rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]

theorem UB.mul {g h : (N : ℕ) → Config N d → ℝ} (hg : UB μ g) (hh : UB μ h) :
    UB μ (fun N X => g N X * h N X) := by
  intro q hq1 hq
  have hq2 : 1 ≤ 2 * q := le_trans hq1 (le_mul_of_one_le_left zero_le (by norm_num))
  have hq2' : 2 * q ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hq
  obtain ⟨K1, hK1, h1⟩ := hg (2 * q) hq2 hq2'
  obtain ⟨K2, hK2, h2⟩ := hh (2 * q) hq2 hq2'
  refine ⟨K1 * K2, mul_nonneg hK1 hK2, fun N hN => ⟨?_, ?_⟩⟩
  · exact (h1 N hN).1.fun_mul (h2 N hN).1
  · have := schroC_holder (p := 2 * q) (q := 2 * q) (r := q) (ν := QN μ N)
      (φ := g N) (f := h N) (h1 N hN).1.aestronglyMeasurable (h2 N hN).1.aestronglyMeasurable
    rw [ENNReal.ofReal_mul hK1]
    exact this.trans (mul_le_mul' (h1 N hN).2 (h2 N hN).2)

theorem UB.sum {ι : Type*} (s : Finset ι) {g : ι → (N : ℕ) → Config N d → ℝ}
    (hg : ∀ i ∈ s, UB μ (g i)) : UB μ (fun N X => ∑ i ∈ s, g i N X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using UB.const (μ := μ) 0
  | insert a s ha ih =>
    have h1 := hg a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have := h1.add h2
    intro q hq1 hq
    obtain ⟨K, hK, hh⟩ := this q hq1 hq
    refine ⟨K, hK, fun N hN => ?_⟩
    simpa [Finset.sum_insert ha] using hh N hN

theorem UB.congr_ae {g h : (N : ℕ) → Config N d → ℝ} (hg : UB μ g)
    (hae : ∀ N, h N =ᵐ[QN μ N] g N) : UB μ h := by
  intro q hq1 hq
  obtain ⟨K, hK, h1⟩ := hg q hq1 hq
  exact ⟨K, hK, fun N hN => ⟨(h1 N hN).1.ae_eq (hae N).symm,
    (eLpNorm_congr_ae (hae N)).trans_le (h1 N hN).2⟩⟩

theorem UB.sq {g : (N : ℕ) → Config N d → ℝ} (hg : UB μ g) : UB μ (fun N X => g N X ^ 2) := by
  have e : (fun (N : ℕ) (X : Config N d) => g N X ^ 2) = fun N X => g N X * g N X := by
    funext N X; ring
  rw [e]
  exact hg.mul hg

end UBLemmas

section FluctUB

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} (hyp : Hyp V W KV KW)
  {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
  (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j)
include hyp hμ he hφ heC

theorem UB_fluct (n : ℕ) : UB (μ : Measure (Torus d)) (fun N X => fluct eC N n X) := by
  intro q hq1 hq
  obtain ⟨n0, hn0⟩ := ENNReal.exists_nat_gt hq
  obtain ⟨C, hC0, hC⟩ := fluct_moment_eC hyp hμ he hφ heC n (n0 + 1)
  refine ⟨C ^ (1 / ((2 * (n0 + 1) : ℕ) : ℝ)), by positivity, fun N hN => ⟨?_, ?_⟩⟩
  · exact (schroC_Z_facts (μ := (μ : Measure (Torus d))) hφ n N).2.mono_exponent le_top
  · have hqle : q ≤ ((2 * (n0 + 1) : ℕ) : ℝ≥0∞) :=
      hn0.le.trans (by exact_mod_cast (by omega : n0 ≤ 2 * (n0 + 1)))
    refine (eLpNorm_le_eLpNorm_of_exponent_le hqle).trans ?_
    exact schroC_eLpNorm_le (schroC_Z_facts (μ := (μ : Measure (Torus d))) hφ n N).2 (n0 + 1)
      (2 * (n0 + 1)) rfl (by omega) (hC N hN)

end FluctUB

section WeightUB

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} (hyp : Hyp V W KV KW)
  {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
  (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j)
  (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (R : ℕ)
include hyp hμ he hφ heC

theorem UB_uR : UB (μ : Measure (Torus d))
    (fun N X => uR A R (fun n => fluct e N n X)) := by
  have hac := minimizer_ac hyp hμ
  have h : UB (μ : Measure (Torus d)) (fun N X => uR A R (fun n => fluct eC N n X)) := by
    unfold uR
    refine UB.const_mul (UB.sum _ fun i _ => UB.sum _ fun j _ => ?_) _
    exact (((UB_fluct hyp hμ he hφ heC i).const_mul _).mul (UB_fluct hyp hμ he hφ heC j))
  exact h.congr_ae fun N => fa_ae_comp hac heC N (uR A R)

theorem UB_vR : UB (μ : Measure (Torus d))
    (fun N X => vR A lam R (fun n => fluct e N n X)) := by
  have hac := minimizer_ac hyp hμ
  have hZ := UB_fluct hyp hμ he hφ heC
  have h : UB (μ : Measure (Torus d)) (fun N X => vR A lam R (fun n => fluct eC N n X)) := by
    unfold vR
    refine UB.add (UB.neg_sub (UB.const_mul (UB.sum _ fun m _ => UB.const_mul ?_ _) _)
      (UB.const _)) (UB.const_mul (UB.sum _ fun i _ => UB.sum _ fun j _ => ?_) _)
    · exact UB.sq (UB.sum _ fun j _ => (hZ j).const_mul _)
    · exact (((hZ i).mul (UB.const _)).mul (UB.const _)).mul (hZ j)
  exact h.congr_ae fun N => fa_ae_comp hac heC N (vR A lam R)

end WeightUB

end SharpLSI.FL
