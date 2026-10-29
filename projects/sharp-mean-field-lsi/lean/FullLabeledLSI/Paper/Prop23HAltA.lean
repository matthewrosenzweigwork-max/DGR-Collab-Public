import FullLabeledLSI.Defs.F05_FiniteRank
import FullLabeledLSI.Paper.Sec6Rank3
import FullLabeledLSI.Infra.SpectralMain
import SharpSymmetricLSI.Statements.R25_Lemma_A_2

/-!
# Proposition 2.3, WP-H (alt), part A: the data of the assembly

* `exists_finiteRankApprox`: a `FiniteRankApprox W μ e` (from `kernel_approximation`, Lemma A.2);
* `exists_inv_of_pos`: the finite-section inverse `C_R = (I + T_R)^{-1}` as an `IsInverseOfIPlus`;
* `exists_CR`: a family `CR` with `IsInverseOfIPlus (A.a R) (CR R)` for all large `R`;
* `exists_C1_rep`: `C¹` representatives `eC` of the eigenfunctions (from the cut package).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

section Approx

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- A finite-rank approximation object exists (Lemma A.2). -/
theorem exists_finiteRankApprox (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    Nonempty (FiniteRankApprox W (μ : Measure (Torus d)) e) := by
  classical
  obtain ⟨KR, hKR⟩ := kernel_approximation hd hyp hr hμ he
  choose s a hsymm hform using hKR.1
  refine ⟨⟨s, fun R i j => if i ∈ s R ∧ j ∈ s R then a R i j else 0, ?_, ?_, ?_⟩⟩
  · intro R i j
    by_cases h : i ∈ s R ∧ j ∈ s R
    · simp [h, hsymm R i j]
    · have : ¬ (j ∈ s R ∧ i ∈ s R) := fun h' => h ⟨h'.2, h'.1⟩
      simp [h, this]
  · intro R i j h
    have : ¬ (i ∈ s R ∧ j ∈ s R) := by
      rintro ⟨h1, h2⟩
      rcases h with h | h
      · exact h h1
      · exact h h2
    simp [this]
  · have : (fun R x y => ∑ i ∈ s R, ∑ j ∈ s R,
        (if i ∈ s R ∧ j ∈ s R then a R i j else 0) * e (i + 1) x * e (j + 1) y) = KR := by
      funext R x y
      rw [hform R x y]
      refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
      simp [hi, hj]
    rw [this]
    exact hKR

end Approx

/-! ### The finite-section inverse -/

section Inverse

variable {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}

theorem exists_inv_of_pos (A : FiniteRankApprox W μ e) (R : ℕ) {σ : ℝ} (hσ : 0 < σ)
    (hpos : ∀ v : ℕ → ℝ, (∀ i, i ∉ A.s R → v i = 0) →
      ∑ i ∈ A.s R, ∑ j ∈ A.s R, v i * ((if i = j then 1 else 0) + A.a R i j) * v j ≥
        (σ / 2) * ∑ i ∈ A.s R, v i ^ 2) :
    ∃ C : ℕ → ℕ → ℝ, IsInverseOfIPlus (A.a R) C := by
  classical
  set S := A.s R with hS
  let M : Matrix S S ℝ := fun i j => (if (i : ℕ) = (j : ℕ) then 1 else 0) + A.a R i j
  have hz0 : ∀ z : S → ℝ, M.mulVec z = 0 → z = 0 := by
    intro z hz
    set v : ℕ → ℝ := fun i => if h : i ∈ S then z ⟨i, h⟩ else 0 with hv
    have hvS : ∀ i : S, v i = z i := fun i => by simp [hv, i.2]
    have hv0 : ∀ i, i ∉ A.s R → v i = 0 := fun i hi => by simp [hv, hS ▸ hi]
    have hq : ∑ i ∈ S, ∑ j ∈ S, v i * ((if i = j then 1 else 0) + A.a R i j) * v j = 0 := by
      rw [← Finset.sum_coe_sort S]
      simp_rw [← Finset.sum_coe_sort S (fun j => v _ * _ * v j)]
      have : ∀ i : S, ∑ j : S, v i * ((if (i : ℕ) = j then 1 else 0) + A.a R i j) * v j =
          z i * (M.mulVec z) i := by
        intro i
        rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hvS, hvS]
        simp only [M]
        ring
      simp_rw [this, hz]
      simp
    have h1 := hpos v hv0
    rw [hq] at h1
    have h2 : ∑ i ∈ S, v i ^ 2 ≤ 0 := by
      by_contra hcon
      have := mul_pos (half_pos hσ) (not_le.1 hcon)
      linarith
    have h3 : ∀ i ∈ S, v i ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (v i)).1
        (le_antisymm h2 (Finset.sum_nonneg fun i _ => sq_nonneg (v i)))
    funext i
    have := h3 i i.2
    rw [hvS] at this
    simpa using this
  have hU : IsUnit M := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    have : M.mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have := hz0 _ this
    exact sub_eq_zero.1 this
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 hU
  have hMi : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet
  set Cf : ℕ → ℕ → ℝ := fun k j =>
    if h : k ∈ S ∧ j ∈ S then (M⁻¹) ⟨k, h.1⟩ ⟨j, h.2⟩ else if k = j then 1 else 0 with hCf
  refine ⟨Cf, fun j => ?_⟩
  by_cases hj : j ∈ S
  · -- column inside `S`
    have hzero : ∀ k, k ∉ S → Cf k j = 0 := by
      intro k hk
      have : ¬ (k ∈ S ∧ j ∈ S) := fun h => hk h.1
      have hkj : k ≠ j := fun h => hk (h ▸ hj)
      simp [hCf, this, hkj]
    refine ⟨summable_of_ne_finset_zero (s := S) fun k hk => by simp [hzero k hk], fun i => ?_⟩
    refine ⟨summable_of_ne_finset_zero (s := S) fun k hk => by simp [hzero k hk], ?_⟩
    rw [tsum_eq_sum (s := S) fun k hk => by simp [hzero k hk]]
    by_cases hi : i ∈ S
    · have hmat := congrFun (congrFun hMi ⟨i, hi⟩) ⟨j, hj⟩
      rw [Matrix.mul_apply] at hmat
      rw [← Finset.sum_coe_sort S]
      have : ∀ k : S, ((if i = (k : ℕ) then 1 else 0) + A.a R i k) * Cf k j =
          M ⟨i, hi⟩ k * M⁻¹ k ⟨j, hj⟩ := by
        intro k
        have hCk : Cf k j = M⁻¹ k ⟨j, hj⟩ := by simp [hCf, k.2, hj]
        rw [hCk]
      simp_rw [this]
      rw [hmat]
      simp [Matrix.one_apply, Subtype.ext_iff]
    · have hij : i ≠ j := fun h => hi (h ▸ hj)
      simp only [hij, ite_false]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hik : i ≠ k := fun h => hi (h ▸ hk)
      have : A.a R i k = 0 := A.supp R i k (Or.inl hi)
      simp [hik, this]
  · -- column outside `S`
    have hCj : ∀ k, Cf k j = if k = j then 1 else 0 := by
      intro k
      have : ¬ (k ∈ S ∧ j ∈ S) := fun h => hj h.2
      simp [hCf, this]
    refine ⟨summable_of_ne_finset_zero (s := {j}) fun k hk => ?_, fun i => ?_⟩
    · have : k ≠ j := by simpa using hk
      simp [hCj k, this]
    refine ⟨summable_of_ne_finset_zero (s := {j}) fun k hk => ?_, ?_⟩
    · have : k ≠ j := by simpa using hk
      simp [hCj k, this]
    rw [tsum_eq_single j fun k hk => by simp [hCj k, hk]]
    have : A.a R i j = 0 := A.supp R i j (Or.inr hj)
    simp [hCj j, this]

end Inverse

/-! ### The family `CR` -/

section CRfam

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `C_R = (I + T_R)^{-1}` exists for all large `R`. -/
theorem exists_CR (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ)
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) :
    ∃ CR : ℕ → ℕ → ℕ → ℝ, ∀ᶠ R in atTop, IsInverseOfIPlus (A.a R) (CR R) := by
  classical
  obtain ⟨σ, hσ, R0, hR0⟩ := positivity_export hd hyp hr μ hμ e lam he A
  refine ⟨fun R => if h : ∃ C, IsInverseOfIPlus (A.a R) C then h.choose else fun _ _ => 0, ?_⟩
  refine eventually_atTop.2 ⟨R0, fun R hR => ?_⟩
  have h : ∃ C, IsInverseOfIPlus (A.a R) C := exists_inv_of_pos A R hσ (hR0 R hR)
  simp only [h, dite_true]
  exact h.choose_spec

end CRfam

/-! ### `C¹` representatives -/

section C1rep

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem exists_C1_rep (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ)
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    ∃ eC : ℕ → Torus d → ℝ, (∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) ∧ ∀ j, eC j =ᵐ[haar d] e j := by
  obtain ⟨eC, a, Cu, Cl, c, ha, hrls, hup, hlow, hC1, hae, -⟩ :=
    Spectral.cut_package_main hd hyp hr μ hμ e lam he
  refine ⟨eC, hC1, fun j => ?_⟩
  have hca : (volume : Measure (Torus d)) ≪ (μ : Measure (Torus d)) :=
    Measure.absolutelyContinuous_of_le_smul hlow
  exact hca.ae_le (hae j)

end C1rep

end SharpLSI.FL
