import FullLabeledLSI.Paper.Sec8Min4

/-!
# Section 8.3 (linearization), part 12: the upper bounds in (8.11)

* `linInf_le_lam1`: the two-label family `h = ± e₁` (`h̄ = 0`, `η = ± e₁`) has `D/G = λ₁`;
* `linInf_le_lamG`: the one-label test perturbations `h` of `exists_test_pert` have
  `D/G = ∑_{i<n} λ_{i+1} v_i² / ⟨v, C v⟩_n`, and these finite ratios bound `λ_G` below
  (`le_lamG_of_trunc`).
-/

open MeasureTheory InformationTheory Set Filter Topology Finset
open scoped ENNReal NNReal

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem dirichlet_toReal_zero {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hac : μ ≪ haar d) : (dirichlet μ (fun _ => (0 : ℝ))).toReal = 0 := by
  have := dirichlet_toReal_of_wg hac (isWeakGrad_const (ι := Fin d) 0) (K := 0)
    (fun x k => by simp) (fun k => measurable_const)
  simpa using this

theorem dirichlet_toReal_c1 {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
    {f : Torus d → ℝ} (hf : ContDiff ℝ 1 (f ∘ liftT)) (c : ℝ) :
    (dirichlet μ (fun x => c * f x)).toReal = c ^ 2 * ∫ x, ∑ k, cgrad f x k ^ 2 ∂μ := by
  obtain ⟨K, hK⟩ := exists_bound_cgrad hf
  have hw := (isWeakGrad_of_contDiff hf).cmul c
  rw [dirichlet_toReal_of_wg hac hw (K := |c| * |K|)
    (fun x k => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((hK x k).trans (le_abs_self _)) (abs_nonneg _))
    (fun k => measurable_const.mul (measurable_cgrad hf k))]
  rw [← integral_const_mul]
  congr 1; funext x
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by unfold cgrad; ring

theorem linInf_le_lam1 (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    linInf W (μ : Measure (Torus d)) ≤ ENNReal.ofReal (lam 1) := by
  have hac := minimizer_ac hyp hμ
  obtain ⟨eC, heC⟩ := exists_c1_reps hd hyp hr hμ he
  set E : Torus d → ℝ := eC 1 with hE
  have hE1 : ContDiff ℝ 1 (E ∘ liftT) := (heC 1).1
  have hEL := c1_lip hE1
  have hEB : BM E := BM.of_lip hEL
  have hEe : E =ᵐ[(μ : Measure (Torus d))] e 1 := (heC 1).2.2
  have hE0 : ∫ x, E x ∂(μ : Measure (Torus d)) = 0 := by
    have := he.orthonormal 1 0
    rw [he.zero] at this
    simp only [mul_one] at this
    rw [integral_congr_ae hEe]
    simpa using this
  have hE2 : ∫ x, E x ^ 2 ∂(μ : Measure (Torus d)) = 1 := by
    have h1 := he.orthonormal 1 1
    rw [if_pos rfl] at h1
    refine (integral_congr_ae ?_).trans h1
    filter_upwards [hEe] with x hx
    rw [hx]; ring
  have hDE : ∫ x, ∑ k, cgrad E x k ^ 2 ∂(μ : Measure (Torus d)) = lam 1 := by
    have h1 := integral_cgrad_sq hyp hμ he (fun j => ⟨(heC j).1, (heC j).2.1⟩) 1 (fun _ => 1)
    have e1 : (fun y => ∑ i ∈ range 1, (fun _ : ℕ => (1 : ℝ)) i * eC (i + 1) y) = E := by
      funext y; simp [hE]
    rw [e1] at h1
    simpa [lamShift] using h1
  -- the family
  set s : Fin 2 → ℝ := fun a => if a = 0 then 1 else -1 with hs
  have hs2 : ∀ a, s a ^ 2 = 1 := fun a => by fin_cases a <;> simp [hs]
  set θ : Fin 2 → ℝ := fun _ => 1 / 2 with hθ
  set h : Fin 2 → Torus d → ℝ := fun a x => s a * E x with hh
  have hb0 : hb θ h = fun _ => 0 := by
    funext x
    simp only [hb, hθ, hh, Fin.sum_univ_two, hs]
    simp
  have hLip : ∀ a, ∃ L : ℝ≥0, LipschitzWith L (h a) := fun a => lip_smul (s a) hEL
  have hfam : LinFam (μ : Measure (Torus d)) 2 θ h := by
    refine ⟨fun _ => by simp [hθ], by simp [hθ, Fin.sum_univ_two], fun a => ⟨hLip a, ?_, ?_⟩⟩
    · obtain ⟨B, hB⟩ := hEB.2
      refine ⟨|s a| * B, fun x => ?_⟩
      show |s a * E x| ≤ _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg _)
    · show ∫ x, s a * E x ∂(μ : Measure (Torus d)) = 0
      rw [integral_const_mul, hE0, mul_zero]
  have hG : linG W (μ : Measure (Torus d)) θ h = 1 := by
    unfold linG
    rw [hb0]
    have e1 : secondVar W (μ : Measure (Torus d)) (fun _ => (0 : ℝ)) = 0 := by
      unfold secondVar; simp
    rw [e1]
    have e2 : ∀ a, ∫ x, (h a x - (fun _ => (0 : ℝ)) x) ^ 2 ∂(μ : Measure (Torus d)) = 1 := fun a => by
      simp only [hh, sub_zero, mul_pow, hs2 a, one_mul]
      exact hE2
    simp only [e2, hθ, Fin.sum_univ_two]
    norm_num
  have hD : linD W (μ : Measure (Torus d)) θ h = lam 1 := by
    unfold linD
    rw [hb0]
    have e1 : (fun x => (fun _ : Torus d => (0 : ℝ)) x + Top W (μ : Measure (Torus d))
        (fun _ => (0 : ℝ)) x) = fun _ => 0 := by
      funext x; simp [Top]
    rw [e1, dirichlet_toReal_zero hac, zero_add]
    have e2 : ∀ a, (dirichlet (μ : Measure (Torus d))
        (fun x => h a x - (fun _ : Torus d => (0 : ℝ)) x)).toReal = lam 1 := fun a => by
      have : (fun x => h a x - (fun _ : Torus d => (0 : ℝ)) x) = fun x => s a * E x := by
        funext x; simp [hh]
      rw [this, dirichlet_toReal_c1 hac hE1, hs2 a, one_mul, hDE]
    simp only [e2, hθ, Fin.sum_univ_two]
    ring
  unfold linInf
  refine (iInf_le_of_le 2 (iInf_le_of_le θ (iInf_le_of_le h
    (iInf_le_of_le ⟨hfam, by rw [hG]; exact one_pos⟩ ?_))))
  rw [hG, hD, div_one]

end Sec8
end SharpLSI.FL
