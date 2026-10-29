import FullLabeledLSI.Paper.Sec8Min5

/-!
# Section 8.3 (linearization), part 13: (8.11)

`inf = min{λ_G, λ₁}`: lower bound `lower_bound` (Min4), `linInf ≤ λ₁` (Min5) and
`linInf ≤ λ_G` (here, through `le_lamG_of_trunc` and the test perturbations).
-/

open MeasureTheory InformationTheory Set Filter Topology Finset
open scoped ENNReal NNReal

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem linInf_le_lamG (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C) :
    linInf W (μ : Measure (Torus d)) ≤ lamG (lamShift lam) C := by
  have hac := minimizer_ac hyp hμ
  have h21 := prop21Conclusion_of_equilibrium (prop_equilibrium hd hyp hr) hμ
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  have hT := Tmat_symm hyp hμ he
  have hS' := (hasSum_Tmat_sq hyp hμ he).summable
  have hCs : ∀ i j, C i j = C j i := fun i j => C_symm_of_secOp hT hS' hσ0 hσ hC i j
  have hnn := quadC_nonneg hT hS' hσ0 hσ hC
  have hup := quadC_le hT hS' hσ0 hσ hC
  have hcol : ∀ j, Summable fun k => C k j ^ 2 := fun j => (hC j).1
  have hlam0 : 0 < lamShift lam 0 := ((ref_spectrum hd hyp hr hμ).2 e lam he).1 1 le_rfl
  have hlam : ∀ i, 0 < lamShift lam i := fun i =>
    hlam0.trans_le (he.mono (by simp [lamShift] : 0 + 1 ≤ i + 1))
  refine le_lamG_of_trunc hσ0 hCs hnn hup hcol hlam fun n v hQ => ?_
  obtain ⟨eC, heC⟩ := exists_c1_reps hd hyp hr hμ he
  have heC' : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT) ∧
      eC j =ᵐ[(μ : Measure (Torus d))] e j := fun j => ⟨(heC j).1, (heC j).2.2⟩
  obtain ⟨h, hc, hh0, hsum, hsv⟩ := exists_test_pert hd hyp hr hμ he hC heC' n v
  set vfn : Torus d → ℝ := fun x => ∑ i ∈ range n, v i * eC (i + 1) x with hvfn
  have hvc : ContDiff ℝ 1 (vfn ∘ liftT) := by
    have e : vfn ∘ liftT = fun z => ∑ i ∈ range n, v i * (eC (i + 1) ∘ liftT) z := rfl
    rw [e]
    exact ContDiff.sum fun i _ => contDiff_const.mul (heC (i + 1)).1
  have hvL := c1_lip hvc
  have hBh : BM h := BM.of_cont hc
  have hTL := (top_lip_bdd hyp hBh.1 hBh.2.choose_spec hh0).1
  have hhL : ∃ L : ℝ≥0, LipschitzWith L h := by
    have e : h = fun x => vfn x + (-1) * Top W (μ : Measure (Torus d)) h x := by
      funext x; have := hsum x; simp only [hvfn]; linarith
    rw [e]; exact lip_add hvL (lip_smul (-1) hTL)
  have hfam : LinFam (μ : Measure (Torus d)) 1 (fun _ => (1 : ℝ)) (fun _ => h) :=
    ⟨fun _ => one_pos, by simp, fun _ => ⟨hhL, hBh.2, hh0⟩⟩
  have hb_eq : hb (fun _ : Fin 1 => (1 : ℝ)) (fun _ => h) = h := by
    funext x; simp [hb]
  have hG : linG W (μ : Measure (Torus d)) (fun _ : Fin 1 => (1 : ℝ)) (fun _ => h) =
      ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j := by
    unfold linG
    rw [hb_eq, hsv]
    simp
  have hD : linD W (μ : Measure (Torus d)) (fun _ : Fin 1 => (1 : ℝ)) (fun _ => h) =
      ∑ i ∈ range n, lamShift lam i * v i ^ 2 := by
    unfold linD
    rw [hb_eq]
    have e1 : (fun x => h x + Top W (μ : Measure (Torus d)) h x) = vfn := by
      funext x; exact hsum x
    have e2 : (fun x => (fun _ : Fin 1 => h) 0 x - h x) = fun _ => (0 : ℝ) := by
      funext x; simp
    rw [e1]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, one_mul]
    rw [e2, dirichlet_toReal_zero hac, add_zero]
    obtain ⟨K, hK⟩ := exists_bound_cgrad hvc
    rw [dirichlet_toReal_of_wg hac (isWeakGrad_of_contDiff hvc) hK
      (fun k => measurable_cgrad hvc k)]
    exact integral_cgrad_sq hyp hμ he (fun j => ⟨(heC j).1, (heC j).2.1⟩) n v
  calc linInf W (μ : Measure (Torus d)) ≤ ENNReal.ofReal
        (linD W (μ : Measure (Torus d)) (fun _ : Fin 1 => (1 : ℝ)) (fun _ => h) /
          linG W (μ : Measure (Torus d)) (fun _ : Fin 1 => (1 : ℝ)) (fun _ => h)) :=
        iInf_le_of_le 1 (iInf_le_of_le _ (iInf_le_of_le _
          (iInf_le_of_le ⟨hfam, by rw [hG]; exact hQ⟩ le_rfl)))
    _ = _ := by rw [hD, hG, ENNReal.ofReal_div_of_pos hQ]

/-- **(8.11)**: the infimum of the linearized quotients is `min{λ_G, λ₁}`. -/
theorem lin_min (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C) :
    linInf W (μ : Measure (Torus d)) =
      min (lamG (lamShift lam) C) (ENNReal.ofReal (lam 1)) :=
  le_antisymm (le_min (linInf_le_lamG hd hyp hr hμ he hC) (linInf_le_lam1 hd hyp hr hμ he))
    (lower_bound hd hyp hr hμ he hC)

end Sec8
end SharpLSI.FL
