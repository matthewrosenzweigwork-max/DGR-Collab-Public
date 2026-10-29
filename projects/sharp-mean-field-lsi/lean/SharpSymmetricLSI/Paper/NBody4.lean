import SharpSymmetricLSI.Paper.NBody3

/-!
# Eigen-identity and Bessel inequalities for the occupation basis (Phase 3, lane D; R29)

`∫ ∇Ψ·∇B_α dμ^{⊗N} = Λ_α ⟨Ψ, B_α⟩` for `Ψ ∈ H¹(μ^{⊗N})`; hence, for finite families,
`∑ Λ_α ⟨Ψ,B_α⟩² ≤ ∫|∇Ψ|²` and `∑ ⟨Ψ,B_α⟩² ≤ ∫Ψ²`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- Expanding `0 ≤ ∫ ∑ₘ (vₘ - ∑ₐ aₐ wₐ,ₘ)²`. -/
theorem expand_sq_nonneg {Ω A ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    [Fintype ι] (S : Finset A) (v : Ω → ι → ℝ) (w : A → Ω → ι → ℝ) (a : A → ℝ)
    (hv : ∀ m, MemLp (fun x => v x m) 2 P) (hw : ∀ α m, MemLp (fun x => w α x m) 2 P) :
    0 ≤ ∫ x, ∑ m, v x m ^ 2 ∂P - 2 * ∑ α ∈ S, a α * ∫ x, ∑ m, v x m * w α x m ∂P +
      ∑ α ∈ S, ∑ β ∈ S, a α * a β * ∫ x, ∑ m, w α x m * w β x m ∂P := by
  have hvv : Integrable (fun x => ∑ m, v x m ^ 2) P :=
    integrable_finsetSum _ fun m _ => (hv m).integrable_sq
  have hvw : ∀ α, Integrable (fun x => ∑ m, v x m * w α x m) P := fun α =>
    integrable_finsetSum _ fun m _ => (hv m).integrable_mul (hw α m)
  have hww : ∀ α β, Integrable (fun x => ∑ m, w α x m * w β x m) P := fun α β =>
    integrable_finsetSum _ fun m _ => (hw α m).integrable_mul (hw β m)
  set f2 : Ω → ℝ := fun x => ∑ α ∈ S, a α * ∑ m, v x m * w α x m
  set f3 : Ω → ℝ := fun x => ∑ α ∈ S, ∑ β ∈ S, a α * a β * ∑ m, w α x m * w β x m
  have hpt : ∀ x, ∑ m, (v x m - ∑ α ∈ S, a α * w α x m) ^ 2 =
      ∑ m, v x m ^ 2 - 2 * f2 x + f3 x := fun x => by
    have hm : ∀ m, (v x m - ∑ α ∈ S, a α * w α x m) ^ 2 = v x m ^ 2 -
        2 * ∑ α ∈ S, a α * (v x m * w α x m) +
          ∑ α ∈ S, ∑ β ∈ S, a α * a β * (w α x m * w β x m) := fun m => by
      have e1 : (∑ α ∈ S, a α * w α x m) ^ 2 =
          ∑ α ∈ S, ∑ β ∈ S, a α * a β * (w α x m * w β x m) := by
        rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring
      have e2 : 2 * v x m * ∑ α ∈ S, a α * w α x m = 2 * ∑ α ∈ S, a α * (v x m * w α x m) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun α _ => by ring
      rw [sub_sq, e1, e2]
    have c2 : ∑ m, ∑ α ∈ S, a α * (v x m * w α x m) = ∑ α ∈ S, a α * ∑ m, v x m * w α x m := by
      rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    have c3 : ∑ m, ∑ α ∈ S, ∑ β ∈ S, a α * a β * (w α x m * w β x m) =
        ∑ α ∈ S, ∑ β ∈ S, a α * a β * ∑ m, w α x m * w β x m := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    show _ = ∑ m, v x m ^ 2 - 2 * (∑ α ∈ S, a α * ∑ m, v x m * w α x m) +
      ∑ α ∈ S, ∑ β ∈ S, a α * a β * ∑ m, w α x m * w β x m
    rw [Finset.sum_congr rfl fun m _ => hm m, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, c2, c3]
  have h0 : 0 ≤ ∫ x, ∑ m, (v x m - ∑ α ∈ S, a α * w α x m) ^ 2 ∂P :=
    integral_nonneg fun x => Finset.sum_nonneg fun m _ => sq_nonneg _
  have hf2 : Integrable f2 P := integrable_finsetSum _ fun α _ => (hvw α).const_mul _
  have hf3 : Integrable f3 P :=
    integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => (hww α β).const_mul _
  have hI : ∫ x, ∑ m, (v x m - ∑ α ∈ S, a α * w α x m) ^ 2 ∂P =
      ∫ x, ∑ m, v x m ^ 2 ∂P - 2 * ∫ x, f2 x ∂P + ∫ x, f3 x ∂P := by
    simp_rw [hpt]
    rw [integral_add (f := fun x => ∑ m, v x m ^ 2 - 2 * f2 x) (g := f3) (hvv.sub (hf2.const_mul _))
      hf3, integral_sub (f := fun x => ∑ m, v x m ^ 2) (g := fun x => 2 * f2 x) hvv
      (hf2.const_mul _), integral_const_mul]
  have hf2' : ∫ x, f2 x ∂P = ∑ α ∈ S, a α * ∫ x, ∑ m, v x m * w α x m ∂P := by
    simp only [f2]
    rw [integral_finsetSum _ fun α _ => (hvw α).const_mul _]
    simp_rw [integral_const_mul]
  have hf3' : ∫ x, f3 x ∂P = ∑ α ∈ S, ∑ β ∈ S, a α * a β * ∫ x, ∑ m, w α x m * w β x m ∂P := by
    simp only [f3]
    rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => (hww α β).const_mul _]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [integral_finsetSum _ fun β _ => (hww α β).const_mul _]
    simp_rw [integral_const_mul]
  rw [hI, hf2', hf3'] at h0
  exact h0

section occ
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
include hyp hμ

theorem memLp_weakGradC {N : ℕ} {Ψ : Config N d → ℝ}
    (hΨ : MemH1C (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) Ψ) (i : Fin N) (k : Fin d) :
    MemLp (fun X => weakGradC Ψ X i k) 2 (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := by
  obtain ⟨a, b, ha0, hb0, ha, hb⟩ := minimizer_pi_comparison hyp hμ (N := N)
  set P := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  have : IsProbabilityMeasure (P.map flat) :=
    (Measure.isProbabilityMeasure_map_iff measurable_flat.aemeasurable).mpr inferInstance
  exact (measurableEmbedding_flat.memLp_map_measure_iff).mp (memLp_grad_P hb hΨ (i, k))

include he

theorem ae_weakGradC_occBasis {N : ℕ} (γ : ℕ →₀ ℕ) :
    ∀ᵐ X ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))), ∀ i k,
      weakGradC (occBasis e γ N) X i k = occGrad e γ N (flat X) (i, k) := by
  set P := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  have hac : P.map flat ≪ volume := by
    rw [← map_flat_volume N]
    exact (pi_ac_volume (minimizer_ac hyp hμ) N).map measurable_flat
  have h1 := hac.ae_le (weakGrad_ae_eq (isWeakGrad_occBasis hyp hμ he γ N))
  have h2 := ae_of_ae_map measurable_flat.aemeasurable h1
  filter_upwards [h2] with X hX i k
  simp only [weakGradC, hX]

/-- **`⟨∇Ψ, ∇B_α⟩ = Λ_α ⟨Ψ, B_α⟩`.** -/
theorem eigen_occBasis {N : ℕ} {Ψ : Config N d → ℝ}
    (hΨ : MemH1C (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) Ψ) (α : ℕ →₀ ℕ) :
    ∫ X, ∑ i, ∑ k, weakGradC Ψ X i k * weakGradC (occBasis e α N) X i k
        ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) =
      occEnergy lam α * ∫ X, Ψ X * occBasis e α N X
        ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := by
  set P := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  set sα := Real.sqrt ((occFactorial α : ℝ) / (N.descFactorial (occSize α) : ℝ))
  have hac : (μ : Measure (Torus d)) ≪ haar d := minimizer_ac hyp hμ
  have htg : ∀ (c : Fin N → ℕ) i k, MemLp (tensorGrad e c i k) 2 P := fun c i k => by
    unfold tensorGrad
    refine memLp_prod_eval (f := fun j => (Function.update (fun j => e (c j)) i
      (fun x => weakGrad (e (c i)) x k)) j) fun j => ?_
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]; exact memLp_grad_comp hac (he.memH1 _) k
    · rw [Function.update_of_ne hj]; exact he.memLp _
  have hgΨ := memLp_weakGradC hyp hμ hΨ
  have hT : ∀ c : Fin N → ℕ, MemLp (fun X : Config N d => ∏ j, e (c j) (X j)) 2 P := fun c =>
    memLp_prod_eval fun j => he.memLp _
  have hΨL : MemLp Ψ 2 P :=
    (measurableEmbedding_flat.memLp_map_measure_iff).mp hΨ.2.1
  have hpt : ∀ᵐ X ∂P, ∑ i, ∑ k, weakGradC Ψ X i k * weakGradC (occBasis e α N) X i k =
      sα * ∑ c ∈ occLabellings α N, ∑ i, ∑ k,
        weakGradC Ψ X i k * tensorGrad e (fun j => (c j : ℕ)) i k X := by
    filter_upwards [ae_weakGradC_occBasis hyp hμ he α] with X hX
    have hG : ∀ i k, occGrad e α N (flat X) (i, k) =
        sα * ∑ c ∈ occLabellings α N, tensorGrad e (fun j => (c j : ℕ)) i k X := fun _ _ => rfl
    simp only [hX, hG, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun c _ => by ring
  have hint : ∀ (c : Fin N → ℕ) i, Integrable (fun X => ∑ k, weakGradC Ψ X i k *
      tensorGrad e c i k X) P := fun c i =>
    integrable_finsetSum (f := fun k X => weakGradC Ψ X i k * tensorGrad e c i k X) _
      fun k _ => (hgΨ i k).integrable_mul (htg c i k)
  rw [integral_congr_ae hpt, integral_const_mul,
    integral_finsetSum (f := fun (c : Fin N → Fin (α.support.sup id + 2)) X => ∑ i, ∑ k,
      weakGradC Ψ X i k * tensorGrad e (fun j => (c j : ℕ)) i k X) _
      fun c _ => integrable_finsetSum _ fun i _ => hint _ i]
  have hsplit : ∀ c : Fin N → Fin (α.support.sup id + 2), ∫ X, ∑ i, ∑ k, weakGradC Ψ X i k *
      tensorGrad e (fun j => (c j : ℕ)) i k X ∂P = ∑ i, ∫ X, ∑ k, weakGradC Ψ X i k *
      tensorGrad e (fun j => (c j : ℕ)) i k X ∂P := fun c =>
    integral_finsetSum _ fun i _ => hint _ i
  simp_rw [hsplit]
  have h1 : ∀ c ∈ occLabellings α N, ∑ i, ∫ X, ∑ k, weakGradC Ψ X i k *
      tensorGrad e (fun j => (c j : ℕ)) i k X ∂P =
      occEnergy lam α * ∫ X, Ψ X * ∏ j, e (c j : ℕ) (X j) ∂P := fun c hc => by
    rw [Finset.sum_congr rfl fun i _ => eigen_tensor_H1 hyp hμ he hΨ (fun j => (c j : ℕ)) i,
      ← Finset.sum_mul, sum_lam_labelling hyp hμ he hc]
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have h2 : ∑ c ∈ occLabellings α N, ∫ X, Ψ X * ∏ j, e (c j : ℕ) (X j) ∂P =
      ∫ X, ∑ c ∈ occLabellings α N, Ψ X * ∏ j, e (c j : ℕ) (X j) ∂P :=
    (integral_finsetSum (f := fun (c : Fin N → Fin (α.support.sup id + 2)) X =>
      Ψ X * ∏ j, e (c j : ℕ) (X j)) _ fun c _ => hΨL.integrable_mul (hT _)).symm
  rw [h2]
  unfold occBasis
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => by ring

/-- **Bessel in `L²(μ^{⊗N})`.** -/
theorem bessel_occ_L2 {N : ℕ} {Ψ : Config N d → ℝ}
    (hΨ : MemLp Ψ 2 (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))))
    (S : Finset (ℕ →₀ ℕ)) (hS : ∀ α ∈ S, occSize α ≤ N) :
    ∑ α ∈ S, (∫ X, Ψ X * occBasis e α N X ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))))
      ^ 2 ≤ ∫ X, Ψ X ^ 2 ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := by
  set P := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  set c : (ℕ →₀ ℕ) → ℝ := fun α => ∫ X, Ψ X * occBasis e α N X ∂P
  have h := expand_sq_nonneg (P := P) (ι := Unit) S (fun X _ => Ψ X) (fun α X _ => occBasis e α N X)
    c (fun _ => hΨ) (fun α _ => memLp_occBasis hyp hμ he α N)
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  have horth : ∀ α ∈ S, ∀ β ∈ S, ∫ X, occBasis e α N X * occBasis e β N X ∂P =
      if α = β then 1 else 0 := fun α hα β hβ =>
    integral_occBasis_mul he.memLp he.orthonormal (hS α hα) (hS β hβ)
  have h3 : ∑ α ∈ S, ∑ β ∈ S, c α * c β * ∫ X, occBasis e α N X * occBasis e β N X ∂P =
      ∑ α ∈ S, c α ^ 2 := by
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [Finset.sum_congr rfl fun β hβ => by rw [horth α hα β hβ]]
    simp [Finset.sum_ite_eq, hα, sq]
  have h2 : ∑ α ∈ S, c α * ∫ X, Ψ X * occBasis e α N X ∂P = ∑ α ∈ S, c α ^ 2 :=
    Finset.sum_congr rfl fun α _ => by simp [c, sq]
  rw [h2, h3] at h
  linarith

/-- **Energy Bessel**: `∑ Λ_α ⟨Ψ,B_α⟩² ≤ ∫ |∇Ψ|²`. -/
theorem bessel_occ_energy {N : ℕ} {Ψ : Config N d → ℝ}
    (hΨ : MemH1C (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) Ψ)
    (S : Finset (ℕ →₀ ℕ)) (hS : ∀ α ∈ S, occSize α ≤ N) :
    ∑ α ∈ S, occEnergy lam α *
      (∫ X, Ψ X * occBasis e α N X ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))) ^ 2 ≤
      ∫ X, gradSqC Ψ X ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := by
  set P := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  set c : (ℕ →₀ ℕ) → ℝ := fun α => ∫ X, Ψ X * occBasis e α N X ∂P
  have h := expand_sq_nonneg (P := P) (ι := Fin N × Fin d) S
    (fun X p => weakGradC Ψ X p.1 p.2) (fun α X p => weakGradC (occBasis e α N) X p.1 p.2) c
    (fun p => memLp_weakGradC hyp hμ hΨ p.1 p.2)
    (fun α p => memLp_weakGradC hyp hμ (memH1C_occBasis hyp hμ he α N) p.1 p.2)
  simp only [Fintype.sum_prod_type] at h
  have h1 : ∫ X, ∑ i, ∑ k, weakGradC Ψ X i k ^ 2 ∂P = ∫ X, gradSqC Ψ X ∂P := rfl
  have h2 : ∑ α ∈ S, c α * ∫ X, ∑ i, ∑ k, weakGradC Ψ X i k * weakGradC (occBasis e α N) X i k ∂P =
      ∑ α ∈ S, occEnergy lam α * c α ^ 2 :=
    Finset.sum_congr rfl fun α _ => by rw [eigen_occBasis hyp hμ he hΨ α]; simp only [c]; ring
  have h3 : ∑ α ∈ S, ∑ β ∈ S, c α * c β * ∫ X, ∑ i, ∑ k, weakGradC (occBasis e α N) X i k *
      weakGradC (occBasis e β N) X i k ∂P = ∑ α ∈ S, occEnergy lam α * c α ^ 2 := by
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [Finset.sum_congr rfl fun β hβ => by rw [dirichlet_occBasis hyp hμ he (hS α hα) (hS β hβ)]]
    simp [Finset.sum_ite_eq, hα, sq]
    ring
  rw [h1, h2, h3] at h
  linarith

end occ

end SharpLSI
