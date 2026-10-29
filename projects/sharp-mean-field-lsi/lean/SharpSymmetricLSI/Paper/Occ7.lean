import SharpSymmetricLSI.Paper.Occ6
import SharpSymmetricLSI.Paper.R37Rescaling
import SharpSymmetricLSI.Paper.ProductFisherGrad
import SharpSymmetricLSI.Paper.WeightedHS1
import SharpSymmetricLSI.Paper.ForceExp

/-!
# `B_{α,N} ∈ H¹(μ^{⊗N})` (Phase 3, lane D; R28)

The weak gradient of `B_{α,N}` on the flattened torus is the sum over labellings of the block
gradients (`isWeakGrad_blockProd`); its components are tensor products of `e_j`, `∇e_j ∈ L²(μ)`.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem memLp_prod_eval {N : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {f : Fin N → Torus d → ℝ} (hf : ∀ i, MemLp (f i) 2 μ) :
    MemLp (fun X : Config N d => ∏ i, f i (X i)) 2 (Measure.pi fun _ : Fin N => μ) := by
  refine (memLp_two_iff_integrable_sq ?_).mpr ?_
  · have := Finset.aestronglyMeasurable_prod (μ := Measure.pi fun _ : Fin N => μ) Finset.univ
      fun i _ => (hf i).aestronglyMeasurable.comp_quasiMeasurePreserving
        (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving
    refine this.congr (Eventually.of_forall fun X => ?_)
    simp [Finset.prod_apply]
  · have : (fun X : Config N d => (∏ i, f i (X i)) ^ 2) = fun X => ∏ i, f i (X i) ^ 2 := by
      funext X; rw [Finset.prod_pow]
    rw [this]
    exact Integrable.fintype_prod (f := fun i x => f i x ^ 2) fun i => (hf i).integrable_sq

section memH1
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
include hyp hμ he

theorem integrable_e_haar (j : ℕ) : Integrable (e j) (haar d) := by
  obtain ⟨C, hC⟩ := haar_le_smul_minimizer hyp hμ (d := d)
  exact ((he.memLp j).of_measure_le_smul ENNReal.ofReal_ne_top hC).integrable one_le_two

theorem memLp_grad_e (j : ℕ) (k : Fin d) :
    MemLp (fun x => weakGrad (e j) x k) 2 (μ : Measure (Torus d)) := by
  refine (he.memH1 j).2.2.of_le (((isWeakGrad_weakGrad (he.memH1 j).1).aestronglyMeasurable_grad
    k).mono_ac (minimizer_ac hyp hμ)) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact abs_le_sqrt_sqNorm _ k

theorem integrable_grad_e_haar (j : ℕ) (k : Fin d) :
    Integrable (fun x => weakGrad (e j) x k) (haar d) := by
  obtain ⟨C, hC⟩ := haar_le_smul_minimizer hyp hμ (d := d)
  exact ((memLp_grad_e hyp hμ he j k).of_measure_le_smul ENNReal.ofReal_ne_top hC).integrable
    one_le_two

/-- The explicit weak gradient of `B_{α,N} ∘ unflat`. -/
def occGrad (e : ℕ → Torus d → ℝ) (α : ℕ →₀ ℕ) (N : ℕ) (y : UnitAddTorus (Fin N × Fin d))
    (p : Fin N × Fin d) : ℝ :=
  Real.sqrt ((occFactorial α : ℝ) / (N.descFactorial (occSize α) : ℝ)) *
    ∑ c ∈ occLabellings α N, blockProd (Function.update (fun i => e (c i : ℕ)) p.1
      (fun x => weakGrad (e (c p.1 : ℕ)) x p.2)) y

theorem isWeakGrad_occBasis (α : ℕ →₀ ℕ) (N : ℕ) :
    IsWeakGrad (occBasis e α N ∘ unflat) (occGrad e α N) := by
  have hb : ∀ c : Fin N → Fin (α.support.sup id + 2), IsWeakGrad (blockProd fun i => e (c i : ℕ))
      (fun y p => blockProd (Function.update (fun i => e (c i : ℕ)) p.1
        (fun x => weakGrad (e (c p.1 : ℕ)) x p.2)) y) := fun c => by
    have := isWeakGrad_blockProd (fun i => e (c i : ℕ)) (fun i => weakGrad (e (c i : ℕ)))
      (fun i => isWeakGrad_weakGrad (he.memH1 _).1) (fun i => integrable_e_haar hyp hμ he _)
      (fun i k => integrable_grad_e_haar hyp hμ he _ k)
    simpa using this
  have := (isWeakGrad_finsetSum (occLabellings α N) fun c _ => hb c).const_mul
    (Real.sqrt ((occFactorial α : ℝ) / (N.descFactorial (occSize α) : ℝ)))
  exact this

theorem memLp_occBasis (α : ℕ →₀ ℕ) (N : ℕ) :
    MemLp (occBasis e α N) 2 (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := by
  unfold occBasis
  exact (memLp_finsetSum _ fun c _ => memLp_prod_eval fun i => he.memLp _).const_mul _

theorem memLp_occGrad_flat (α : ℕ →₀ ℕ) (N : ℕ) (p : Fin N × Fin d) :
    MemLp (fun X : Config N d => occGrad e α N (flat X) p) 2
      (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := by
  have hfe : (fun X : Config N d => occGrad e α N (flat X) p) = fun X =>
      Real.sqrt ((occFactorial α : ℝ) / (N.descFactorial (occSize α) : ℝ)) *
        ∑ c ∈ occLabellings α N, ∏ i, (Function.update (fun i => e (c i : ℕ)) p.1
          (fun x => weakGrad (e (c p.1 : ℕ)) x p.2)) i (X i) := rfl
  rw [hfe]
  refine (memLp_finsetSum (f := fun (c : Fin N → Fin (α.support.sup id + 2)) (X : Config N d) =>
    ∏ i, (Function.update (fun i => e (c i : ℕ)) p.1 (fun x => weakGrad (e (c p.1 : ℕ)) x p.2)) i
      (X i)) _ fun c _ => ?_).const_mul _
  exact memLp_prod_eval fun i => by
    by_cases hi : i = p.1
    · subst hi; rw [Function.update_self]; exact memLp_grad_e hyp hμ he _ _
    · rw [Function.update_of_ne hi]; exact he.memLp _

/-- **`B_{α,N} ∈ H¹(μ^{⊗N})`.** -/
theorem memH1C_occBasis (α : ℕ →₀ ℕ) (N : ℕ) :
    MemH1C (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) (occBasis e α N) := by
  set P := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  have hw := isWeakGrad_occBasis hyp hμ he α N
  have hac : P.map flat ≪ volume := by
    rw [← map_flat_volume N]
    exact (pi_ac_volume (minimizer_ac hyp hμ) N).map measurable_flat
  refine ⟨⟨_, hw⟩, ?_, ?_⟩
  · exact (measurableEmbedding_flat.memLp_map_measure_iff).mpr (memLp_occBasis hyp hμ he α N)
  · have hae : (fun y => Real.sqrt (sqNorm (weakGrad (occBasis e α N ∘ unflat) y))) =ᵐ[P.map flat]
        fun y => Real.sqrt (sqNorm (occGrad e α N y)) :=
      hac.ae_le ((weakGrad_ae_eq hw).mono fun y hy => by simp only [hy])
    refine MemLp.ae_eq hae.symm ?_
    refine (measurableEmbedding_flat.memLp_map_measure_iff).mpr ?_
    have hsum : MemLp (fun X : Config N d => ∑ p, |occGrad e α N (flat X) p|) 2 P :=
      memLp_finsetSum _ fun p _ => (memLp_occGrad_flat hyp hμ he α N p).abs
    refine hsum.of_le ?_ (Eventually.of_forall fun X => ?_)
    · show AEStronglyMeasurable (fun X => Real.sqrt (∑ p, occGrad e α N (flat X) p ^ 2)) P
      refine Real.continuous_sqrt.comp_aestronglyMeasurable ?_
      have := Finset.aestronglyMeasurable_sum (μ := P) Finset.univ
        (f := fun p X => occGrad e α N (flat X) p ^ 2)
        fun p _ => ((memLp_occGrad_flat hyp hμ he α N p).aestronglyMeasurable.pow 2)
      exact this.congr (Eventually.of_forall fun X => by simp [Finset.sum_apply])
    · simp only [Function.comp, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [abs_of_nonneg (Finset.sum_nonneg fun p _ => abs_nonneg _)]
      rw [Real.sqrt_le_left (Finset.sum_nonneg fun p _ => abs_nonneg _)]
      unfold sqNorm
      calc ∑ p, occGrad e α N (flat X) p ^ 2 = ∑ p, |occGrad e α N (flat X) p| ^ 2 := by
            simp_rw [sq_abs]
        _ ≤ (∑ p, |occGrad e α N (flat X) p|) ^ 2 :=
            Finset.sum_sq_le_sq_sum_of_nonneg fun p _ => abs_nonneg _

end memH1

end SharpLSI
