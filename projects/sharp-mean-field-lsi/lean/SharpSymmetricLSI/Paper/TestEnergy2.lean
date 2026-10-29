import SharpSymmetricLSI.Paper.TestEnergy1
import SharpSymmetricLSI.Paper.GroundT6
import SharpSymmetricLSI.Defs.D16_GaussianLimit

/-!
# R33 groundwork: `|∇φ_N|² = ∑_{i,j} ∂_iφ ∂_jφ (Z_N) A_{N,ij}` (manuscript (8.14))
-/

open MeasureTheory Filter Topology Real

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The empirical mobility `A_{N,ij} = N⁻¹ ∑_l ∇e_i(X_l)·∇e_j(X_l)` (manuscript (8.13)). -/
noncomputable def mobA (eC : ℕ → Torus d → ℝ) (N : ℕ) (X : Config N d) (i j : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ l, ∑ k, cgrad (eC (i + 1)) (X l) k * cgrad (eC (j + 1)) (X l) k

theorem rpow_neg_half_sq (N : ℕ) : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (N : ℝ)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num [Real.rpow_neg_one]

/-- The square of a sum over `i`, summed over `l, k`, regrouped as a double sum over `i, j`. -/
theorem sum_sq_regroup {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ] (x : ι → κ → ρ → ℝ) :
    ∑ l, ∑ k, (∑ i, x i l k) ^ 2 = ∑ i, ∑ j, ∑ l, ∑ k, x i l k * x j l k := by
  have h : ∀ l k, (∑ i, x i l k) ^ 2 = ∑ i, ∑ j, x i l k * x j l k := fun l k => by
    rw [sq, Finset.sum_mul_sum]
  simp_rw [h]
  calc ∑ l, ∑ k, ∑ i, ∑ j, x i l k * x j l k = ∑ l, ∑ i, ∑ k, ∑ j, x i l k * x j l k :=
        Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ j, ∑ k, x i l k * x j l k :=
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ j, ∑ k, x i l k * x j l k := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_comm

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e eC : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT))
  (heC : ∀ j, eC j =ᵐ[haar d] e j) (N : ℕ) (c : Cyl)
include hyp hμ hφ heC

omit hyp hμ hφ in
theorem cyl_ae_eq :
    ((fun X => c.φ (fun i => fluct e N i X)) ∘ unflat : UnitAddTorus (Fin N × Fin d) → ℝ)
      =ᵐ[volume] (fun X => c.φ (zC eC N c.J X)) ∘ unflat := by
  have hb : ∀ (b : Fin N) (j : ℕ), (fun y : UnitAddTorus (Fin N × Fin d) => e j (projBlock b y))
      =ᵐ[volume] fun y => eC j (projBlock b y) := fun b j =>
    (measurePreserving_projBlock b).quasiMeasurePreserving.ae_eq_comp (heC j).symm
  have hall : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin N × Fin d))), ∀ (b : Fin N) (j : ℕ),
      e j (projBlock b y) = eC j (projBlock b y) := by
    rw [ae_all_iff]; intro b; rw [ae_all_iff]; intro j; exact hb b j
  filter_upwards [hall] with y hy
  simp only [Function.comp_apply]
  congr 1
  funext i
  simp only [fluct, zC]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  exact hy l _

/-- **`|∇φ_N|² = ∑ ∂_iφ ∂_jφ A_{ij}`** a.e. under `μ^{⊗N}`. -/
theorem gradSqC_cyl_ae :
    ∀ᵐ X ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))),
      gradSqC (fun X => c.φ (fun i => fluct e N i X)) X =
        ∑ i : Fin c.J, ∑ j : Fin c.J, fderiv ℝ c.φ (zC eC N c.J X) (Pi.single i 1) *
          fderiv ℝ c.φ (zC eC N c.J X) (Pi.single j 1) * mobA eC N X i j := by
  have h := (isWeakGrad_cyl hφ N c).congr_ae (cyl_ae_eq heC N c).symm
  filter_upwards [ae_pi_of_ae_volume hyp hμ (weakGrad_ae_eq h)] with X hX
  unfold gradSqC weakGradC
  simp_rw [hX]
  have e1 : unflat (flat X) = X := rfl
  have e2 : ∀ l, projBlock l (flat X) = X l := fun _ => rfl
  try simp only [e1, e2]
  rw [sum_sq_regroup (fun (i : Fin c.J) (l : Fin N) (k : Fin d) =>
    fderiv ℝ c.φ (zC eC N c.J X) (Pi.single i 1) *
      ((N : ℝ) ^ (-(1 / 2 : ℝ)) * cgrad (eC (i + 1)) (X l) k))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold mobA
  rw [← rpow_neg_half_sq N, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end

end SharpLSI
