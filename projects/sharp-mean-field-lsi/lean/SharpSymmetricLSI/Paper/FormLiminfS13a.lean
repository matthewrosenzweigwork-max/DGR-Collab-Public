import SharpSymmetricLSI.Paper.FormLiminf8
import SharpSymmetricLSI.Paper.TestEnergy2

/-!
# R33: the five-term split of the particle generator `genL`
-/

open MeasureTheory Filter Topology Real

namespace SharpLSI

variable {d : ℕ}

theorem genL_split (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (eC : ℕ → Torus d → ℝ) (lam : ℕ → ℝ)
    (N : ℕ) (c : Cyl) (s : Finset ℕ) (a : ℕ → ℕ → ℝ) (X : Config N d) :
    genL W μ eC lam N c X =
      (∑ i : Fin c.J, lam ((i : ℕ) + 1) * (zC eC N c.J X i * cylD c i (zC eC N c.J X) -
          fderiv ℝ (cylD c i) (zC eC N c.J X) (Pi.single i 1))) +
      (∑ i : Fin c.J, cylD c i (zC eC N c.J X) * ∑ p ∈ s, ∑ q ∈ s, a p q *
          ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) * (if p = (i : ℕ) then lam ((i : ℕ) + 1) else 0)) -
      (∑ i : Fin c.J, ∑ j : Fin c.J, fderiv ℝ (cylD c i) (zC eC N c.J X) (Pi.single j 1) *
          (mobA eC N X j i - if (j : ℕ) = i then lam ((i : ℕ) + 1) else 0)) +
      (∑ i : Fin c.J, cylD c i (zC eC N c.J X) * (forceD W μ eC N i X - ∑ p ∈ s, ∑ q ∈ s, a p q *
          ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) * mobA eC N X p i)) +
      (∑ i : Fin c.J, cylD c i (zC eC N c.J X) * ∑ p ∈ s, ∑ q ∈ s, a p q *
          ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) *
          (mobA eC N X p i - if p = (i : ℕ) then lam ((i : ℕ) + 1) else 0)) := by
  have hdiag : ∀ i : Fin c.J, ∑ j : Fin c.J, fderiv ℝ (cylD c i) (zC eC N c.J X) (Pi.single j 1) *
      (if (j : ℕ) = i then lam ((i : ℕ) + 1) else 0) =
      fderiv ℝ (cylD c i) (zC eC N c.J X) (Pi.single i 1) * lam ((i : ℕ) + 1) := fun i => by
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (fun h => hj (Fin.ext h)), mul_zero])
      (by simp), if_pos rfl]
  unfold genL
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib, hdiag]
  have e1 : ∑ i : Fin c.J, lam ((i : ℕ) + 1) * zC eC N c.J X i * cylD c i (zC eC N c.J X) =
      ∑ i : Fin c.J, lam ((i : ℕ) + 1) * (zC eC N c.J X i * cylD c i (zC eC N c.J X)) :=
    Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
  have e2 : ∑ i : Fin c.J, fderiv ℝ (cylD c i) (zC eC N c.J X) (Pi.single i 1) * lam ((i : ℕ) + 1) =
      ∑ i : Fin c.J, lam ((i : ℕ) + 1) * fderiv ℝ (cylD c i) (zC eC N c.J X) (Pi.single i 1) :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e1, e2]
  ring

end SharpLSI
