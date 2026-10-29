import FullLabeledLSI.Examples.E01g4_Near
import FullLabeledLSI.Examples.Paper.Sec9LamG
import FullLabeledLSI.Examples.E01g6_Alt

/-!
# Lane D, Task C (E01g7): `λ_G` versus the real infimum `Λ_F`
-/

open MeasureTheory InformationTheory Filter Topology
open scoped Real ENNReal ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

theorem LamF_pos {C : Torus 1 → ℝ} (δ : ℝ) (hδ : 0 < δ)
    (hsup : ∀ n : ℤ, n ≠ 0 → chat C n ≤ 1 - δ) : 0 < LamF C := by
  have ha : 0 < aCos := by unfold aCos; positivity
  unfold LamF
  refine lt_of_lt_of_le (b := aCos * δ) (by positivity) (le_ciInf fun n => ?_)
  have h := hsup ((n : ℤ) + 1) (by omega)
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    nlinarith
  have h2 : δ ≤ 1 - chat C ((n : ℤ) + 1) := by linarith
  calc aCos * δ ≤ aCos * 1 * δ := by simp
    _ ≤ aCos * ((n : ℝ) + 1) ^ 2 * (1 - chat C ((n : ℤ) + 1)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 ha.le) h2 hδ.le (by positivity)

/-- `λ_G ≤ ofReal r` whenever `Λ_F ≤ r`. -/
theorem lamG_le_of_LamF_le {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) (hyp : ∃ KV KW : ℝ, Hyp zeroV (attrW C) KV KW)
    (hsup : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, n ≠ 0 → chat C n ≤ 1 - δ)
    (e : ℕ → Torus 1 → ℝ) (lam : ℕ → ℝ) (Cm : ℕ → ℕ → ℝ)
    (he : IsRefEigenbasis (haar 1) e lam) (hCm : IsInverseOfIPlus (Tmat (attrW C) (haar 1) e) Cm)
    {r : ℝ} (hr : LamF C ≤ r) : lamG (lamShift lam) Cm ≤ ENNReal.ofReal r := by
  obtain ⟨δ, hδ, hs⟩ := hsup
  have hpos := LamF_pos δ hδ hs
  have hr0 : 0 ≤ r := by linarith
  rw [lamG_formula hC hmin hyp ⟨δ, hδ, hs⟩ e lam Cm he hCm]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hlt : LamF C < r + ε := by
    have : (0 : ℝ) < ε := by exact_mod_cast hε
    linarith
  unfold LamF at hlt
  obtain ⟨n, hn⟩ := exists_lt_of_ciInf_lt hlt
  calc (⨅ n : ℕ, ENNReal.ofReal (aCos * ((n : ℝ) + 1) ^ 2 * (1 - chat C ((n : ℤ) + 1))))
      ≤ ENNReal.ofReal (aCos * ((n : ℝ) + 1) ^ 2 * (1 - chat C ((n : ℤ) + 1))) := iInf_le _ n
    _ ≤ ENNReal.ofReal (r + ε) := ENNReal.ofReal_le_ofReal hn.le
    _ = ENNReal.ofReal r + ε := by
        rw [ENNReal.ofReal_add hr0 (by positivity)]; simp

end SharpLSI.FL.Ex.LaneD
