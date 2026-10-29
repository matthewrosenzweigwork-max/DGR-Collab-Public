import SharpSymmetricLSI.Paper.Defective4
import SharpSymmetricLSI.Paper.CondEntropy4

/-!
# R03 (Proposition 2.2), part 5: past, current particle and rest as blocks of the flat torus

For `j < N`, `blockIdx : ((Fin j × Fin d) ⊕ Fin d) ⊕ (Fin (N-j-1) × Fin d) ≃ Fin N × Fin d` sends
the three blocks to the particles `< j`, `= j`, `> j`. A configuration `X` corresponds to
`join (join (flat (past X)) (X j)) (flat (rest X))` (`reidx_flat`), and Lebesgue measure on the
configurations corresponds to Lebesgue measure on the blocks.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d N : ℕ}

/-- The block index equivalence. -/
def blockIdx (j : ℕ) (hj : j < N) :
    ((Fin j × Fin d) ⊕ Fin d) ⊕ (Fin (N - j - 1) × Fin d) ≃ Fin N × Fin d where
  toFun s := match s with
    | Sum.inl (Sum.inl (a, k)) => (⟨a, by have := a.2; omega⟩, k)
    | Sum.inl (Sum.inr k) => (⟨j, hj⟩, k)
    | Sum.inr (b, k) => (⟨j + 1 + b, by have := b.2; omega⟩, k)
  invFun q :=
    if h : q.1.val < j then Sum.inl (Sum.inl (⟨q.1.val, h⟩, q.2))
    else if h' : q.1.val = j then Sum.inl (Sum.inr q.2)
    else Sum.inr (⟨q.1.val - j - 1, by have := q.1.2; omega⟩, q.2)
  left_inv s := by
    rcases s with ((⟨a, k⟩ | k) | ⟨b, k⟩)
    · simp [a.2]
    · simp
    · have h1 : ¬ (j + 1 + (b : ℕ) < j) := by omega
      have h2 : ¬ (j + 1 + (b : ℕ) = j) := by omega
      simp only [h1, h2, dite_false, if_false]
      congr 2; ext; simp; omega
  right_inv q := by
    obtain ⟨i, k⟩ := q
    by_cases h : i.val < j
    · simp [h]
    · by_cases h' : i.val = j
      · simp [h, h']; ext; simp [h']
      · simp only [h, h', dite_false, if_false]
        ext <;> simp; omega

/-- The particles after `j`. -/
def restC (j : ℕ) (hj : j < N) (X : Config N d) : Config (N - j - 1) d :=
  fun b => X ⟨j + 1 + b, by have := b.2; omega⟩

theorem measurable_restC (j : ℕ) (hj : j < N) : Measurable (restC (d := d) j hj) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

/-- The flat configuration in block coordinates. -/
theorem reidx_symm_flat (j : ℕ) (hj : j < N) (X : Config N d) :
    reidx (blockIdx j hj).symm (flat X) =
      join (join (flat (past j hj.le X)) (X ⟨j, hj⟩)) (flat (restC j hj X)) := by
  funext s
  rcases s with ((⟨a, k⟩ | k) | ⟨b, k⟩) <;> rfl

theorem flat_reidx_join (j : ℕ) (hj : j < N) (p : Config j d) (x : Torus d)
    (z : Config (N - j - 1) d) :
    unflat (reidx (blockIdx j hj) (join (join (flat p) x) (flat z))) ⟨j, hj⟩ = x := by
  funext k
  show join (join (flat p) x) (flat z) ((blockIdx j hj).symm (⟨j, hj⟩, k)) = x k
  simp [blockIdx, join]

end SharpLSI
