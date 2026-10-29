import SharpSymmetricLSI.Paper.ProductFisherDens

/-!
# (2.11): the gradient of `Φ` on configurations (Phase 3, lane D; R6)

`∇ᵢΦ(X) = ∇V(xᵢ) + ∇log ρ(xᵢ) + N⁻¹ ∑_{j≠i} ∇₁W(xᵢ,xⱼ)`, using `W(x,y) = W(y,x)`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} {N : ℕ}

/-- Swap of the two particles on `𝕋^{2×d}` and on `ℝ^{2×d}`. -/
def swapT (Y : UnitAddTorus (Fin 2 × Fin d)) : UnitAddTorus (Fin 2 × Fin d) :=
  fun q => Y (Fin.rev q.1, q.2)

noncomputable def swapL : (Fin 2 × Fin d → ℝ) →L[ℝ] (Fin 2 × Fin d → ℝ) :=
  ContinuousLinearMap.pi fun q => ContinuousLinearMap.proj (Fin.rev q.1, q.2)

theorem swapL_apply (x : Fin 2 × Fin d → ℝ) (q : Fin 2 × Fin d) :
    swapL x q = x (Fin.rev q.1, q.2) := rfl

theorem secT_swapT (Y : UnitAddTorus (Fin 2 × Fin d)) : secT (swapT Y) = swapL (secT Y) := rfl

theorem W2_swap (hyp : Hyp V W KV KW) (x : Fin 2 × Fin d → ℝ) :
    (W2 W ∘ liftT) (swapL x) = (W2 W ∘ liftT) x := by
  simp only [Function.comp, W2, unflat]
  rw [hyp.symm]
  rfl

theorem lineDeriv_comp_clm' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : F → ℝ) (T : E →L[ℝ] F) (x v : E) :
    lineDeriv ℝ (g ∘ T) x v = lineDeriv ℝ g (T x) (T v) := by
  unfold lineDeriv
  congr 1
  funext t
  simp [map_add, map_smul]

theorem swapL_single (b : Fin 2) (k : Fin d) :
    swapL (Pi.single (b, k) (1 : ℝ)) = Pi.single (Fin.rev b, k) 1 := by
  funext q
  obtain ⟨c, j⟩ := q
  rw [swapL_apply]
  by_cases h : c = Fin.rev b
  · subst h; simp [Pi.single_apply, Prod.ext_iff]
  · have h' : Fin.rev c ≠ b := fun e => h (by rw [← e, Fin.rev_rev])
    simp [Pi.single_apply, Prod.ext_iff, h, h']

theorem lipGrad_W2_swap (hyp : Hyp V W KV KW) (Y : UnitAddTorus (Fin 2 × Fin d)) (b : Fin 2)
    (k : Fin d) : lipGrad (W2 W) (swapT Y) (Fin.rev b, k) = lipGrad (W2 W) Y (b, k) := by
  unfold lipGrad
  rw [secT_swapT, ← swapL_single, ← lineDeriv_comp_clm']
  congr 1
  funext x
  exact W2_swap hyp x

theorem projPair_swap (i j : Fin N) (y : UnitAddTorus (Fin N × Fin d)) :
    projPair j i y = swapT (projPair i j y) := by
  funext q
  obtain ⟨b, k⟩ := q
  simp only [projPair, swapT]
  fin_cases b <;> rfl

/-- The one-body part `∇V + ∇log ρ`. -/
noncomputable def aGrad (V : Torus d → ℝ) (ρ : Torus d → ℝ) (x : Torus d) (k : Fin d) : ℝ :=
  lipGrad V x k + gLog ρ x k

/-- `∇₁W(x,y)` as the Lipschitz gradient of `W2`. -/
noncomputable def bGrad (W : Torus d → Torus d → ℝ) (x y : Torus d) (k : Fin d) : ℝ :=
  lipGrad (W2 W) (flat ![x, y]) (0, k)

theorem projPair_flat (X : Config N d) (i j : Fin N) :
    projPair i j (flat X) = flat ![X i, X j] := by
  funext q
  obtain ⟨b, k⟩ := q
  fin_cases b <;> rfl

theorem gPhi_flat (hyp : Hyp V W KV KW) (hN : 1 ≤ N) {ρ : Torus d → ℝ} (X : Config N d)
    (i : Fin N) (k : Fin d) :
    gPhi V W ρ N (flat X) (i, k) =
      aGrad V ρ (X i) k + 1 / (N : ℝ) * ∑ j ∈ Finset.univ.erase i, bGrad W (X i) (X j) k := by
  unfold gPhi
  have h1 : ∑ i' : Fin N, (if i = i' then lipGrad V (projBlock i' (flat X)) k +
      gLog ρ (projBlock i' (flat X)) k else 0) = aGrad V ρ (X i) k := by
    rw [Finset.sum_ite_eq]; simp [aGrad, projBlock_flat]
  rw [h1]
  congr 1
  have hp : ∀ a b : Fin N, (if a = b then 0 else pairGrad a b (lipGrad (W2 W)) (flat X) (i, k)) =
      (if a = b then 0 else if i = a then bGrad W (X a) (X b) k else 0) +
      (if a = b then 0 else if i = b then bGrad W (X b) (X a) k else 0) := by
    intro a b
    by_cases hab : a = b
    · simp [hab]
    · simp only [hab, if_false, pairGrad]
      by_cases hia : i = a
      · subst hia
        have hib : ¬ i = b := hab
        simp [hib, bGrad, projPair_flat]
      · by_cases hib : i = b
        · subst hib
          simp only [hia, if_false, if_true, zero_add, bGrad]
          rw [projPair_swap, ← lipGrad_W2_swap hyp _ 0 k, projPair_flat]
          rfl
        · simp [hia, hib]
  simp_rw [hp, Finset.sum_add_distrib]
  have e1 : ∑ a : Fin N, ∑ b : Fin N, (if a = b then 0 else if i = a then bGrad W (X a) (X b) k
      else 0) = ∑ j ∈ Finset.univ.erase i, bGrad W (X i) (X j) k := by
    rw [Finset.sum_eq_single i]
    · rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      simp only [↓reduceIte, add_zero]
      refine Finset.sum_congr rfl fun j hj => ?_
      have : ¬ i = j := fun h => (Finset.mem_erase.mp hj).1 h.symm
      simp [this]
    · intro a _ hai
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [Ne.symm hai]
    · simp
  have e2 : ∑ a : Fin N, ∑ b : Fin N, (if a = b then 0 else if i = b then bGrad W (X b) (X a) k
      else 0) = ∑ j ∈ Finset.univ.erase i, bGrad W (X i) (X j) k := by
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single i]
    · rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      simp only [↓reduceIte, add_zero]
      refine Finset.sum_congr rfl fun j hj => ?_
      have : ¬ j = i := (Finset.mem_erase.mp hj).1
      simp [this]
    · intro b _ hbi
      refine Finset.sum_eq_zero fun a _ => ?_
      simp [Ne.symm hbi]
    · simp
  rw [e1, e2]
  have hN0 : (N : ℝ) ≠ 0 := by have : (0 : ℝ) < N := by exact_mod_cast hN
                               exact this.ne'
  field_simp
  ring

end SharpLSI
