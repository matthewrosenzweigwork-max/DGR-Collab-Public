import SharpSymmetricLSI.Paper.SemiconvexLip2
import SharpSymmetricLSI.Defs.D02_Hypotheses

/-!
# Hypothesis (1.2) ⇒ `V`, `W` Lipschitz with bounded weak gradients (Phase 3, lane D; R6)

The semiconvexity of `W` on `(ℝ^d)²` is transported to the coordinates `Fin 2 × Fin d` of the
two-particle configuration space by a coordinate permutation.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal NNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem coordSemiconvex_V (hyp : Hyp V W KV KW) : CoordSemiconvex V KV := by
  intro φ hφ hφc hφ0 k
  have h := hyp.semiconvex_V φ hφ hφc hφ0 (Pi.single k 1)
  have : ∑ j, (Pi.single k (1 : ℝ) : Fin d → ℝ) j ^ 2 = 1 := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  rwa [this, mul_one] at h

/-- `Fin d ⊕ Fin d ≃ Fin 2 × Fin d`. -/
def sumFinTwo (d : ℕ) : Fin d ⊕ Fin d ≃ Fin 2 × Fin d where
  toFun := Sum.elim (fun j => (0, j)) (fun j => (1, j))
  invFun := fun p => if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  left_inv := by intro s; cases s <;> simp
  right_inv := by
    rintro ⟨a, j⟩
    fin_cases a <;> simp

/-- The coordinate permutation `(ℝ^d)² ≃ ℝ^{Fin 2 × Fin d}`. -/
noncomputable def pairEquiv (d : ℕ) : (Fin d → ℝ) × (Fin d → ℝ) ≃ᵐ (Fin 2 × Fin d → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin d ⊕ Fin d => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 × Fin d => ℝ) (sumFinTwo d))

theorem pairEquiv_apply (p : (Fin d → ℝ) × (Fin d → ℝ)) (a : Fin 2) (j : Fin d) :
    pairEquiv d p (a, j) = if a = 0 then p.1 j else p.2 j := by
  by_cases ha : a = 0
  · rw [ha, if_pos rfl]
    have : ((0 : Fin 2), j) = sumFinTwo d (Sum.inl j) := rfl
    simp only [pairEquiv, MeasurableEquiv.trans_apply]
    rw [this, MeasurableEquiv.piCongrLeft_apply_apply]
    rfl
  · have ha1 : a = 1 := by omega
    rw [ha1, if_neg (by decide)]
    have : ((1 : Fin 2), j) = sumFinTwo d (Sum.inr j) := rfl
    simp only [pairEquiv, MeasurableEquiv.trans_apply]
    rw [this, MeasurableEquiv.piCongrLeft_apply_apply]
    rfl

theorem measurePreserving_pairEquiv :
    MeasurePreserving (pairEquiv d) ((volume : Measure (Fin d → ℝ)).prod volume) volume := by
  have h1 := (measurePreserving_sumPiEquivProdPi (fun _ : Fin d ⊕ Fin d => (volume : Measure ℝ))).symm
  have h2 := measurePreserving_piCongrLeft (fun _ : Fin 2 × Fin d => (volume : Measure ℝ))
    (sumFinTwo d)
  exact h2.comp h1

/-- `pairEquiv` as a continuous linear map. -/
noncomputable def pairCLM (d : ℕ) : ((Fin d → ℝ) × (Fin d → ℝ)) →L[ℝ] (Fin 2 × Fin d → ℝ) :=
  ContinuousLinearMap.pi fun q => if q.1 = 0 then (ContinuousLinearMap.proj q.2).comp
    (ContinuousLinearMap.fst ℝ _ _) else (ContinuousLinearMap.proj q.2).comp
    (ContinuousLinearMap.snd ℝ _ _)

theorem pairCLM_eq : ⇑(pairCLM d) = ⇑(pairEquiv d) := by
  funext p q
  obtain ⟨a, j⟩ := q
  rw [pairEquiv_apply]
  simp only [pairCLM, ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

theorem fderiv_comp_clm_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : F → ℝ} (hg : Differentiable ℝ g) (T : E →L[ℝ] F)
    (q v : E) : fderiv ℝ (g ∘ T) q v = fderiv ℝ g (T q) (T v) := by
  rw [((hg (T q)).hasFDerivAt.comp q T.hasFDerivAt).fderiv]
  rfl

theorem secondDirDeriv_comp_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : F → ℝ} (hφ : ContDiff ℝ ∞ φ) (T : E →L[ℝ] F)
    (ξ q : E) : secondDirDeriv (φ ∘ T) ξ q = secondDirDeriv φ (T ξ) (T q) := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hd' : Differentiable ℝ (fun z => fderiv ℝ φ z (T ξ)) :=
    ((hφ.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const).differentiable (by simp)
  unfold secondDirDeriv
  have e : (fun y => fderiv ℝ (φ ∘ T) y ξ) = (fun z => fderiv ℝ φ z (T ξ)) ∘ T := by
    funext y; exact fderiv_comp_clm_apply hd T y ξ
  rw [e, fderiv_comp_clm_apply hd' T q ξ]

/-- The two-particle function `Y ↦ W(Y₀, Y₁)` on `𝕋^{Fin 2 × Fin d}`. -/
noncomputable def W2 (W : Torus d → Torus d → ℝ) : UnitAddTorus (Fin 2 × Fin d) → ℝ :=
  (fun X : Config 2 d => W (X 0) (X 1)) ∘ unflat

theorem W2_liftT_pair (p : (Fin d → ℝ) × (Fin d → ℝ)) :
    W2 W (liftT (pairEquiv d p)) = W (liftT p.1) (liftT p.2) := by
  simp only [W2, Function.comp]
  congr 1 <;> funext j <;> simp [liftT, pairEquiv_apply]

theorem coordSemiconvex_W2 (hyp : Hyp V W KV KW) : CoordSemiconvex (W2 W) KW := by
  intro φ hφ hφc hφ0 k
  obtain ⟨a, j⟩ := k
  set T := pairCLM d
  set ξ : (Fin d → ℝ) × (Fin d → ℝ) :=
    if a = 0 then (Pi.single j 1, 0) else (0, Pi.single j 1) with hξ
  have hTξ : T ξ = Pi.single (a, j) 1 := by
    rw [pairCLM_eq]
    funext q; obtain ⟨b, i⟩ := q
    rw [pairEquiv_apply]
    fin_cases a <;> fin_cases b <;> by_cases h : i = j <;> simp [hξ, h, Pi.single_apply]
  have hξ1 : ∑ i, ξ.1 i ^ 2 + ∑ i, ξ.2 i ^ 2 = 1 := by
    have hs : ∑ i, (Pi.single j (1 : ℝ) : Fin d → ℝ) i ^ 2 = 1 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hi; simp [hi]
      · simp
    fin_cases a <;> simp [hξ, hs]
  have hφT : ContDiff ℝ ∞ (φ ∘ T) := hφ.comp T.contDiff
  have hTinj : Function.Injective T := by
    rw [pairCLM_eq]; exact (pairEquiv d).injective
  have hce : Topology.IsClosedEmbedding ⇑T :=
    LinearMap.isClosedEmbedding_of_injective (f := T.toLinearMap) (LinearMap.ker_eq_bot.mpr hTinj)
  have hφTc : HasCompactSupport (φ ∘ T) := hφc.comp_isClosedEmbedding hce
  have h := hyp.semiconvex_W (φ ∘ T) hφT hφTc (fun p => hφ0 _) ξ
  rw [hξ1, mul_one] at h
  have hmp := measurePreserving_pairEquiv (d := d)
  have e1 : ∫ p, (φ ∘ T) p = ∫ x, φ x := by
    rw [show (φ ∘ T) = φ ∘ (pairEquiv d) by rw [pairCLM_eq]]
    exact hmp.integral_comp' φ
  have e2 : ∫ p, W (liftT p.1) (liftT p.2) * secondDirDeriv (φ ∘ T) ξ p =
      ∫ x, W2 W (liftT x) * secondDirDeriv φ (Pi.single (a, j) 1) x := by
    have : (fun p : (Fin d → ℝ) × (Fin d → ℝ) => W (liftT p.1) (liftT p.2) *
        secondDirDeriv (φ ∘ T) ξ p) = (fun x => W2 W (liftT x) *
          secondDirDeriv φ (Pi.single (a, j) 1) x) ∘ (pairEquiv d) := by
      funext p
      simp only [Function.comp]
      rw [secondDirDeriv_comp_clm hφ T ξ p, hTξ, W2_liftT_pair, pairCLM_eq]
    rw [this]
    exact hmp.integral_comp' (fun x => W2 W (liftT x) * secondDirDeriv φ (Pi.single (a, j) 1) x)
  rw [e1, e2] at h
  exact h

end SharpLSI
