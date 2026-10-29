import SharpSymmetricLSI.Paper.ProductFisherFormula
import FullLabeledLSI.Paper.Sec3RecEntropy

/-!
# Fisher information of products with nonidentical factors, I: weak gradients

Generalization of `PhiF`, `gPhi` (ProductFisherGrad, ProductFisherSimp) to a per-label density
`ρs : Fin N → Torus d → ℝ`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff NNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} {N : ℕ}

/-- `Φ = H_N ∘ unflat + ∑ᵢ log ρᵢ(yᵢ)` on the flat torus. -/
def PhiFG (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρs : Fin N → Torus d → ℝ)
    (y : UnitAddTorus (Fin N × Fin d)) : ℝ :=
  ∑ i, (V (projBlock i y) + logD (ρs i) (projBlock i y)) +
    1 / (2 * (N : ℝ)) * ∑ i, ∑ j, (if i = j then 0 else W2 W (projPair i j y))

/-- The weak gradient of `Φ`. -/
def gPhiG (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρs : Fin N → Torus d → ℝ)
    (y : UnitAddTorus (Fin N × Fin d)) (p : Fin N × Fin d) : ℝ :=
  ∑ i, (if p.1 = i then lipGrad V (projBlock i y) p.2 + gLog (ρs i) (projBlock i y) p.2 else 0) +
    1 / (2 * (N : ℝ)) * ∑ i, ∑ j, (if i = j then 0 else pairGrad i j (lipGrad (W2 W)) y p)

theorem PhiFG_flat (hyp : Hyp V W KV KW) (ρs : Fin N → Torus d → ℝ) (X : Config N d) :
    PhiFG V W ρs (flat X) = hamiltonian V W N X + ∑ i, Real.log (ρs i (X i)) := by
  unfold PhiFG hamiltonian
  rw [Finset.sum_add_distrib]
  have h1 : ∀ i j, (if i = j then 0 else W2 W (projPair i j (flat X))) = W (X i) (X j) := by
    intro i j
    split_ifs with h
    · subst h; rw [hyp.diag]
    · rfl
  simp_rw [h1, projBlock_flat]
  simp only [logD]
  ring

theorem isWeakGrad_PhiFG (hyp : Hyp V W KV KW) {ρs : Fin N → Torus d → ℝ}
    (hs : ∀ i, IsSmoothT (ρs i)) (hpos : ∀ i x, 0 < ρs i x) :
    IsWeakGrad (PhiFG V W ρs) (gPhiG V W ρs) := by
  have hVw := isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp)
  have hWw := isWeakGrad_lipGrad (continuous_W2 hyp) (lipschitz_W2 hyp)
  have iV : Integrable V volume := integrable_of_continuous hyp.continuous_V
  have igV : ∀ k, Integrable (fun x => lipGrad V x k) volume := fun k =>
    integrable_of_bdd_meas (measurable_lipGrad hyp.continuous_V k)
      (abs_lipGrad_le (lipschitz_V hyp) · k)
  have iW : Integrable (W2 W) volume := integrable_of_continuous (continuous_W2 hyp)
  have igW : ∀ q, Integrable (fun x => lipGrad (W2 W) x q) volume := fun q =>
    integrable_of_bdd_meas (measurable_lipGrad (continuous_W2 hyp) q)
      (abs_lipGrad_le (lipschitz_W2 hyp) · q)
  have hblock : ∀ i : Fin N, IsWeakGrad
      (fun y => V (projBlock i y) + logD (ρs i) (projBlock i y))
      (fun y p => if p.1 = i then lipGrad V (projBlock i y) p.2 + gLog (ρs i) (projBlock i y) p.2
        else 0) := by
    intro i
    have hL := contDiff_logD (hs i) (hpos i)
    have hLw : IsWeakGrad (logD (ρs i)) (gLog (ρs i)) :=
      isWeakGrad_of_contDiff (hL.of_le (by simp))
    have hlogc : Continuous (logD (ρs i)) :=
      isOpenQuotientMap_liftT.continuous_comp_iff.mp hL.continuous
    have iL : Integrable (logD (ρs i)) volume := integrable_of_continuous hlogc
    have igL : ∀ k, Integrable (fun x => gLog (ρs i) x k) volume := fun k => by
      obtain ⟨C, hC⟩ := smoothGrad_bdd hL k
      exact integrable_of_bdd_meas (measurable_smoothGrad hL k) hC
    exact isWeakGrad_comp_projBlock i (hVw.add hLw) (iV.add iL) fun k => (igV k).add (igL k)
  have hpairs : ∀ i j : Fin N, IsWeakGrad (fun y => if i = j then 0 else W2 W (projPair i j y))
      (fun y p => if i = j then 0 else pairGrad i j (lipGrad (W2 W)) y p) := by
    intro i j
    by_cases h : i = j
    · simp only [h, ite_true]; exact isWeakGrad_const 0
    · simp only [h, ite_false]; exact isWeakGrad_comp_projPair h hWw iW igW
  have hsum1 := isWeakGrad_finsetSum Finset.univ fun i _ => hblock i
  have hsum2 := (isWeakGrad_finsetSum Finset.univ fun i _ =>
    isWeakGrad_finsetSum Finset.univ fun j _ => hpairs i j).cmul (1 / (2 * (N : ℝ)))
  exact hsum1.add hsum2

theorem PhiFG_bdd (hyp : Hyp V W KV KW) {ρs : Fin N → Torus d → ℝ}
    (hs : ∀ i, IsSmoothT (ρs i)) (hpos : ∀ i x, 0 < ρs i x) :
    ∃ C, ∀ y, |PhiFG V W ρs y| ≤ C := by
  obtain ⟨BV, hBV⟩ := exists_bound_of_continuous hyp.continuous_V
  have hBL := fun i => logD_bdd (hs i) (hpos i)
  choose BL hBL using hBL
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (continuous_W2 hyp)
  have hBW0 : 0 ≤ BW := (abs_nonneg _).trans (hBW 0)
  refine ⟨∑ i, (BV + BL i) + |1 / (2 * (N : ℝ))| * (N * (N * BW)), fun y => ?_⟩
  unfold PhiFG
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact (abs_add_le _ _).trans (add_le_add (hBV _) (hBL i _))
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (abs_sum_le_card_mul (B := N * BW) fun i =>
      (abs_sum_le_card_mul (B := BW) fun j => ?_).trans (by simp)).trans (by simp)
    split_ifs
    · simpa using hBW0
    · exact hBW _

theorem gPhiG_bdd (hyp : Hyp V W KV KW) {ρs : Fin N → Torus d → ℝ}
    (hs : ∀ i, IsSmoothT (ρs i)) (hpos : ∀ i x, 0 < ρs i x) :
    ∃ C, ∀ y p, |gPhiG V W ρs y p| ≤ C := by
  set LV := ((Real.toNNReal (KV * Fintype.card (Fin d) / 2) : ℝ≥0) : ℝ)
  set LW := ((Real.toNNReal (KW * Fintype.card (Fin 2 × Fin d) / 2) : ℝ≥0) : ℝ)
  have hCL := fun i => gLog_bdd (hs i) (hpos i)
  choose CL hCL using hCL
  have hLW0 : 0 ≤ LW := NNReal.coe_nonneg _
  have hLV0 : 0 ≤ LV := NNReal.coe_nonneg _
  have hV : ∀ x k, |lipGrad V x k| ≤ LV := fun x k => abs_lipGrad_le (lipschitz_V hyp) x k
  have hW : ∀ x q, |lipGrad (W2 W) x q| ≤ LW := fun x q => abs_lipGrad_le (lipschitz_W2 hyp) x q
  refine ⟨∑ i, (LV + max (CL i) 0) + |1 / (2 * (N : ℝ))| * (N * (N * LW)), fun y p => ?_⟩
  unfold gPhiG
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    split_ifs
    · exact (abs_add_le _ _).trans
        (add_le_add (hV _ _) ((hCL i _ _).trans (le_max_left _ _)))
    · simp only [abs_zero]; exact add_nonneg hLV0 (le_max_right _ _)
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (abs_sum_le_card_mul (B := N * LW) fun i =>
      (abs_sum_le_card_mul (B := LW) fun j => ?_).trans (by simp)).trans (by simp)
    unfold pairGrad
    split_ifs
    · simpa using hLW0
    · exact hW _ _
    · exact hW _ _
    · simpa using hLW0

/-- `√Z exp(Φ/2)` has weak gradient `√Z exp(Φ/2) ∇Φ / 2`. -/
theorem isWeakGrad_expPhiG (hyp : Hyp V W KV KW) {ρs : Fin N → Torus d → ℝ}
    (hs : ∀ i, IsSmoothT (ρs i)) (hpos : ∀ i x, 0 < ρs i x) (c : ℝ) :
    IsWeakGrad (fun y => c * Real.exp (PhiFG V W ρs y / 2))
      (fun y p => c * (Real.exp (PhiFG V W ρs y / 2) / 2 * gPhiG V W ρs y p)) := by
  have hΦ := isWeakGrad_PhiFG hyp hs hpos
  obtain ⟨B, hB⟩ := PhiFG_bdd hyp hs hpos
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  obtain ⟨Cg, hCg⟩ := gPhiG_bdd hyp hs hpos
  have iΦ : Integrable (PhiFG V W ρs) volume :=
    Integrable.of_bound hΦ.aestronglyMeasurable_fun B (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hB y)
  have igΦ : ∀ p, Integrable (fun y => gPhiG V W ρs y p) volume := fun p =>
    Integrable.of_bound (hΦ.aestronglyMeasurable_grad p) Cg (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hCg y p)
  obtain ⟨L, hL⟩ := deriv_expCut_bdd B hB0
  have h := isWeakGrad_comp hΦ iΦ igΦ ((contDiff_expCut B hB0).of_le (by simp)) hL
  have e1 : (fun y => expCut B hB0 (PhiFG V W ρs y)) = fun y => Real.exp (PhiFG V W ρs y / 2) :=
    funext fun y => expCut_eq hB0 (hB y)
  have e2 : (fun y p => deriv (expCut B hB0) (PhiFG V W ρs y) * gPhiG V W ρs y p) =
      fun y p => Real.exp (PhiFG V W ρs y / 2) / 2 * gPhiG V W ρs y p :=
    funext fun y => funext fun p => by rw [deriv_expCut hB0 (hB y)]
  rw [e1, e2] at h
  exact h.cmul c

theorem gPhiG_flat (hyp : Hyp V W KV KW) (hN : 1 ≤ N) (ρs : Fin N → Torus d → ℝ)
    (X : Config N d) (i : Fin N) (k : Fin d) :
    gPhiG V W ρs (flat X) (i, k) =
      aGrad V (ρs i) (X i) k + 1 / (N : ℝ) * ∑ j ∈ Finset.univ.erase i, bGrad W (X i) (X j) k := by
  unfold gPhiG
  have h1 : ∑ i' : Fin N, (if i = i' then lipGrad V (projBlock i' (flat X)) k +
      gLog (ρs i') (projBlock i' (flat X)) k else 0) = aGrad V (ρs i) (X i) k := by
    rw [Finset.sum_ite_eq]; simp [aGrad, projBlock_flat]
  rw [h1]
  congr 1
  have hp : ∀ a b : Fin N, (if a = b then 0 else pairGrad a b (lipGrad (W2 W)) (flat X) (i, k)) =
      (if a = b then 0 else if i = a then bGrad W (X a) (X b) k else 0) +
      (if a = b then 0 else if i = b then bGrad W (X b) (X a) k else 0) := by
    intro a b
    by_cases hab : a = b
    · simp [hab]
    · simp only [hab, ite_false, pairGrad]
      by_cases hia : i = a
      · subst hia
        have hib : ¬ i = b := hab
        simp [hib, bGrad, projPair_flat]
      · by_cases hib : i = b
        · subst hib
          simp only [hia, ite_false, ite_true, zero_add, bGrad]
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
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  field_simp
  ring

end SharpLSI.FL
