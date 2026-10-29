import SharpSymmetricLSI.Paper.PairProj
import SharpSymmetricLSI.Paper.SemiconvexHyp
import SharpSymmetricLSI.Paper.ProductEntropy

/-!
# (2.11): weak gradients for product states (Phase 3, lane D; R6)

`√(dν_N/dP_N) = √Z_N exp(Φ/2)` with `Φ = H_N + ∑ᵢ log ρ(xᵢ)`; the weak gradient of `Φ` on the
flat torus is assembled from the Lipschitz weak gradients of `V`, `W` (blocks and pairs) and the
smooth gradient of `log ρ`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff NNReal

namespace SharpLSI

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem isWeakGrad_finsetSum {α : Type*} (s : Finset α) {f : α → UnitAddTorus ι → ℝ}
    {g : α → UnitAddTorus ι → ι → ℝ} (h : ∀ a ∈ s, IsWeakGrad (f a) (g a)) :
    IsWeakGrad (fun y => ∑ a ∈ s, f a y) (fun y k => ∑ a ∈ s, g a y k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact isWeakGrad_const (ι := ι) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem exists_bound_secT {h : (ι → ℝ) → ℝ} (hc : Continuous h) :
    ∃ C, ∀ y : UnitAddTorus ι, |h (secT y)| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ_pi fun _ : ι => isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨C, fun y => ?_⟩
  have hm : secT y ∈ univ.pi fun _ : ι => Icc (0 : ℝ) 1 := fun i _ => by
    have := ((AddCircle.measurableEquivIoc 1 0) (y i)).2
    simp only [zero_add] at this
    exact ⟨this.1.le, this.2⟩
  simpa [Real.norm_eq_abs] using hC _ hm

theorem integrable_of_bdd_meas {g : UnitAddTorus ι → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ y, |g y| ≤ C) : Integrable g volume :=
  Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]; exact hC y)

/-- Smooth periodic functions: weak gradient bounded. -/
theorem smoothGrad_bdd {f : UnitAddTorus ι → ℝ} (hf : ContDiff ℝ ∞ (f ∘ liftT)) (k : ι) :
    ∃ C, ∀ y, |fderiv ℝ (f ∘ liftT) (secT y) (Pi.single k 1)| ≤ C :=
  exists_bound_secT ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)

theorem measurable_smoothGrad {f : UnitAddTorus ι → ℝ} (hf : ContDiff ℝ ∞ (f ∘ liftT)) (k : ι) :
    Measurable fun y => fderiv ℝ (f ∘ liftT) (secT y) (Pi.single k 1) :=
  ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).measurable.comp measurable_secT

section Phi

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} {N : ℕ}

theorem continuous_W2 (hyp : Hyp V W KV KW) : Continuous (W2 W) := by
  have e : W2 W = Function.uncurry W ∘ (fun Y : UnitAddTorus (Fin 2 × Fin d) =>
      ((fun k => Y (0, k) : Torus d), (fun k => Y (1, k) : Torus d))) := rfl
  rw [e]
  exact hyp.continuous_W.comp ((continuous_pi fun k => continuous_apply ((0 : Fin 2), k)).prodMk
    (continuous_pi fun k => continuous_apply ((1 : Fin 2), k)))

theorem projBlock_flat (X : Config N d) (i : Fin N) : projBlock i (flat X) = X i := rfl

theorem lipschitz_V (hyp : Hyp V W KV KW) :
    LipschitzWith (Real.toNNReal (KV * Fintype.card (Fin d) / 2)) (V ∘ liftT) :=
  lipschitz_of_coordSemiconvex hyp.continuous_V hyp.KV_nonneg (coordSemiconvex_V hyp)

theorem lipschitz_W2 (hyp : Hyp V W KV KW) :
    LipschitzWith (Real.toNNReal (KW * Fintype.card (Fin 2 × Fin d) / 2)) (W2 W ∘ liftT) :=
  lipschitz_of_coordSemiconvex (continuous_W2 hyp) hyp.KW_nonneg (coordSemiconvex_W2 hyp)

/-- `log ρ`. -/
noncomputable def logD (ρ : Torus d → ℝ) : Torus d → ℝ := fun x => Real.log (ρ x)

/-- The smooth gradient of `log ρ`. -/
noncomputable def gLog (ρ : Torus d → ℝ) (y : Torus d) (k : Fin d) : ℝ :=
  fderiv ℝ (logD ρ ∘ liftT) (secT y) (Pi.single k 1)

theorem contDiff_logD {ρ : Torus d → ℝ} (hs : IsSmoothT ρ) (hpos : ∀ x, 0 < ρ x) :
    ContDiff ℝ ∞ (logD ρ ∘ liftT) :=
  hs.log fun x => (hpos _).ne'

/-- `Φ = H_N ∘ unflat + ∑ᵢ log ρ(yᵢ)` on the flat torus. -/
noncomputable def PhiF (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ : Torus d → ℝ) (N : ℕ)
    (y : UnitAddTorus (Fin N × Fin d)) : ℝ :=
  ∑ i, (V (projBlock i y) + logD ρ (projBlock i y)) +
    1 / (2 * (N : ℝ)) * ∑ i, ∑ j, (if i = j then 0 else W2 W (projPair i j y))

/-- The weak gradient of `Φ`. -/
noncomputable def gPhi (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ : Torus d → ℝ) (N : ℕ)
    (y : UnitAddTorus (Fin N × Fin d)) (p : Fin N × Fin d) : ℝ :=
  ∑ i, (if p.1 = i then lipGrad V (projBlock i y) p.2 + gLog ρ (projBlock i y) p.2 else 0) +
    1 / (2 * (N : ℝ)) * ∑ i, ∑ j, (if i = j then 0 else pairGrad i j (lipGrad (W2 W)) y p)

theorem PhiF_flat (hyp : Hyp V W KV KW) (ρ : Torus d → ℝ) (X : Config N d) :
    PhiF V W ρ N (flat X) = hamiltonian V W N X + ∑ i, Real.log (ρ (X i)) := by
  unfold PhiF hamiltonian
  rw [Finset.sum_add_distrib]
  have h1 : ∀ i j, (if i = j then 0 else W2 W (projPair i j (flat X))) = W (X i) (X j) := by
    intro i j
    split_ifs with h
    · subst h; rw [hyp.diag]
    · rfl
  simp_rw [h1, projBlock_flat]
  simp only [logD]
  ring

theorem isWeakGrad_PhiF (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hs : IsSmoothT ρ)
    (hpos : ∀ x, 0 < ρ x) : IsWeakGrad (PhiF V W ρ N) (gPhi V W ρ N) := by
  have hVw := isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp)
  have hWw := isWeakGrad_lipGrad (continuous_W2 hyp) (lipschitz_W2 hyp)
  have hL := contDiff_logD hs hpos
  have hLw : IsWeakGrad (logD ρ) (gLog ρ) := isWeakGrad_of_contDiff (hL.of_le (by simp))
  have hlogc : Continuous (logD ρ) := isOpenQuotientMap_liftT.continuous_comp_iff.mp hL.continuous
  have hVLw := hVw.add hLw
  have iV : Integrable V volume := integrable_of_continuous hyp.continuous_V
  have iL : Integrable (logD ρ) volume := integrable_of_continuous hlogc
  have igV : ∀ k, Integrable (fun x => lipGrad V x k) volume := fun k =>
    integrable_of_bdd_meas (measurable_lipGrad hyp.continuous_V k)
      (abs_lipGrad_le (lipschitz_V hyp) · k)
  have igL : ∀ k, Integrable (fun x => gLog ρ x k) volume := fun k => by
    obtain ⟨C, hC⟩ := smoothGrad_bdd hL k
    exact integrable_of_bdd_meas (measurable_smoothGrad hL k) hC
  have iW : Integrable (W2 W) volume := integrable_of_continuous (continuous_W2 hyp)
  have igW : ∀ q, Integrable (fun x => lipGrad (W2 W) x q) volume := fun q =>
    integrable_of_bdd_meas (measurable_lipGrad (continuous_W2 hyp) q)
      (abs_lipGrad_le (lipschitz_W2 hyp) · q)
  have hblock : ∀ i : Fin N, IsWeakGrad (fun y => V (projBlock i y) + logD ρ (projBlock i y))
      (fun y p => if p.1 = i then lipGrad V (projBlock i y) p.2 + gLog ρ (projBlock i y) p.2
        else 0) := fun i =>
    isWeakGrad_comp_projBlock i hVLw (iV.add iL) fun k => (igV k).add (igL k)
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

theorem abs_sum_le_card_mul {α : Type*} [Fintype α] {f : α → ℝ} {B : ℝ} (h : ∀ a, |f a| ≤ B) :
    |∑ a, f a| ≤ Fintype.card α * B := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ a, |f a| ≤ ∑ _a : α, B := Finset.sum_le_sum fun a _ => h a
    _ = _ := by simp

theorem logD_bdd {ρ : Torus d → ℝ} (hs : IsSmoothT ρ) (hpos : ∀ x, 0 < ρ x) :
    ∃ C, ∀ x, |logD ρ x| ≤ C :=
  exists_bound_of_continuous (isOpenQuotientMap_liftT.continuous_comp_iff.mp
    (contDiff_logD hs hpos).continuous)

theorem gLog_bdd {ρ : Torus d → ℝ} (hs : IsSmoothT ρ) (hpos : ∀ x, 0 < ρ x) :
    ∃ C, ∀ x k, |gLog ρ x k| ≤ C := by
  have hL := contDiff_logD hs hpos
  obtain ⟨C, hC⟩ := exists_bound_secT (ι := Fin d) (h := fun x => ‖fderiv ℝ (logD ρ ∘ liftT) x‖)
    (hL.continuous_fderiv (by simp)).norm
  refine ⟨C, fun x k => ?_⟩
  have h1 := (fderiv ℝ (logD ρ ∘ liftT) (secT x)).le_opNorm (Pi.single k 1)
  have h2 : ‖(Pi.single k 1 : Fin d → ℝ)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    by_cases h : j = k
    · subst h; simp
    · simp [h]
  have h3 := hC x
  rw [abs_of_nonneg (norm_nonneg _)] at h3
  rw [gLog, ← Real.norm_eq_abs]
  calc _ ≤ _ := h1
    _ ≤ ‖fderiv ℝ (logD ρ ∘ liftT) (secT x)‖ * 1 := by gcongr
    _ ≤ C := by rw [mul_one]; exact h3

theorem PhiF_bdd (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hs : IsSmoothT ρ) (hpos : ∀ x, 0 < ρ x) :
    ∃ C, ∀ y, |PhiF V W ρ N y| ≤ C := by
  obtain ⟨BV, hBV⟩ := exists_bound_of_continuous hyp.continuous_V
  obtain ⟨BL, hBL⟩ := logD_bdd hs hpos
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (continuous_W2 hyp)
  have hBW0 : 0 ≤ BW := (abs_nonneg _).trans (hBW 0)
  refine ⟨N * (BV + BL) + |1 / (2 * (N : ℝ))| * (N * (N * BW)), fun y => ?_⟩
  unfold PhiF
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (abs_sum_le_card_mul fun i => (abs_add_le _ _).trans (add_le_add (hBV _) (hBL _))).trans
      (by simp)
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (abs_sum_le_card_mul (B := N * BW) fun i =>
      (abs_sum_le_card_mul (B := BW) fun j => ?_).trans (by simp)).trans (by simp)
    split_ifs
    · simpa using hBW0
    · exact hBW _

theorem gPhi_bdd (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hs : IsSmoothT ρ) (hpos : ∀ x, 0 < ρ x) :
    ∃ C, ∀ y p, |gPhi V W ρ N y p| ≤ C := by
  set LV := ((Real.toNNReal (KV * Fintype.card (Fin d) / 2) : ℝ≥0) : ℝ)
  set LW := ((Real.toNNReal (KW * Fintype.card (Fin 2 × Fin d) / 2) : ℝ≥0) : ℝ)
  obtain ⟨CL, hCL⟩ := gLog_bdd hs hpos
  have hLW0 : 0 ≤ LW := NNReal.coe_nonneg _
  have hLV0 : 0 ≤ LV := NNReal.coe_nonneg _
  have hV : ∀ x k, |lipGrad V x k| ≤ LV := fun x k => abs_lipGrad_le (lipschitz_V hyp) x k
  have hW : ∀ x q, |lipGrad (W2 W) x q| ≤ LW := fun x q => abs_lipGrad_le (lipschitz_W2 hyp) x q
  refine ⟨N * (LV + max CL 0) + |1 / (2 * (N : ℝ))| * (N * (N * LW)), fun y p => ?_⟩
  unfold gPhi
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (abs_sum_le_card_mul (B := LV + max CL 0) fun i => ?_).trans (by simp)
    split_ifs
    · exact (abs_add_le _ _).trans (add_le_add (hV _ _) ((hCL _ _).trans (le_max_left _ _)))
    · simp only [abs_zero]; positivity
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

/-- A smooth cutoff of `t ↦ exp(t/2)` agreeing with it on `[-B, B]`. -/
noncomputable def expCut (B : ℝ) (hB : 0 ≤ B) (t : ℝ) : ℝ :=
  (⟨B + 1, B + 2, by linarith, by linarith⟩ : ContDiffBump (0 : ℝ)) t * Real.exp (t / 2)

theorem contDiff_expCut (B : ℝ) (hB : 0 ≤ B) : ContDiff ℝ ∞ (expCut B hB) :=
  (ContDiffBump.contDiff _).mul (Real.contDiff_exp.comp (contDiff_id.div_const 2))

theorem expCut_eventuallyEq {B : ℝ} (hB : 0 ≤ B) {t : ℝ} (ht : |t| ≤ B) :
    expCut B hB =ᶠ[𝓝 t] fun s => Real.exp (s / 2) := by
  have hball : Metric.ball (0 : ℝ) (B + 1) ∈ 𝓝 t :=
    Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith)
  filter_upwards [hball] with s hs
  simp only [expCut]
  rw [ContDiffBump.one_of_mem_closedBall _ (Metric.ball_subset_closedBall hs), one_mul]

theorem expCut_eq {B : ℝ} (hB : 0 ≤ B) {t : ℝ} (ht : |t| ≤ B) : expCut B hB t = Real.exp (t / 2) :=
  (expCut_eventuallyEq hB ht).eq_of_nhds

theorem deriv_expCut {B : ℝ} (hB : 0 ≤ B) {t : ℝ} (ht : |t| ≤ B) :
    deriv (expCut B hB) t = Real.exp (t / 2) / 2 := by
  rw [(expCut_eventuallyEq hB ht).deriv_eq]
  have h : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) * (1 / 2)) t :=
    ((hasDerivAt_id' t).div_const 2).exp
  rw [h.deriv]; ring

theorem deriv_expCut_bdd (B : ℝ) (hB : 0 ≤ B) : ∃ L, ∀ t, |deriv (expCut B hB) t| ≤ L := by
  have hc : HasCompactSupport (expCut B hB) :=
    (ContDiffBump.hasCompactSupport _).mul_right
  obtain ⟨L, hL⟩ := hc.deriv.exists_bound_of_continuous
    ((contDiff_expCut B hB).continuous_deriv (by simp))
  exact ⟨L, fun t => by rw [← Real.norm_eq_abs]; exact hL t⟩

/-- `√Z exp(Φ/2)` has weak gradient `√Z exp(Φ/2) ∇Φ / 2`. -/
theorem isWeakGrad_expPhi (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hs : IsSmoothT ρ)
    (hpos : ∀ x, 0 < ρ x) (c : ℝ) :
    IsWeakGrad (fun y => c * Real.exp (PhiF V W ρ N y / 2))
      (fun y p => c * (Real.exp (PhiF V W ρ N y / 2) / 2 * gPhi V W ρ N y p)) := by
  have hΦ := isWeakGrad_PhiF (N := N) hyp hs hpos
  obtain ⟨B, hB⟩ := PhiF_bdd (N := N) hyp hs hpos
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  obtain ⟨Cg, hCg⟩ := gPhi_bdd (N := N) hyp hs hpos
  have iΦ : Integrable (PhiF V W ρ N) volume :=
    Integrable.of_bound hΦ.aestronglyMeasurable_fun B (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hB y)
  have igΦ : ∀ p, Integrable (fun y => gPhi V W ρ N y p) volume := fun p =>
    Integrable.of_bound (hΦ.aestronglyMeasurable_grad p) Cg (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hCg y p)
  obtain ⟨L, hL⟩ := deriv_expCut_bdd B hB0
  have h := isWeakGrad_comp hΦ iΦ igΦ ((contDiff_expCut B hB0).of_le (by simp)) hL
  have e1 : (fun y => expCut B hB0 (PhiF V W ρ N y)) = fun y => Real.exp (PhiF V W ρ N y / 2) :=
    funext fun y => expCut_eq hB0 (hB y)
  have e2 : (fun y p => deriv (expCut B hB0) (PhiF V W ρ N y) * gPhi V W ρ N y p) =
      fun y p => Real.exp (PhiF V W ρ N y / 2) / 2 * gPhi V W ρ N y p :=
    funext fun y => funext fun p => by rw [deriv_expCut hB0 (hB y)]
  rw [e1, e2] at h
  exact h.cmul c

end Phi

end SharpLSI
