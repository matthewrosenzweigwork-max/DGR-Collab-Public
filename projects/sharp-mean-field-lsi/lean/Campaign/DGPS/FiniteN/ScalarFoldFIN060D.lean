import DGPS.FiniteN.Tools.AuxiliaryTransferTorus
import DGPS.FiniteN.Tools.ConditionalMeanDerivative

/-!
# FIN060 (part D): smoothness of the conditional mean

For a bounded measurable test function `f`, the conditional particle mean `w ↦ q_w^{⊗N}(f)` is
`C^∞`.  This is used to apply the auxiliary Poincare inequality, proved for smooth bounded
functions with bounded gradient, to the conditional mean in the FIN013 transfer.
-/

open MeasureTheory ProbabilityTheory
open scoped ContDiff ENNReal

namespace DGPS.FiniteN.ScalarFoldFIN060

open DGPS.FiniteN.Tools.ConditionalMeanDerivative DGPS.FiniteN.Tools.Hubbard
  DGPS.FiniteN.Tools.GaussianCoupling DGPS.FiniteN.Tools.BoundedComparison
  DGPS.FiniteN.Tools.AuxiliaryTransfer

/-- The continuous linear map `a ↦ lin a`. -/
noncomputable def linCLM_FIN060 (k : ℕ) : (Fin k → ℝ) →L[ℝ] ((Fin k → ℝ) →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => lin a
      map_add' := fun a b => by
        ext v
        simp [lin_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r a => by
        ext v
        simp [lin_apply, Finset.mul_sum, mul_assoc] }

theorem linCLM_apply_FIN060 {k : ℕ} (a : Fin k → ℝ) : linCLM_FIN060 k a = lin a := rfl

theorem contDiff_tilt_FIN060 {k : ℕ} {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    [IsFiniteMeasure ν] {V : Y → ℝ} {S : Y → Fin k → ℝ} (hV : Measurable V) (hS : Measurable S)
    {c u : ℝ} (hc0 : 0 ≤ c) (hc : ∀ y j, |S y j| ≤ c) (hu : ∀ y, -u ≤ V y) (n : ℕ) :
    ∀ g : Y → ℝ, Measurable g → (∃ B : ℝ, ∀ y, |g y| ≤ B) →
      ContDiff ℝ n (tilt (ν := ν) g V S) := by
  induction n with
  | zero =>
    intro g hg ⟨B, hB⟩
    have hB0 : 0 ≤ max B 0 := le_max_right _ _
    refine contDiff_zero.2 ?_
    refine continuous_iff_continuousAt.2 fun w => ?_
    exact (hasFDerivAt_tilt (ν := ν) hg hV hS hB0 hc0 (fun y => (hB y).trans (le_max_left _ _))
      hc hu w).continuousAt
  | succ n ih =>
    intro g hg ⟨B, hB⟩
    have hB0 : 0 ≤ max B 0 := le_max_right _ _
    have hcomp : ContDiff ℝ n (fun w => fun j : Fin k => tilt (ν := ν) (fun y => g y * S y j) V S w) := by
      refine contDiff_pi.2 fun j => ih _ ?_ ⟨max B 0 * c, fun y => ?_⟩
      · exact hg.mul ((measurable_pi_apply j).comp hS)
      · rw [abs_mul]
        exact mul_le_mul ((hB y).trans (le_max_left _ _)) (hc y j) (abs_nonneg _) hB0
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun w => linCLM_FIN060 k (fun j => tilt (ν := ν) (fun y => g y * S y j) V S w),
      (linCLM_FIN060 k).contDiff.comp hcomp, fun w => ?_⟩
    exact hasFDerivAt_tilt (ν := ν) hg hV hS hB0 hc0 (fun y => (hB y).trans (le_max_left _ _))
      hc hu w

section Transfer

variable {k : ℕ} {M : Type*} [MeasurableSpace M] {m : Measure M} [IsFiniteMeasure m] {U : M → ℝ}
  {φ : M → Fin k → ℝ}

/-- The tilted integral of a bounded measurable function against the Hubbard data is `C^∞`. -/
theorem contDiff_tilt_hubbard_FIN060 (hyp : HubbardHyp m U φ) {N : ℕ+} {g : (Fin N → M) → ℝ}
    (hg : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    ContDiff ℝ ∞ (tilt (ν := Measure.pi fun _ : Fin N => m) g (potSum U) (fieldSum φ)) := by
  obtain ⟨c, hc0, hc⟩ := abs_fieldSum_le hyp (N := N)
  obtain ⟨c0, hc0'⟩ := hyp.U_lower
  have hVm : Measurable (potSum U : (Fin N → M) → ℝ) :=
    Finset.measurable_sum _ fun i _ => hyp.U_meas.comp (measurable_pi_apply i)
  have hu : ∀ x : (Fin N → M), -(N * |c0|) ≤ potSum U x := by
    intro x
    unfold potSum
    have : ∀ i : Fin N, -|c0| ≤ U (x i) := fun i => by
      linarith [hc0' (x i), neg_abs_le c0]
    calc -(N * |c0|) = ∑ _i : Fin N, -|c0| := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => this i
  exact contDiff_infty.2 fun n => contDiff_tilt_FIN060 hVm (measurable_fieldSum hyp) hc0 hc hu n
    g hg ⟨B, hB⟩

/-- The conditional particle mean of a bounded measurable function is `C^∞` in `w`. -/
theorem contDiff_condMean_FIN060 (hyp : HubbardHyp m U φ) {N : ℕ+} {f : (Fin N → M) → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    ContDiff ℝ ∞ (condMean U φ m N f) := by
  have hnum := contDiff_tilt_hubbard_FIN060 (m := m) hyp hf hB
  have hden := contDiff_tilt_hubbard_FIN060 (m := m) hyp (N := N) (g := fun _ => (1 : ℝ))
    measurable_const (B := 1) (fun _ => by simp)
  have hfun : condMean U φ m N f = fun w =>
      tilt (ν := Measure.pi fun _ : Fin N => m) f (potSum U) (fieldSum φ) w /
        tilt (ν := Measure.pi fun _ : Fin N => m) (fun _ => (1 : ℝ)) (potSum U) (fieldSum φ) w := by
    funext w
    simp only [condMean, integral_condLaw hyp N w, tilt_one hyp]
  rw [hfun]
  refine hnum.div hden fun w => ?_
  rw [tilt_one hyp]
  exact (pow_pos (auxPartition_pos hyp (m := m) w) _).ne'

variable {D : Matrix (Fin k) (Fin k) ℝ} (hyp : HubbardHyp m U φ)
include hyp

/-- The auxiliary test class used in FIN060: smooth bounded functions with bounded Euclidean
gradient. -/
def AuxSmoothFIN060 {k : ℕ} (g : (Fin k → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ∞ g ∧ (∃ B : ℝ, ∀ w, |g w| ≤ B) ∧
    ∃ B' : ℝ, ∀ w, ∑ j, (fderiv ℝ g w (Pi.single j 1)) ^ 2 ≤ B'

/-- **Auxiliary-to-particle Poincare transfer with smooth auxiliary tests** (a copy of
`poincare_transfer` whose auxiliary hypothesis is only needed for `AuxSmoothFIN060`). -/
theorem poincare_transfer_FIN060 (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) {lam : ℝ} (hlam : 0 < lam)
    (haux : PoincareAt (auxLaw D h U φ m N) AuxSmoothFIN060 auxGradSq lam⁻¹)
    {Sm : ((Fin N → M) → ℝ) → Prop} {Γ : ((Fin N → M) → ℝ) → (Fin N → M) → ℝ≥0∞}
    (hSm : ∀ f, Sm f → Measurable f ∧ ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hΓ : ∀ f, Sm f → Measurable (Γ f))
    {C : (Fin k → ℝ) → ℝ} (hC : Measurable C)
    (hcond : ∀ w, PoincareAt (condLaw U φ m N w) Sm Γ (C w))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, ∫⁻ w, ENNReal.ofReal (C w) ∂(gaussLaw D N (posteriorCenter D h φ N x)) ≤
      ENNReal.ofReal K)
    {L : ℝ} (hL : ∀ x, √(∑ j, φ x j ^ 2) ≤ L) :
    PoincareAt (hubbardParticleLaw D h U φ m N) Sm Γ (K * (1 + N * L ^ 2 / lam)) := by
  intro f hfS
  obtain ⟨hf, B, hB⟩ := hSm f hfS
  have hΓf := hΓ f hfS
  have := isProbabilityMeasure_auxLaw hyp hD h N
  have := isProbabilityMeasure_particleLaw hyp hD h N
  set P := hubbardParticleLaw D h U φ m N with hP
  set η := auxLaw D h U φ m N with hη
  set a := condMean U φ m N f with ha
  have hder : ∀ w, HasFDerivAt a (lin (condGrad U φ m N f w)) w :=
    fun w => hasFDerivAt_condMean hyp hf hB w
  have ha_bdd : ∃ B' : ℝ, ∀ w, |a w| ≤ B' := ⟨B, abs_condMean_le hyp N hB⟩
  set T : ℝ≥0∞ := ∫⁻ w, ENNReal.ofReal (C w) * ∫⁻ x, Γ f x ∂(condLaw U φ m N w) ∂η with hT
  have hV : ∫⁻ w, ENNReal.ofReal (variance f (condLaw U φ m N w)) ∂η ≤ T :=
    lintegral_mono fun w => by
      have := isProbabilityMeasure_condLaw hyp N w
      have hmem : MemLp f 2 (condLaw U φ m N w) :=
        MemLp.of_bound hf.aestronglyMeasurable B
          (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)
      rw [hmem.ofReal_variance_eq]
      exact hcond w f hfS
  have hgrad : ∫⁻ w, auxGradSq a w ∂η ≤ ENNReal.ofReal (N * L ^ 2) * T := by
    calc ∫⁻ w, auxGradSq a w ∂η
        ≤ ∫⁻ w, ENNReal.ofReal (N * L ^ 2) *
            ENNReal.ofReal (variance f (condLaw U φ m N w)) ∂η := by
          refine lintegral_mono fun w => ?_
          unfold auxGradSq
          have hfd : fderiv ℝ a w = lin (condGrad U φ m N f w) := (hder w).fderiv
          have hs : ∑ j, (fderiv ℝ a w (Pi.single j 1)) ^ 2 =
              ∑ j, condGrad U φ m N f w j ^ 2 := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hfd, lin_apply]
            simp [Pi.single_apply]
          rw [hs, ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal
            (condGrad_sq_le hyp hf hB w hL)
      _ = ENNReal.ofReal (N * L ^ 2) *
            ∫⁻ w, ENNReal.ofReal (variance f (condLaw U φ m N w)) ∂η :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (N * L ^ 2) * T := by gcongr
  have ha_smooth : ContDiff ℝ ∞ a := contDiff_condMean_FIN060 hyp hf hB
  have ha_grad : ∃ B' : ℝ, ∀ w, ∑ j, (fderiv ℝ a w (Pi.single j 1)) ^ 2 ≤ B' := by
    refine ⟨N * L ^ 2 * B ^ 2, fun w => ?_⟩
    have hfd : fderiv ℝ a w = lin (condGrad U φ m N f w) := (hder w).fderiv
    have hs : ∑ j, (fderiv ℝ a w (Pi.single j 1)) ^ 2 =
        ∑ j, condGrad U φ m N f w j ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hfd, lin_apply]
      simp [Pi.single_apply]
    rw [hs]
    have hP := isProbabilityMeasure_condLaw hyp N w
    have hvar : Var[f; condLaw U φ m N w] ≤ B ^ 2 := by
      have h1 := variance_le_sq_of_bounded (μ := condLaw U φ m N w) (a := -B) (b := B) (X := f)
        (Filter.Eventually.of_forall fun x => abs_le.1 (hB x)) hf.aemeasurable
      calc _ ≤ ((B - -B) / 2) ^ 2 := h1
        _ = B ^ 2 := by ring
    exact (condGrad_sq_le hyp hf hB w hL).trans
      (mul_le_mul_of_nonneg_left hvar (by positivity))
  have haux' := haux a ⟨ha_smooth, ha_bdd, ha_grad⟩
  have hsplit := ofReal_variance_split hyp hD h N hf hB
  have hfP : MemLp f 2 P :=
    MemLp.of_bound hf.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)
  have hx : 0 ≤ (N : ℝ) * L ^ 2 / lam := by positivity
  have hstep : evariance f P ≤ ENNReal.ofReal (1 + N * L ^ 2 / lam) * T := by
    calc evariance f P
        = ∫⁻ w, ENNReal.ofReal (variance f (condLaw U φ m N w)) ∂η + evariance a η := by
          rw [← hfP.ofReal_variance_eq]; exact hsplit
      _ ≤ T + ENNReal.ofReal lam⁻¹ * (ENNReal.ofReal (N * L ^ 2) * T) :=
          add_le_add hV (haux'.trans (by gcongr))
      _ = ENNReal.ofReal (1 + N * L ^ 2 / lam) * T := by
          have e : lam⁻¹ * ((N : ℝ) * L ^ 2) = N * L ^ 2 / lam := by
            rw [div_eq_inv_mul]
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hlam.le), e,
            ENNReal.ofReal_add zero_le_one hx, ENNReal.ofReal_one, add_mul, one_mul]
  have hCm : Measurable fun w => ENNReal.ofReal (C w) := ENNReal.measurable_ofReal.comp hC
  have hTle : T ≤ ENNReal.ofReal K * ∫⁻ x, Γ f x ∂P := by
    have hG : Measurable fun z : (Fin k → ℝ) × (Fin N → M) => ENNReal.ofReal (C z.1) * Γ f z.2 :=
      (hCm.comp measurable_fst).mul (hΓf.comp measurable_snd)
    have e1 : T = ∫⁻ z, ENNReal.ofReal (C z.1) * Γ f z.2 ∂(hubbardJoint D h U φ m N) := by
      rw [lintegral_joint_eq hyp hD h N hG]
      refine lintegral_congr fun w => ?_
      exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    rw [e1, lintegral_joint_eq_gauss hyp hD h N hG]
    calc ∫⁻ x, ∫⁻ w, ENNReal.ofReal (C w) * Γ f x
          ∂(gaussLaw D N (posteriorCenter D h φ N x)) ∂P
        = ∫⁻ x, (∫⁻ w, ENNReal.ofReal (C w)
          ∂(gaussLaw D N (posteriorCenter D h φ N x))) * Γ f x ∂P :=
          lintegral_congr fun x => lintegral_mul_const _ hCm
      _ ≤ ∫⁻ x, ENNReal.ofReal K * Γ f x ∂P :=
          lintegral_mono fun x => by gcongr; exact hK x
      _ = ENNReal.ofReal K * ∫⁻ x, Γ f x ∂P := lintegral_const_mul _ hΓf
  calc evariance f P ≤ ENNReal.ofReal (1 + N * L ^ 2 / lam) * T := hstep
    _ ≤ ENNReal.ofReal (1 + N * L ^ 2 / lam) * (ENNReal.ofReal K * ∫⁻ x, Γ f x ∂P) :=
        by gcongr
    _ = ENNReal.ofReal (K * (1 + N * L ^ 2 / lam)) * ∫⁻ x, Γ f x ∂P := by
        rw [ENNReal.ofReal_mul hK0]; ring

end Transfer

end DGPS.FiniteN.ScalarFoldFIN060
