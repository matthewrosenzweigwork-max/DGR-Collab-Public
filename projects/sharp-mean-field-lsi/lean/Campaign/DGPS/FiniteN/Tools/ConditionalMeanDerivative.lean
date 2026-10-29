import DGPS.FiniteN.Tools.Hubbard
import DGPS.FiniteN.Tools.BoundedComparison
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DGPS.FiniteN.Tools.ConditionalMeanDerivative

variable {k : ℕ}

/-- The continuous linear functional `v ↦ ∑ⱼ aⱼ vⱼ` on `ℝ^k`. -/
noncomputable def lin (a : Fin k → ℝ) : (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ j, a j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) j

theorem lin_apply (a v : Fin k → ℝ) : lin a v = ∑ j, a j * v j := by
  simp [lin]

section Param

variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [IsFiniteMeasure ν]

/-- The tilted integral `A(w) = ∫ g e^{w·S - V} dν`. -/
noncomputable def tilt (g V : Y → ℝ) (S : Y → Fin k → ℝ) (w : Fin k → ℝ) : ℝ :=
  ∫ y, g y * Real.exp (w ⬝ᵥ S y - V y) ∂ν

theorem norm_lin_le (a : Fin k → ℝ) {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ j, |a j| ≤ c) :
    ‖lin a‖ ≤ k * c := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [lin_apply, Real.norm_eq_abs]
  calc |∑ j, a j * v j| ≤ ∑ j, |a j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin k, c * ‖v‖ := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul (hc j) (by simpa using norm_le_pi_norm v j) (abs_nonneg _) hc0
    _ = k * c * ‖v‖ := by simp [mul_assoc]

theorem abs_dot_le {w s : Fin k → ℝ} {r c : ℝ} (hw : ∀ j, |w j| ≤ r) (hs : ∀ j, |s j| ≤ c)
    (hr : 0 ≤ r) : w ⬝ᵥ s ≤ k * r * c := by
  have hc0 : 0 ≤ c ∨ k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact Or.inr h
    · exact Or.inl ((abs_nonneg _).trans (hs ⟨0, h⟩))
  calc w ⬝ᵥ s ≤ ∑ j, |w j * s j| := by
        unfold dotProduct; exact Finset.sum_le_sum fun j _ => le_abs_self _
    _ ≤ ∑ _j : Fin k, r * c := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]; exact mul_le_mul (hw j) (hs j) (abs_nonneg _) hr
    _ = k * r * c := by simp [mul_assoc]

theorem hasFDerivAt_tilt {g V : Y → ℝ} {S : Y → Fin k → ℝ} (hg : Measurable g)
    (hV : Measurable V) (hS : Measurable S) {B c u : ℝ} (hB0 : 0 ≤ B) (hc0 : 0 ≤ c)
    (hB : ∀ y, |g y| ≤ B)
    (hc : ∀ y j, |S y j| ≤ c) (hu : ∀ y, -u ≤ V y) (w0 : Fin k → ℝ) :
    HasFDerivAt (tilt (ν := ν) g V S) (lin fun j => tilt (ν := ν) (fun y => g y * S y j) V S w0) w0 := by
  have hSj : ∀ j, Measurable fun y => S y j := fun j => (measurable_pi_apply j).comp hS
  have hmeasE : ∀ w : Fin k → ℝ, Measurable fun y => Real.exp (w ⬝ᵥ S y - V y) := by
    intro w
    refine Real.measurable_exp.comp ((Finset.measurable_sum _ fun j _ => ?_).sub hV)
    exact measurable_const.mul (hSj j)
  set r : ℝ := ‖w0‖ + 1 with hr
  have hr0 : 0 ≤ r := by positivity
  set bound : ℝ := B * Real.exp (k * r * c + u) * (k * c) with hbound
  have hbound0 : 0 ≤ bound := by positivity
  let F : (Fin k → ℝ) → Y → ℝ := fun w y => g y * Real.exp (w ⬝ᵥ S y - V y)
  let F' : (Fin k → ℝ) → Y → (Fin k → ℝ) →L[ℝ] ℝ :=
    fun w y => (g y * Real.exp (w ⬝ᵥ S y - V y)) • lin (S y)
  have hexp : ∀ w ∈ Metric.ball w0 1, ∀ y, Real.exp (w ⬝ᵥ S y - V y) ≤ Real.exp (k * r * c + u) := by
    intro w hw y
    refine Real.exp_le_exp.2 ?_
    have hwj : ∀ j, |w j| ≤ r := by
      intro j
      have h1 : ‖w‖ ≤ ‖w0‖ + ‖w - w0‖ := by
        simpa using norm_add_le w0 (w - w0)
      have h2 : ‖w - w0‖ < 1 := by simpa [dist_eq_norm] using hw
      have : |w j| ≤ ‖w‖ := by simpa using norm_le_pi_norm w j
      linarith
    have := abs_dot_le hwj (hc y) hr0
    linarith [hu y]
  have hF'eq : ∀ w, F' w = fun y => ∑ j, (g y * Real.exp (w ⬝ᵥ S y - V y) * S y j) •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) j := by
    intro w; funext y
    simp [F', lin, Finset.smul_sum, smul_smul]
  have hF'm : ∀ w, AEStronglyMeasurable (F' w) ν := by
    intro w
    rw [hF'eq]
    refine Measurable.aestronglyMeasurable ?_
    refine Finset.measurable_sum _ fun j _ => Measurable.smul_const ?_ _
    exact (hg.mul (hmeasE w)).mul (hSj j)
  have hF'bd : ∀ w ∈ Metric.ball w0 1, ∀ y, ‖F' w y‖ ≤ bound := by
    intro w hw y
    have h1 : ‖lin (S y)‖ ≤ k * c := norm_lin_le _ hc0 (hc y)
    calc ‖F' w y‖ = |g y| * Real.exp (w ⬝ᵥ S y - V y) * ‖lin (S y)‖ := by
          simp only [F', norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ B * Real.exp (k * r * c + u) * (k * c) := by
          have hE := Real.exp_pos (w ⬝ᵥ S y - V y)
          gcongr
          · exact hB y
          · exact (Real.exp_le_exp.1 (hexp w hw y))
  have hFint : Integrable (F w0) ν := by
    refine Integrable.mono' (integrable_const (B * Real.exp (k * r * c + u)))
      (hg.mul (hmeasE w0)).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    simp only [F, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hB y) (hexp w0 (Metric.mem_ball_self one_pos) y) (Real.exp_pos _).le hB0
  have hmain : HasFDerivAt (fun w => ∫ y, F w y ∂ν) (∫ y, F' w0 y ∂ν) w0 := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.ball w0 1)
      (bound := fun _ => bound) (Metric.ball_mem_nhds _ one_pos) ?_ hFint (hF'm w0) ?_
      (integrable_const _) ?_
    · exact Filter.Eventually.of_forall fun w => ((hg.mul (hmeasE w))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y w hw => hF'bd w hw y
    · refine Filter.Eventually.of_forall fun y w _ => ?_
      have hl : HasFDerivAt (fun w : Fin k → ℝ => w ⬝ᵥ S y - V y) (lin (S y)) w := by
        have h0 := (lin (S y)).hasFDerivAt (x := w)
        have h1 := h0.sub_const (V y)
        convert h1 using 1
        funext w'
        simp [lin_apply, dotProduct, mul_comm]
      have := (hl.exp).const_mul (g y)
      convert this using 1
      simp only [F', smul_smul]
  have hint' : Integrable (F' w0) ν :=
    Integrable.mono' (integrable_const bound) (hF'm w0)
      (Filter.Eventually.of_forall fun y => hF'bd w0 (Metric.mem_ball_self one_pos) y)
  have hder : ∫ y, F' w0 y ∂ν = lin fun j => tilt (ν := ν) (fun y => g y * S y j) V S w0 := by
    ext v
    rw [ContinuousLinearMap.integral_apply hint', lin_apply]
    have hterm : ∀ j, Integrable (fun y => g y * S y j * Real.exp (w0 ⬝ᵥ S y - V y)) ν := by
      intro j
      refine Integrable.mono' (integrable_const (B * c * Real.exp (k * r * c + u)))
        (((hg.mul (hSj j)).mul (hmeasE w0)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun y => ?_)
      simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (mul_le_mul (hB y) (hc y j) (abs_nonneg _) hB0)
        (hexp w0 (Metric.mem_ball_self one_pos) y) (Real.exp_pos _).le (by positivity)
    have : ∀ y, F' w0 y v = ∑ j, g y * S y j * Real.exp (w0 ⬝ᵥ S y - V y) * v j := by
      intro y
      simp only [F', smul_apply, lin_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [this]
    rw [integral_finsetSum _ fun j _ => (hterm j).mul_const _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const]
    rfl
  rw [hder] at hmain
  exact hmain

end Param

open DGPS.FiniteN.Tools.Hubbard

section Particle

variable {M : Type*} [MeasurableSpace M] {m : Measure M} {U : M → ℝ} {φ : M → Fin k → ℝ}

/-- The conditional particle law `q_w^{⊗N}`. -/
noncomputable def condLaw (U : M → ℝ) (φ : M → Fin k → ℝ) (m : Measure M) (N : ℕ+)
    (w : Fin k → ℝ) : Measure (Fin N → M) :=
  Measure.pi fun _ : Fin N => siteLaw U φ m w

/-- The particle Hamiltonian part `∑ᵢ U(xᵢ)`. -/
noncomputable def potSum (U : M → ℝ) {N : ℕ+} (x : Fin N → M) : ℝ := ∑ i, U (x i)

theorem condLaw_eq [IsFiniteMeasure m] (hyp : HubbardHyp m U φ) (N : ℕ+) (w : Fin k → ℝ) :
    condLaw U φ m N w = (Measure.pi fun _ : Fin N => m).withDensity fun x =>
      ENNReal.ofReal (Real.exp (w ⬝ᵥ fieldSum φ x - potSum U x) /
        auxPartition U φ m w ^ (N : ℕ)) := by
  have hz := auxPartition_pos hyp (m := m) w
  unfold condLaw siteLaw
  rw [pi_withDensity_ofReal (siteDensity U φ m w)
    ((integrable_expTerm hyp w).div_const _) (fun x => div_nonneg (expTerm_pos w x).le hz.le)]
  congr 1
  funext x
  congr 1
  unfold siteDensity potSum
  rw [exp_field_eq_prod, Finset.prod_div_distrib]
  simp

theorem integral_condLaw [IsFiniteMeasure m] (hyp : HubbardHyp m U φ) (N : ℕ+) (w : Fin k → ℝ)
    (h : (Fin N → M) → ℝ) :
    ∫ x, h x ∂condLaw U φ m N w =
      tilt (ν := Measure.pi fun _ : Fin N => m) h (potSum U) (fieldSum φ) w /
        auxPartition U φ m w ^ (N : ℕ) := by
  have hz := auxPartition_pos hyp (m := m) w
  have hmeas : Measurable fun x : Fin N → M => ENNReal.ofReal (Real.exp (w ⬝ᵥ fieldSum φ x - potSum U x) /
        auxPartition U φ m w ^ (N : ℕ)) := by
    refine ENNReal.measurable_ofReal.comp (Measurable.div_const ?_ _)
    refine Real.measurable_exp.comp (Measurable.sub ?_ ?_)
    · unfold dotProduct
      refine Finset.measurable_sum _ fun i _ => measurable_const.mul ?_
      exact (measurable_pi_apply i).comp (measurable_fieldSum hyp)
    · unfold potSum
      exact Finset.measurable_sum _ fun i _ => hyp.U_meas.comp (measurable_pi_apply i)
  rw [condLaw_eq hyp, integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold tilt
  rw [← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le (pow_pos hz _).le)]
  ring

theorem tilt_one [IsFiniteMeasure m] (hyp : HubbardHyp m U φ) (N : ℕ+) (w : Fin k → ℝ) :
    tilt (ν := Measure.pi fun _ : Fin N => m) (fun _ => (1 : ℝ)) (potSum U) (fieldSum φ) w =
      auxPartition U φ m w ^ (N : ℕ) := by
  have hz := auxPartition_pos hyp (m := m) w
  have := isProbabilityMeasure_siteLaw hyp (m := m) w
  have : IsProbabilityMeasure (condLaw U φ m N w) := by
    unfold condLaw; infer_instance
  have h1 := integral_condLaw hyp N w (fun _ => (1 : ℝ))
  rw [integral_const, probReal_univ, one_smul] at h1
  have hp : 0 < auxPartition U φ m w ^ (N : ℕ) := pow_pos hz _
  field_simp at h1
  linarith

/-- The conditional particle mean `M_f(w) = q_w^{⊗N}(f)`. -/
noncomputable def condMean (U : M → ℝ) (φ : M → Fin k → ℝ) (m : Measure M) (N : ℕ+)
    (f : (Fin N → M) → ℝ) (w : Fin k → ℝ) : ℝ :=
  ∫ x, f x ∂condLaw U φ m N w

/-- The `j`-th component of `Cov_{q_w^{⊗N}}(f, ∑ᵢ φ(xᵢ))`. -/
noncomputable def condGrad (U : M → ℝ) (φ : M → Fin k → ℝ) (m : Measure M) (N : ℕ+)
    (f : (Fin N → M) → ℝ) (w : Fin k → ℝ) (j : Fin k) : ℝ :=
  cov[f, fun x => fieldSum φ x j; condLaw U φ m N w]

theorem isProbabilityMeasure_condLaw [IsFiniteMeasure m] (hyp : HubbardHyp m U φ) (N : ℕ+)
    (w : Fin k → ℝ) : IsProbabilityMeasure (condLaw U φ m N w) := by
  have := isProbabilityMeasure_siteLaw hyp (m := m) w
  unfold condLaw; infer_instance

theorem measurable_fieldSum_apply (hyp : HubbardHyp m U φ) {N : ℕ+} (j : Fin k) :
    Measurable fun x : Fin N → M => fieldSum φ x j :=
  (measurable_pi_apply j).comp (measurable_fieldSum hyp)

theorem abs_fieldSum_le (hyp : HubbardHyp m U φ) {N : ℕ+} :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (x : Fin N → M) j, |fieldSum φ x j| ≤ c := by
  obtain ⟨L, hL⟩ := hyp.φ_bound
  refine ⟨N * max L 0, by positivity, fun x j => ?_⟩
  unfold fieldSum
  rw [Finset.sum_apply]
  calc |∑ i, φ (x i) j| ≤ ∑ i, |φ (x i) j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, max L 0 := Finset.sum_le_sum fun i _ => by
        have : |φ (x i) j| ≤ ‖φ (x i)‖ := by simpa using norm_le_pi_norm (φ (x i)) j
        exact (this.trans (hL _)).trans (le_max_left _ _)
    _ = N * max L 0 := by simp

theorem memLp_condLaw [IsFiniteMeasure m] (hyp : HubbardHyp m U φ) {N : ℕ+} (w : Fin k → ℝ)
    {g : (Fin N → M) → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    MemLp g 2 (condLaw U φ m N w) := by
  have := isProbabilityMeasure_condLaw hyp N w
  exact MemLp.of_bound hg.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)

theorem condGrad_eq [IsFiniteMeasure m] (hyp : HubbardHyp m U φ) {N : ℕ+}
    {f : (Fin N → M) → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) (w : Fin k → ℝ)
    (j : Fin k) :
    condGrad U φ m N f w j =
      tilt (ν := Measure.pi fun _ : Fin N => m) (fun y => f y * fieldSum φ y j) (potSum U)
          (fieldSum φ) w / auxPartition U φ m w ^ (N : ℕ) -
        (tilt (ν := Measure.pi fun _ : Fin N => m) f (potSum U) (fieldSum φ) w /
          auxPartition U φ m w ^ (N : ℕ)) *
        (tilt (ν := Measure.pi fun _ : Fin N => m) (fun y => fieldSum φ y j) (potSum U)
          (fieldSum φ) w / auxPartition U φ m w ^ (N : ℕ)) := by
  have := isProbabilityMeasure_condLaw hyp N w
  obtain ⟨c, hc0, hc⟩ := abs_fieldSum_le hyp (N := N)
  have h1 := memLp_condLaw hyp w hf hB
  have h2 := memLp_condLaw hyp w (measurable_fieldSum_apply hyp (N := N) j) (fun x => hc x j)
  unfold condGrad
  rw [covariance_eq_sub h1 h2]
  simp only [Pi.mul_apply]
  rw [integral_condLaw hyp N w, integral_condLaw hyp N w f,
    integral_condLaw hyp N w (fun y => fieldSum φ y j)]

theorem hasFDerivAt_condMean [IsFiniteMeasure m] (hyp : HubbardHyp m U φ) {N : ℕ+}
    {f : (Fin N → M) → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) (w : Fin k → ℝ) :
    HasFDerivAt (condMean U φ m N f) (lin (condGrad U φ m N f w)) w := by
  obtain ⟨c, hc0, hc⟩ := abs_fieldSum_le hyp (N := N)
  obtain ⟨c0, hc0'⟩ := hyp.U_lower
  have hVm : Measurable (potSum U : (Fin N → M) → ℝ) :=
    Finset.measurable_sum _ fun i _ => hyp.U_meas.comp (measurable_pi_apply i)
  have hu : ∀ x : Fin N → M, -(N * |c0|) ≤ potSum U x := by
    intro x
    unfold potSum
    have : ∀ i : Fin N, -|c0| ≤ U (x i) := fun i => by
      linarith [hc0' (x i), neg_abs_le c0]
    calc -(N * |c0|) = ∑ _i : Fin N, -|c0| := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => this i
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hA := hasFDerivAt_tilt (ν := Measure.pi fun _ : Fin N => m) hf hVm
    (measurable_fieldSum hyp) hB0 hc0 (fun y => (hB y).trans (le_max_left _ _)) hc hu w
  have hA1 := hasFDerivAt_tilt (ν := Measure.pi fun _ : Fin N => m)
    (g := fun _ => (1 : ℝ)) measurable_const hVm (measurable_fieldSum hyp) zero_le_one hc0
    (fun y => by simp) hc hu w
  set T1 := tilt (ν := Measure.pi fun _ : Fin N => m) (fun _ => (1 : ℝ)) (potSum U) (fieldSum φ) w
    with hT1
  have hT1pos : 0 < T1 := by
    rw [hT1, tilt_one hyp]; exact pow_pos (auxPartition_pos hyp w) _
  have hinv := (hasDerivAt_inv hT1pos.ne').comp_hasFDerivAt w hA1
  have hprod := hA.mul hinv
  have hfun : condMean U φ m N f = (tilt (ν := Measure.pi fun _ : Fin N => m) f (potSum U)
      (fieldSum φ)) * (Inv.inv ∘ tilt (ν := Measure.pi fun _ : Fin N => m) (fun _ => (1 : ℝ))
      (potSum U) (fieldSum φ)) := by
    funext w'
    simp only [condMean, integral_condLaw hyp N w', Pi.mul_apply, Function.comp, tilt_one hyp,
      div_eq_mul_inv]
  rw [hfun]
  convert hprod using 1
  ext v
  have hT1e : T1 = auxPartition U φ m w ^ (N : ℕ) := tilt_one hyp N w
  simp only [add_apply, smul_apply, lin_apply, smul_eq_mul, Function.comp,
    one_mul, condGrad_eq hyp hf hB w, ← hT1, hT1e, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := (pow_pos (auxPartition_pos hyp (m := m) w) (N : ℕ)).ne'
  rw [tilt_one hyp] at *
  field_simp
  ring

/-- The variance of the feature sum `g · ∑ᵢ φ(xᵢ)` is at most `N L² |g|²` (FIN004). -/
theorem variance_feature_sum_le [IsFiniteMeasure m] (hyp : HubbardHyp m U φ) {N : ℕ+}
    (w : Fin k → ℝ) (g : Fin k → ℝ) {L : ℝ} (hL' : ∀ x, √(∑ j, φ x j ^ 2) ≤ L) :
    Var[fun x : Fin N → M => ∑ j, g j * fieldSum φ x j; condLaw U φ m N w] ≤
      N * L ^ 2 * ∑ j, g j ^ 2 := by
  have hprob := isProbabilityMeasure_siteLaw hyp (m := m) w
  have hP := isProbabilityMeasure_condLaw hyp N w
  set G : ℝ := ∑ j, g j ^ 2 with hG
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun j _ => sq_nonneg _
  let a : M → ℝ := fun y => ∑ j, g j * φ y j
  have ha : Measurable a := Finset.measurable_sum _ fun j _ =>
    measurable_const.mul ((measurable_pi_apply j).comp hyp.φ_meas)
  let F : M → EuclideanSpace ℝ (Fin 1) := fun y => WithLp.toLp 2 (fun _ => a y)
  have hF : Measurable F := by
    unfold F
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).measurable.comp
      (Measurable.of_eval fun _ => ha)
  have hpt : ∀ y : M, |a y| ≤ √G * L := by
    intro y
    have hs := hL' y
    have hL0 : 0 ≤ L := (Real.sqrt_nonneg _).trans hs
    have h : ∑ j, φ y j ^ 2 ≤ L ^ 2 := (Real.sqrt_le_iff.1 hs).2
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g (fun j => φ y j)
    have h2 : a y ^ 2 ≤ (√G * L) ^ 2 := by
      calc a y ^ 2 ≤ G * ∑ j, φ y j ^ 2 := hcs
        _ ≤ G * L ^ 2 := mul_le_mul_of_nonneg_left h hG0
        _ = (√G * L) ^ 2 := by rw [mul_pow, Real.sq_sqrt hG0]
    exact abs_le.2 (abs_le_of_sq_le_sq' h2 (by positivity))
  have hψ : ∀ (i : Fin N) (x : Fin N → M), ‖F (x i)‖ ≤ √G * L := by
    intro i x
    simpa [F, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs] using hpt (x i)
  have hind : iIndepFun (fun (i : Fin N) (x : Fin N → M) => F (x i)) (condLaw U φ m N w) :=
    iIndepFun_pi (μ := fun _ => siteLaw U φ m w) (X := fun _ => F) (fun _ => hF.aemeasurable)
  have hbd := (DGPS.FiniteN.bounded_comparison_tensorization_and_covariance).2.2
    (μ := condLaw U φ m N w) (φ := fun (i : Fin N) (x : Fin N → M) => F (x i))
    (fun i => hF.comp (measurable_pi_apply i)) hind hψ
  have hfun : (fun x : Fin N → M => ∑ j, g j * fieldSum φ x j) =
      fun x => (∑ i, F (x i)) 0 := by
    funext x
    simp only [F, a, fieldSum, WithLp.ofLp_sum, Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hvar : Var[fun x : Fin N → M => ∑ j, g j * fieldSum φ x j; condLaw U φ m N w] ≤
      N * (√G * L) ^ 2 := by
    refine le_trans (le_of_eq ?_) hbd
    unfold Tools.BoundedComparison.traceCov
    rw [hfun]
    simp
  calc _ ≤ N * (√G * L) ^ 2 := hvar
    _ = N * L ^ 2 * G := by rw [mul_pow, Real.sq_sqrt hG0]; ring

theorem condGrad_sq_le [IsFiniteMeasure m] (hyp : HubbardHyp m U φ) {N : ℕ+}
    {f : (Fin N → M) → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) (w : Fin k → ℝ)
    {L : ℝ} (hL : ∀ x, √(∑ j, φ x j ^ 2) ≤ L) :
    ∑ j, condGrad U φ m N f w j ^ 2 ≤ N * L ^ 2 * Var[f; condLaw U φ m N w] := by
  have hP := isProbabilityMeasure_condLaw hyp N w
  set g : Fin k → ℝ := condGrad U φ m N f w with hg
  set G : ℝ := ∑ j, g j ^ 2 with hG
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun j _ => sq_nonneg _
  obtain ⟨c, hc0, hc⟩ := abs_fieldSum_le hyp (N := N)
  have hS : ∀ j, MemLp (fun x : Fin N → M => fieldSum φ x j) 2 (condLaw U φ m N w) := fun j =>
    memLp_condLaw hyp w (measurable_fieldSum_apply hyp j) (fun x => hc x j)
  have hf2 : MemLp f 2 (condLaw U φ m N w) := memLp_condLaw hyp w hf hB
  have hT : MemLp (fun x : Fin N → M => ∑ j, g j * fieldSum φ x j) 2 (condLaw U φ m N w) := by
    exact memLp_finsetSum (p := 2) (μ := condLaw U φ m N w) Finset.univ
      (f := fun j (x : Fin N → M) => g j * fieldSum φ x j) (fun j _ => (hS j).const_mul (g j))
  have hcov : cov[f, fun x : Fin N → M => ∑ j, g j * fieldSum φ x j; condLaw U φ m N w] = G := by
    rw [covariance_fun_sum_right (fun j => (hS j).const_mul (g j)) hf2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [covariance_const_mul_right]
    simp [hg, condGrad, sq]
  have hvarT := variance_feature_sum_le (N := N) hyp w g hL
  have hquad : ∀ t : ℝ, 0 ≤ Var[fun x : Fin N → M => ∑ j, g j * fieldSum φ x j;
        condLaw U φ m N w] * (t * t) + (-2 * G) * t + Var[f; condLaw U φ m N w] := by
    intro t
    have h1 := variance_nonneg (f - fun x : Fin N → M => t * ∑ j, g j * fieldSum φ x j)
      (condLaw U φ m N w)
    rw [variance_sub hf2 (hT.const_mul t), covariance_const_mul_right, hcov,
      variance_const_mul] at h1
    nlinarith [h1]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  have hVf := variance_nonneg f (condLaw U φ m N w)
  by_cases hG' : G = 0
  · rw [hG']; positivity
  · have hGp : 0 < G := lt_of_le_of_ne hG0 (Ne.symm hG')
    have h3 : G * G ≤ (N * L ^ 2 * G) * Var[f; condLaw U φ m N w] := by
      have h4 : G * G ≤ Var[fun x : Fin N → M => ∑ j, g j * fieldSum φ x j;
        condLaw U φ m N w] * Var[f; condLaw U φ m N w] := by nlinarith [hd]
      exact h4.trans (mul_le_mul_of_nonneg_right hvarT hVf)
    nlinarith [h3]

theorem conditional_mean_derivative [IsFiniteMeasure m]
    (hyp : HubbardHyp m U φ) {N : ℕ+} {f : (Fin N → M) → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) :
    (∀ w, HasFDerivAt (condMean U φ m N f) (lin (condGrad U φ m N f w)) w) ∧
    ∀ {L : ℝ}, (∀ x, √(∑ j, φ x j ^ 2) ≤ L) → ∀ w,
      ∑ j, condGrad U φ m N f w j ^ 2 ≤ N * L ^ 2 * Var[f; condLaw U φ m N w] :=
  ⟨fun w => hasFDerivAt_condMean hyp hf hB w, fun hL w => condGrad_sq_le hyp hf hB w hL⟩

end Particle

end DGPS.FiniteN.Tools.ConditionalMeanDerivative

namespace DGPS.FiniteN

open Tools.ConditionalMeanDerivative Tools.Hubbard

/-- **FIN012: derivative of the conditional particle mean.**  Let `m` be a finite measure on `M`,
`U` a measurable potential bounded below and `φ : M → ℝ^k` a measurable bounded feature (`hyp`), and
`q_w ∝ exp(w·φ - U) dm` the conditional site law of the Hubbard identity (FIN010, `siteLaw`).  For
a bounded measurable particle observable `f` on `M^N`, the conditional mean
`M_f(w) = q_w^{⊗N}(f)` (`condMean`) is Fréchet differentiable at every `w`, with gradient
`∇M_f(w) = Cov_{q_w^{⊗N}}(f, ∑ᵢ φ(xᵢ))` (`condGrad`, componentwise covariances, `lin` the
associated linear functional); and if `|φ| ≤ L` (Euclidean norm) then
`|∇M_f(w)|² ≤ N L² Var_{q_w^{⊗N}}(f)`, using the covariance trace bound of FIN004. -/
theorem derivative_of_conditional_particle_mean {M : Type*} [MeasurableSpace M] {k : ℕ}
    {m : Measure M} [IsFiniteMeasure m] {U : M → ℝ} {φ : M → Fin k → ℝ}
    (hyp : HubbardHyp m U φ) (N : ℕ+) {f : (Fin N → M) → ℝ} (hf : Measurable f)
    (hfb : ∃ B : ℝ, ∀ x, |f x| ≤ B) :
    (∀ w : Fin k → ℝ, IsProbabilityMeasure (condLaw U φ m N w) ∧
      HasFDerivAt (condMean U φ m N f) (lin (condGrad U φ m N f w)) w) ∧
    ∀ {L : ℝ}, (∀ x, √(∑ j, φ x j ^ 2) ≤ L) → ∀ w : Fin k → ℝ,
      ∑ j, condGrad U φ m N f w j ^ 2 ≤
        (N : ℝ) * L ^ 2 * ProbabilityTheory.variance f (condLaw U φ m N w) := by
  obtain ⟨B, hB⟩ := hfb
  obtain ⟨h1, h2⟩ := conditional_mean_derivative hyp hf hB
  exact ⟨fun w => ⟨isProbabilityMeasure_condLaw hyp N w, h1 w⟩, fun hL w => h2 hL w⟩

end DGPS.FiniteN
