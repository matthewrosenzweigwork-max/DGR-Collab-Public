import DGPS.Lipschitz.HessianKernel
import DGPS.Analysis.ParameterImplicitFunction

open MeasureTheory
open scoped ContDiff RealInnerProductSpace

namespace DGPS.Lipschitz

section NemytskiiLog

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The set of continuous functions `h` with `1 + h > 0` everywhere. -/
def posSet (X : Type*) [TopologicalSpace X] [CompactSpace X] : Set C(X, ℝ) :=
  {h | ∀ x, 0 < 1 + h x}

theorem exists_lower_of_mem_posSet {h : C(X, ℝ)} (hh : h ∈ posSet X) :
    ∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ 1 + h x := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨1, one_pos, fun x => (hX.false x).elim⟩
  · obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
      (f := fun x => 1 + h x) (by fun_prop)
    exact ⟨1 + h x0, hh x0, fun x => hx0 (Set.mem_univ x)⟩

theorem isOpen_posSet : IsOpen (posSet X) := by
  rw [isOpen_iff_mem_nhds]
  intro h hh
  obtain ⟨m, hm, hmx⟩ := exists_lower_of_mem_posSet hh
  rw [Metric.mem_nhds_iff]
  refine ⟨m, hm, fun k hk x => ?_⟩
  have h1 : |k x - h x| ≤ dist k h := by
    have := ContinuousMap.dist_apply_le_dist (f := k) (g := h) x
    rwa [Real.dist_eq] at this
  have h2 : dist k h < m := hk
  have := abs_le.mp h1
  have := hmx x
  linarith [(abs_le.mp h1).1]

open Classical in
/-- The Nemytskii logarithm `h ↦ log (1 + h)`, junk value `0` off the positivity set. -/
noncomputable def nemLog (h : C(X, ℝ)) : C(X, ℝ) :=
  if hp : h ∈ posSet X then
    ⟨fun x => Real.log (1 + h x), by
      refine continuous_iff_continuousAt.2 fun x => ?_
      exact ContinuousAt.comp (g := Real.log) (f := fun x => 1 + h x)
        (Real.continuousAt_log (hp x).ne') (by fun_prop)⟩
  else 0

theorem nemLog_apply {h : C(X, ℝ)} (hh : h ∈ posSet X) (x : X) :
    nemLog h x = Real.log (1 + h x) := by
  simp [nemLog, hh]

/-- `1 + h` is a unit of `C(X,ℝ)` on the positivity set. -/
noncomputable def unitOne {h : C(X, ℝ)} (hh : h ∈ posSet X) : C(X, ℝ)ˣ where
  val := 1 + h
  inv := ⟨fun x => (1 + h x)⁻¹, by
    refine continuous_iff_continuousAt.2 fun x => ?_
    exact ContinuousAt.inv₀ (by fun_prop) (hh x).ne'⟩
  val_inv := by ext x; simp [(hh x).ne']
  inv_val := by ext x; simp [(hh x).ne']

theorem ringInverse_apply {h : C(X, ℝ)} (hh : h ∈ posSet X) (x : X) :
    Ring.inverse (1 + h) x = (1 + h x)⁻¹ := by
  have : (1 + h) = ((unitOne hh : C(X, ℝ)ˣ) : C(X, ℝ)) := rfl
  rw [this, Ring.inverse_unit]
  rfl

theorem abs_log_one_add_sub_le {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |Real.log (1 + s) - s| ≤ 2 * s ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -s) (by rw [abs_neg]; linarith) 1
  simp only [Finset.sum_range_one, abs_neg] at h
  have e : (-s) ^ (0 + 1) / ((0 : ℕ) + 1 : ℝ) + Real.log (1 - -s) = Real.log (1 + s) - s := by
    push_cast; ring_nf
  rw [e] at h
  refine h.trans ?_
  have h1 : |s| ≤ 1 / 2 := hs
  rw [div_le_iff₀ (by linarith)]
  have h2 : |s| ^ (1 + 1) = s ^ 2 := by rw [← sq_abs s]
  rw [h2]
  nlinarith [mul_nonneg (sq_nonneg s) (by linarith : (0:ℝ) ≤ 1 - 2 * |s|)]

/-- Inverse of `1 + h` in the Banach algebra `C(X,ℝ)`. -/
noncomputable def invOne (h : C(X, ℝ)) : C(X, ℝ) := Ring.inverse (1 + h)

theorem invOne_apply {h : C(X, ℝ)} (hh : h ∈ posSet X) (x : X) :
    invOne h x = (1 + h x)⁻¹ := ringInverse_apply hh x

theorem abs_apply_le_norm (k : C(X, ℝ)) (x : X) : |k x| ≤ ‖k‖ := by
  simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm k x

/-- Multiplication by a fixed continuous function, as a continuous linear map. -/
noncomputable def mulOp (g : C(X, ℝ)) : C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  ContinuousLinearMap.mul ℝ C(X, ℝ) g

theorem mulOp_apply (g k : C(X, ℝ)) (x : X) : mulOp g k x = g x * k x := rfl

theorem add_mem_posSet {h k : C(X, ℝ)} {m : ℝ} (hm : ∀ x, m ≤ 1 + h x) (hk : ‖k‖ ≤ m / 2)
    (hm0 : 0 < m) : h + k ∈ posSet X := by
  intro x
  have := (abs_le.mp ((abs_apply_le_norm k x).trans hk)).1
  have h2 := hm x
  simp only [ContinuousMap.add_apply]
  linarith

theorem hasFDerivAt_nemLog {h0 : C(X, ℝ)} (hh : h0 ∈ posSet X) :
    HasFDerivAt (nemLog (X := X)) (mulOp (invOne h0)) h0 := by
  obtain ⟨m, hm, hmx⟩ := exists_lower_of_mem_posSet hh
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hδ : 0 < min (m / 2) (c * m ^ 2 / 2) := lt_min (by linarith) (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : C(X, ℝ)) hδ] with k hk
  rw [mem_ball_zero_iff] at hk
  have hk1 : ‖k‖ ≤ m / 2 := (hk.trans_le (min_le_left _ _)).le
  have hk2 : ‖k‖ ≤ c * m ^ 2 / 2 := (hk.trans_le (min_le_right _ _)).le
  have hP : h0 + k ∈ posSet X := add_mem_posSet hmx hk1 hm
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
  have hx := hmx x
  have hkx : |k x| ≤ ‖k‖ := abs_apply_le_norm k x
  have ha : 0 < 1 + h0 x := lt_of_lt_of_le hm hx
  set s := k x / (1 + h0 x) with hs
  have hs1 : |s| ≤ ‖k‖ / m := by
    rw [hs, abs_div, abs_of_pos ha]
    exact div_le_div₀ (norm_nonneg _) hkx hm hx
  have hs2 : |s| ≤ 1 / 2 := by
    refine hs1.trans ?_
    rw [div_le_iff₀ hm]; linarith
  have hlog : Real.log (1 + h0 x + k x) = Real.log (1 + h0 x) + Real.log (1 + s) := by
    rw [← Real.log_mul ha.ne']
    · congr 1; rw [hs]; field_simp
    · have := (abs_le.mp hs2).1; linarith
  have key := abs_log_one_add_sub_le hs2
  have e : (nemLog (h0 + k) - nemLog h0 - mulOp (invOne h0) k) x
      = Real.log (1 + s) - s := by
    simp only [ContinuousMap.sub_apply, mulOp_apply, nemLog_apply hP, nemLog_apply hh,
      invOne_apply hh, ContinuousMap.add_apply]
    rw [← add_assoc, hlog, hs]; ring
  rw [e, Real.norm_eq_abs]
  refine key.trans ?_
  have h3 : s ^ 2 ≤ (‖k‖ / m) ^ 2 := by
    rw [← sq_abs s]; exact pow_le_pow_left₀ (abs_nonneg _) hs1 2
  have h4 : 2 * (‖k‖ / m) ^ 2 ≤ c * ‖k‖ := by
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg k, mul_nonneg (norm_nonneg k) (sub_nonneg.2 hk2)]
  linarith

theorem contDiffOn_invOne (n : WithTop ℕ∞) : ContDiffOn ℝ n (invOne (X := X)) (posSet X) := by
  intro h hh
  have h1 : ContDiffAt ℝ n (Ring.inverse : C(X, ℝ) → C(X, ℝ)) ((unitOne hh : C(X, ℝ)ˣ) : C(X, ℝ)) :=
    contDiffAt_ringInverse ℝ _
  have h2 : ContDiffAt ℝ n (fun k : C(X, ℝ) => 1 + k) h := by fun_prop
  exact (h1.comp h h2).contDiffWithinAt

theorem differentiableOn_nemLog : DifferentiableOn ℝ (nemLog (X := X)) (posSet X) :=
  fun _ hh => (hasFDerivAt_nemLog hh).differentiableAt.differentiableWithinAt

theorem contDiffOn_nemLog : ContDiffOn ℝ ∞ (nemLog (X := X)) (posSet X) := by
  rw [contDiffOn_infty_iff_fderiv_of_isOpen isOpen_posSet]
  refine ⟨differentiableOn_nemLog, ?_⟩
  have h1 : ContDiffOn ℝ ∞ (⇑(ContinuousLinearMap.mul ℝ C(X, ℝ)) ∘ invOne (X := X))
      (posSet X) :=
    ContDiff.comp_contDiffOn (g := ⇑(ContinuousLinearMap.mul ℝ C(X, ℝ)))
      (ContinuousLinearMap.contDiff _) (contDiffOn_invOne (X := X) ∞)
  refine (show ContDiffOn ℝ ∞ (fun h : C(X, ℝ) => mulOp (invOne h)) (posSet X) from h1).congr fun h hh => ?_
  exact (hasFDerivAt_nemLog hh).fderiv

end NemytskiiLog

variable {d : ℕ}

section Projection

variable (μ : Measure (Torus d)) [IsProbabilityMeasure μ]

theorem integrable_cts (f : C(Torus d, ℝ)) : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- `f ↦ ∫ f dμ` as a continuous linear functional on `C(𝕋)`. -/
noncomputable def intCLM : C(Torus d, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => integral_add (integrable_cts μ f) (integrable_cts μ g)
      map_smul' := fun c f => by simp [integral_const_mul] }
    1 (fun f => by
      have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => f x) (C := ‖f‖)
        (Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm f x)
      simpa using h)

theorem intCLM_apply (f : C(Torus d, ℝ)) : intCLM μ f = ∫ x, f x ∂μ := rfl

/-- `f ↦ ∫ g f dμ`. -/
noncomputable def pairCLM (g : C(Torus d, ℝ)) : C(Torus d, ℝ) →L[ℝ] ℝ :=
  (intCLM μ).comp (mulOp g)

theorem pairCLM_apply (g f : C(Torus d, ℝ)) : pairCLM μ g f = ∫ x, g x * f x ∂μ := rfl

/-- The raw projection `f ↦ f - (∫ f) - ∑ ⟨f, φ_i⟩ φ_i`. -/
noncomputable def projRaw {k : ℕ} (φ : Fin k → C(Torus d, ℝ)) :
    C(Torus d, ℝ) →L[ℝ] C(Torus d, ℝ) :=
  ContinuousLinearMap.id ℝ _ - (intCLM μ).smulRight (1 : C(Torus d, ℝ)) -
    ∑ i, (pairCLM μ (φ i)).smulRight (φ i)

theorem projRaw_apply {k : ℕ} (φ : Fin k → C(Torus d, ℝ)) (f : C(Torus d, ℝ)) (x : Torus d) :
    projRaw μ φ f x = f x - (∫ y, f y ∂μ) - ∑ i, (∫ y, φ i y * f y ∂μ) * φ i x := by
  simp [projRaw, pairCLM_apply, intCLM_apply, ContinuousMap.sum_apply]

end Projection

section Basis

variable (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))

/-- `φ` consists of continuous representatives of an orthonormal basis of `E`. -/
structure IsEquilibriumBasis {k : ℕ} (φ : Fin k → C(Torus d, ℝ)) : Prop where
  orthonormal : Orthonormal ℝ fun i => ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ (φ i)
  span_eq : Submodule.span ℝ (Set.range fun i => ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ (φ i))
    = (nullspace A μ).map (meanZeroL2 μ).subtype

variable {A μ}

theorem IsEquilibriumBasis.toLp_mem {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ) (i : Fin k) :
    ∃ e ∈ nullspace A μ, ((e : meanZeroL2 μ) : Lp ℝ 2 (μ : Measure (Torus d))) =
      ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ (φ i) := by
  have : ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ (φ i) ∈
      (nullspace A μ).map (meanZeroL2 μ).subtype := by
    rw [← hφ.span_eq]; exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨e, he, h⟩ := this
  exact ⟨e, he, h⟩

theorem IsEquilibriumBasis.integral_eq_zero {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ) (i : Fin k) : ∫ x, φ i x ∂(μ : Measure (Torus d)) = 0 := by
  obtain ⟨e, -, he⟩ := hφ.toLp_mem i
  have := (mem_meanZeroL2 μ _).1 e.2
  rw [he, integral_toLp_eq] at this
  exact this

theorem inner_toLp_toLp (f g : C(Torus d, ℝ)) :
    ⟪ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ f, ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ g⟫ =
      ∫ x, f x * g x ∂(μ : Measure (Torus d)) := by
  rw [inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := (μ : Measure (Torus d))) (𝕜 := ℝ) f,
    ContinuousMap.coeFn_toLp (p := 2) (μ := (μ : Measure (Torus d))) (𝕜 := ℝ) g] with x h1 h2
  rw [h1, h2]

theorem IsEquilibriumBasis.pair_eq {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ) (j i : Fin k) :
    pairCLM (μ : Measure (Torus d)) (φ j) (φ i) = if j = i then 1 else 0 := by
  have := (orthonormal_iff_ite.1 hφ.orthonormal) j i
  rw [inner_toLp_toLp] at this
  exact this

theorem integral_one_cts : intCLM (μ : Measure (Torus d)) 1 = 1 := by
  simp [intCLM_apply]

theorem IsEquilibriumBasis.projRaw_mem {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ) (f : C(Torus d, ℝ)) :
    projRaw (μ : Measure (Torus d)) φ f ∈ Ysub A μ := by
  have hpair1 : ∀ j, pairCLM (μ : Measure (Torus d)) (φ j) 1 = 0 := fun j => by
    have := hφ.integral_eq_zero j
    simpa [pairCLM_apply] using this
  rw [mem_Ysub]
  have hmean : intCLM (μ : Measure (Torus d)) (projRaw (μ : Measure (Torus d)) φ f) = 0 := by
    have h1 : ∀ i, pairCLM (μ : Measure (Torus d)) (φ i) f * intCLM (μ : Measure (Torus d)) (φ i) = 0 :=
      fun i => by rw [intCLM_apply, hφ.integral_eq_zero i, mul_zero]
    simp [projRaw, map_sum, integral_one_cts, h1]
  refine ⟨hmean, fun e he => ?_⟩
  have hspan : ((e : meanZeroL2 μ) : Lp ℝ 2 (μ : Measure (Torus d))) ∈
      Submodule.span ℝ (Set.range fun i => ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ (φ i)) := by
    rw [hφ.span_eq]; exact ⟨e, he, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hspan
  rw [← hc, sum_inner]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [inner_smul_left, inner_toLp_toLp]
  have hP : pairCLM (μ : Measure (Torus d)) (φ j) (projRaw (μ : Measure (Torus d)) φ f) = 0 := by
    simp [projRaw, hpair1, hφ.pair_eq]
  have hP' : ∫ x, φ j x * projRaw (μ : Measure (Torus d)) φ f x ∂(μ : Measure (Torus d)) = 0 := hP
  rw [hP']; simp

theorem IsEquilibriumBasis.projRaw_of_mem {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ) {f : C(Torus d, ℝ)} (hf : f ∈ Ysub A μ) :
    projRaw (μ : Measure (Torus d)) φ f = f := by
  rw [mem_Ysub] at hf
  have h1 : ∀ i, pairCLM (μ : Measure (Torus d)) (φ i) f = 0 := fun i => by
    obtain ⟨e, he, he'⟩ := hφ.toLp_mem i
    have := hf.2 e he
    rw [he', inner_toLp_toLp] at this
    exact this
  ext x
  rw [projRaw_apply]
  have h2 : ∀ i, (∫ y, φ i y * f y ∂(μ : Measure (Torus d))) = 0 := h1
  simp [h2, hf.1]

/-- The projection onto `Y`. -/
noncomputable def projY {k : ℕ} {φ : Fin k → C(Torus d, ℝ)} (hφ : IsEquilibriumBasis A μ φ) :
    C(Torus d, ℝ) →L[ℝ] Ysub A μ :=
  (projRaw (μ : Measure (Torus d)) φ).codRestrict (Ysub A μ) hφ.projRaw_mem

theorem coe_projY {k : ℕ} {φ : Fin k → C(Torus d, ℝ)} (hφ : IsEquilibriumBasis A μ φ)
    (f : C(Torus d, ℝ)) : (projY hφ f : C(Torus d, ℝ)) = projRaw (μ : Measure (Torus d)) φ f := rfl

theorem isOpenPosMeasure_of_minimizer
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν) :
    (μ : Measure (Torus d)).IsOpenPosMeasure := by
  refine ⟨fun U hUo hne => ?_⟩
  have hg := minimizer_eq_gibbs A μ hmin
  have hq : ∀ x, 0 < gibbsDensity A (μ : Measure (Torus d)) x := fun x => by
    unfold gibbsDensity
    exact div_pos (Real.exp_pos _) (gibbsPartition_pos A _)
  have hcont : Continuous (gibbsDensity A (μ : Measure (Torus d))) := by
    unfold gibbsDensity
    exact (Real.continuous_exp.comp (continuous_equilibriumPotential A _).neg).div_const _
  rw [hg, gibbsMeasure_eq_withDensity]
  rw [Ne, withDensity_apply_eq_zero' (by
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      hcont.measurable.aemeasurable))]
  have : {x | ENNReal.ofReal (gibbsDensity A (μ : Measure (Torus d)) x) ≠ 0} ∩ U = U := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_iff_right_iff_imp]
    intro _; simpa using hq x
  rw [this]
  exact hUo.measure_ne_zero _ hne

theorem IsEquilibriumBasis.centeredOperatorC_phi {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ)
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν) (i : Fin k) :
    centeredOperatorC A (μ : Measure (Torus d)) (φ i) = -φ i := by
  have := isOpenPosMeasure_of_minimizer hmin
  obtain ⟨e, he, he'⟩ := hφ.toLp_mem i
  refine (ContinuousMap.toLp_inj (μ : Measure (Torus d)) (p := 2) (𝕜 := ℝ)).1 ?_
  rw [toLp_centeredOperatorC, map_neg, ← he', centeredOperator_of_mem_nullspace A μ he]

end Basis


section Reduction

variable {A : InteractionData d} {μ : ProbabilityMeasure (Torus d)}

/-- The parameter space of the reduction. -/
abbrev Par (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- `a ↦ ∑ a_i φ_i`. -/
noncomputable def phiMap {k : ℕ} (φ : Fin k → C(Torus d, ℝ)) : Par k →L[ℝ] C(Torus d, ℝ) :=
  ∑ i, (EuclideanSpace.proj i : Par k →L[ℝ] ℝ).smulRight (φ i)

theorem phiMap_apply {k : ℕ} (φ : Fin k → C(Torus d, ℝ)) (a : Par k) (x : Torus d) :
    phiMap φ a x = ∑ i, a i * φ i x := by
  simp [phiMap, ContinuousMap.sum_apply]

/-- `(a, y) ↦ ∑ a_i φ_i + y`. -/
noncomputable def hMap (A : InteractionData d) (μ : ProbabilityMeasure (Torus d)) {k : ℕ}
    (φ : Fin k → C(Torus d, ℝ)) : Par k × Ysub A μ →L[ℝ] C(Torus d, ℝ) :=
  (phiMap φ).comp (ContinuousLinearMap.fst ℝ _ _) +
    (Ysub A μ).subtypeL.comp (ContinuousLinearMap.snd ℝ _ _)

theorem hMap_apply {k : ℕ} (φ : Fin k → C(Torus d, ℝ)) (p : Par k × Ysub A μ) :
    hMap A μ φ p = phiMap φ p.1 + (p.2 : C(Torus d, ℝ)) := rfl

/-- The Euler operator `h ↦ log (1 + h) + T h`. -/
noncomputable def euler (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))
    (h : C(Torus d, ℝ)) : C(Torus d, ℝ) :=
  nemLog h + centeredOperatorC A (μ : Measure (Torus d)) h

/-- The reduced map `F(a, y) = P_Y [log (1 + h) + T h]`, `h = ∑ a_i φ_i + y`. -/
noncomputable def redMap {k : ℕ} {φ : Fin k → C(Torus d, ℝ)} (hφ : IsEquilibriumBasis A μ φ)
    (p : Par k × Ysub A μ) : Ysub A μ :=
  projY hφ (euler A μ (hMap A μ φ p))

theorem nemLog_zero : nemLog (0 : C(Torus d, ℝ)) = 0 := by
  have h0 : (0 : C(Torus d, ℝ)) ∈ posSet (Torus d) := fun x => by simp
  ext x
  rw [nemLog_apply h0]; simp

theorem invOne_zero : invOne (0 : C(Torus d, ℝ)) = 1 := by
  unfold invOne; simp

theorem mulOp_one : mulOp (1 : C(Torus d, ℝ)) = ContinuousLinearMap.id ℝ _ := by
  ext f x; simp [mulOp_apply]

theorem zero_mem_posSet : (0 : C(Torus d, ℝ)) ∈ posSet (Torus d) := fun x => by simp

theorem redMap_zero {k : ℕ} {φ : Fin k → C(Torus d, ℝ)} (hφ : IsEquilibriumBasis A μ φ) :
    redMap hφ (0, 0) = 0 := by
  unfold redMap euler
  have : hMap A μ φ ((0 : Par k), (0 : Ysub A μ)) = 0 := by simp [hMap_apply]
  rw [this, nemLog_zero]; simp

theorem hasFDerivAt_euler :
    HasFDerivAt (euler A μ) (ContinuousLinearMap.id ℝ _ + centeredOperatorC A (μ : Measure (Torus d)))
      (0 : C(Torus d, ℝ)) := by
  have h1 := hasFDerivAt_nemLog (zero_mem_posSet (d := d))
  rw [invOne_zero, mulOp_one] at h1
  exact h1.add (centeredOperatorC A (μ : Measure (Torus d))).hasFDerivAt

theorem contDiffAt_euler   : ContDiffAt ℝ ∞ (euler A μ) (0 : C(Torus d, ℝ)) := by
  unfold euler
  have h1 : ContDiffAt ℝ ∞ (nemLog (X := Torus d)) 0 := by
    have := (contDiffOn_nemLog (X := Torus d)).contDiffAt (isOpen_posSet.mem_nhds (zero_mem_posSet (d := d)))
    exact this
  exact h1.add (centeredOperatorC A (μ : Measure (Torus d))).contDiff.contDiffAt

end Reduction

section ImplicitInfty

open Filter Set Topology

variable {P W V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace P] [CompleteSpace V] in
/-- Bootstrap: an implicit function with the derivative formula, whose graph lies in an open set
where `F` is `C^∞`, is `C^∞` on its (open) domain. -/
theorem lip034_bootstrap {F : P × W → V} {S : Set (P × W)} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F S) {U : Set P} (hU : IsOpen U) {ψ : P → W}
    (hgraph : ∀ p ∈ U, (p, ψ p) ∈ S)
    (hder : ∀ p ∈ U, (fderiv ℝ F (p, ψ p) ∘L ContinuousLinearMap.inr ℝ P W).IsInvertible ∧
      HasFDerivAt ψ (-(fderiv ℝ F (p, ψ p) ∘L ContinuousLinearMap.inr ℝ P W).inverse ∘L
        (fderiv ℝ F (p, ψ p) ∘L ContinuousLinearMap.inl ℝ P W)) p) :
    ContDiffOn ℝ ∞ ψ U := by
  rw [contDiffOn_infty]
  intro n
  induction n with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun p hp => (hder p hp).2.continuousAt.continuousWithinAt
  | succ n ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun p hp => (hder p hp).2.differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have hG : ContDiffOn ℝ n (fun p => (p, ψ p)) U := contDiffOn_id.prodMk ih
    have hFd : ContDiffOn ℝ n (fderiv ℝ F) S :=
      (hF.fderiv_of_isOpen hS (m := (n : ℕ∞ω)) (by exact_mod_cast le_top))
    have hD : ContDiffOn ℝ n (fun p => fderiv ℝ F (p, ψ p)) U :=
      hFd.comp hG (fun p hp => hgraph p hp)
    have hB : ContDiffOn ℝ n (fun p => fderiv ℝ F (p, ψ p) ∘L ContinuousLinearMap.inr ℝ P W) U :=
      hD.clm_comp contDiffOn_const
    have hA : ContDiffOn ℝ n (fun p => fderiv ℝ F (p, ψ p) ∘L ContinuousLinearMap.inl ℝ P W) U :=
      hD.clm_comp contDiffOn_const
    have hΦ : ContDiffOn ℝ n (fun p => -(fderiv ℝ F (p, ψ p) ∘L ContinuousLinearMap.inr ℝ P W).inverse ∘L
        (fderiv ℝ F (p, ψ p) ∘L ContinuousLinearMap.inl ℝ P W)) U := by
      intro p hp
      obtain ⟨e, he⟩ := (hder p hp).1
      have h1 : ContDiffAt ℝ n (ContinuousLinearMap.inverse : (W →L[ℝ] V) → (V →L[ℝ] W))
          (fderiv ℝ F (p, ψ p) ∘L ContinuousLinearMap.inr ℝ P W) := by
        rw [← he]; exact contDiffAt_map_inverse e
      have h2 := h1.comp_contDiffWithinAt p (hB p hp)
      exact (h2.clm_comp (hA p hp)).neg
    exact hΦ.congr fun p hp => (hder p hp).2.fderiv
end ImplicitInfty

section Implicit

variable {A : InteractionData d} {μ : ProbabilityMeasure (Torus d)}

theorem contDiff_hMap {k : ℕ} (φ : Fin k → C(Torus d, ℝ)) : ContDiff ℝ ∞ (hMap A μ φ) :=
  ContinuousLinearMap.contDiff (E := Par k × Ysub A μ) (F := C(Torus d, ℝ)) _

theorem contDiff_projY {k : ℕ} {φ : Fin k → C(Torus d, ℝ)} (hφ : IsEquilibriumBasis A μ φ) :
    ContDiff ℝ ∞ (projY hφ) :=
  ContinuousLinearMap.contDiff (E := C(Torus d, ℝ)) (F := Ysub A μ) _

theorem contDiffAt_redMap {k : ℕ} {φ : Fin k → C(Torus d, ℝ)} (hφ : IsEquilibriumBasis A μ φ) :
    ContDiffAt ℝ ∞ (redMap hφ) ((0 : Par k), (0 : Ysub A μ)) := by
  have e : hMap A μ φ ((0 : Par k), (0 : Ysub A μ)) = 0 := by simp [hMap_apply]
  have h1 : ContDiffAt ℝ ∞ (euler A μ) (hMap A μ φ ((0 : Par k), (0 : Ysub A μ))) := by
    rw [e]; exact contDiffAt_euler
  have h0 : ContDiffAt ℝ ∞ (hMap A μ φ) ((0 : Par k), (0 : Ysub A μ)) :=
    (contDiff_hMap φ).contDiffAt
  have h2 : ContDiffAt ℝ ∞ (euler A μ ∘ hMap A μ φ) ((0 : Par k), (0 : Ysub A μ)) :=
    ContDiffAt.comp _ h1 h0
  exact ContDiffAt.comp (g := projY hφ) _ (contDiff_projY hφ).contDiffAt h2

theorem hasFDerivAt_redMap {k : ℕ} {φ : Fin k → C(Torus d, ℝ)} (hφ : IsEquilibriumBasis A μ φ) :
    HasFDerivAt (redMap hφ)
      ((projY hφ).comp ((ContinuousLinearMap.id ℝ _ +
        centeredOperatorC A (μ : Measure (Torus d))).comp (hMap A μ φ)))
      ((0 : Par k), (0 : Ysub A μ)) := by
  have e : hMap A μ φ ((0 : Par k), (0 : Ysub A μ)) = 0 := by simp [hMap_apply]
  have h1 : HasFDerivAt (euler A μ) (ContinuousLinearMap.id ℝ _ +
      centeredOperatorC A (μ : Measure (Torus d))) (hMap A μ φ ((0 : Par k), (0 : Ysub A μ))) := by
    rw [e]; exact hasFDerivAt_euler
  have h2 : HasFDerivAt (euler A μ ∘ hMap A μ φ) _ ((0 : Par k), (0 : Ysub A μ)) :=
    h1.comp _ (hMap A μ φ).hasFDerivAt
  exact HasFDerivAt.comp (g := projY hφ) _ (projY hφ).hasFDerivAt h2

theorem phiMap_zero {k : ℕ} (φ : Fin k → C(Torus d, ℝ)) : phiMap φ 0 = 0 := map_zero _

theorem fderiv_redMap_inr_apply {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ) (z : Ysub A μ) :
    ((fderiv ℝ (redMap hφ) ((0 : Par k), (0 : Ysub A μ)) ∘L
      ContinuousLinearMap.inr ℝ (Par k) (Ysub A μ)) z : C(Torus d, ℝ)) =
      (z : C(Torus d, ℝ)) + centeredOperatorC A (μ : Measure (Torus d)) (z : C(Torus d, ℝ)) := by
  rw [(hasFDerivAt_redMap hφ).fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inr_apply,
    coe_projY, add_apply, ContinuousLinearMap.id_apply, hMap_apply,
    phiMap_zero, zero_add]
  exact (hφ.projRaw_of_mem (add_mem z.2 (centeredOperatorC_mem A μ z.2)))


theorem lip034_isInvertible_redMap {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ) :
    (fderiv ℝ (redMap hφ) ((0 : Par k), (0 : Ysub A μ)) ∘L
      ContinuousLinearMap.inr ℝ (Par k) (Ysub A μ)).IsInvertible := by
  obtain ⟨S, hS⟩ := fredholm_inverse_Ysub A μ
  set L := fderiv ℝ (redMap hφ) ((0 : Par k), (0 : Ysub A μ)) ∘L
      ContinuousLinearMap.inr ℝ (Par k) (Ysub A μ) with hL
  have hLz : ∀ z : Ysub A μ, ((L z : Ysub A μ) : C(Torus d, ℝ)) =
      (z : C(Torus d, ℝ)) + centeredOperatorC A (μ : Measure (Torus d)) (z : C(Torus d, ℝ)) :=
    fun z => fderiv_redMap_inr_apply hφ z
  have h1 : ∀ z, S (L z) = z := fun z => (hS (L z) z).1 (hLz z).symm
  have h2 : ∀ y, L (S y) = y := fun y => Subtype.ext (by
    rw [hLz]; exact (hS y (S y)).2 rfl)
  exact ⟨ContinuousLinearEquiv.equivOfInverse L S h1 h2, rfl⟩

theorem centeredOperatorC_phiMap {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ)
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν) (a : Par k) :
    centeredOperatorC A (μ : Measure (Torus d)) (phiMap φ a) = -phiMap φ a := by
  have hsum : phiMap φ a = ∑ i, a i • φ i := by
    ext x; rw [phiMap_apply, ContinuousMap.sum_apply]; simp
  rw [hsum, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hφ.centeredOperatorC_phi hmin i, smul_neg]

theorem hMap_zero_right {k : ℕ} (φ : Fin k → C(Torus d, ℝ)) (z : Ysub A μ) :
    hMap A μ φ ((0 : Par k), z) = (z : C(Torus d, ℝ)) := by
  simp [hMap_apply]

/-- `redMap` is `C^∞` on the open set where `1 + h > 0`. -/
theorem contDiffOn_redMap {k : ℕ} {φ : Fin k → C(Torus d, ℝ)} (hφ : IsEquilibriumBasis A μ φ) :
    ContDiffOn ℝ ∞ (redMap hφ) (hMap A μ φ ⁻¹' posSet (Torus d)) := by
  have h0 : ContDiffOn ℝ ∞ (euler A μ) (posSet (Torus d)) :=
    contDiffOn_nemLog.add (centeredOperatorC A (μ : Measure (Torus d))).contDiff.contDiffOn
  have h1 : ContDiffOn ℝ ∞ (euler A μ ∘ hMap A μ φ) (hMap A μ φ ⁻¹' posSet (Torus d)) :=
    h0.comp (contDiff_hMap φ).contDiffOn (fun _ hp => hp)
  exact (contDiff_projY hφ).comp_contDiffOn h1

theorem isOpen_hMap_preimage {k : ℕ} (φ : Fin k → C(Torus d, ℝ)) :
    IsOpen (hMap A μ φ ⁻¹' posSet (Torus d)) :=
  isOpen_posSet.preimage (contDiff_hMap φ).continuous

/-- **S3b.** Smooth Lyapunov–Schmidt graph: near `0` the equation `P_Y [log (1 + h) + T h] = 0`
has a unique solution `y(a) ∈ Y` in a neighbourhood of `0`, `y` is `C^∞`, `y 0 = 0`,
`Dy 0 = 0`, and `1 + ∑ a_i φ_i + y a > 0`. -/
theorem lip034_graph {k : ℕ} {φ : Fin k → C(Torus d, ℝ)} (hφ : IsEquilibriumBasis A μ φ)
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν) :
    ∃ U : Set (Par k), IsOpen U ∧ (0 : Par k) ∈ U ∧ ∃ Wn : Set (Ysub A μ), IsOpen Wn ∧
      (0 : Ysub A μ) ∈ Wn ∧ ∃ y : Par k → Ysub A μ,
      y 0 = 0 ∧ fderiv ℝ y 0 = 0 ∧ ContDiffOn ℝ ∞ y U ∧
      (∀ a ∈ U, y a ∈ Wn ∧ redMap hφ (a, y a) = 0 ∧
        hMap A μ φ (a, y a) ∈ posSet (Torus d)) ∧
      (∀ a ∈ U, ∀ w ∈ Wn, redMap hφ (a, w) = 0 → w = y a) := by
  obtain ⟨U₁, hU₁o, h0U₁, Wn, hWno, h0Wn, ψ, hψ0, hψz, hψu, hψ1, hψd, -, -⟩ :=
    DGPS.Analysis.parameter_implicit_function_and_differentiated_remainders
      (F := redMap hφ) (p₀ := (0 : Par k)) (w₀ := (0 : Ysub A μ)) (k := 1) le_rfl
      ((contDiffAt_redMap hφ).of_le (by exact_mod_cast le_top)) (redMap_zero hφ)
      (lip034_isInvertible_redMap hφ)
  set S := hMap A μ φ ⁻¹' posSet (Torus d) with hS
  have hSo : IsOpen S := isOpen_hMap_preimage φ
  have hcont : ContinuousOn (fun p => (p, ψ p)) U₁ :=
    continuousOn_id.prodMk hψ1.continuousOn
  set U := U₁ ∩ (fun p => (p, ψ p)) ⁻¹' S with hU
  have hUo : IsOpen U := hcont.isOpen_inter_preimage hU₁o hSo
  have h0S : ((0 : Par k), (0 : Ysub A μ)) ∈ S := by
    show hMap A μ φ ((0 : Par k), (0 : Ysub A μ)) ∈ posSet (Torus d)
    have : hMap A μ φ ((0 : Par k), (0 : Ysub A μ)) = 0 := by simp [hMap_apply]
    rw [this]; exact zero_mem_posSet
  have h0U : (0 : Par k) ∈ U := ⟨h0U₁, by simpa [hψ0] using h0S⟩
  have hgraph : ∀ p ∈ U, (p, ψ p) ∈ S := fun p hp => hp.2
  have hsm : ContDiffOn ℝ ∞ ψ U :=
    lip034_bootstrap hSo (contDiffOn_redMap hφ) hUo hgraph
      (fun p hp => hψd p hp.1)
  refine ⟨U, hUo, h0U, Wn, hWno, h0Wn, ψ, hψ0, ?_, hsm,
    fun a ha => ⟨(hψz a ha.1).1, (hψz a ha.1).2, ha.2⟩,
    fun a ha w hw hz => hψu a ha.1 w hw hz⟩
  have hd := (hψd 0 h0U₁).2
  rw [hψ0] at hd
  have hA : fderiv ℝ (redMap hφ) ((0 : Par k), (0 : Ysub A μ)) ∘L
      ContinuousLinearMap.inl ℝ (Par k) (Ysub A μ) = 0 := by
    refine ContinuousLinearMap.ext fun a => Subtype.ext ?_
    rw [(hasFDerivAt_redMap hφ).fderiv]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inl_apply,
      coe_projY, add_apply, ContinuousLinearMap.id_apply, hMap_apply, Submodule.coe_zero,
      add_zero, zero_apply]
    rw [centeredOperatorC_phiMap hφ hmin]
    simp
  rw [hA] at hd
  simpa using hd.fderiv

/-- `f ↦ (∫ φ_i f dμ)_i`, the coordinates of the `E`-component. -/
noncomputable def bMap (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {k : ℕ}
    (φ : Fin k → C(Torus d, ℝ)) : C(Torus d, ℝ) →L[ℝ] Par k :=
  ∑ i, (pairCLM μ (φ i)).smulRight (EuclideanSpace.single i (1 : ℝ))

theorem bMap_apply (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {k : ℕ}
    (φ : Fin k → C(Torus d, ℝ)) (f : C(Torus d, ℝ)) (i : Fin k) :
    bMap μ φ f i = ∫ x, φ i x * f x ∂μ := by
  simp [bMap, pairCLM_apply, Pi.single_apply]

/-- **S4.** On the graph neighbourhood: positivity of `1 + h`, the Euler expression
`log (1 + h) + T h = c + ∑ b_i φ_i`, and smoothness of `b` and `c`, with `b 0 = 0`, `D b 0 = 0`. -/
theorem lip034_euler_expansion {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ)
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν) :
    ∃ U : Set (Par k), IsOpen U ∧ (0 : Par k) ∈ U ∧ ∃ y : Par k → Ysub A μ,
      y 0 = 0 ∧ fderiv ℝ y 0 = 0 ∧ ContDiffOn ℝ ∞ y U ∧
      (∀ a ∈ U, redMap hφ (a, y a) = 0) ∧
      (∀ a ∈ U, ∀ x, 0 < 1 + (phiMap φ a + (y a : C(Torus d, ℝ))) x) ∧
      ∃ (b : Par k → Par k) (c : Par k → ℝ),
        ContDiffOn ℝ ∞ b U ∧ ContDiffOn ℝ ∞ c U ∧ b 0 = 0 ∧ fderiv ℝ b 0 = 0 ∧
        (∀ a ∈ U, ∀ x, Real.log (1 + (phiMap φ a + (y a : C(Torus d, ℝ))) x) +
          centeredOperatorC A (μ : Measure (Torus d)) (phiMap φ a + (y a : C(Torus d, ℝ))) x =
          c a + ∑ i, b a i * φ i x) := by
  obtain ⟨U, hUo, h0U, Wn, -, -, y, hy0, hyd, hsm, hgr, -⟩ := lip034_graph hφ hmin
  set m : Measure (Torus d) := (μ : Measure (Torus d)) with hm
  set H : Par k → C(Torus d, ℝ) := fun a => hMap A μ φ (a, y a) with hH
  have hHeq : ∀ a, H a = phiMap φ a + (y a : C(Torus d, ℝ)) := fun a => rfl
  have hpos : ∀ a ∈ U, H a ∈ posSet (Torus d) := fun a ha => (hgr a ha).2.2
  have hHsm : ContDiffOn ℝ ∞ H U :=
    (contDiff_hMap φ).comp_contDiffOn (contDiffOn_id.prodMk hsm)
  have hE : ContDiffOn ℝ ∞ (fun a => euler A μ (H a)) U := by
    have h0 : ContDiffOn ℝ ∞ (euler A μ) (posSet (Torus d)) :=
      contDiffOn_nemLog.add (centeredOperatorC A m).contDiff.contDiffOn
    exact h0.comp hHsm hpos
  have hbsm : ContDiff ℝ ∞ (bMap m φ) :=
    ContinuousLinearMap.contDiff (E := C(Torus d, ℝ)) (F := Par k) _
  have hcsm : ContDiff ℝ ∞ (intCLM m) :=
    ContinuousLinearMap.contDiff (E := C(Torus d, ℝ)) (F := ℝ) _
  refine ⟨U, hUo, h0U, y, hy0, hyd, hsm, fun a ha => (hgr a ha).2.1,
    fun a ha x => hpos a ha x, fun a => bMap m φ (euler A μ (H a)),
    fun a => intCLM m (euler A μ (H a)), hbsm.comp_contDiffOn hE, hcsm.comp_contDiffOn hE,
    ?_, ?_, ?_⟩
  · have : H 0 = 0 := by rw [hHeq, hy0]; simp
    show bMap m φ (euler A μ (H 0)) = 0
    rw [this]
    unfold euler
    rw [nemLog_zero]; simp
  · have hd : DifferentiableAt ℝ y 0 :=
        (hsm.differentiableOn (by simp)).differentiableAt (hUo.mem_nhds h0U)
    have hy := hd.hasFDerivAt
    have hH0 : H 0 = 0 := by rw [hHeq, hy0]; simp
    have hsub : HasFDerivAt (fun a => ((y a : Ysub A μ) : C(Torus d, ℝ)))
        (0 : Par k →L[ℝ] C(Torus d, ℝ)) (0 : Par k) := by
      have h1 :=
        HasFDerivAt.comp (𝕜 := ℝ) (E := Par k) (F := Ysub A μ) (G := C(Torus d, ℝ))
          (g := (Ysub A μ).subtypeL) (f := y) (g' := (Ysub A μ).subtypeL)
          (f' := fderiv ℝ y 0) (0 : Par k) (Ysub A μ).subtypeL.hasFDerivAt hy
      rw [hyd] at h1
      simpa [Function.comp_def] using h1
    have hH' : HasFDerivAt H (phiMap φ + (0 : Par k →L[ℝ] C(Torus d, ℝ))) (0 : Par k) :=
      (phiMap φ).hasFDerivAt.add hsub
    have hE' : HasFDerivAt (euler A μ) (ContinuousLinearMap.id ℝ _ +
        centeredOperatorC A m) (H 0) := by rw [hH0]; exact hasFDerivAt_euler
    have hB := (bMap m φ).hasFDerivAt.comp (0 : Par k) (hE'.comp (0 : Par k) hH')
    have hz : (bMap m φ).comp ((ContinuousLinearMap.id ℝ _ + centeredOperatorC A m).comp
        (phiMap φ + (0 : Par k →L[ℝ] C(Torus d, ℝ)))) = 0 := by
      refine ContinuousLinearMap.ext fun a => ?_
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, add_apply, zero_apply,
        ContinuousLinearMap.id_apply, add_zero]
      rw [centeredOperatorC_phiMap hφ hmin]; simp
    rw [hz] at hB
    exact hB.fderiv
  · intro a ha x
    have hz := (hgr a ha).2.1
    have hz' : projRaw m φ (euler A μ (H a)) = 0 := by
      have := congrArg (fun w : Ysub A μ => (w : C(Torus d, ℝ))) hz
      simpa [redMap, coe_projY] using this
    have hx := congrArg (fun f : C(Torus d, ℝ) => f x) hz'
    simp only [projRaw_apply, ContinuousMap.zero_apply] at hx
    have hP : euler A μ (H a) x = Real.log (1 + H a x) +
        centeredOperatorC A m (H a) x := by
      unfold euler
      simp [nemLog_apply (hpos a ha)]
      rfl
    show Real.log (1 + (phiMap φ a + (y a : C(Torus d, ℝ))) x) +
          centeredOperatorC A m (phiMap φ a + (y a : C(Torus d, ℝ))) x =
          intCLM m (euler A μ (H a)) + ∑ i, bMap m φ (euler A μ (H a)) i * φ i x
    rw [← hHeq, ← hP]
    simp only [bMap_apply, intCLM_apply]
    linarith

end Implicit

section LipschitzRegularity

variable {A : InteractionData d} {μ : ProbabilityMeasure (Torus d)}

theorem lip034_exp_lipschitz {g : Torus d → ℝ} {L M : ℝ} (hg : TorusLipschitzWith L g)
    (hM : ∀ x, g x ≤ M) : TorusLipschitzWith (Real.exp M * L) fun x => Real.exp (g x) := by
  have key : ∀ s t : ℝ, t ≤ s → s ≤ M → |Real.exp s - Real.exp t| ≤ Real.exp M * (s - t) := by
    intro s t hts hsM
    have h1 : 1 - Real.exp (-(s - t)) ≤ s - t := by
      have := Real.add_one_le_exp (-(s - t)); linarith
    have h2 : Real.exp s - Real.exp t = Real.exp s * (1 - Real.exp (-(s - t))) := by
      rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
    have h3 : 0 ≤ 1 - Real.exp (-(s - t)) := by
      have : Real.exp (-(s - t)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      linarith
    rw [h2, abs_of_nonneg (mul_nonneg (Real.exp_pos s).le h3)]
    exact mul_le_mul (Real.exp_le_exp.2 hsM) h1 h3 (Real.exp_pos M).le
  intro x y
  have hd := hg x y
  have hd0 : 0 ≤ torusDist x y := Real.sqrt_nonneg _
  rcases le_total (g y) (g x) with h | h
  · have := key (g x) (g y) h (hM x)
    calc |Real.exp (g x) - Real.exp (g y)| ≤ Real.exp M * (g x - g y) := this
      _ ≤ Real.exp M * (L * torusDist x y) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans hd) (Real.exp_pos M).le
      _ = _ := by ring
  · have := key (g y) (g x) h (hM y)
    rw [abs_sub_comm]
    have hd' : g y - g x ≤ L * torusDist x y := by
      have := hg y x
      rw [torusDist_metric.2.1] at this
      exact (le_abs_self _).trans this
    calc |Real.exp (g y) - Real.exp (g x)| ≤ Real.exp M * (g y - g x) := this
      _ ≤ Real.exp M * (L * torusDist x y) :=
        mul_le_mul_of_nonneg_left hd' (Real.exp_pos M).le
      _ = _ := by ring

theorem lip034_centeredOperatorC_lipschitz (hA : LipschitzData A) (f : C(Torus d, ℝ)) :
    ∃ L, TorusLipschitzWith L fun x => centeredOperatorC A (μ : Measure (Torus d)) f x := by
  obtain ⟨L, hL⟩ := kernel_integral_lipschitz A hA (μ : Measure (Torus d))
    (ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ f)
  refine ⟨L, fun x y => ?_⟩
  have e : ∀ z, centeredOperatorC A (μ : Measure (Torus d)) f z =
      ∫ w, centeredKernel A (μ : Measure (Torus d)) z w *
        (ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ f) w ∂(μ : Measure (Torus d)) :=
    fun z => Tcont_apply A _ _ z
  simp only [e]
  exact hL x y

theorem lip034_lipschitz_add {f g : Torus d → ℝ} {L M : ℝ} (hf : TorusLipschitzWith L f)
    (hg : TorusLipschitzWith M g) : TorusLipschitzWith (L + M) fun x => f x + g x := by
  intro x y
  have := abs_add_le (f x - f y) (g x - g y)
  have h0 : 0 ≤ torusDist x y := Real.sqrt_nonneg _
  calc |(f x + g x) - (f y + g y)| = |(f x - f y) + (g x - g y)| := by ring_nf
    _ ≤ _ := this
    _ ≤ L * torusDist x y + M * torusDist x y := add_le_add (hf x y) (hg x y)
    _ = _ := by ring

theorem lip034_lipschitz_smul {f : Torus d → ℝ} {L : ℝ} (hf : TorusLipschitzWith L f) (c : ℝ) :
    TorusLipschitzWith (|c| * L) fun x => c * f x := by
  intro x y
  have h0 : 0 ≤ torusDist x y := Real.sqrt_nonneg _
  have : (c * f x - c * f y) = c * (f x - f y) := by ring
  rw [this, abs_mul]
  calc |c| * |f x - f y| ≤ |c| * (L * torusDist x y) :=
        mul_le_mul_of_nonneg_left (hf x y) (abs_nonneg _)
    _ = _ := by ring

theorem lip034_lipschitz_sum {n : ℕ} {f : Fin n → Torus d → ℝ} {L : Fin n → ℝ}
    (hf : ∀ i, TorusLipschitzWith (L i) (f i)) :
    TorusLipschitzWith (∑ i, L i) fun x => ∑ i, f i x := by
  induction n with
  | zero => intro x y; simp
  | succ n ih =>
    have := lip034_lipschitz_add (ih (f := fun i => f i.castSucc) (L := fun i => L i.castSucc)
      fun i => hf _) (hf (Fin.last n))
    rw [Fin.sum_univ_castSucc]
    simpa [Fin.sum_univ_castSucc] using this

theorem lip034_phi_lipschitz (hA : LipschitzData A) {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ)
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν) (i : Fin k) :
    ∃ L, TorusLipschitzWith L fun x => φ i x := by
  obtain ⟨L, hL⟩ := lip034_centeredOperatorC_lipschitz (μ := μ) hA (φ i)
  refine ⟨L, fun x y => ?_⟩
  have e : ∀ z, φ i z = -centeredOperatorC A (μ : Measure (Torus d)) (φ i) z := fun z => by
    rw [hφ.centeredOperatorC_phi hmin]; simp
  simp only [e]
  have := hL x y
  rwa [show -centeredOperatorC A (μ : Measure (Torus d)) (φ i) x -
    -centeredOperatorC A (μ : Measure (Torus d)) (φ i) y =
    -(centeredOperatorC A (μ : Measure (Torus d)) (φ i) x -
      centeredOperatorC A (μ : Measure (Torus d)) (φ i) y) by ring, abs_neg]

/-- S5: spatial Lipschitz regularity of a positive solution of the Euler expression. -/
theorem lip034_lipschitz_of_euler (hA : LipschitzData A) {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ)
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν)
    {h : C(Torus d, ℝ)} (hpos : ∀ x, 0 < 1 + h x) {c : ℝ} {b : Par k}
    (heq : ∀ x, Real.log (1 + h x) + centeredOperatorC A (μ : Measure (Torus d)) h x =
      c + ∑ i, b i * φ i x) :
    ∃ L, TorusLipschitzWith L fun x => h x := by
  choose Lφ hLφ using lip034_phi_lipschitz hA hφ hmin
  obtain ⟨LT, hLT⟩ := lip034_centeredOperatorC_lipschitz (μ := μ) hA h
  have hS : TorusLipschitzWith (∑ i, |b i| * Lφ i) fun x => ∑ i, b i * φ i x :=
    lip034_lipschitz_sum fun i => lip034_lipschitz_smul (hLφ i) (b i)
  have hg : TorusLipschitzWith (|(-1 : ℝ)| * LT + (∑ i, |b i| * Lφ i))
      fun x => (-1 : ℝ) * centeredOperatorC A (μ : Measure (Torus d)) h x + ∑ i, b i * φ i x :=
    lip034_lipschitz_add (lip034_lipschitz_smul hLT (-1)) hS
  -- the logarithm, up to the constant `c`
  have hlog : ∀ x, Real.log (1 + h x) = c + ((-1 : ℝ) * centeredOperatorC A
      (μ : Measure (Torus d)) h x + ∑ i, b i * φ i x) := fun x => by
    have := heq x; linarith
  set G : Torus d → ℝ := fun x => (-1 : ℝ) * centeredOperatorC A (μ : Measure (Torus d)) h x +
    ∑ i, b i * φ i x with hGdef
  have hGc : Continuous G := by
    have : Continuous fun x => centeredOperatorC A (μ : Measure (Torus d)) h x := by fun_prop
    simp only [hGdef]; fun_prop
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, c + G x ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn
      (continuous_const.add hGc).continuousOn
    exact ⟨M, fun x => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM x (Set.mem_univ x))⟩
  have hgc : TorusLipschitzWith (|(-1 : ℝ)| * LT + (∑ i, |b i| * Lφ i)) fun x => c + G x := by
    intro x y
    have := hg x y
    simpa using this
  have := lip034_exp_lipschitz hgc hM
  refine ⟨Real.exp M * (|(-1 : ℝ)| * LT + (∑ i, |b i| * Lφ i)), fun x y => ?_⟩
  have e : ∀ z, h z = Real.exp (c + G z) - 1 := fun z => by
    rw [← hlog z, Real.exp_log (hpos z)]; ring
  have key := this x y
  rw [show h x - h y = Real.exp (c + G x) - Real.exp (c + G y) by rw [e x, e y]; ring]
  exact key

end LipschitzRegularity

end DGPS.Lipschitz
