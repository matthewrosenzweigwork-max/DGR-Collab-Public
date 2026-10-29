import DGPS.Variational.PositiveRankOne
import DGPS.Variational.WeightedScoreInformation
import DGPS.Variational.SpeciesGap
import DGPS.Variational.FrozenGibbs
import DGPS.Basic.SquareRootHeatRecovery
import DGPS.FiniteN.Tools.WeightedSobolev
import DGPS.Foundations.SobolevEmbedding
import DGPS.Foundations.PeriodicSmoothing

/-!
# Exact-barycenter binary dilution (EX017)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace DGPS.Examples

variable {d : ℕ}

/-- A smooth, strictly positive probability density on the torus. -/
structure SmoothPositiveProbability (d : ℕ) where
  p : Torus d → ℝ
  smooth : IsSmoothPeriodic p
  pos : ∀ x, 0 < p x
  mass : ∫ x, p x ∂haar d = 1

end DGPS.Examples

namespace DGPS.Examples.SmoothPositiveProbability

variable {d : ℕ}

variable (q : SmoothPositiveProbability d)

theorem continuous : Continuous q.p := q.smooth.continuous_torus

theorem sqrt_smooth : IsSmoothPeriodic fun x => √(q.p x) :=
  DGPS.Lipschitz.isSmoothPeriodic_sqrt q.smooth q.pos

/-- The absolute-admissible density `√p`. -/
noncomputable def toAbsoluteDensity : AbsoluteDensity d where
  sqrt := fun x => √(q.p x)
  sqrt_mem := ⟨_, q.sqrt_smooth.isWeakGradient⟩
  sqrt_nonneg := Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _
  mass_one := by
    have : (fun x => √(q.p x) ^ 2) = q.p := funext fun x => Real.sq_sqrt (q.pos x).le
    rw [this, q.mass]

theorem exists_bounds : ∃ m M : ℝ, 0 < m ∧ ∀ x, m ≤ q.p x ∧ q.p x ≤ M := by
  obtain ⟨a, -, ha⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty q.continuous.continuousOn
  obtain ⟨b, -, hb⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty q.continuous.continuousOn
  exact ⟨q.p a, q.p b, q.pos a, fun x => ⟨ha (Set.mem_univ x), hb (Set.mem_univ x)⟩⟩

/-- The bounded positive reference with density `p`. -/
noncomputable def reference : BoundedPositiveReference d where
  density := q.p
  measurable_density := q.continuous.measurable
  lower := Classical.choose q.exists_bounds
  upper := Classical.choose (Classical.choose_spec q.exists_bounds)
  lower_pos := (Classical.choose_spec (Classical.choose_spec q.exists_bounds)).1
  lower_le := Filter.Eventually.of_forall fun x =>
    ((Classical.choose_spec (Classical.choose_spec q.exists_bounds)).2 x).1
  le_upper := Filter.Eventually.of_forall fun x =>
    ((Classical.choose_spec (Classical.choose_spec q.exists_bounds)).2 x).2
  mass_one := q.mass

theorem reference_measure :
    q.reference.measure = (densityMeasure q.toAbsoluteDensity : Measure (Torus d)) := by
  rw [densityMeasure_coe]
  unfold BoundedPositiveReference.measure
  congr 1
  funext x
  show ENNReal.ofReal (q.p x) = ENNReal.ofReal (√(q.p x) ^ 2)
  rw [Real.sq_sqrt (q.pos x).le]

theorem integrable_of_continuous {f : Torus d → ℝ} (hf : Continuous f) :
    Integrable f (haar d) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Dilution is admissible: `0 < ε < 1` and `ε ρ < q` pointwise. -/
def Admissible (q ρ : SmoothPositiveProbability d) (ε : ℝ) : Prop :=
  0 < ε ∧ ε < 1 ∧ ∀ x, ε * ρ.p x < q.p x

/-- The compensating species `(q - ε ρ)/(1 - ε)`. -/
noncomputable def dilutedDensity (q ρ : SmoothPositiveProbability d) (ε : ℝ)
    (h : Admissible q ρ ε) : SmoothPositiveProbability d where
  p := fun x => (q.p x - ε * ρ.p x) / (1 - ε)
  smooth := by
    have h1 : ContDiff ℝ ∞ ((fun x => q.p x - ε * ρ.p x) ∘ torusLift) :=
      q.smooth.sub (contDiff_const.mul ρ.smooth)
    exact h1.div_const (1 - ε)
  pos := fun x => div_pos (sub_pos.2 (h.2.2 x)) (sub_pos.2 h.2.1)
  mass := by
    have h1 : 1 - ε ≠ 0 := (sub_pos.2 h.2.1).ne'
    rw [integral_div, integral_sub (integrable_of_continuous q.continuous)
      ((integrable_of_continuous ρ.continuous).const_mul ε), integral_const_mul, q.mass, ρ.mass]
    field_simp

open Classical in
/-- The binary dilution family: weights `ε, 1 - ε`, densities `ρ` and `(q - ε ρ)/(1 - ε)`,
defined as the one-species family `q` outside the admissible range. -/
noncomputable def binaryDilution (q ρ : SmoothPositiveProbability d) (ε : ℝ) :
    SpeciesFamily d :=
  if h : Admissible q ρ ε then
    SpeciesFamily.twoSpecies ε h.1 h.2.1 ρ.toAbsoluteDensity
      (dilutedDensity q ρ ε h).toAbsoluteDensity
  else SpeciesFamily.single q.toAbsoluteDensity

open Classical in
theorem binaryDilution_of_admissible {q ρ : SmoothPositiveProbability d} {ε : ℝ}
    (h : Admissible q ρ ε) :
    binaryDilution q ρ ε = SpeciesFamily.twoSpecies ε h.1 h.2.1 ρ.toAbsoluteDensity
      (dilutedDensity q ρ ε h).toAbsoluteDensity := by
  simp only [binaryDilution, h, ↓reduceDIte]

theorem absoluteDensity_ext {a b : AbsoluteDensity d} (h : a.sqrt = b.sqrt) : a = b := by
  cases a; cases b; cases h; rfl

theorem barycenter_twoSpecies {q ρ : SmoothPositiveProbability d} {ε : ℝ}
    (h : Admissible q ρ ε) :
    barycenter (SpeciesFamily.twoSpecies ε h.1 h.2.1 ρ.toAbsoluteDensity
      (dilutedDensity q ρ ε h).toAbsoluteDensity) = q.toAbsoluteDensity := by
  refine absoluteDensity_ext ?_
  funext x
  have h1 : (1 - ε) ≠ 0 := (sub_pos.2 h.2.1).ne'
  show Real.sqrt (∑ s : Fin 2, _) = _
  rw [Fin.sum_univ_two]
  simp only [SpeciesFamily.twoSpecies, toAbsoluteDensity, dilutedDensity, Fin.val_zero,
    Fin.val_one, one_ne_zero, ↓reduceIte]
  rw [Real.sq_sqrt (ρ.pos x).le, Real.sq_sqrt (div_pos (sub_pos.2 (h.2.2 x)) (sub_pos.2 h.2.1)).le]
  congr 1
  field_simp
  ring


/-! ### Smooth calculus for relative square roots -/

theorem div_smooth (q p : SmoothPositiveProbability d) :
    IsSmoothPeriodic fun x => p.p x / q.p x := by
  have h : ContDiff ℝ ∞ ((fun x => p.p x / q.p x) ∘ torusLift) :=
    p.smooth.div q.smooth (fun z => (q.pos _).ne')
  exact h

theorem div_pos' (q p : SmoothPositiveProbability d) (x : Torus d) : 0 < p.p x / q.p x :=
  div_pos (p.pos x) (q.pos x)

/-- The relative square root `√(p/q)` as a smooth function. -/
noncomputable def relRoot (q p : SmoothPositiveProbability d) : Torus d → ℝ :=
  fun x => √(p.p x / q.p x)

theorem relRoot_smooth (q p : SmoothPositiveProbability d) : IsSmoothPeriodic (relRoot q p) :=
  DGPS.Lipschitz.isSmoothPeriodic_sqrt (div_smooth q p) (div_pos' q p)

theorem relRoot_mul_sqrt (q p : SmoothPositiveProbability d) (x : Torus d) :
    relRoot q p x * √(q.p x) = √(p.p x) := by
  unfold relRoot
  rw [← Real.sqrt_mul (div_pos' q p x).le, div_mul_cancel₀ _ (q.pos x).ne']

theorem score_diff_eq (q p : SmoothPositiveProbability d) (x : Torus d) :
    (2 : ℝ) • smoothGrad (fun y => √(p.p y)) x
        - √(p.p x) • ((2 * (√(q.p x))⁻¹) • smoothGrad (fun y => √(q.p y)) x)
      = (2 * √(q.p x)) • smoothGrad (relRoot q p) x := by
  have hw : 0 < √(q.p x) := Real.sqrt_pos.2 (q.pos x)
  ext j
  have hfun : (fun y => relRoot q p y * √(q.p y)) = fun y => √(p.p y) :=
    funext fun y => relRoot_mul_sqrt q p y
  have key := coordPartial_mul (relRoot_smooth q p) q.sqrt_smooth j x
  rw [hfun] at key
  simp only [PiLp.sub_apply, PiLp.smul_apply, smoothGrad_apply, smul_eq_mul]
  rw [key, ← relRoot_mul_sqrt q p x]
  field_simp
  ring


theorem norm_sq_two_sqrt_smul (q : SmoothPositiveProbability d) (v : Tangent d) (x : Torus d) :
    ‖(2 * √(q.p x)) • v‖ ^ 2 = 4 * q.p x * ‖v‖ ^ 2 := by
  have h0 : 0 ≤ √(q.p x) := Real.sqrt_nonneg _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow,
    Real.sq_sqrt (q.pos x).le]
  ring

theorem scoreInformation_eq {F : SpeciesFamily d} {q p : SmoothPositiveProbability d}
    {s : Fin F.count} (hb : barycenter F = q.toAbsoluteDensity)
    (hs : F.density s = p.toAbsoluteDensity) :
    F.scoreInformation s =
      ∫⁻ x, ENNReal.ofReal (4 * q.p x * ‖smoothGrad (relRoot q p) x‖ ^ 2) ∂haar d := by
  have h1 : IsWeakGradient p.toAbsoluteDensity.sqrt (F.sqrtGradient s) := by
    have := F.isWeakGradient_sqrtGradient s
    rwa [hs] at this
  have h2 : IsWeakGradient q.toAbsoluteDensity.sqrt F.barycenterWeakGrad := by
    have := F.isWeakGradient_barycenterWeakGrad
    rwa [hb] at this
  have e1 := h1.ae_eq p.sqrt_smooth.isWeakGradient
  have e2 := h2.ae_eq q.sqrt_smooth.isWeakGradient
  unfold SpeciesFamily.scoreInformation
  refine lintegral_congr_ae ?_
  filter_upwards [e1, e2] with x hx1 hx2
  have hsc : F.score x = (2 * (√(q.p x))⁻¹) • smoothGrad (fun y => √(q.p y)) x := by
    rw [SpeciesFamily.score_eq, hb, hx2]
    rfl
  have hd : F.scoreDifference s x = (2 * √(q.p x)) • smoothGrad (relRoot q p) x := by
    rw [← score_diff_eq q p x]
    unfold SpeciesFamily.scoreDifference
    rw [hsc, hx1, hs]
    rfl
  rw [hd, norm_sq_two_sqrt_smul]


/-- The probability measure `p m` of a smooth positive probability density. -/
noncomputable def meas (p : SmoothPositiveProbability d) : Measure (Torus d) :=
  (densityMeasure p.toAbsoluteDensity : Measure (Torus d))

theorem meas_eq_withDensity (q p : SmoothPositiveProbability d) :
    p.meas = q.reference.measure.withDensity fun x => ENNReal.ofReal (p.p x / q.p x) := by
  have hq : Measurable fun x => ENNReal.ofReal (q.p x) :=
    ENNReal.measurable_ofReal.comp q.continuous.measurable
  have hr : Measurable fun x => ENNReal.ofReal (p.p x / q.p x) :=
    ENNReal.measurable_ofReal.comp (div_smooth q p).continuous_torus.measurable
  unfold meas BoundedPositiveReference.measure
  rw [densityMeasure_coe]
  show _ = ((haar d).withDensity fun x => ENNReal.ofReal (q.p x)).withDensity _
  rw [← withDensity_mul _ hq hr]
  congr 1
  funext x
  show ENNReal.ofReal (√(p.p x) ^ 2) = ENNReal.ofReal (q.p x) * ENNReal.ofReal (p.p x / q.p x)
  rw [Real.sq_sqrt (p.pos x).le, ← ENNReal.ofReal_mul (q.pos x).le, mul_div_cancel₀ _ (q.pos x).ne']

theorem meas_ac (q p : SmoothPositiveProbability d) : p.meas ≪ q.reference.measure := by
  rw [meas_eq_withDensity q p]
  exact withDensity_absolutelyContinuous _ _

theorem relativeSqrt_ae_eq_relRoot (q p : SmoothPositiveProbability d) :
    relativeSqrt p.meas q.reference =ᵐ[haar d] relRoot q p := by
  have hr : Measurable fun x => ENNReal.ofReal (p.p x / q.p x) :=
    ENNReal.measurable_ofReal.comp (div_smooth q p).continuous_torus.measurable
  have h1 := Measure.rnDeriv_withDensity q.reference.measure hr
  rw [← meas_eq_withDensity q p] at h1
  filter_upwards [q.reference.haar_ac_measure.ae_le h1] with x hx
  unfold relativeSqrt relRoot
  rw [hx, ENNReal.toReal_ofReal (div_pos' q p x).le]

/-- The integrand of the relative Fisher information `4 q |∇ √(p/q)|²`. -/
noncomputable def fisherDensity (q p : SmoothPositiveProbability d) (x : Torus d) : ℝ :=
  4 * q.p x * ‖smoothGrad (relRoot q p) x‖ ^ 2

theorem fisherDensity_nonneg (q p : SmoothPositiveProbability d) (x : Torus d) :
    0 ≤ fisherDensity q p x := by
  unfold fisherDensity
  have := q.pos x
  positivity

theorem fisherDensity_continuous (q p : SmoothPositiveProbability d) :
    Continuous (fisherDensity q p) := by
  unfold fisherDensity
  exact (continuous_const.mul q.continuous).mul
    ((relRoot_smooth q p).continuous_smoothGrad.norm.pow 2)

theorem ordinaryRelativeFisher_smooth (q p : SmoothPositiveProbability d) :
    ordinaryRelativeFisher p.meas q.reference =
      ∫⁻ x, ENNReal.ofReal (fisherDensity q p x) ∂haar d := by
  have hg : IsWeakGradient (relativeSqrt p.meas q.reference) (smoothGrad (relRoot q p)) :=
    (relRoot_smooth q p).isWeakGradient.congr_ae (relativeSqrt_ae_eq_relRoot q p).symm
      (Filter.EventuallyEq.refl _ _)
  rw [ordinaryRelativeFisher_eq (meas_ac q p) hg]
  unfold BoundedPositiveReference.measure
  have hq : Measurable fun x => ENNReal.ofReal (q.reference.density x) :=
    ENNReal.measurable_ofReal.comp q.continuous.measurable
  have hm : Measurable fun x => ‖smoothGrad (relRoot q p) x‖ₑ ^ 2 :=
    ((relRoot_smooth q p).continuous_smoothGrad.measurable.enorm).pow_const 2
  rw [lintegral_withDensity_eq_lintegral_mul _ hq hm, ← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_congr fun x => ?_
  show 4 * (ENNReal.ofReal (q.p x) * ‖smoothGrad (relRoot q p) x‖ₑ ^ 2) =
    ENNReal.ofReal (4 * q.p x * ‖smoothGrad (relRoot q p) x‖ ^ 2)
  have := q.pos x
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.ofReal_ofNat, mul_assoc]


theorem integral_ratio (q p : SmoothPositiveProbability d) :
    ∫ x, p.p x / q.p x ∂q.reference.measure = 1 := by
  unfold BoundedPositiveReference.measure
  have hq : Measurable fun x => ENNReal.ofReal (q.reference.density x) :=
    ENNReal.measurable_ofReal.comp q.continuous.measurable
  rw [integral_withDensity_eq_integral_toReal_smul hq
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have : (fun x => (ENNReal.ofReal (q.reference.density x)).toReal • (p.p x / q.p x)) = p.p := by
    funext x
    show (ENNReal.ofReal (q.p x)).toReal • (p.p x / q.p x) = p.p x
    rw [ENNReal.toReal_ofReal (q.pos x).le, smul_eq_mul, mul_div_cancel₀ _ (q.pos x).ne']
  rw [this, p.mass]

theorem relativeEntropy_smooth (q p : SmoothPositiveProbability d) :
    relativeEntropy p.meas q.reference.measure =
      ∫⁻ x, ENNReal.ofReal (p.p x / q.p x * Real.log (p.p x / q.p x) - p.p x / q.p x + 1)
        ∂q.reference.measure := by
  rw [meas_eq_withDensity q p, relativeEntropy_withDensity
    (Filter.Eventually.of_forall fun x => (div_pos' q p x).le)
    (div_smooth q p).continuous_torus.measurable.aemeasurable]
  exact entropy_mass_one (integral_ratio q p)

theorem relativeEntropy_le (q p : SmoothPositiveProbability d) {K : ℝ}
    (h : ∀ x, (p.p x / q.p x - 1) ^ 2 ≤ K) :
    relativeEntropy p.meas q.reference.measure ≤ ENNReal.ofReal K := by
  rw [relativeEntropy_smooth]
  calc _ ≤ ∫⁻ _, ENNReal.ofReal K ∂q.reference.measure := by
        refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
        have hv := div_pos' q p x
        have hl := Real.log_le_sub_one_of_pos hv
        have : p.p x / q.p x * Real.log (p.p x / q.p x) ≤ p.p x / q.p x * (p.p x / q.p x - 1) :=
          mul_le_mul_of_nonneg_left hl hv.le
        nlinarith [h x]
    _ = ENNReal.ofReal K := by simp

/-! ### Estimates for the compensating species -/

theorem exists_ratio_bound (q p : SmoothPositiveProbability d) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ x, p.p x / q.p x ≤ R := by
  obtain ⟨b, -, hb⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (div_smooth q p).continuous_torus.continuousOn
  exact ⟨max 1 (p.p b / q.p b), le_max_left _ _,
    fun x => (hb (Set.mem_univ x)).trans (le_max_right _ _)⟩

theorem exists_grad_bound (q p : SmoothPositiveProbability d) :
    ∃ G : ℝ, ∀ x, ‖smoothGrad (fun y => p.p y / q.p y) x‖ ≤ G := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (div_smooth q p).continuous_smoothGrad.continuousOn
  exact ⟨C, fun x => hC x (Set.mem_univ x)⟩

open Classical in
/-- The compensating species as a total function of `ε` (equal to `q` when not admissible). -/
noncomputable def dilution (q ρ : SmoothPositiveProbability d) (ε : ℝ) :
    SmoothPositiveProbability d :=
  if h : Admissible q ρ ε then dilutedDensity q ρ ε h else q

open Classical in
theorem dilution_of_admissible {q ρ : SmoothPositiveProbability d} {ε : ℝ}
    (h : Admissible q ρ ε) : dilution q ρ ε = dilutedDensity q ρ ε h := by
  simp only [dilution, h, ↓reduceDIte]

theorem dilution_ratio {q ρ : SmoothPositiveProbability d} {ε : ℝ} (h : Admissible q ρ ε)
    (x : Torus d) :
    (dilution q ρ ε).p x / q.p x = 1 / (1 - ε) - ε / (1 - ε) * (ρ.p x / q.p x) := by
  have h1 : (1 - ε) ≠ 0 := (sub_pos.2 h.2.1).ne'
  have h2 := (q.pos x).ne'
  rw [dilution_of_admissible h]
  show (q.p x - ε * ρ.p x) / (1 - ε) / q.p x = _
  field_simp

theorem dilution_entropy_le {q ρ : SmoothPositiveProbability d} {R : ℝ} (hR1 : 1 ≤ R)
    (hR : ∀ x, ρ.p x / q.p x ≤ R) {ε : ℝ} (h : Admissible q ρ ε) (hε : ε ≤ 1 / 2) :
    relativeEntropy (dilution q ρ ε).meas q.reference.measure ≤
      ENNReal.ofReal (4 * (1 + R) ^ 2 * ε ^ 2) := by
  refine relativeEntropy_le q _ fun x => ?_
  have h1 : 0 < 1 - ε := sub_pos.2 h.2.1
  have hr := div_pos' q ρ x
  have hrR := hR x
  have e : (dilution q ρ ε).p x / q.p x - 1 = ε * (1 - ρ.p x / q.p x) / (1 - ε) := by
    rw [dilution_ratio h]; field_simp; ring
  rw [e, div_pow, div_le_iff₀ (by positivity)]
  have h3 : (1 - ρ.p x / q.p x) ^ 2 ≤ (1 + R) ^ 2 := by nlinarith
  have h4 : (1 / 2 : ℝ) ≤ 1 - ε := by linarith
  have h5 : (1 / 4 : ℝ) ≤ (1 - ε) ^ 2 := by nlinarith
  have h6 : 0 ≤ ε := h.1.le
  calc (ε * (1 - ρ.p x / q.p x)) ^ 2 = ε ^ 2 * (1 - ρ.p x / q.p x) ^ 2 := by ring
    _ ≤ ε ^ 2 * (1 + R) ^ 2 := by gcongr
    _ ≤ 4 * (1 + R) ^ 2 * ε ^ 2 * (1 - ε) ^ 2 := by
        have : 0 ≤ ε ^ 2 * (1 + R) ^ 2 := by positivity
        nlinarith

theorem relRoot_dilution_grad {q ρ : SmoothPositiveProbability d} {ε : ℝ} (h : Admissible q ρ ε)
    (x : Torus d) :
    smoothGrad (relRoot q (dilution q ρ ε)) x =
      (-(ε / (1 - ε)) / (2 * √((dilution q ρ ε).p x / q.p x))) •
        smoothGrad (fun y => ρ.p y / q.p y) x := by
  have hfun : relRoot q (dilution q ρ ε) =
      fun y => √(1 / (1 - ε) - ε / (1 - ε) * (ρ.p y / q.p y)) := by
    funext y
    unfold relRoot
    rw [dilution_ratio h]
  have hsm : IsSmoothPeriodic fun y => 1 / (1 - ε) - ε / (1 - ε) * (ρ.p y / q.p y) :=
    contDiff_const.sub (contDiff_const.mul (div_smooth q ρ))
  have hpos : ∀ y, 0 < 1 / (1 - ε) - ε / (1 - ε) * (ρ.p y / q.p y) := fun y => by
    rw [← dilution_ratio h]; exact div_pos' q _ y
  have hr1 : DifferentiableAt ℝ ((fun y => ρ.p y / q.p y) ∘ torusLift) (SharpLSI.secT x) :=
    ((div_smooth q ρ).differentiable (by simp)) _
  have hder : ∀ j, coordPartial j (fun y => 1 / (1 - ε) - ε / (1 - ε) * (ρ.p y / q.p y)) x =
      -(ε / (1 - ε)) * coordPartial j (fun y => ρ.p y / q.p y) x := by
    intro j
    show fderiv ℝ ((fun y => 1 / (1 - ε) - ε / (1 - ε) * (ρ.p y / q.p y)) ∘ torusLift)
      (SharpLSI.secT x) (Pi.single j 1) = _
    have : ((fun y => 1 / (1 - ε) - ε / (1 - ε) * (ρ.p y / q.p y)) ∘ torusLift) =
        fun z => 1 / (1 - ε) - ε / (1 - ε) * ((fun y => ρ.p y / q.p y) ∘ torusLift) z := rfl
    rw [this, fderiv_const_sub, fderiv_const_mul hr1]
    simp [coordPartial]
  ext j
  rw [hfun]
  simp only [smoothGrad_apply, PiLp.smul_apply, smul_eq_mul]
  rw [DGPS.Lipschitz.coordPartial_sqrt hsm hpos j x, hder j]
  have : (dilution q ρ ε).p x / q.p x = 1 / (1 - ε) - ε / (1 - ε) * (ρ.p x / q.p x) :=
    dilution_ratio h x
  rw [this]
  ring


theorem dilution_fisher_le {q ρ : SmoothPositiveProbability d} {R G M : ℝ}
    (hR : ∀ x, ρ.p x / q.p x ≤ R) (hG : ∀ x, ‖smoothGrad (fun y => ρ.p y / q.p y) x‖ ≤ G)
    (hM : ∀ x, q.p x ≤ M) {ε : ℝ} (h : Admissible q ρ ε) (hεR : ε * R ≤ 1 / 2)
    (hε : ε ≤ 1 / 2) :
    ∫⁻ x, ENNReal.ofReal (fisherDensity q (dilution q ρ ε) x) ∂haar d ≤
      ENNReal.ofReal (8 * M * G ^ 2 * ε ^ 2) := by
  have h1 : 0 < 1 - ε := sub_pos.2 h.2.1
  have h0 : 0 < ε := h.1
  calc _ ≤ ∫⁻ _, ENNReal.ofReal (8 * M * G ^ 2 * ε ^ 2) ∂haar d := by
        refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
        have hr := div_pos' q ρ x
        have hrR := hR x
        have hφ : (1 / 2 : ℝ) ≤ (dilution q ρ ε).p x / q.p x := by
          rw [dilution_ratio h]
          have : 1 / (1 - ε) - ε / (1 - ε) * (ρ.p x / q.p x) = (1 - ε * (ρ.p x / q.p x)) / (1 - ε) := by
            field_simp
          rw [this, le_div_iff₀ h1]
          nlinarith
        have hφ0 : 0 < (dilution q ρ ε).p x / q.p x := div_pos' q _ x
        have hGn : 0 ≤ G := (norm_nonneg _).trans (hG x)
        have hq := q.pos x
        have hMx := hM x
        have hM0 : 0 ≤ M := hq.le.trans hMx
        unfold fisherDensity
        rw [relRoot_dilution_grad h x, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, div_pow]
        have hs : √((dilution q ρ ε).p x / q.p x) ^ 2 = (dilution q ρ ε).p x / q.p x :=
          Real.sq_sqrt hφ0.le
        rw [mul_pow, hs, neg_sq, div_pow]
        have hk : ε ^ 2 / (1 - ε) ^ 2 / (2 ^ 2 * ((dilution q ρ ε).p x / q.p x)) ≤ 2 * ε ^ 2 := by
          have h5 : (1 / 4 : ℝ) ≤ (1 - ε) ^ 2 := by nlinarith
          rw [div_le_iff₀ (by positivity), div_le_iff₀ (by positivity)]
          nlinarith [sq_nonneg ε, mul_nonneg (sq_nonneg ε) (sub_nonneg.2 h5),
            mul_nonneg (sq_nonneg ε) (sub_nonneg.2 hφ)]
        have hv : ‖smoothGrad (fun y => ρ.p y / q.p y) x‖ ^ 2 ≤ G ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hG x) 2
        calc 4 * q.p x * (ε ^ 2 / (1 - ε) ^ 2 / (2 ^ 2 * ((dilution q ρ ε).p x / q.p x)) *
              ‖smoothGrad (fun y => ρ.p y / q.p y) x‖ ^ 2)
            ≤ 4 * M * (2 * ε ^ 2 * G ^ 2) := by gcongr
          _ = 8 * M * G ^ 2 * ε ^ 2 := by ring
    _ = _ := by simp

theorem gap_binaryDilution (A : InteractionData d) {q ρ : SmoothPositiveProbability d} {ε : ℝ}
    (h : Admissible q ρ ε) (hG : scalarGap A q.toAbsoluteDensity = 0) :
    (speciesGap A (binaryDilution q ρ ε) : ℝ≥0∞) =
      ENNReal.ofReal ε * relativeEntropy ρ.meas q.reference.measure +
      ENNReal.ofReal (1 - ε) * relativeEntropy (dilution q ρ ε).meas q.reference.measure := by
  rw [binaryDilution_of_admissible h, speciesGap_decomposition, barycenter_twoSpecies h, hG]
  show ((0 : ℝ≥0) : ℝ≥0∞) + ∑ s : Fin 2, _ = _
  rw [Fin.sum_univ_two, ← reference_measure, dilution_of_admissible h]
  simp [SpeciesFamily.twoSpecies, meas]

theorem dissipation_binaryDilution (A : InteractionData d) (b : AbsoluteDrift A)
    {q ρ : SmoothPositiveProbability d} {ε : ℝ}
    (h : Admissible q ρ ε) (hD : scalarDissipation A b q.toAbsoluteDensity = 0) :
    speciesDissipation A b (binaryDilution q ρ ε) =
      ENNReal.ofReal ε * ∫⁻ x, ENNReal.ofReal (fisherDensity q ρ x) ∂haar d +
      ENNReal.ofReal (1 - ε) *
        ∫⁻ x, ENNReal.ofReal (fisherDensity q (dilution q ρ ε) x) ∂haar d := by
  have hF := binaryDilution_of_admissible h
  have hb := barycenter_twoSpecies h
  rw [hF, (speciesDissipation_decomposition A b _).2, hb, hD]
  show (0 : ℝ≥0∞) + ∑ s : Fin 2, _ = _
  rw [Fin.sum_univ_two, zero_add]
  congr 2
  · exact scoreInformation_eq (q := q) (p := ρ) (s := 0) hb (by simp [SpeciesFamily.twoSpecies])
  · rw [dilution_of_admissible h]
    exact scoreInformation_eq (q := q) (p := dilutedDensity q ρ ε h) (s := 1) hb
      (by simp [SpeciesFamily.twoSpecies])

/-! ### The family quotient -/

theorem real_limit {i h C : ℝ} (hh : 0 < h) {a b : ℝ → ℝ}
    (ha : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ a ε ∧ a ε ≤ C * ε ^ 2)
    (hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ b ε ∧ b ε ≤ C * ε ^ 2) :
    Tendsto (fun ε => (ε * i + (1 - ε) * a ε) / (2 * (ε * h + (1 - ε) * b ε))) (𝓝[>] 0)
      (𝓝 (i / (2 * h))) := by
  have key : ∀ {c : ℝ → ℝ}, (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ c ε ∧ c ε ≤ C * ε ^ 2) →
      Tendsto (fun ε => c ε / ε) (𝓝[>] 0) (𝓝 0) := by
    intro c hc
    have hlim : Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun ε : ℝ => C * ε) (𝓝 0) (𝓝 (C * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      simpa using this.mono_left nhdsWithin_le_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards [hc, self_mem_nhdsWithin] with ε h1 h2
      exact div_nonneg h1.1 (le_of_lt h2)
    · filter_upwards [hc, self_mem_nhdsWithin] with ε h1 (h2 : 0 < ε)
      rw [div_le_iff₀ h2]
      nlinarith [h1.2]
  have hu := key ha
  have hv := key hb
  have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hmain : Tendsto (fun ε : ℝ => (i + (1 - ε) * (a ε / ε)) / (2 * (h + (1 - ε) * (b ε / ε))))
      (𝓝[>] 0) (𝓝 ((i + (1 - 0) * 0) / (2 * (h + (1 - 0) * 0)))) := by
    refine Tendsto.div ?_ ?_ ?_
    · exact tendsto_const_nhds.add ((tendsto_const_nhds.sub hε).mul hu)
    · exact tendsto_const_nhds.mul (tendsto_const_nhds.add ((tendsto_const_nhds.sub hε).mul hv))
    · simpa using hh.ne'
  simp only [sub_zero, one_mul, add_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (h2 : 0 < ε)
  have e1 : ε * i + (1 - ε) * a ε = ε * (i + (1 - ε) * (a ε / ε)) := by field_simp
  have e2 : 2 * (ε * h + (1 - ε) * b ε) = ε * (2 * (h + (1 - ε) * (b ε / ε))) := by
    field_simp
  rw [e1, e2, mul_div_mul_left _ _ h2.ne']

theorem fisher_lt_top (q p : SmoothPositiveProbability d) :
    ∫⁻ x, ENNReal.ofReal (fisherDensity q p x) ∂haar d < ⊤ := by
  obtain ⟨C, hC⟩ := (isCompact_univ.bddAbove_image
    (fisherDensity_continuous q p).continuousOn : BddAbove (fisherDensity q p '' Set.univ))
  calc _ ≤ ∫⁻ _, ENNReal.ofReal C ∂haar d :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hC ⟨x, Set.mem_univ _, rfl⟩)
    _ < ⊤ := by simp

theorem entropy_lt_top (q p : SmoothPositiveProbability d) :
    relativeEntropy p.meas q.reference.measure < ⊤ := by
  obtain ⟨R, -, hR⟩ := exists_ratio_bound q p
  refine lt_of_le_of_lt (relativeEntropy_le q p (K := (1 + R) ^ 2) fun x => ?_) (by simp)
  have h1 := div_pos' q p x
  have h2 := hR x
  nlinarith

theorem ennreal_quot {ε i h a b : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (hi : 0 ≤ i) (hh : 0 < h)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal ((ε * i + (1 - ε) * a) / (2 * (ε * h + (1 - ε) * b))) =
      (ENNReal.ofReal ε * ENNReal.ofReal i + ENNReal.ofReal (1 - ε) * ENNReal.ofReal a) /
        (2 * (ENNReal.ofReal ε * ENNReal.ofReal h + ENNReal.ofReal (1 - ε) * ENNReal.ofReal b)) := by
  have h2 : 0 < 1 - ε := sub_pos.2 h1
  have hden : 0 < 2 * (ε * h + (1 - ε) * b) := by positivity
  rw [ENNReal.ofReal_div_of_pos hden, ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul h0.le,
    ENNReal.ofReal_mul h2.le, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul h0.le, ENNReal.ofReal_mul h2.le, ENNReal.ofReal_ofNat]

theorem family_quotient (A : InteractionData d) (b : AbsoluteDrift A)
    (q ρ : SmoothPositiveProbability d) (hG : scalarGap A q.toAbsoluteDensity = 0)
    (hD : scalarDissipation A b q.toAbsoluteDensity = 0)
    (hH : 0 < relativeEntropy ρ.meas q.reference.measure) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      (∀ ε : ℝ, 0 < ε → ε < ε₀ →
        Admissible q ρ ε ∧ barycenter (binaryDilution q ρ ε) = q.toAbsoluteDensity ∧
          0 < speciesGap A (binaryDilution q ρ ε)) ∧
      Tendsto (fun ε => speciesQuotient A b (binaryDilution q ρ ε)) (𝓝[>] 0)
        (𝓝 (ordinaryRelativeFisher ρ.meas q.reference /
          (2 * relativeEntropy ρ.meas q.reference.measure))) := by
  obtain ⟨R, hR1, hR⟩ := exists_ratio_bound q ρ
  obtain ⟨G, hGb⟩ := exists_grad_bound q ρ
  obtain ⟨m, M, hm, hmM⟩ := q.exists_bounds
  have hR0 : 0 < R := by linarith
  have hM0 : 0 ≤ M := hm.le.trans ((hmM 0).1.trans (hmM 0).2)
  have hadm : ∀ ε : ℝ, 0 < ε → ε < 1 / (2 * R) → Admissible q ρ ε ∧ ε * R ≤ 1 / 2 ∧ ε ≤ 1 / 2 := by
    intro ε h0 h1
    have h2 : ε * R < 1 / 2 := by
      rw [lt_div_iff₀ (by positivity)] at h1
      linarith
    have h3 : ε ≤ 1 / 2 := by nlinarith
    refine ⟨⟨h0, by linarith, fun x => ?_⟩, h2.le, h3⟩
    have hx := hR x
    have hq := q.pos x
    rw [div_le_iff₀ hq] at hx
    nlinarith
  set H := relativeEntropy ρ.meas q.reference.measure with hHdef
  set I := ∫⁻ x, ENNReal.ofReal (fisherDensity q ρ x) ∂haar d with hIdef
  have hHt : H ≠ ⊤ := (entropy_lt_top q ρ).ne
  have hIt : I ≠ ⊤ := (fisher_lt_top q ρ).ne
  have hHe : H = ENNReal.ofReal H.toReal := (ENNReal.ofReal_toReal hHt).symm
  have hIe : I = ENNReal.ofReal I.toReal := (ENNReal.ofReal_toReal hIt).symm
  have hh0 : 0 < H.toReal := ENNReal.toReal_pos hH.ne' hHt
  refine ⟨1 / (2 * R), by positivity, fun ε h0 h1 => ?_, ?_⟩
  · obtain ⟨hA, -, -⟩ := hadm ε h0 h1
    refine ⟨hA, ?_, ?_⟩
    · rw [binaryDilution_of_admissible hA]; exact barycenter_twoSpecies hA
    · have := gap_binaryDilution A hA hG
      have hpos : 0 < ENNReal.ofReal ε * H := ENNReal.mul_pos (by simpa using h0) hH.ne'
      have : 0 < (speciesGap A (binaryDilution q ρ ε) : ℝ≥0∞) :=
        lt_of_lt_of_le hpos (this ▸ le_self_add)
      exact_mod_cast this
  · -- the limit
    set J : ℝ → ℝ≥0∞ := fun ε => ∫⁻ x, ENNReal.ofReal (fisherDensity q (dilution q ρ ε) x) ∂haar d
      with hJ
    set K : ℝ → ℝ≥0∞ := fun ε => relativeEntropy (dilution q ρ ε).meas q.reference.measure
      with hK
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < 1 / (2 * R) := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / (2 * R) by positivity)] with ε h
      exact h
    have hJb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), J ε ≤ ENNReal.ofReal (8 * M * G ^ 2 * ε ^ 2) := by
      filter_upwards [hev] with ε ⟨h0, h1⟩
      obtain ⟨hA, h2, h3⟩ := hadm ε h0 h1
      exact dilution_fisher_le hR hGb (fun x => (hmM x).2) hA h2 h3
    have hKb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), K ε ≤ ENNReal.ofReal (4 * (1 + R) ^ 2 * ε ^ 2) := by
      filter_upwards [hev] with ε ⟨h0, h1⟩
      obtain ⟨hA, h2, h3⟩ := hadm ε h0 h1
      exact dilution_entropy_le hR1 hR hA h3
    have hlim := real_limit (i := I.toReal) (h := H.toReal) (C := max (8 * M * G ^ 2) (4 * (1 + R) ^ 2))
      (a := fun ε => (J ε).toReal) (b := fun ε => (K ε).toReal) hh0
      (by
        filter_upwards [hJb] with ε h
        refine ⟨ENNReal.toReal_nonneg, ?_⟩
        refine (ENNReal.toReal_le_of_le_ofReal (by positivity) h).trans ?_
        have := mul_le_mul_of_nonneg_right (le_max_left (8 * M * G ^ 2) (4 * (1 + R) ^ 2))
          (sq_nonneg ε)
        linarith)
      (by
        filter_upwards [hKb] with ε h
        refine ⟨ENNReal.toReal_nonneg, ?_⟩
        refine (ENNReal.toReal_le_of_le_ofReal (by positivity) h).trans ?_
        have := mul_le_mul_of_nonneg_right (le_max_right (8 * M * G ^ 2) (4 * (1 + R) ^ 2))
          (sq_nonneg ε)
        linarith)
    have hlim' := (ENNReal.tendsto_ofReal hlim)
    rw [ordinaryRelativeFisher_smooth]
    have htarget : ENNReal.ofReal (I.toReal / (2 * H.toReal)) = I / (2 * H) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num),
        ← hHe, ← hIe]
      simp
    rw [← htarget]
    refine hlim'.congr' ?_
    filter_upwards [hev, hJb, hKb] with ε ⟨h0, h1⟩ hJε hKε
    obtain ⟨hA, -, -⟩ := hadm ε h0 h1
    have hJt : J ε ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hJε
    have hKt : K ε ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKε
    unfold speciesQuotient
    rw [dissipation_binaryDilution A b hA hD, gap_binaryDilution A hA hG]
    rw [ennreal_quot h0 hA.2.1 ENNReal.toReal_nonneg hh0 ENNReal.toReal_nonneg
      ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hIt, ENNReal.ofReal_toReal hHt,
      ENNReal.ofReal_toReal hJt, ENNReal.ofReal_toReal hKt]

end DGPS.Examples.SmoothPositiveProbability

namespace DGPS.Examples

variable {d : ℕ}

/-- **EX017, exact-barycenter binary dilution.**  For a smooth positive equilibrium `q` (scalar gap
and dissipation vanish at `q`) and a smooth positive probability density `ρ` with `H(ρ|q) > 0`,
for all small `ε > 0` the binary family with weights `ε, 1 - ε` and densities `ρ`,
`(q - ε ρ)/(1 - ε)` is admissible, has barycenter exactly `q` and positive gap, and its quotient
tends to `I(ρ|q) / (2 H(ρ|q))` as `ε → 0+`.  Consequently `r_ms ≤ I(ρ|q) / (2 H(ρ|q))` for every
such smooth positive competitor `ρ`; no attainment or uniform weight bound is used. -/
theorem exact_barycenter_binary_dilution (A : InteractionData d) (b : AbsoluteDrift A)
    (q ρ : SmoothPositiveProbability d) (hG : scalarGap A q.toAbsoluteDensity = 0)
    (hD : scalarDissipation A b q.toAbsoluteDensity = 0)
    (hH : 0 < relativeEntropy ρ.meas q.reference.measure) :
    (∃ ε₀ : ℝ, 0 < ε₀ ∧
      (∀ ε : ℝ, 0 < ε → ε < ε₀ →
        SmoothPositiveProbability.Admissible q ρ ε ∧
          barycenter (SmoothPositiveProbability.binaryDilution q ρ ε) = q.toAbsoluteDensity ∧
          0 < speciesGap A (SmoothPositiveProbability.binaryDilution q ρ ε)) ∧
      Tendsto (fun ε => speciesQuotient A b (SmoothPositiveProbability.binaryDilution q ρ ε))
        (𝓝[>] 0)
        (𝓝 (ordinaryRelativeFisher ρ.meas q.reference /
          (2 * relativeEntropy ρ.meas q.reference.measure)))) ∧
    speciesRate A b ≤ ordinaryRelativeFisher ρ.meas q.reference /
      (2 * relativeEntropy ρ.meas q.reference.measure) := by
  obtain ⟨ε₀, h0, hall, hlim⟩ := SmoothPositiveProbability.family_quotient A b q ρ hG hD hH
  refine ⟨⟨ε₀, h0, hall, hlim⟩, ?_⟩
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT h0] with ε hε
  exact speciesRate_le A b _ (hall ε hε.1 hε.2).2.2

end DGPS.Examples
