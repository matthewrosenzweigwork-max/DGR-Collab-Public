import DGPS.Examples.ThreeSpeciesCircle.Model
import DGPS.Circle.QuantitativeLSI
import DGPS.Analysis.CircleLSI
import DGPS.Analysis.RelativeFisher
import DGPS.Foundations.CompactSobolev
import DGPS.Foundations.SobolevEmbedding
import DGPS.Foundations.SobolevEntropy
import DGPS.Foundations.RateArithmetic
import DGPS.Equilibrium.GaussianRate

open MeasureTheory Filter Topology

/-!
# Ordinary optimizers on the circle: information comparison and strict Haar LSI

Ordinary base problem for the three-species circle model (packet STR024).
For `μ_h = threefoldReference h` with `|h| ≤ b`:
* `fisher_le_two_ordinary`: `I_m(ρ) ≤ 2 I(ρ | μ_h) + C`;
* `circleEntropy_le_log_information`: `H(ρ | m) ≤ 6 log (2 + I_m(ρ))`;
* `boundedQuotient_bounds`: bounded ordinary quotient gives bounded `I_m`, `H`;
* `haarLSI_strict_positiveEntropy`: `I − 2 a₀ H ≥ a₀ H² / 6`, hence strict.
-/

open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

theorem abs_cosHarm_le (k : ℕ) (x : Torus 1) : |cosHarm k x| ≤ 1 := by
  unfold cosHarm
  exact (Complex.abs_re_le_norm _).trans (by simp)

theorem integral_referenceDensity_eq_one (h : ℝ) : ∫ x, referenceDensity h x ∂haar 1 = 1 := by
  have := torusIntegral_density_mul h 0
  simp only [mul_zero, cosHarm_zero, mul_one] at this
  rw [this, div_self besselI_zero_pos.ne']

theorem besselI_zero_eq_integral (h : ℝ) :
    besselI 0 h = ∫ x, Real.exp (h * cosHarm 3 x) ∂haar 1 := by
  have h1 := integral_referenceDensity_eq_one h
  unfold referenceDensity at h1
  rw [integral_div, div_eq_one_iff_eq besselI_zero_pos.ne'] at h1
  exact h1.symm

theorem besselI_zero_le (h : ℝ) : besselI 0 h ≤ Real.exp |h| := by
  rw [besselI_zero_eq_integral]
  have : ∀ x : Torus 1, Real.exp (h * cosHarm 3 x) ≤ Real.exp |h| := fun x => by
    apply Real.exp_le_exp.2
    calc h * cosHarm 3 x ≤ |h * cosHarm 3 x| := le_abs_self _
      _ = |h| * |cosHarm 3 x| := abs_mul _ _
      _ ≤ |h| * 1 := mul_le_mul_of_nonneg_left (abs_cosHarm_le 3 x) (abs_nonneg _)
      _ = |h| := mul_one _
  calc ∫ x, Real.exp (h * cosHarm 3 x) ∂haar 1 ≤ ∫ _x, Real.exp |h| ∂haar 1 :=
        integral_mono (integrable_of_continuous_torus (by have := continuous_cosHarm 3; fun_prop))
          (integrable_const _) this
    _ = Real.exp |h| := by simp

theorem exp_neg_le_besselI_zero (h : ℝ) : Real.exp (-|h|) ≤ besselI 0 h := by
  rw [besselI_zero_eq_integral]
  have : ∀ x : Torus 1, Real.exp (-|h|) ≤ Real.exp (h * cosHarm 3 x) := fun x => by
    apply Real.exp_le_exp.2
    have := (abs_le.1 (show |h * cosHarm 3 x| ≤ |h| by
      rw [abs_mul]
      calc |h| * |cosHarm 3 x| ≤ |h| * 1 := mul_le_mul_of_nonneg_left (abs_cosHarm_le 3 x) (abs_nonneg _)
        _ = |h| := mul_one _)).1
    linarith
  calc Real.exp (-|h|) = ∫ _x, Real.exp (-|h|) ∂haar 1 := by simp
    _ ≤ _ := integral_mono (integrable_const _)
        (integrable_of_continuous_torus (by have := continuous_cosHarm 3; fun_prop)) this

theorem referenceDensity_le (h : ℝ) (x : Torus 1) : referenceDensity h x ≤ Real.exp (2 * |h|) := by
  unfold referenceDensity
  rw [div_le_iff₀ besselI_zero_pos]
  calc Real.exp (h * cosHarm 3 x) ≤ Real.exp |h| := by
        apply Real.exp_le_exp.2
        calc h * cosHarm 3 x ≤ |h * cosHarm 3 x| := le_abs_self _
          _ = |h| * |cosHarm 3 x| := abs_mul _ _
          _ ≤ |h| * 1 := mul_le_mul_of_nonneg_left (abs_cosHarm_le 3 x) (abs_nonneg _)
          _ = |h| := mul_one _
    _ = Real.exp (2 * |h|) * Real.exp (-|h|) := by rw [← Real.exp_add]; ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_neg_le_besselI_zero h) (Real.exp_pos _).le

theorem le_referenceDensity (h : ℝ) (x : Torus 1) : Real.exp (-(2 * |h|)) ≤ referenceDensity h x := by
  unfold referenceDensity
  rw [le_div_iff₀ besselI_zero_pos]
  calc Real.exp (-(2 * |h|)) * besselI 0 h ≤ Real.exp (-(2 * |h|)) * Real.exp |h| :=
        mul_le_mul_of_nonneg_left (besselI_zero_le h) (Real.exp_pos _).le
    _ = Real.exp (-|h|) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (h * cosHarm 3 x) := by
        apply Real.exp_le_exp.2
        have := (abs_le.1 (show |h * cosHarm 3 x| ≤ |h| by
          rw [abs_mul]
          calc |h| * |cosHarm 3 x| ≤ |h| * 1 := mul_le_mul_of_nonneg_left (abs_cosHarm_le 3 x) (abs_nonneg _)
            _ = |h| := mul_one _)).1
        linarith

/-- The bounded positive reference `μ_h = q_h m`. -/
noncomputable def ordinaryReference (h : ℝ) : BoundedPositiveReference 1 where
  density := referenceDensity h
  measurable_density := (continuous_referenceDensity h).measurable
  lower := Real.exp (-(2 * |h|))
  upper := Real.exp (2 * |h|)
  lower_pos := Real.exp_pos _
  lower_le := Filter.Eventually.of_forall (le_referenceDensity h)
  le_upper := Filter.Eventually.of_forall (referenceDensity_le h)
  mass_one := integral_referenceDensity_eq_one h

theorem ordinaryReference_measure (h : ℝ) :
    (ordinaryReference h).measure = threefoldReference h := rfl

theorem referenceDensity_pt (h t : ℝ) :
    referenceDensity h (pt t) = Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) / besselI 0 h := by
  simp only [referenceDensity, cosHarm_pt]
  push_cast; rfl

theorem torusLipschitz_referenceDensity (h : ℝ) :
    TorusLipschitzWith (6 * Real.pi * |h| * Real.exp (2 * |h|)) (referenceDensity h) := by
  set L : ℝ := 6 * Real.pi * |h| * Real.exp (2 * |h|) with hL
  have hL0 : 0 ≤ L := by positivity
  set f : ℝ → ℝ := fun t => referenceDensity h (pt t) with hf
  have hd : ∀ t, HasDerivAt f (Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) *
      (h * (-Real.sin (2 * Real.pi * 3 * t) * (2 * Real.pi * 3))) / besselI 0 h) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * 3 * t) (2 * Real.pi * 3) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * Real.pi * 3)
    have := ((h1.cos).const_mul h).exp.div_const (besselI 0 h)
    simpa [hf, referenceDensity_pt] using this
  have hbound : ∀ t, ‖deriv f t‖ ≤ L := by
    intro t
    rw [(hd t).deriv, Real.norm_eq_abs]
    have hI := besselI_zero_pos (h := h)
    have hq : Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) / besselI 0 h ≤ Real.exp (2 * |h|) := by
      have := referenceDensity_le h (pt t)
      rwa [referenceDensity_pt] at this
    have e : Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) *
        (h * (-Real.sin (2 * Real.pi * 3 * t) * (2 * Real.pi * 3))) / besselI 0 h =
        (Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) / besselI 0 h) *
        (h * (-Real.sin (2 * Real.pi * 3 * t) * (2 * Real.pi * 3))) := by ring
    rw [e, abs_mul, abs_of_pos (div_pos (Real.exp_pos _) hI)]
    have hs : |h * (-Real.sin (2 * Real.pi * 3 * t) * (2 * Real.pi * 3))| ≤ |h| * (6 * Real.pi) := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi * 3)]
      have := Real.abs_sin_le_one (2 * Real.pi * 3 * t)
      have h0 : 0 ≤ |h| := abs_nonneg _
      have h2 : |Real.sin (2 * Real.pi * 3 * t)| * (2 * Real.pi * 3) ≤ 6 * Real.pi := by
        nlinarith [Real.pi_pos]
      calc |h| * (|Real.sin (2 * Real.pi * 3 * t)| * (2 * Real.pi * 3)) ≤ |h| * (6 * Real.pi) :=
            mul_le_mul_of_nonneg_left h2 h0
        _ = _ := rfl
    calc _ ≤ Real.exp (2 * |h|) * (|h| * (6 * Real.pi)) :=
          mul_le_mul hq hs (abs_nonneg _) (Real.exp_pos _).le
      _ = L := by rw [hL]; ring
  have hdiff : ∀ t, DifferentiableAt ℝ f t := fun t => (hd t).differentiableAt
  intro x y
  obtain ⟨a, b, rfl, rfl, hab, -⟩ := exists_lifts_one x y
  have := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun t _ => hdiff t) (fun t _ => hbound t) (Set.mem_univ b) (Set.mem_univ a)
  rw [← hab]
  simpa [hf, Real.norm_eq_abs] using this

theorem ordinaryReference_lip (h : ℝ) : (ordinaryReference h).hasPositiveLipschitzDensity :=
  ⟨_, Real.exp (-(2 * |h|)), Real.exp_pos _, le_referenceDensity h, torusLipschitz_referenceDensity h⟩

/-- A bound for the weak gradient of `log` of the reference density. -/
noncomputable def logGradBound (h : ℝ) : ℝ :=
  Real.exp (2 * |h|) * (6 * Real.pi * |h| * Real.exp (2 * |h|))

theorem logGradBound_nonneg (h : ℝ) : 0 ≤ logGradBound h := by unfold logGradBound; positivity

theorem norm_logGrad_le (h : ℝ) : ∀ᵐ x ∂haar 1,
    ‖weakGradient (fun x => Real.log ((ordinaryReference h).density x))
      ((ordinaryReference h).memH1_log (ordinaryReference_lip h)) x‖ ≤ logGradBound h := by
  have hw := (isWeakGradient_weakGradient ((ordinaryReference h).memH1_log (ordinaryReference_lip h))).ae_eq
    (RelativeFisher.isWeakGradient_log (ordinaryReference_lip h))
  filter_upwards [hw] with x hx
  rw [hx, norm_smul, norm_inv]
  have hp : Real.exp (-(2 * |h|)) ≤ ‖referenceDensity h x‖ := by
    rw [Real.norm_eq_abs, abs_of_pos (referenceDensity_pos (h := h) x)]
    exact le_referenceDensity h x
  have h1 : ‖referenceDensity h x‖⁻¹ ≤ Real.exp (2 * |h|) := by
    have := inv_anti₀ (Real.exp_pos _) hp
    rwa [← Real.exp_neg, neg_neg] at this
  have h2 : ‖RelativeFisher.lipGradVec (referenceDensity h) x‖ ≤
      6 * Real.pi * |h| * Real.exp (2 * |h|) := by
    have := RelativeFisher.abs_lipGradVec_le (torusLipschitz_referenceDensity h) x 0
    have hc : ((Real.toNNReal (6 * Real.pi * |h| * Real.exp (2 * |h|) * Real.sqrt ((1:ℕ):ℝ)) : ℝ≥0) : ℝ)
        = 6 * Real.pi * |h| * Real.exp (2 * |h|) := by
      rw [Real.coe_toNNReal _ (by positivity)]; simp
    rw [hc] at this
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
    exact this
  exact mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le

/-- The ordinary Fisher information `I(ρ | μ_h)` of an absolute density against `μ_h`. -/
noncomputable def ordinaryFisher (h : ℝ) (ρ : AbsoluteDensity 1) : ℝ≥0∞ :=
  ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) (ordinaryReference h)

theorem fisher_le_two_ordinary (h : ℝ) (ρ : AbsoluteDensity 1) :
    ENNReal.ofReal (DGPS.Analysis.circleFisherInformation ρ) ≤
      2 * ordinaryFisher h ρ + ENNReal.ofReal (2 * logGradBound h ^ 2) := by
  obtain ⟨-, hint, -, -⟩ := DGPS.Analysis.circle_quantitative_lsi_on_the_absolute_domain ρ
  set G := weakGradient ρ.sqrt ρ.sqrt_mem with hG
  set S := weakGradient (fun x => Real.log ((ordinaryReference h).density x))
    ((ordinaryReference h).memH1_log (ordinaryReference_lip h)) with hS
  have hI : ENNReal.ofReal (DGPS.Analysis.circleFisherInformation ρ) =
      ∫⁻ x, ENNReal.ofReal (4 * ‖G x‖ ^ 2) ∂haar 1 := by
    unfold DGPS.Analysis.circleFisherInformation
    rw [← hG, ← integral_const_mul]
    exact ofReal_integral_eq_lintegral_ofReal (hint.const_mul 4)
      (Filter.Eventually.of_forall fun x => by positivity)
  have hF : ordinaryFisher h ρ = ∫⁻ x, ‖(2 : ℝ) • G x - ρ.sqrt x • S x‖ₑ ^ 2 ∂haar 1 :=
    positiveReference_absolute_identity (ordinaryReference h) (ordinaryReference_lip h) ρ
  have hmass : ∫⁻ x, ENNReal.ofReal (ρ.sqrt x ^ 2) ∂haar 1 = 1 := by
    have h1 : ∫⁻ x, ENNReal.ofReal (ρ.density x) ∂haar 1 = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal ρ.integrable_density
        (Filter.Eventually.of_forall ρ.density_nonneg), ρ.integral_density]
      simp
    exact h1
  have hpt : ∀ᵐ x ∂haar 1, ENNReal.ofReal (4 * ‖G x‖ ^ 2) ≤
      2 * ‖(2 : ℝ) • G x - ρ.sqrt x • S x‖ₑ ^ 2 +
        ENNReal.ofReal (2 * logGradBound h ^ 2) * ENNReal.ofReal (ρ.sqrt x ^ 2) := by
    filter_upwards [norm_logGrad_le h] with x hx
    have hK := logGradBound_nonneg h
    set e := (2 : ℝ) • G x - ρ.sqrt x • S x with he
    have h2G : (2:ℝ) • G x = e + ρ.sqrt x • S x := by rw [he]; abel
    have n1 : 2 * ‖G x‖ ≤ ‖e‖ + |ρ.sqrt x| * logGradBound h := by
      have : ‖(2:ℝ) • G x‖ = 2 * ‖G x‖ := by rw [norm_smul]; norm_num
      rw [← this, h2G]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs]
      gcongr
    have n2 : 4 * ‖G x‖ ^ 2 ≤ 2 * ‖e‖ ^ 2 + 2 * logGradBound h ^ 2 * ρ.sqrt x ^ 2 := by
      have h0 : 0 ≤ |ρ.sqrt x| * logGradBound h := by positivity
      have h3 : (2 * ‖G x‖) ^ 2 ≤ (‖e‖ + |ρ.sqrt x| * logGradBound h) ^ 2 :=
        pow_le_pow_left₀ (by positivity) n1 2
      have h4 : (|ρ.sqrt x| * logGradBound h) ^ 2 = logGradBound h ^ 2 * ρ.sqrt x ^ 2 := by
        rw [mul_pow, sq_abs]; ring
      nlinarith [sq_nonneg (‖e‖ - |ρ.sqrt x| * logGradBound h)]
    calc ENNReal.ofReal (4 * ‖G x‖ ^ 2)
        ≤ ENNReal.ofReal (2 * ‖e‖ ^ 2 + 2 * logGradBound h ^ 2 * ρ.sqrt x ^ 2) :=
          ENNReal.ofReal_le_ofReal n2
      _ = 2 * ‖e‖ₑ ^ 2 + ENNReal.ofReal (2 * logGradBound h ^ 2) * ENNReal.ofReal (ρ.sqrt x ^ 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity), ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
          simp
  rw [hI]
  calc ∫⁻ x, ENNReal.ofReal (4 * ‖G x‖ ^ 2) ∂haar 1
      ≤ ∫⁻ x, (2 * ‖(2 : ℝ) • G x - ρ.sqrt x • S x‖ₑ ^ 2 +
        ENNReal.ofReal (2 * logGradBound h ^ 2) * ENNReal.ofReal (ρ.sqrt x ^ 2)) ∂haar 1 :=
        lintegral_mono_ae hpt
    _ = 2 * ordinaryFisher h ρ + ENNReal.ofReal (2 * logGradBound h ^ 2) := by
        rw [lintegral_add_right' _ (by
          exact (ρ.integrable_density.aemeasurable.ennreal_ofReal).const_mul _),
          lintegral_const_mul' _ _ (by norm_num), ← hF, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hmass,
          mul_one]

instance isProbabilityMeasure_threefoldReference (h : ℝ) :
    IsProbabilityMeasure (threefoldReference h) := (ordinaryReference h).isProbabilityMeasure

/-- The entropy `H(ρ | μ_h)` of an absolute density relative to `μ_h`. -/
noncomputable def ordinaryEntropy (h : ℝ) (ρ : AbsoluteDensity 1) : ℝ≥0∞ :=
  relativeEntropy (densityMeasure ρ : Measure (Torus 1)) (threefoldReference h)

theorem circleEntropy_eq (ρ : AbsoluteDensity 1) :
    DGPS.Analysis.circleEntropy ρ = ∫ x, ρ.density x * Real.log (ρ.density x) ∂haar 1 := by
  rw [← (absoluteDensity_entropy_finite ρ).2.2.2]
  unfold DGPS.Analysis.circleEntropy
  congr 1
  rw [densityMeasure_coe]
  exact (relativeEntropy_withDensity (P := haar 1)
    (Filter.Eventually.of_forall ρ.density_nonneg) ρ.integrable_density.aemeasurable).symm

theorem abs_log_referenceDensity_le (h : ℝ) (x : Torus 1) :
    |Real.log (referenceDensity h x)| ≤ 2 * |h| := by
  rw [abs_le]
  constructor
  · have := Real.log_le_log (Real.exp_pos _) (le_referenceDensity h x)
    rw [Real.log_exp] at this; exact this
  · have := Real.log_le_log (referenceDensity_pos (h := h) x) (referenceDensity_le h x)
    rw [Real.log_exp] at this; exact this

theorem integrable_density_mul_log_reference (h : ℝ) (ρ : AbsoluteDensity 1) :
    Integrable (fun x => ρ.density x * Real.log (referenceDensity h x)) (haar 1) := by
  refine ρ.integrable_density.mul_bdd (c := 2 * |h|) ?_ ?_
  · exact ((continuous_referenceDensity h).log
      (fun x => (referenceDensity_pos (h := h) x).ne')).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_log_referenceDensity_le h x

theorem abs_integral_density_mul_log_reference_le (h : ℝ) (ρ : AbsoluteDensity 1) :
    |∫ x, ρ.density x * Real.log (referenceDensity h x) ∂haar 1| ≤ 2 * |h| := by
  have hb : ∀ x, |ρ.density x * Real.log (referenceDensity h x)| ≤ ρ.density x * (2 * |h|) := by
    intro x
    rw [abs_mul, abs_of_nonneg (ρ.density_nonneg x)]
    exact mul_le_mul_of_nonneg_left (abs_log_referenceDensity_le h x) (ρ.density_nonneg x)
  calc _ ≤ ∫ x, |ρ.density x * Real.log (referenceDensity h x)| ∂haar 1 := abs_integral_le_integral_abs
    _ ≤ ∫ x, ρ.density x * (2 * |h|) ∂haar 1 :=
        integral_mono (integrable_density_mul_log_reference h ρ).abs
          (ρ.integrable_density.mul_const _) hb
    _ = 2 * |h| := by rw [integral_mul_const, ρ.integral_density, one_mul]

theorem ordinaryEntropy_eq (h : ℝ) (ρ : AbsoluteDensity 1) :
    ordinaryEntropy h ρ = ENNReal.ofReal (DGPS.Analysis.circleEntropy ρ -
      ∫ x, ρ.density x * Real.log (referenceDensity h x) ∂haar 1) := by
  set q := referenceDensity h with hq
  have hqm : Measurable q := (continuous_referenceDensity h).measurable
  have hqpos : ∀ x, 0 < q x := fun x => referenceDensity_pos (h := h) x
  set v : Torus 1 → ℝ := fun x => ρ.density x / q x with hv
  have hvm : AEMeasurable v (haar 1) := ρ.integrable_density.aemeasurable.div hqm.aemeasurable
  have hvnn : ∀ x, 0 ≤ v x := fun x => div_nonneg (ρ.density_nonneg x) (hqpos x).le
  have hqv : ∀ x, q x * v x = ρ.density x := fun x => by
    show q x * (ρ.density x / q x) = _
    field_simp [(hqpos x).ne']
  have hν : (densityMeasure ρ : Measure (Torus 1)) =
      (threefoldReference h).withDensity fun x => ENNReal.ofReal (v x) := by
    unfold threefoldReference
    rw [← withDensity_mul₀ hqm.ennreal_ofReal.aemeasurable hvm.ennreal_ofReal, densityMeasure_coe]
    congr 1
    funext x
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hqpos x).le, hqv x]
    rfl
  have hPac : threefoldReference h ≪ haar 1 := withDensity_absolutelyContinuous _ _
  have hmass : ∫ x, v x ∂threefoldReference h = 1 := by
    rw [integral_threefoldReference]
    exact (integral_congr_ae (Filter.Eventually.of_forall hqv)).trans ρ.integral_density
  unfold ordinaryEntropy
  rw [hν, relativeEntropy_withDensity (Filter.Eventually.of_forall hvnn) (hvm.mono_ac hPac),
    entropy_mass_one hmass]
  set F : Torus 1 → ℝ := fun x => v x * Real.log (v x) - v x + 1 with hF
  have hFnn : ∀ x, 0 ≤ F x := fun x => self_mul_log_sub_add_one_nonneg (hvnn x)
  have hΨ : ∀ x, q x * F x = ρ.density x * Real.log (ρ.density x) - ρ.density x * Real.log (q x)
      - ρ.density x + q x := by
    intro x
    rcases eq_or_ne (ρ.density x) 0 with h0 | h0
    · have : v x = 0 := by rw [hv]; simp [h0]
      simp [hF, this, h0]
    · have hvx : v x ≠ 0 := div_ne_zero h0 (hqpos x).ne'
      have : Real.log (v x) = Real.log (ρ.density x) - Real.log (q x) := by
        rw [hv]; exact Real.log_div h0 (hqpos x).ne'
      simp only [hF]
      rw [this]
      have := hqv x
      calc q x * (v x * (Real.log (ρ.density x) - Real.log (q x)) - v x + 1)
          = (q x * v x) * (Real.log (ρ.density x) - Real.log (q x)) - q x * v x + q x := by ring
        _ = _ := by rw [this]; ring
  have hFm : AEMeasurable (fun x => ENNReal.ofReal (F x)) (haar 1) := by
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    exact ((hvm.mul (Real.measurable_log.comp_aemeasurable hvm)).sub hvm).add_const 1
  change ∫⁻ x, ENNReal.ofReal (F x) ∂(haar 1).withDensity (fun x => ENNReal.ofReal (q x)) = _
  rw [lintegral_withDensity_eq_lintegral_mul₀ hqm.ennreal_ofReal.aemeasurable hFm]
  have i4 : Integrable q (haar 1) :=
    (continuous_referenceDensity h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hΨi : Integrable (fun x => ρ.density x * Real.log (ρ.density x) -
      ρ.density x * Real.log (q x) - ρ.density x + q x) (haar 1) :=
    (((absoluteDensity_entropy_finite ρ).1.sub (integrable_density_mul_log_reference h ρ)).sub
      ρ.integrable_density).add i4
  have hΨnn : 0 ≤ᵐ[haar 1] fun x => ρ.density x * Real.log (ρ.density x) -
      ρ.density x * Real.log (q x) - ρ.density x + q x :=
    Filter.Eventually.of_forall fun x => by
      have := mul_nonneg (hqpos x).le (hFnn x)
      rw [hΨ x] at this
      exact this
  have hcongr : ∀ x, (ENNReal.ofReal (q x) * ENNReal.ofReal (F x)) = ENNReal.ofReal
      (ρ.density x * Real.log (ρ.density x) - ρ.density x * Real.log (q x) - ρ.density x + q x) := by
    intro x
    rw [← ENNReal.ofReal_mul (hqpos x).le, hΨ x]
  have hl : ∫⁻ x, ENNReal.ofReal (q x) * ENNReal.ofReal (F x) ∂haar 1 =
      ENNReal.ofReal (∫ x, (ρ.density x * Real.log (ρ.density x) - ρ.density x * Real.log (q x)
        - ρ.density x + q x) ∂haar 1) := by
    rw [ofReal_integral_eq_lintegral_ofReal hΨi hΨnn]
    exact lintegral_congr hcongr
  show ∫⁻ x, ENNReal.ofReal (q x) * ENNReal.ofReal (F x) ∂haar 1 = _
  rw [hl, circleEntropy_eq]
  congr 1
  have i1 := (absoluteDensity_entropy_finite ρ).1
  have i2 := integrable_density_mul_log_reference h ρ
  have i3 := ρ.integrable_density
  have j1 : Integrable (fun x => ρ.density x * Real.log (ρ.density x) -
      ρ.density x * Real.log (q x)) (haar 1) := i1.sub i2
  have j2 : Integrable (fun x => ρ.density x * Real.log (ρ.density x) -
      ρ.density x * Real.log (q x) - ρ.density x) (haar 1) := j1.sub i3
  rw [integral_add j2 i4, integral_sub j1 i3, integral_sub i1 i2,
    ρ.integral_density, integral_referenceDensity_eq_one]
  ring

theorem circleFisherInformation_nonneg (ρ : AbsoluteDensity 1) :
    0 ≤ DGPS.Analysis.circleFisherInformation ρ := by
  unfold DGPS.Analysis.circleFisherInformation
  positivity

theorem circleEntropy_nonneg (ρ : AbsoluteDensity 1) : 0 ≤ DGPS.Analysis.circleEntropy ρ :=
  ENNReal.toReal_nonneg

/-- Entropy is controlled by the logarithm of the information. -/
theorem circleEntropy_le_log_information (ρ : AbsoluteDensity 1) :
    DGPS.Analysis.circleEntropy ρ ≤ 6 * Real.log (2 + DGPS.Analysis.circleFisherInformation ρ) := by
  obtain ⟨-, -, -, h4⟩ := DGPS.Analysis.circle_quantitative_lsi_on_the_absolute_domain ρ
  refine h4.trans ?_
  have hI := circleFisherInformation_nonneg ρ
  have hpi : 1 ≤ 12 * (4 * Real.pi ^ 2) := by nlinarith [Real.pi_gt_three]
  have : 1 + DGPS.Analysis.circleFisherInformation ρ / (12 * (4 * Real.pi ^ 2)) ≤
      2 + DGPS.Analysis.circleFisherInformation ρ := by
    have : DGPS.Analysis.circleFisherInformation ρ / (12 * (4 * Real.pi ^ 2)) ≤
        DGPS.Analysis.circleFisherInformation ρ := div_le_self hI hpi
    linarith
  have hpos : 0 < 1 + DGPS.Analysis.circleFisherInformation ρ / (12 * (4 * Real.pi ^ 2)) := by positivity
  have := Real.log_le_log hpos this
  linarith

/-- Solving `H ≤ 6 log (1 + a H + c)` for `H`. -/
theorem solve_entropy_log {a c H : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hH : 0 ≤ H)
    (h : H ≤ 6 * Real.log (1 + a * H + c)) :
    H ≤ 2 * (6 * ((1 + c) / (12 * a + 1) - 1 + Real.log (12 * a + 1))) := by
  have hd : 0 < 12 * a + 1 := by positivity
  have hx : 0 < 1 + a * H + c := by positivity
  set ε := 1 / (12 * a + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hlog : Real.log (1 + a * H + c) ≤ ε * (1 + a * H + c) - 1 + Real.log (12 * a + 1) := by
    have h1 : Real.log (ε * (1 + a * H + c)) ≤ ε * (1 + a * H + c) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_mul hε0.ne' hx.ne'] at h1
    have : Real.log ε = -Real.log (12 * a + 1) := by rw [hε, one_div, Real.log_inv]
    linarith
  have h6 : 6 * a * ε ≤ 1 / 2 := by
    rw [hε, mul_one_div, div_le_div_iff₀ hd (by norm_num)]
    nlinarith
  have e : ε * (1 + a * H + c) = (1 + c) / (12 * a + 1) + a * ε * H := by
    rw [hε]; field_simp; ring
  rw [e] at hlog
  nlinarith [mul_nonneg ha hε0.le, mul_nonneg (mul_nonneg ha hε0.le) hH]

theorem logGradBound_le {h b : ℝ} (hb : |h| ≤ b) : logGradBound h ≤ logGradBound b := by
  have hb0 : 0 ≤ b := (abs_nonneg h).trans hb
  have hbb : |b| = b := abs_of_nonneg hb0
  unfold logGradBound
  rw [hbb]
  have h1 : Real.exp (2 * |h|) ≤ Real.exp (2 * b) := Real.exp_le_exp.2 (by linarith)
  gcongr

/-- A bounded ordinary quotient forces bounded information and bounded entropy. -/
theorem boundedQuotient_bounds {b : ℝ} (hb : 0 ≤ b) (M : ℝ≥0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ h : ℝ, |h| ≤ b → ∀ ρ : AbsoluteDensity 1,
      0 < ordinaryEntropy h ρ → ordinaryFisher h ρ / (2 * ordinaryEntropy h ρ) ≤ M →
      DGPS.Analysis.circleFisherInformation ρ ≤ B ∧ DGPS.Analysis.circleEntropy ρ ≤ B := by
  set a0 : ℝ := 4 * Real.pi ^ 2 with ha0
  have ha0pos : 0 < a0 := by positivity
  set Cb : ℝ := 2 * logGradBound b ^ 2 with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  set a : ℝ := 4 * M / (12 * a0) with ha
  set c : ℝ := (4 * M * (2 * b) + Cb) / (12 * a0) with hc
  have ha_nn : 0 ≤ a := by positivity
  have hc_nn : 0 ≤ c := by positivity
  set K0 : ℝ := 2 * (6 * ((1 + c) / (12 * a + 1) - 1 + Real.log (12 * a + 1))) with hK0
  set K : ℝ := max K0 0 with hK
  have hK_nn : 0 ≤ K := le_max_right _ _
  refine ⟨max K (4 * M * (K + 2 * b) + Cb), (le_max_right _ _).trans' (by positivity), ?_⟩
  intro h hh ρ hpos hq
  have hH0 := circleEntropy_nonneg ρ
  have hI0 := circleFisherInformation_nonneg ρ
  rw [ordinaryEntropy_eq] at hpos hq
  set J := ∫ x, ρ.density x * Real.log (referenceDensity h x) ∂haar 1 with hJ
  have hJb := abs_integral_density_mul_log_reference_le h ρ
  rw [← hJ] at hJb
  have hGr : 0 < DGPS.Analysis.circleEntropy ρ - J := ENNReal.ofReal_pos.1 hpos
  have h2G0 : (2 : ℝ≥0∞) * ENNReal.ofReal (DGPS.Analysis.circleEntropy ρ - J) ≠ 0 := by
    simp [hpos.ne']
  have h2Gt : (2 : ℝ≥0∞) * ENNReal.ofReal (DGPS.Analysis.circleEntropy ρ - J) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hF : ordinaryFisher h ρ ≤ M * (2 * ENNReal.ofReal (DGPS.Analysis.circleEntropy ρ - J)) := by
    exact (ENNReal.div_le_iff h2G0 h2Gt).1 hq
  have hP1 := fisher_le_two_ordinary h ρ
  have hGle : DGPS.Analysis.circleEntropy ρ - J ≤ DGPS.Analysis.circleEntropy ρ + 2 * b := by
    have := (abs_le.1 hJb).2
    have := (abs_le.1 hJb).1
    linarith [hh]
  have hCle : 2 * logGradBound h ^ 2 ≤ Cb := by
    rw [hCb]
    have := logGradBound_le hh
    have h0 := logGradBound_nonneg h
    nlinarith
  have hIreal : DGPS.Analysis.circleFisherInformation ρ ≤
      4 * M * (DGPS.Analysis.circleEntropy ρ + 2 * b) + Cb := by
    have h1 : ENNReal.ofReal (DGPS.Analysis.circleFisherInformation ρ) ≤
        ENNReal.ofReal (4 * M * (DGPS.Analysis.circleEntropy ρ - J) + Cb) := by
      refine hP1.trans ?_
      calc 2 * ordinaryFisher h ρ + ENNReal.ofReal (2 * logGradBound h ^ 2)
          ≤ 2 * (M * (2 * ENNReal.ofReal (DGPS.Analysis.circleEntropy ρ - J))) +
              ENNReal.ofReal Cb := by
            gcongr
        _ = ENNReal.ofReal (4 * M * (DGPS.Analysis.circleEntropy ρ - J) + Cb) := by
            have e : 4 * (M : ℝ) * (DGPS.Analysis.circleEntropy ρ - J) =
                2 * ((M : ℝ) * (2 * (DGPS.Analysis.circleEntropy ρ - J))) := by ring
            have hm : ENNReal.ofReal (2 * ((M : ℝ) * (2 * (DGPS.Analysis.circleEntropy ρ - J)))) =
                2 * (M * (2 * ENNReal.ofReal (DGPS.Analysis.circleEntropy ρ - J))) := by
              rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_mul M.coe_nonneg,
                ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
              simp
            rw [ENNReal.ofReal_add (by positivity) hCb0, e, hm]
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
    have : (M : ℝ) * (DGPS.Analysis.circleEntropy ρ - J) ≤ M * (DGPS.Analysis.circleEntropy ρ + 2 * b) :=
      mul_le_mul_of_nonneg_left hGle M.2
    nlinarith
  have hHlog : DGPS.Analysis.circleEntropy ρ ≤ 6 * Real.log (1 + a * DGPS.Analysis.circleEntropy ρ + c) := by
    obtain ⟨-, -, -, h4⟩ := DGPS.Analysis.circle_quantitative_lsi_on_the_absolute_domain ρ
    refine h4.trans ?_
    have hpos : 0 < 1 + DGPS.Analysis.circleFisherInformation ρ / (12 * (4 * Real.pi ^ 2)) := by positivity
    have hle : 1 + DGPS.Analysis.circleFisherInformation ρ / (12 * (4 * Real.pi ^ 2)) ≤
        1 + a * DGPS.Analysis.circleEntropy ρ + c := by
      have : DGPS.Analysis.circleFisherInformation ρ / (12 * a0) ≤
          (4 * M * (DGPS.Analysis.circleEntropy ρ + 2 * b) + Cb) / (12 * a0) :=
        div_le_div_of_nonneg_right hIreal (by positivity)
      have e : (4 * M * (DGPS.Analysis.circleEntropy ρ + 2 * b) + Cb) / (12 * a0) =
          a * DGPS.Analysis.circleEntropy ρ + c := by
        rw [ha, hc]; field_simp; ring
      rw [e] at this
      linarith
    have := Real.log_le_log hpos hle
    linarith
  have hHK := solve_entropy_log ha_nn hc_nn hH0 hHlog
  refine ⟨?_, (hHK.trans (le_max_left _ _)).trans (le_max_left _ _)⟩
  refine hIreal.trans ?_
  refine le_trans ?_ (le_max_right _ _)
  have : (M : ℝ) * (DGPS.Analysis.circleEntropy ρ + 2 * b) ≤ M * (K + 2 * b) :=
    mul_le_mul_of_nonneg_left (by linarith [hHK.trans (le_max_left K0 0)]) M.2
  nlinarith

/-- Haar rigidity: for positive entropy the sharp Haar LSI `I ≥ 2 a₀ H` (`a₀ = 4π²`) is strict, with
the quantitative remainder `I - 2 a₀ H ≥ (a₀/6) H² > 0`; in the angular normalisation `a = 1` this is
`I/a₀ - 2 H ≥ H²/6`. -/
theorem haarLSI_strict_positiveEntropy (ρ : AbsoluteDensity 1)
    (hH : 0 < DGPS.Analysis.circleEntropy ρ) :
    (4 * Real.pi ^ 2) / 6 * DGPS.Analysis.circleEntropy ρ ^ 2 ≤
      DGPS.Analysis.circleFisherInformation ρ -
        2 * (4 * Real.pi ^ 2) * DGPS.Analysis.circleEntropy ρ ∧
    2 * (4 * Real.pi ^ 2) * DGPS.Analysis.circleEntropy ρ < DGPS.Analysis.circleFisherInformation ρ ∧
    DGPS.Analysis.circleEntropy ρ ^ 2 / 6 ≤
      DGPS.Analysis.circleFisherInformation ρ / (4 * Real.pi ^ 2) -
        2 * DGPS.Analysis.circleEntropy ρ := by
  obtain ⟨-, -, h3, -⟩ := DGPS.Analysis.circle_quantitative_lsi_on_the_absolute_domain ρ
  have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
  have h1 : (4 * Real.pi ^ 2) / 6 * DGPS.Analysis.circleEntropy ρ ^ 2 ≤
      DGPS.Analysis.circleFisherInformation ρ -
        2 * (4 * Real.pi ^ 2) * DGPS.Analysis.circleEntropy ρ := by linarith
  refine ⟨h1, ?_, ?_⟩
  · have : 0 < (4 * Real.pi ^ 2) / 6 * DGPS.Analysis.circleEntropy ρ ^ 2 := by positivity
    linarith
  · have e : DGPS.Analysis.circleFisherInformation ρ / (4 * Real.pi ^ 2) -
        2 * DGPS.Analysis.circleEntropy ρ =
        (DGPS.Analysis.circleFisherInformation ρ -
          2 * (4 * Real.pi ^ 2) * DGPS.Analysis.circleEntropy ρ) / (4 * Real.pi ^ 2) := by
      field_simp
    rw [e, le_div_iff₀ hpi]
    nlinarith


theorem tsum_le_liminf_tsum {ι : Type*} (a : ℕ → ι → ℝ≥0∞) (A : ι → ℝ≥0∞)
    (h : ∀ k, Tendsto (fun n => a n k) atTop (𝓝 (A k))) :
    ∑' k, A k ≤ liminf (fun n => ∑' k, a n k) atTop := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have ht : Tendsto (fun n => ∑ k ∈ s, a n k) atTop (𝓝 (∑ k ∈ s, A k)) :=
    tendsto_finsetSum _ fun k _ => h k
  rw [← ht.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun n => ENNReal.sum_le_tsum s)

theorem tendsto_fourierCoeff_of_ae_bound {d : ℕ} {f : ℕ → Torus d → ℝ} {F : Torus d → ℝ}
    (hf : ∀ n, MemLp (f n) 2 (haar d)) (hF : MemLp F 2 (haar d)) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hb : ∀ n, ∀ᵐ x ∂haar d, |f n x - F x| ≤ ε n)
    (k : Fin d → ℤ) :
    Tendsto (fun n => DGPS.fourierCoeff (f n) k) atTop (𝓝 (DGPS.fourierCoeff F k)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have key : ∀ n, ‖DGPS.fourierCoeff (f n) k - DGPS.fourierCoeff F k‖ ≤ |ε n| := by
    intro n
    rw [← fourierCoeff_sub' (hf n) hF]
    have h1 : ‖DGPS.fourierCoeff (fun x => f n x - F x) k‖ ^ 2 ≤ ∫ x, (f n x - F x) ^ 2 ∂haar d :=
      norm_sq_fourierCoeff_le ((hf n).sub hF) k
    have h2 : ∫ x, (f n x - F x) ^ 2 ∂haar d ≤ ε n ^ 2 := by
      calc _ ≤ ∫ _x, ε n ^ 2 ∂haar d :=
            integral_mono_ae ((hf n).sub hF).integrable_sq (integrable_const _)
              (by
                filter_upwards [hb n] with x hx
                exact sq_le_sq.mpr (hx.trans (le_abs_self _)))
        _ = ε n ^ 2 := by simp
    exact (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp (by rw [sq_abs]; exact h1.trans h2)
  exact squeeze_zero (fun _ => norm_nonneg _) key (by simpa using hε.abs)


theorem ofReal_integral_sq_eq_tsum {d : ℕ} {f : Torus d → ℝ} (hf : MemLp f 2 (haar d)) :
    ENNReal.ofReal (∫ x, f x ^ 2 ∂haar d) =
      ∑' k, ENNReal.ofReal (‖DGPS.fourierCoeff f k‖ ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
    (hasSum_sq_fourierCoeff hf).summable, (hasSum_sq_fourierCoeff hf).tsum_eq]

theorem ofReal_integral_sq_le_liminf {d : ℕ} {f : ℕ → Torus d → ℝ} {F : Torus d → ℝ}
    (hf : ∀ n, MemLp (f n) 2 (haar d)) (hF : MemLp F 2 (haar d))
    (hc : ∀ k, Tendsto (fun n => DGPS.fourierCoeff (f n) k) atTop (𝓝 (DGPS.fourierCoeff F k))) :
    ENNReal.ofReal (∫ x, F x ^ 2 ∂haar d) ≤
      liminf (fun n => ENNReal.ofReal (∫ x, f n x ^ 2 ∂haar d)) atTop := by
  simp_rw [ofReal_integral_sq_eq_tsum (hf _)]
  rw [ofReal_integral_sq_eq_tsum hF]
  exact tsum_le_liminf_tsum _ _ fun k => ENNReal.tendsto_ofReal (((hc k).norm).pow 2)

theorem tsum_gradWeight_le_liminf {d : ℕ} {u : ℕ → Torus d → ℝ} {W : Torus d → ℝ}
    {g : ℕ → Torus d → Tangent d} (hg : ∀ n, IsWeakGradient (u n) (g n))
    (hc : ∀ k, Tendsto (fun n => DGPS.fourierCoeff (u n) k) atTop (𝓝 (DGPS.fourierCoeff W k))) :
    ∑' k, ENNReal.ofReal (gradWeight k * ‖DGPS.fourierCoeff W k‖ ^ 2) ≤
      liminf (fun n => ENNReal.ofReal (∫ x, ‖g n x‖ ^ 2 ∂haar d)) atTop := by
  have h1 : ∀ n, ENNReal.ofReal (∫ x, ‖g n x‖ ^ 2 ∂haar d) =
      ∑' k, ENNReal.ofReal (gradWeight k * ‖DGPS.fourierCoeff (u n) k‖ ^ 2) := fun n => by
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun k => mul_nonneg (by unfold gradWeight; positivity) (by positivity))
      (hasSum_gradWeight_weakGradient (hg n)).summable,
      (hasSum_gradWeight_weakGradient (hg n)).tsum_eq]
  simp_rw [h1]
  exact tsum_le_liminf_tsum _ _ fun k =>
    ENNReal.tendsto_ofReal ((((hc k).norm).pow 2).const_mul _)


theorem exists_subseq_uniform_holder {w : ℕ → Torus 1 → ℝ} (hw : ∀ n, Continuous (w n))
    {R Γ : ℝ} (hR : ∀ n x, |w n x| ≤ R)
    (hΓ : ∀ n x y, |w n x - w n y| ≤ Γ * Real.sqrt (torusDist x y)) :
    ∃ (φ : ℕ → ℕ) (W : Torus 1 → ℝ) (ε : ℕ → ℝ), StrictMono φ ∧ Continuous W ∧
      (∀ x, |W x| ≤ R) ∧ Tendsto ε atTop (𝓝 0) ∧ ∀ n x, |w (φ n) x - W x| ≤ ε n := by
  let f : ℕ → BoundedContinuousFunction (Torus 1) ℝ := fun n =>
    BoundedContinuousFunction.mkOfBound ⟨w n, hw n⟩ (2 * R) (fun x y => by
      rw [Real.dist_eq]
      have h1 := hR n x
      have h2 := hR n y
      show |w n x - w n y| ≤ 2 * R
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith)
  have hf : ∀ n x, f n x = w n x := fun n x => rfl
  have hcomp : IsCompact (closure (Set.range f)) := by
    refine BoundedContinuousFunction.arzela_ascoli (Set.Icc (-R) R) isCompact_Icc _ ?_ ?_
    · rintro g x ⟨n, rfl⟩
      rw [hf]
      exact abs_le.mp (hR n x)
    · intro x₀
      rw [Metric.equicontinuousAt_iff_right]
      intro e he
      have hc : Continuous fun x : Torus 1 => Γ * Real.sqrt (torusDist x₀ x) := by
        refine continuous_const.mul (Real.continuous_sqrt.comp ?_)
        have he : torusDist x₀ = fun x => ‖x₀ 0 - x 0‖ :=
          funext (torusDist_one x₀)
        rw [he]
        exact (continuous_const.sub (continuous_apply 0)).norm
      have h0 : Γ * Real.sqrt (torusDist x₀ x₀) = 0 := by
        rw [torusDist_one]; simp
      have hnhds : ∀ᶠ x in 𝓝 x₀, Γ * Real.sqrt (torusDist x₀ x) < e := by
        refine hc.continuousAt.eventually (gt_mem_nhds ?_)
        show Γ * Real.sqrt (torusDist x₀ x₀) < e
        rw [h0]; exact he
      filter_upwards [hnhds] with x hx
      rintro ⟨g, n, rfl⟩
      rw [Real.dist_eq]
      show |w n x₀ - w n x| < e
      exact lt_of_le_of_lt (hΓ n x₀ x) hx
  obtain ⟨F, -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩)
  refine ⟨φ, F, fun n => dist (f (φ n)) F, hφ, F.continuous, ?_, ?_, ?_⟩
  · intro x
    have ht : Tendsto (fun n => w (φ n) x) atTop (𝓝 (F x)) :=
      ((continuous_eval_const x).tendsto F).comp hlim
    have hmem : F x ∈ Set.Icc (-R) R :=
      isClosed_Icc.mem_of_tendsto ht (Eventually.of_forall fun n => abs_le.mp (hR _ x))
    exact abs_le.mpr hmem
  · exact tendsto_iff_dist_tendsto_zero.mp hlim
  · intro n x
    have := BoundedContinuousFunction.dist_coe_le_dist (f := f (φ n)) (g := F) x
    rw [Real.dist_eq] at this
    exact this


theorem toReal_eLpNorm_two_vec {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {F : α → E} (hF : MemLp F 2 μ) :
    (eLpNorm F 2 μ).toReal = Real.sqrt (∫ x, ‖F x‖ ^ 2 ∂μ) := by
  rw [hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  norm_num

theorem circleFisher_eq_four_mul (ρ : AbsoluteDensity 1) :
    DGPS.Analysis.circleFisherInformation ρ =
      4 * ∫ x, ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 ∂haar 1 := rfl

theorem exists_limit_of_bounded_fisher (ρ : ℕ → AbsoluteDensity 1) {B : ℝ}
    (hB : ∀ n, DGPS.Analysis.circleFisherInformation (ρ n) ≤ B) :
    ∃ (φ : ℕ → ℕ) (ρL : AbsoluteDensity 1) (ε : ℕ → ℝ) (R : ℝ),
      StrictMono φ ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n)).sqrt x - ρL.sqrt x| ≤ ε n) ∧
      (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n)).sqrt x| ≤ R) ∧ (∀ x, |ρL.sqrt x| ≤ R) ∧
      ENNReal.ofReal (DGPS.Analysis.circleFisherInformation ρL) ≤
        liminf (fun n => ENNReal.ofReal (DGPS.Analysis.circleFisherInformation (ρ (φ n)))) atTop := by
  set u : ℕ → Torus 1 → ℝ := fun n => (ρ n).sqrt with hu
  set g : ℕ → Torus 1 → Tangent 1 := fun n => weakGradient (ρ n).sqrt (ρ n).sqrt_mem with hg
  have hgw : ∀ n, IsWeakGradient (u n) (g n) := fun n => isWeakGradient_weakGradient (ρ n).sqrt_mem
  have hgint : ∀ n, ∫ x, ‖g n x‖ ^ 2 ∂haar 1 ≤ B / 4 := fun n => by
    have := hB n
    rw [circleFisher_eq_four_mul] at this
    linarith
  have hgnn : ∀ n, 0 ≤ ∫ x, ‖g n x‖ ^ 2 ∂haar 1 := fun n => integral_nonneg fun _ => by positivity
  set Γ : ℝ := Real.sqrt (B / 4) with hΓ
  have hΓn : ∀ n, (eLpNorm (g n) 2 (haar 1)).toReal ≤ Γ := fun n => by
    rw [toReal_eLpNorm_two_vec (hgw n).memLp_grad]
    exact Real.sqrt_le_sqrt (hgint n)
  have hu2 : ∀ n, (eLpNorm (u n) 2 (haar 1)).toReal = 1 := fun n => by
    rw [toReal_eLpNorm_two (ρ n).memLp_sqrt, (ρ n).mass_one, Real.sqrt_one]
  choose w hwc hwae hwh hwb _ using fun n => sobolev_embedding_dim_one (hgw n)
  have hΓ0 : 0 ≤ Γ := Real.sqrt_nonneg _
  obtain ⟨φ, W, ε, hφ, hWc, hWb, hε, hWε⟩ := exists_subseq_uniform_holder (w := w) hwc
    (R := 1 + Γ) (Γ := Γ)
    (fun n x => (hwb n x).trans (by rw [hu2 n]; linarith [hΓn n]))
    (fun n x y => (hwh n x y).trans
      (mul_le_mul_of_nonneg_right (hΓn n) (Real.sqrt_nonneg _)))
  have hWm : MemLp W 2 (haar 1) :=
    MemLp.of_bound hWc.aestronglyMeasurable (1 + Γ) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hWb x)
  have hae : ∀ n, ∀ᵐ x ∂haar 1, |u (φ n) x - W x| ≤ ε n := fun n => by
    filter_upwards [hwae (φ n)] with x hx
    rw [← hx]; exact hWε n x
  have hcoef := tendsto_fourierCoeff_of_ae_bound (f := fun n => u (φ n))
    (fun n => (ρ (φ n)).memLp_sqrt) hWm hε hae
  -- finite Fourier energy of the limit
  have hbound : ∀ n, ENNReal.ofReal (∫ x, ‖g (φ n) x‖ ^ 2 ∂haar 1) ≤ ENNReal.ofReal (B / 4) :=
    fun n => ENNReal.ofReal_le_ofReal (hgint _)
  have hfat := tsum_gradWeight_le_liminf (u := fun n => u (φ n)) (g := fun n => g (φ n))
    (fun n => hgw (φ n)) hcoef
  have hlimle : liminf (fun n => ENNReal.ofReal (∫ x, ‖g (φ n) x‖ ^ 2 ∂haar 1)) atTop ≤
      ENNReal.ofReal (B / 4) :=
    (liminf_le_liminf (Eventually.of_forall hbound)).trans (by simp)
  have hfin : ∑' k, ENNReal.ofReal (gradWeight k * ‖fourierCoeff W k‖ ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hfat.trans hlimle)
  have hsum : FiniteFourierEnergy W := by
    have := ENNReal.summable_toReal hfin
    refine this.congr fun k => ?_
    rw [ENNReal.toReal_ofReal (mul_nonneg (by unfold gradWeight; positivity) (by positivity))]
  obtain ⟨G, hG⟩ := exists_weakGradient_of_finiteFourierEnergy hWm hsum
  -- pointwise a.e. convergence
  have hpt : ∀ᵐ x ∂haar 1, Tendsto (fun n => u (φ n) x) atTop (𝓝 (W x)) := by
    have hall : ∀ᵐ x ∂haar 1, ∀ n, |u (φ n) x - W x| ≤ ε n := ae_all_iff.mpr hae
    filter_upwards [hall] with x hx
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by rw [Real.norm_eq_abs]; exact hx n)
      hε
  have hubd : ∀ n, ∀ᵐ x ∂haar 1, |u (φ n) x| ≤ 1 + Γ := fun n => by
    filter_upwards [hwae (φ n)] with x hx
    rw [← hx]
    exact (hwb _ x).trans (by rw [hu2 (φ n)]; linarith [hΓn (φ n)])
  have hnn : 0 ≤ᵐ[haar 1] W := by
    have hall : ∀ᵐ x ∂haar 1, ∀ n, |u (φ n) x - W x| ≤ ε n := ae_all_iff.mpr hae
    have hall2 : ∀ᵐ x ∂haar 1, ∀ n, 0 ≤ u (φ n) x :=
      ae_all_iff.mpr fun n => (ρ (φ n)).sqrt_nonneg
    filter_upwards [hall, hall2] with x h1 h2
    have h3 : ∀ n, -ε n ≤ W x := fun n => by
      have := abs_le.mp (h1 n); linarith [h2 n]
    have := le_of_tendsto' hε.neg h3
    simpa using this
  have hmass : ∫ x, W x ^ 2 ∂haar 1 = 1 := by
    have ht : Tendsto (fun n => ∫ x, u (φ n) x ^ 2 ∂haar 1) atTop
        (𝓝 (∫ x, W x ^ 2 ∂haar 1)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 + Γ) ^ 2)
        (fun n => (ρ (φ n)).memLp_sqrt.integrable_sq.aestronglyMeasurable) (integrable_const _)
        (fun n => ?_) (hpt.mono fun x hx => hx.pow 2)
      filter_upwards [hubd n] with x hx
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    exact tendsto_nhds_unique ht
      (tendsto_const_nhds.congr fun n => ((ρ (φ n)).mass_one).symm)
  let ρL : AbsoluteDensity 1 := ⟨W, ⟨G, hG⟩, hnn, hmass⟩
  refine ⟨φ, ρL, ε, 1 + Γ, hφ, hε, hae, hubd, hWb, ?_⟩
  have hHS := hasSum_gradWeight_weakGradient
    (isWeakGradient_weakGradient (show MemH1 W from ⟨G, hG⟩))
  have hI : ENNReal.ofReal (DGPS.Analysis.circleFisherInformation ρL) =
      4 * ∑' k, ENNReal.ofReal (gradWeight k * ‖fourierCoeff W k‖ ^ 2) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun k => mul_nonneg (by unfold gradWeight; positivity) (by positivity)) hHS.summable,
      hHS.tsum_eq, circleFisher_eq_four_mul,
      ENNReal.ofReal_mul (by norm_num)]
    simp
    rfl
  have hIn : ∀ n, ENNReal.ofReal (DGPS.Analysis.circleFisherInformation (ρ (φ n))) =
      4 * ENNReal.ofReal (∫ x, ‖g (φ n) x‖ ^ 2 ∂haar 1) := fun n => by
    rw [circleFisher_eq_four_mul, ENNReal.ofReal_mul (by norm_num)]
    simp [hg]
  simp_rw [hIn]
  rw [ENNReal.liminf_const_mul_of_ne_top (by simp), hI]
  gcongr


theorem tendsto_integral_comp_mul {u : ℕ → Torus 1 → ℝ} {W : Torus 1 → ℝ} {R Cc : ℝ}
    {T : ℝ → ℝ} (hT : Continuous T) {c : Torus 1 → ℝ} (hc : Continuous c)
    (hcb : ∀ x, |c x| ≤ Cc)
    (hum : ∀ n, AEStronglyMeasurable (u n) (haar 1))
    (hub : ∀ n, ∀ᵐ x ∂haar 1, |u n x| ≤ R)
    (hpt : ∀ᵐ x ∂haar 1, Tendsto (fun n => u n x) atTop (𝓝 (W x))) :
    Tendsto (fun n => ∫ x, T (u n x) * c x ∂haar 1) atTop
      (𝓝 (∫ x, T (W x) * c x ∂haar 1)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc (a := -R) (b := R) |>.exists_bound_of_continuousOn hT.continuousOn
  refine tendsto_integral_of_dominated_convergence (fun _ => C * Cc)
    (fun n => (hT.comp_aestronglyMeasurable (hum n)).mul hc.aestronglyMeasurable)
    (integrable_const _) (fun n => ?_) (hpt.mono fun x hx => ((hT.tendsto _).comp hx).mul_const _)
  filter_upwards [hub n] with x hx
  rw [norm_mul]
  exact mul_le_mul (hC _ (abs_le.mp hx |> fun h => ⟨h.1, h.2⟩)) (by rw [Real.norm_eq_abs]; exact hcb x)
    (norm_nonneg _) ((norm_nonneg _).trans (hC _ (abs_le.mp hx |> fun h => ⟨h.1, h.2⟩)))

theorem tendsto_circleEntropy {ρ : ℕ → AbsoluteDensity 1} {ρL : AbsoluteDensity 1} {R : ℝ}
    (hub : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x| ≤ R)
    (hpt : ∀ᵐ x ∂haar 1, Tendsto (fun n => (ρ n).sqrt x) atTop (𝓝 (ρL.sqrt x))) :
    Tendsto (fun n => DGPS.Analysis.circleEntropy (ρ n)) atTop
      (𝓝 (DGPS.Analysis.circleEntropy ρL)) := by
  have hT : Continuous fun t : ℝ => t ^ 2 * Real.log (t ^ 2) :=
    Real.continuous_mul_log.comp (continuous_pow 2)
  have := tendsto_integral_comp_mul (T := fun t : ℝ => t ^ 2 * Real.log (t ^ 2)) hT
    (c := fun _ => 1) continuous_const (Cc := 1) (fun _ => by simp)
    (fun n => (ρ n).memLp_sqrt.aestronglyMeasurable) hub hpt
  simpa [circleEntropy_eq, AbsoluteDensity.density] using this

theorem tendsto_integral_density_mul_log {ρ : ℕ → AbsoluteDensity 1} {ρL : AbsoluteDensity 1}
    {R : ℝ} (h : ℝ)
    (hub : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x| ≤ R)
    (hpt : ∀ᵐ x ∂haar 1, Tendsto (fun n => (ρ n).sqrt x) atTop (𝓝 (ρL.sqrt x))) :
    Tendsto (fun n => ∫ x, (ρ n).density x * Real.log (referenceDensity h x) ∂haar 1) atTop
      (𝓝 (∫ x, ρL.density x * Real.log (referenceDensity h x) ∂haar 1)) := by
  have hc : Continuous fun x => Real.log (referenceDensity h x) :=
    (continuous_referenceDensity h).log fun x => (referenceDensity_pos (h := h) x).ne'
  exact tendsto_integral_comp_mul (T := fun t : ℝ => t ^ 2) (continuous_pow 2) hc
    (fun x => abs_log_referenceDensity_le h x) (fun n => (ρ n).memLp_sqrt.aestronglyMeasurable) hub hpt

theorem tendsto_ordinaryEntropy {ρ : ℕ → AbsoluteDensity 1} {ρL : AbsoluteDensity 1} {R : ℝ}
    (h : ℝ) (hub : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x| ≤ R)
    (hpt : ∀ᵐ x ∂haar 1, Tendsto (fun n => (ρ n).sqrt x) atTop (𝓝 (ρL.sqrt x))) :
    Tendsto (fun n => ordinaryEntropy h (ρ n)) atTop (𝓝 (ordinaryEntropy h ρL)) := by
  simp_rw [ordinaryEntropy_eq]
  exact ENNReal.tendsto_ofReal
    ((tendsto_circleEntropy hub hpt).sub (tendsto_integral_density_mul_log h hub hpt))


theorem fourierCoeff_const_mul {d : ℕ} (c : ℝ) (f : Torus d → ℝ) (k : Fin d → ℤ) :
    DGPS.fourierCoeff (fun x => c * f x) k = (c : ℂ) * DGPS.fourierCoeff f k := by
  unfold DGPS.fourierCoeff UnitAddTorus.mFourierCoeff
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul, Complex.ofReal_mul]
  ring

theorem tangent1_norm (v : Tangent 1) : ‖v‖ = |v 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]

/-- The scalar (only) coordinate of the weak gradient of `log` of the reference density. -/
noncomputable def logScore (h : ℝ) : Torus 1 → ℝ := fun x =>
  weakGradient (fun x => Real.log ((ordinaryReference h).density x))
    ((ordinaryReference h).memH1_log (ordinaryReference_lip h)) x 0

theorem abs_logScore_le (h : ℝ) : ∀ᵐ x ∂haar 1, |logScore h x| ≤ logGradBound h := by
  filter_upwards [norm_logGrad_le h] with x hx
  unfold logScore
  rw [← tangent1_norm]
  exact hx

theorem aestronglyMeasurable_logScore (h : ℝ) : AEStronglyMeasurable (logScore h) (haar 1) :=
  (memLp_coord (isWeakGradient_weakGradient
    ((ordinaryReference h).memH1_log (ordinaryReference_lip h))).memLp_grad 0).aestronglyMeasurable

theorem memLp_mul_logScore (h : ℝ) {u : Torus 1 → ℝ} (hu : MemLp u 2 (haar 1)) :
    MemLp (fun x => u x * logScore h x) 2 (haar 1) := by
  refine (hu.const_mul (logGradBound h)).mono
    (hu.aestronglyMeasurable.mul (aestronglyMeasurable_logScore h)) ?_
  filter_upwards [abs_logScore_le h] with x hx
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (logGradBound_nonneg h)]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

theorem ordinaryFisher_eq (h : ℝ) (ρ : AbsoluteDensity 1) :
    ordinaryFisher h ρ = ENNReal.ofReal (∫ x,
      (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * logScore h x) ^ 2 ∂haar 1) := by
  have hG := isWeakGradient_weakGradient ρ.sqrt_mem
  have hF : ordinaryFisher h ρ = ∫⁻ x, ‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x -
      ρ.sqrt x • weakGradient (fun x => Real.log ((ordinaryReference h).density x))
        ((ordinaryReference h).memH1_log (ordinaryReference_lip h)) x‖ₑ ^ 2 ∂haar 1 :=
    positiveReference_absolute_identity (ordinaryReference h) (ordinaryReference_lip h) ρ
  have hm : MemLp (fun x => 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * logScore h x) 2
      (haar 1) :=
    ((memLp_coord hG.memLp_grad 0).const_mul 2).sub (memLp_mul_logScore h ρ.memLp_sqrt)
  rw [hF, ofReal_integral_eq_lintegral_ofReal hm.integrable_sq
    (Eventually.of_forall fun x => sq_nonneg _)]
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), tangent1_norm]
  have : ((2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x -
      ρ.sqrt x • weakGradient (fun x => Real.log ((ordinaryReference h).density x))
        ((ordinaryReference h).memH1_log (ordinaryReference_lip h)) x) 0 =
      2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * logScore h x := by
    simp [logScore]
  rw [this, sq_abs]


theorem ordinaryFisher_le_liminf (h : ℝ) (ρ : ℕ → AbsoluteDensity 1) (ρL : AbsoluteDensity 1)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hae : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - ρL.sqrt x| ≤ ε n) :
    ordinaryFisher h ρL ≤ liminf (fun n => ordinaryFisher h (ρ n)) atTop := by
  simp_rw [ordinaryFisher_eq]
  have hG : ∀ n, IsWeakGradient (ρ n).sqrt (weakGradient (ρ n).sqrt (ρ n).sqrt_mem) :=
    fun n => isWeakGradient_weakGradient (ρ n).sqrt_mem
  have hGL := isWeakGradient_weakGradient ρL.sqrt_mem
  have hmem : ∀ n, MemLp (fun x => 2 * weakGradient (ρ n).sqrt (ρ n).sqrt_mem x 0
      - (ρ n).sqrt x * logScore h x) 2 (haar 1) := fun n =>
    ((memLp_coord (hG n).memLp_grad 0).const_mul 2).sub (memLp_mul_logScore h (ρ n).memLp_sqrt)
  have hmemL : MemLp (fun x => 2 * weakGradient ρL.sqrt ρL.sqrt_mem x 0
      - ρL.sqrt x * logScore h x) 2 (haar 1) :=
    ((memLp_coord hGL.memLp_grad 0).const_mul 2).sub (memLp_mul_logScore h ρL.memLp_sqrt)
  refine ofReal_integral_sq_le_liminf hmem hmemL fun k => ?_
  have hu : Tendsto (fun n => DGPS.fourierCoeff (ρ n).sqrt k) atTop
      (𝓝 (DGPS.fourierCoeff ρL.sqrt k)) :=
    tendsto_fourierCoeff_of_ae_bound (fun n => (ρ n).memLp_sqrt) ρL.memLp_sqrt hε hae k
  have hv : Tendsto (fun n => DGPS.fourierCoeff (fun x => (ρ n).sqrt x * logScore h x) k) atTop
      (𝓝 (DGPS.fourierCoeff (fun x => ρL.sqrt x * logScore h x) k)) := by
    refine tendsto_fourierCoeff_of_ae_bound (fun n => memLp_mul_logScore h (ρ n).memLp_sqrt)
      (memLp_mul_logScore h ρL.memLp_sqrt)
      (ε := fun n => |ε n| * logGradBound h) ?_ (fun n => ?_) k
    · simpa using (hε.abs.mul_const (logGradBound h))
    · filter_upwards [hae n, abs_logScore_le h] with x hx hs
      rw [← sub_mul, abs_mul]
      exact mul_le_mul (hx.trans (le_abs_self _)) hs (abs_nonneg _) (abs_nonneg _)
  have hid : ∀ (u : AbsoluteDensity 1), DGPS.fourierCoeff (fun x => 2 * weakGradient u.sqrt u.sqrt_mem x 0
      - u.sqrt x * logScore h x) k = 2 * (2 * Real.pi * Complex.I * (k 0 : ℂ) *
        DGPS.fourierCoeff u.sqrt k) - DGPS.fourierCoeff (fun x => u.sqrt x * logScore h x) k := by
    intro u
    have hGu := isWeakGradient_weakGradient u.sqrt_mem
    rw [fourierCoeff_sub' ((memLp_coord hGu.memLp_grad 0).const_mul 2)
      (memLp_mul_logScore h u.memLp_sqrt), fourierCoeff_const_mul,
      fourierCoeff_weakGradient hGu 0 k]
    simp
  simp_rw [hid]
  exact ((hu.const_mul _).const_mul _).sub hv


theorem circle_boundedQuotient_compactness {b : ℝ} (hb : 0 ≤ b) (M : ℝ≥0) (h : ℝ) (hh : |h| ≤ b)
    (ρ : ℕ → AbsoluteDensity 1) (hpos : ∀ n, 0 < ordinaryEntropy h (ρ n))
    (hq : ∀ n, ordinaryFisher h (ρ n) / (2 * ordinaryEntropy h (ρ n)) ≤ M) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ n, DGPS.Analysis.circleFisherInformation (ρ n) ≤ B ∧
        DGPS.Analysis.circleEntropy (ρ n) ≤ B) ∧
      ∃ (φ : ℕ → ℕ) (ρL : AbsoluteDensity 1) (ε : ℕ → ℝ), StrictMono φ ∧
        Tendsto ε atTop (𝓝 0) ∧
        (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n)).sqrt x - ρL.sqrt x| ≤ ε n) ∧
        Tendsto (fun n => DGPS.Analysis.circleEntropy (ρ (φ n))) atTop
          (𝓝 (DGPS.Analysis.circleEntropy ρL)) ∧
        Tendsto (fun n => ordinaryEntropy h (ρ (φ n))) atTop (𝓝 (ordinaryEntropy h ρL)) ∧
        ENNReal.ofReal (DGPS.Analysis.circleFisherInformation ρL) ≤
          liminf (fun n => ENNReal.ofReal (DGPS.Analysis.circleFisherInformation (ρ (φ n)))) atTop ∧
        ordinaryFisher h ρL ≤ liminf (fun n => ordinaryFisher h (ρ (φ n))) atTop := by
  obtain ⟨B, hB0, hB⟩ := boundedQuotient_bounds hb M
  have hBn : ∀ n, DGPS.Analysis.circleFisherInformation (ρ n) ≤ B ∧
      DGPS.Analysis.circleEntropy (ρ n) ≤ B := fun n => hB h hh (ρ n) (hpos n) (hq n)
  obtain ⟨φ, ρL, ε, R, hφ, hε, hae, hub, -, hlsc⟩ :=
    exists_limit_of_bounded_fisher ρ (fun n => (hBn n).1)
  have hpt : ∀ᵐ x ∂haar 1, Tendsto (fun n => (ρ (φ n)).sqrt x) atTop (𝓝 (ρL.sqrt x)) := by
    have hall : ∀ᵐ x ∂haar 1, ∀ n, |(ρ (φ n)).sqrt x - ρL.sqrt x| ≤ ε n :=
      ae_all_iff.mpr hae
    filter_upwards [hall] with x hx
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hε.abs)
    exact (hx n).trans (le_abs_self _)
  exact ⟨B, hB0, hBn, φ, ρL, ε, hφ, hε, hae, tendsto_circleEntropy hub hpt,
    tendsto_ordinaryEntropy h hub hpt, hlsc, ordinaryFisher_le_liminf h (fun n => ρ (φ n)) ρL hε hae⟩

/-- The relative square root as an explicit function. -/
noncomputable def str025_u (h : ℝ) (ρ : AbsoluteDensity 1) : Torus 1 → ℝ :=
  fun x => ρ.sqrt x * (ordinaryReference h).density x ^ (-(1 / 2) : ℝ)

noncomputable def str025_grad (h : ℝ) (ρ : AbsoluteDensity 1) : Torus 1 → Tangent 1 :=
  fun x => (ordinaryReference h).density x ^ (-(1 / 2) : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x +
    ρ.sqrt x • (((-(1 / 2) : ℝ) * (ordinaryReference h).density x ^ (-(1 / 2) - 1 : ℝ)) •
      RelativeFisher.lipGradVec (ordinaryReference h).density x)

theorem str025_isWeak (h : ℝ) (ρ : AbsoluteDensity 1) :
    IsWeakGradient (str025_u h ρ) (str025_grad h ρ) :=
  RelativeFisher.mul_rpow_isWeakGradient (ordinaryReference_lip h) (r := (-(1 / 2) : ℝ)) (by norm_num)
    (isWeakGradient_weakGradient ρ.sqrt_mem)

noncomputable def str025_prob (h : ℝ) : ProbabilityMeasure (Torus 1) :=
  ⟨threefoldReference h, isProbabilityMeasure_threefoldReference h⟩

noncomputable def str025_test (h : ℝ) (ρ : AbsoluteDensity 1) : WeakH1Test (str025_prob h) where
  fn := str025_u h ρ
  grad := str025_grad h ρ
  isWeak := (isMeasureWeakGradient_iff (ordinaryReference h)).2
    ((isWeightedWeakGradient_iff (ordinaryReference h)).2 (str025_isWeak h ρ))

theorem str025_fisher_eq (h : ℝ) (ρ : AbsoluteDensity 1) :
    ordinaryFisher h ρ = 4 * dirichletEnergy (str025_prob h) (str025_test h ρ) := by
  set P := ordinaryReference h with hP
  set ν : Measure (Torus 1) := (densityMeasure ρ : Measure (Torus 1)) with hν
  have hνac : ν ≪ P.measure :=
    (withDensity_absolutelyContinuous _ _).trans P.haar_ac_measure
  have habs : (fun x => Real.sqrt (ν.rnDeriv (haar 1) x).toReal) =ᵐ[haar 1] ρ.sqrt := by
    have h0 := Measure.rnDeriv_withDensity₀ (haar 1)
      (f := fun x => ENNReal.ofReal (ρ.sqrt x ^ 2))
      (by exact (ρ.memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal)
    filter_upwards [h0, ρ.sqrt_nonneg] with x hx hx0
    rw [hν, densityMeasure_coe, hx, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq hx0]
  have hrel : relativeSqrt ν P =ᵐ[haar 1] str025_u h ρ := by
    filter_upwards [RelativeFisher.relativeSqrt_ae_eq P ν, habs] with x h1 h2
    rw [h1, h2]; rfl
  have hws := (str025_isWeak h ρ).congr_ae hrel.symm (Filter.EventuallyEq.refl _ _)
  unfold ordinaryFisher
  rw [ordinaryRelativeFisher_eq hνac hws]
  rfl


noncomputable def str025_w (h : ℝ) : Torus 1 → ℝ := fun x => Real.sqrt (referenceDensity h x)

theorem str025_w_pos (h : ℝ) (x : Torus 1) : 0 < str025_w h x :=
  Real.sqrt_pos.2 (referenceDensity_pos (h := h) x)

theorem str025_w_sq (h : ℝ) (x : Torus 1) : str025_w h x ^ 2 = referenceDensity h x :=
  Real.sq_sqrt (referenceDensity_pos (h := h) x).le

theorem str025_w_ge (h : ℝ) (x : Torus 1) : Real.exp (-|h|) ≤ str025_w h x := by
  unfold str025_w
  apply Real.le_sqrt_of_sq_le
  rw [← Real.exp_nat_mul]
  have := le_referenceDensity h x
  convert this using 2
  push_cast; ring

theorem str025_w_le (h : ℝ) (x : Torus 1) : str025_w h x ≤ Real.exp |h| := by
  unfold str025_w
  rw [Real.sqrt_le_left (Real.exp_pos _).le]
  have := referenceDensity_le h x
  calc referenceDensity h x ≤ Real.exp (2 * |h|) := this
    _ = Real.exp |h| ^ 2 := by rw [← Real.exp_nat_mul]; push_cast; ring_nf

theorem str025_continuous_w (h : ℝ) : Continuous (str025_w h) :=
  (continuous_referenceDensity h).sqrt

theorem str025_integrable_w_sq (h : ℝ) : Integrable (fun x => str025_w h x ^ 2) (haar 1) := by
  simp_rw [str025_w_sq]
  exact (continuous_referenceDensity h).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem str025_integral_w_sq (h : ℝ) : ∫ x, str025_w h x ^ 2 ∂haar 1 = 1 := by
  simp_rw [str025_w_sq]
  exact integral_referenceDensity_eq_one h

theorem str025_integrable_sw (h : ℝ) (ρ : AbsoluteDensity 1) :
    Integrable (fun x => ρ.sqrt x * str025_w h x) (haar 1) :=
  (ρ.memLp_sqrt.integrable one_le_two).mul_bdd (c := Real.exp |h|)
    (str025_continuous_w h).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (str025_w_pos h x)]; exact str025_w_le h x)

theorem str025_integral_sq_sub (h : ℝ) (ρ : AbsoluteDensity 1) (c : ℝ) :
    ∫ x, (ρ.sqrt x - c * str025_w h x) ^ 2 ∂haar 1 =
      1 - 2 * c * (∫ x, ρ.sqrt x * str025_w h x ∂haar 1) + c ^ 2 := by
  have e : (fun x => (ρ.sqrt x - c * str025_w h x) ^ 2) = fun x =>
      ρ.sqrt x ^ 2 - 2 * c * (ρ.sqrt x * str025_w h x) + c ^ 2 * str025_w h x ^ 2 := by
    funext x; ring
  have i1 : Integrable (fun x => ρ.sqrt x ^ 2) (haar 1) := ρ.integrable_density
  have i2 : Integrable (fun x => 2 * c * (ρ.sqrt x * str025_w h x)) (haar 1) :=
    (str025_integrable_sw h ρ).const_mul _
  have i3 : Integrable (fun x => c ^ 2 * str025_w h x ^ 2) (haar 1) :=
    (str025_integrable_w_sq h).const_mul _
  have j1 : Integrable (fun x => ρ.sqrt x ^ 2 - 2 * c * (ρ.sqrt x * str025_w h x)) (haar 1) := i1.sub i2
  rw [e, integral_add j1 i3, integral_sub i1 i2, integral_const_mul, integral_const_mul]
  have : ∫ x, ρ.sqrt x ^ 2 ∂haar 1 = 1 := ρ.mass_one
  rw [this, str025_integral_w_sq]; ring

theorem str025_rpow_neg_half (h : ℝ) (x : Torus 1) :
    (ordinaryReference h).density x ^ (-(1 / 2) : ℝ) = (str025_w h x)⁻¹ := by
  show referenceDensity h x ^ (-(1 / 2) : ℝ) = _
  rw [Real.rpow_neg (referenceDensity_pos (h := h) x).le, str025_w, Real.sqrt_eq_rpow]

theorem str025_u_eq (h : ℝ) (ρ : AbsoluteDensity 1) (x : Torus 1) :
    str025_u h ρ x = ρ.sqrt x / str025_w h x := by
  unfold str025_u; rw [str025_rpow_neg_half]; ring

theorem str025_q_mul_u (h : ℝ) (ρ : AbsoluteDensity 1) (x : Torus 1) :
    referenceDensity h x * str025_u h ρ x = ρ.sqrt x * str025_w h x := by
  have := str025_w_pos h x
  rw [str025_u_eq, ← str025_w_sq]; field_simp

theorem str025_q_mul_sq (h : ℝ) (ρ : AbsoluteDensity 1) (c : ℝ) (y : Torus 1) :
    referenceDensity h y * (str025_u h ρ y - c) ^ 2 = (ρ.sqrt y - c * str025_w h y) ^ 2 := by
  have := str025_w_pos h y
  rw [str025_u_eq, ← str025_w_sq]; field_simp

theorem str025_variance (h : ℝ) (ρ : AbsoluteDensity 1) :
    weightedVariance (str025_prob h) (str025_test h ρ).fn =
      1 - (∫ x, ρ.sqrt x * str025_w h x ∂haar 1) ^ 2 := by
  have hm : ∫ y, (str025_test h ρ).fn y ∂((str025_prob h : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)) =
      ∫ x, ρ.sqrt x * str025_w h x ∂haar 1 := by
    show ∫ y, str025_u h ρ y ∂threefoldReference h = _
    rw [integral_threefoldReference]
    exact integral_congr_ae (Filter.Eventually.of_forall (str025_q_mul_u h ρ))
  unfold weightedVariance
  rw [hm]
  show ∫ x, (str025_u h ρ x - _) ^ 2 ∂threefoldReference h = _
  rw [integral_threefoldReference]
  simp_rw [str025_q_mul_sq h ρ _]
  rw [str025_integral_sq_sub]; ring


noncomputable def str025_psi (u : ℝ) : ℝ := u ^ 2 * Real.log (u ^ 2) - u ^ 2 + 1

theorem str025_psi_sub_two_sq_le {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |str025_psi (1 + t) - 2 * t ^ 2| ≤ 10 * |t| ^ 3 := by
  have hx : |-t| < 1 := by rw [abs_neg]; linarith
  have h2 := Real.abs_log_sub_add_sum_range_le hx 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h2
  rw [abs_neg] at h2
  have hlog : Real.log (1 - -t) = Real.log (1 + t) := by ring_nf
  rw [hlog] at h2
  set R := Real.log (1 + t) - t + t ^ 2 / 2 with hR
  have hRb : |R| ≤ 2 * |t| ^ 3 := by
    have e : R = (0 + (-t) ^ (0 + 1) / (↑(0:ℕ) + 1) + (-t) ^ (1 + 1) / (↑(1:ℕ) + 1) + Real.log (1 + t)) := by
      rw [hR]; push_cast; ring
    have h3 : |R| ≤ |t| ^ (2 + 1) / (1 - |t|) := by
      rw [e]; exact h2
    have h4 : |t| ^ (2 + 1) / (1 - |t|) ≤ 2 * |t| ^ 3 := by
      rw [div_le_iff₀ (by linarith)]
      have : 0 ≤ |t| ^ 3 := by positivity
      have e3 : |t| ^ (2 + 1) = |t| ^ 3 := rfl
      rw [e3]
      nlinarith
    exact h3.trans h4
  have hpos : 0 < 1 + t := by
    have := (abs_le.1 ht).1; linarith
  have e1 : str025_psi (1 + t) - 2 * t ^ 2 = -t ^ 4 + 2 * (1 + t) ^ 2 * R := by
    unfold str025_psi
    rw [Real.log_pow]
    have : Real.log (1 + t) = R + t - t ^ 2 / 2 := by rw [hR]; ring
    push_cast
    rw [this]; ring
  rw [e1]
  have ha : |t| ^ 3 = |t| * |t| ^ 2 := by ring
  have h5 : t ^ 4 ≤ |t| ^ 3 / 2 := by
    have : t ^ 4 = |t| ^ 3 * |t| := by
      rw [show t ^ 4 = |t| ^ 4 by rw [pow_abs, abs_of_nonneg (by positivity)]]; ring
    rw [this]
    have : 0 ≤ |t| ^ 3 := by positivity
    nlinarith
  have h6 : |2 * (1 + t) ^ 2 * R| ≤ 9 * |t| ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg (by positivity : 0 ≤ (1 + t) ^ 2)]
    have hb : (1 + t) ^ 2 ≤ 9 / 4 := by
      have := abs_le.1 ht; nlinarith
    calc 2 * (1 + t) ^ 2 * |R| ≤ 2 * (9 / 4) * (2 * |t| ^ 3) := by gcongr
      _ = 9 * |t| ^ 3 := by ring
  calc |-t ^ 4 + 2 * (1 + t) ^ 2 * R| ≤ |-t ^ 4| + |2 * (1 + t) ^ 2 * R| := abs_add_le _ _
    _ ≤ 10 * |t| ^ 3 := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
      have : 0 ≤ |t| ^ 3 := by positivity
      linarith

/-- The entropy integrand. -/
noncomputable def str025_Phi (h : ℝ) (ρ : AbsoluteDensity 1) (x : Torus 1) : ℝ :=
  ρ.density x * Real.log (ρ.density x) - ρ.density x * Real.log (referenceDensity h x)
    - ρ.density x + referenceDensity h x

theorem str025_integrable_Phi (h : ℝ) (ρ : AbsoluteDensity 1) :
    Integrable (str025_Phi h ρ) (haar 1) := by
  have i4 : Integrable (referenceDensity h) (haar 1) :=
    (continuous_referenceDensity h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact (((absoluteDensity_entropy_finite ρ).1.sub (integrable_density_mul_log_reference h ρ)).sub
      ρ.integrable_density).add i4

theorem str025_Hr_eq (h : ℝ) (ρ : AbsoluteDensity 1) :
    DGPS.Analysis.circleEntropy ρ - ∫ x, ρ.density x * Real.log (referenceDensity h x) ∂haar 1 =
      ∫ x, str025_Phi h ρ x ∂haar 1 := by
  have i4 : Integrable (referenceDensity h) (haar 1) :=
    (continuous_referenceDensity h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i1 := (absoluteDensity_entropy_finite ρ).1
  have i2 := integrable_density_mul_log_reference h ρ
  have i3 := ρ.integrable_density
  have j1 : Integrable (fun x => ρ.density x * Real.log (ρ.density x) -
      ρ.density x * Real.log (referenceDensity h x)) (haar 1) := i1.sub i2
  have j2 : Integrable (fun x => ρ.density x * Real.log (ρ.density x) -
      ρ.density x * Real.log (referenceDensity h x) - ρ.density x) (haar 1) := j1.sub i3
  unfold str025_Phi
  rw [integral_add j2 i4, integral_sub j1 i3, integral_sub i1 i2,
    ρ.integral_density, integral_referenceDensity_eq_one, circleEntropy_eq]
  ring

theorem str025_Phi_eq (h : ℝ) (ρ : AbsoluteDensity 1) (x : Torus 1) :
    str025_Phi h ρ x = referenceDensity h x * str025_psi (str025_u h ρ x) := by
  have hw := str025_w_pos h x
  have hq : 0 < referenceDensity h x := referenceDensity_pos (h := h) x
  have hu : str025_u h ρ x ^ 2 = ρ.sqrt x ^ 2 / referenceDensity h x := by
    rw [str025_u_eq, div_pow, str025_w_sq]
  unfold str025_Phi str025_psi
  rw [hu]
  show ρ.sqrt x ^ 2 * Real.log (ρ.sqrt x ^ 2) - ρ.sqrt x ^ 2 * Real.log (referenceDensity h x)
    - ρ.sqrt x ^ 2 + referenceDensity h x = _
  rcases eq_or_ne (ρ.sqrt x) 0 with h0 | h0
  · simp [h0]
  · rw [Real.log_div (pow_ne_zero 2 h0) hq.ne']
    field_simp

theorem str025_entropy_close (h : ℝ) (ρ : AbsoluteDensity 1) {η : ℝ} (hη : η ≤ 1 / 2)
    (hae : ∀ᵐ x ∂haar 1, |str025_u h ρ x - 1| ≤ η) :
    |(∫ x, str025_Phi h ρ x ∂haar 1) - 2 * ∫ x, (ρ.sqrt x - str025_w h x) ^ 2 ∂haar 1| ≤
      10 * η * ∫ x, (ρ.sqrt x - str025_w h x) ^ 2 ∂haar 1 := by
  have iS : Integrable (fun x => (ρ.sqrt x - str025_w h x) ^ 2) (haar 1) := by
    have := ρ.memLp_sqrt.sub ((memLp_top_of_bound (str025_continuous_w h).aestronglyMeasurable
      (Real.exp |h|) (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (str025_w_pos h x)]; exact str025_w_le h x)).mono_exponent
          le_top : MemLp (str025_w h) 2 (haar 1))
    exact this.integrable_sq
  have e1 : (∫ x, str025_Phi h ρ x ∂haar 1) - 2 * ∫ x, (ρ.sqrt x - str025_w h x) ^ 2 ∂haar 1 =
      ∫ x, (str025_Phi h ρ x - 2 * (ρ.sqrt x - str025_w h x) ^ 2) ∂haar 1 := by
    rw [integral_sub (str025_integrable_Phi h ρ) (iS.const_mul 2), integral_const_mul]
  have e2 : 10 * η * ∫ x, (ρ.sqrt x - str025_w h x) ^ 2 ∂haar 1 =
      ∫ x, 10 * η * (ρ.sqrt x - str025_w h x) ^ 2 ∂haar 1 := by
    rw [integral_const_mul]
  rw [e1, e2, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (iS.const_mul (10 * η)) ?_)
  filter_upwards [hae] with x hx
  have h1 := str025_psi_sub_two_sq_le (t := str025_u h ρ x - 1) (hx.trans hη)
  have hq : 0 < referenceDensity h x := referenceDensity_pos (h := h) x
  have key := str025_q_mul_sq h ρ 1 x
  rw [one_mul] at key
  rw [Real.norm_eq_abs, str025_Phi_eq, ← key]
  have h3 : |str025_u h ρ x - 1| ^ 3 ≤ η * (str025_u h ρ x - 1) ^ 2 := by
    have : |str025_u h ρ x - 1| ^ 3 = |str025_u h ρ x - 1| * (str025_u h ρ x - 1) ^ 2 := by
      rw [pow_succ, ← sq_abs (str025_u h ρ x - 1)]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)
  have e : referenceDensity h x * str025_psi (str025_u h ρ x) -
      2 * (referenceDensity h x * (str025_u h ρ x - 1) ^ 2) =
      referenceDensity h x * (str025_psi (1 + (str025_u h ρ x - 1)) - 2 * (str025_u h ρ x - 1) ^ 2) := by
    rw [show 1 + (str025_u h ρ x - 1) = str025_u h ρ x by ring]; ring
  rw [e, abs_mul, abs_of_pos hq]
  calc referenceDensity h x * |str025_psi (1 + (str025_u h ρ x - 1)) - 2 * (str025_u h ρ x - 1) ^ 2|
      ≤ referenceDensity h x * (10 * |str025_u h ρ x - 1| ^ 3) :=
        mul_le_mul_of_nonneg_left h1 hq.le
    _ ≤ referenceDensity h x * (10 * (η * (str025_u h ρ x - 1) ^ 2)) := by gcongr
    _ = 10 * η * (referenceDensity h x * (str025_u h ρ x - 1) ^ 2) := by ring


theorem str025_integrable_S (h : ℝ) (ρ : AbsoluteDensity 1) :
    Integrable (fun x => (ρ.sqrt x - str025_w h x) ^ 2) (haar 1) := by
  have := ρ.memLp_sqrt.sub ((memLp_top_of_bound (str025_continuous_w h).aestronglyMeasurable
    (Real.exp |h|) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (str025_w_pos h x)]; exact str025_w_le h x)).mono_exponent
        le_top : MemLp (str025_w h) 2 (haar 1))
  exact this.integrable_sq

theorem str025_S_le (h : ℝ) (ρ : AbsoluteDensity 1) {η : ℝ}
    (hae : ∀ᵐ x ∂haar 1, |str025_u h ρ x - 1| ≤ η) :
    ∫ x, (ρ.sqrt x - str025_w h x) ^ 2 ∂haar 1 ≤ η ^ 2 := by
  calc ∫ x, (ρ.sqrt x - str025_w h x) ^ 2 ∂haar 1 ≤ ∫ x, η ^ 2 * str025_w h x ^ 2 ∂haar 1 := by
        refine integral_mono_ae (str025_integrable_S h ρ) ((str025_integrable_w_sq h).const_mul _) ?_
        filter_upwards [hae] with x hx
        have hw := str025_w_pos h x
        have key := str025_q_mul_sq h ρ 1 x
        rw [one_mul, ← str025_w_sq] at key
        rw [← key]
        have : (str025_u h ρ x - 1) ^ 2 ≤ η ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
        calc str025_w h x ^ 2 * (str025_u h ρ x - 1) ^ 2 ≤ str025_w h x ^ 2 * η ^ 2 :=
              mul_le_mul_of_nonneg_left this (sq_nonneg _)
          _ = _ := by ring
    _ = η ^ 2 := by rw [integral_const_mul, str025_integral_w_sq, mul_one]

theorem str025_core (h : ℝ) (ρ : AbsoluteDensity 1) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (hae : ∀ᵐ x ∂haar 1, |str025_u h ρ x - 1| ≤ η) (hH : 0 < ordinaryEntropy h ρ) :
    ENNReal.ofReal (2 * (1 - η ^ 2 / 4) / (2 + 10 * η)) * poincareRate (str025_prob h) ≤
      ordinaryFisher h ρ / (2 * ordinaryEntropy h ρ) := by
  set Hr := DGPS.Analysis.circleEntropy ρ -
    ∫ x, ρ.density x * Real.log (referenceDensity h x) ∂haar 1 with hHr
  have hE : ordinaryEntropy h ρ = ENNReal.ofReal Hr := ordinaryEntropy_eq h ρ
  rw [hE] at hH ⊢
  have hHrpos : 0 < Hr := ENNReal.ofReal_pos.1 hH
  set a := ∫ x, ρ.sqrt x * str025_w h x ∂haar 1 with ha
  set S := ∫ x, (ρ.sqrt x - str025_w h x) ^ 2 ∂haar 1 with hS
  have hSa : S = 2 - 2 * a := by
    have := str025_integral_sq_sub h ρ 1
    simp only [one_mul, mul_one, one_pow] at this
    rw [hS, this]; ring
  have hS0 : 0 ≤ S := integral_nonneg fun x => sq_nonneg _
  have hSη : S ≤ η ^ 2 := str025_S_le h ρ hae
  have hcl := str025_entropy_close h ρ hη hae
  rw [← str025_Hr_eq] at hcl
  have hHrS : Hr ≤ (2 + 10 * η) * S := by
    have := (abs_le.1 hcl).2
    rw [← hS] at this
    nlinarith
  have hSpos : 0 < S := by
    by_contra hcon
    have : S = 0 := le_antisymm (not_lt.1 hcon) hS0
    rw [this] at hHrS
    linarith
  have hV : weightedVariance (str025_prob h) (str025_test h ρ).fn = S * (1 - S / 4) := by
    rw [str025_variance, ← ha]
    have : a = 1 - S / 2 := by linarith
    rw [this]; ring
  have hη2 : η ^ 2 ≤ 1 / 4 := by nlinarith
  have hVpos : 0 < weightedVariance (str025_prob h) (str025_test h ρ).fn := by
    rw [hV]; apply mul_pos hSpos; nlinarith
  have hden : 0 < 2 + 10 * η := by linarith
  have hreal : 2 * (1 - η ^ 2 / 4) / (2 + 10 * η) * (2 * Hr) ≤ 4 * (S * (1 - S / 4)) := by
    have h1 : Hr / (2 + 10 * η) ≤ S := by rw [div_le_iff₀ hden]; linarith
    have h2 : 2 * (1 - η ^ 2 / 4) / (2 + 10 * η) * (2 * Hr) = 4 * (1 - η ^ 2 / 4) * (Hr / (2 + 10 * η)) := by
      field_simp; ring
    rw [h2]
    have h3 : 0 ≤ 1 - η ^ 2 / 4 := by linarith
    calc 4 * (1 - η ^ 2 / 4) * (Hr / (2 + 10 * η)) ≤ 4 * (1 - η ^ 2 / 4) * S :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 4 * (S * (1 - S / 4)) := by nlinarith
  have hP := (le_poincareRate_iff_forall (str025_prob h) (poincareRate (str025_prob h))).1 le_rfl
    (str025_test h ρ) hVpos
  rw [str025_fisher_eq h ρ,
    ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hH.ne')) (Or.inl (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top))]
  have hc0 : 0 ≤ 2 * (1 - η ^ 2 / 4) / (2 + 10 * η) := by
    have : 0 ≤ 1 - η ^ 2 / 4 := by linarith
    positivity
  calc ENNReal.ofReal (2 * (1 - η ^ 2 / 4) / (2 + 10 * η)) * poincareRate (str025_prob h) *
        (2 * ENNReal.ofReal Hr)
      = poincareRate (str025_prob h) * ENNReal.ofReal
        (2 * (1 - η ^ 2 / 4) / (2 + 10 * η) * (2 * Hr)) := by
        rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
        simp only [ENNReal.ofReal_ofNat]
        ring
    _ ≤ poincareRate (str025_prob h) * ENNReal.ofReal (4 * (S * (1 - S / 4))) :=
        by gcongr
    _ = 4 * (poincareRate (str025_prob h) *
          ENNReal.ofReal (weightedVariance (str025_prob h) (str025_test h ρ).fn)) := by
        rw [hV, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
        simp only [ENNReal.ofReal_ofNat]
        ring
    _ ≤ 4 * dirichletEnergy (str025_prob h) (str025_test h ρ) := by gcongr


theorem str025_sqrt_eq_of_entropy_zero (h : ℝ) (ρL : AbsoluteDensity 1)
    (h0 : ordinaryEntropy h ρL = 0) : ρL.sqrt =ᵐ[haar 1] str025_w h := by
  have hμ : (densityMeasure ρL : Measure (Torus 1)) = threefoldReference h :=
    relativeEntropy_zero_iff.1 h0
  rw [densityMeasure_coe] at hμ
  unfold threefoldReference at hμ
  have hqm : Measurable (referenceDensity h) := (continuous_referenceDensity h).measurable
  have hae := (withDensity_eq_iff_of_sigmaFinite
    (ρL.integrable_density.aemeasurable.ennreal_ofReal) hqm.ennreal_ofReal.aemeasurable).1 hμ
  have hae2 : ∀ᵐ x ∂haar 1, ρL.sqrt x ^ 2 = referenceDensity h x := by
    filter_upwards [hae] with x hx
    exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (referenceDensity_pos (h := h) x).le).1 hx
  filter_upwards [hae2, ρL.sqrt_nonneg] with x hx hx0
  rw [str025_w, ← hx, Real.sqrt_sq hx0]

theorem str025_ae_u_close (h : ℝ) (ρ : AbsoluteDensity 1) {ε : ℝ}
    (hae : ∀ᵐ x ∂haar 1, |ρ.sqrt x - str025_w h x| ≤ ε) :
    ∀ᵐ x ∂haar 1, |str025_u h ρ x - 1| ≤ |ε| * Real.exp |h| := by
  filter_upwards [hae] with x hx
  have hw := str025_w_pos h x
  have h1 : str025_u h ρ x - 1 = (ρ.sqrt x - str025_w h x) / str025_w h x := by
    rw [str025_u_eq]; field_simp
  rw [h1, abs_div, abs_of_pos hw, div_le_iff₀ hw]
  have : Real.exp |h| * str025_w h x ≥ 1 := by
    have := str025_w_ge h x
    calc 1 = Real.exp |h| * Real.exp (-|h|) := by rw [← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
  calc |ρ.sqrt x - str025_w h x| ≤ |ε| := hx.trans (le_abs_self _)
    _ = |ε| * 1 := by ring
    _ ≤ |ε| * (Real.exp |h| * str025_w h x) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = _ := by ring

theorem str025_endpoint_seq (h : ℝ) (ρ : ℕ → AbsoluteDensity 1)
    (hpos : ∀ n, 0 < ordinaryEntropy h (ρ n))
    (hH : Tendsto (fun n => ordinaryEntropy h (ρ n)) atTop (𝓝 0)) :
    poincareRate (str025_prob h) ≤
      liminf (fun n => ordinaryFisher h (ρ n) / (2 * ordinaryEntropy h (ρ n))) atTop := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨c, hc1, hc2⟩ := exists_between hlt
  have hfreq : ∃ᶠ n in atTop, ordinaryFisher h (ρ n) / (2 * ordinaryEntropy h (ρ n)) < c :=
    Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hc1
  obtain ⟨ψ, hψ, hψc⟩ := Filter.extraction_of_frequently_atTop hfreq
  have hcne : c ≠ ⊤ := (hc2.trans_le le_top).ne
  obtain ⟨B, hB0, hBn, φ, ρL, ε, hφ, hε, hae, -, hent, -, -⟩ :=
    circle_boundedQuotient_compactness (abs_nonneg h) c.toNNReal h le_rfl (fun n => ρ (ψ n))
      (fun n => hpos _) (fun n => by rw [ENNReal.coe_toNNReal hcne]; exact (hψc n).le)
  have h0 : ordinaryEntropy h ρL = 0 :=
    tendsto_nhds_unique hent (hH.comp (hψ.comp hφ).tendsto_atTop)
  have hs := str025_sqrt_eq_of_entropy_zero h ρL h0
  set η : ℕ → ℝ := fun n => |ε n| * Real.exp |h| with hη
  have hηt : Tendsto η atTop (𝓝 0) := by
    have := (hε.abs.mul_const (Real.exp |h|))
    simpa [hη] using this
  have hu : ∀ n, ∀ᵐ x ∂haar 1, |str025_u h (ρ (ψ (φ n))) x - 1| ≤ η n := fun n => by
    refine str025_ae_u_close h _ ?_
    filter_upwards [hae n, hs] with x hx hx2
    rwa [← hx2]
  have hev : ∀ᶠ n in atTop, η n ≤ 1 / 2 := hηt.eventually (ge_mem_nhds (by norm_num))
  have hbound : ∀ᶠ n in atTop, ENNReal.ofReal (2 * (1 - η n ^ 2 / 4) / (2 + 10 * η n)) *
      poincareRate (str025_prob h) ≤ c := by
    filter_upwards [hev] with n hn
    have hn0 : 0 ≤ η n := by positivity
    exact (str025_core h (ρ (ψ (φ n))) hn0 hn (hu n) (hpos _)).trans (hψc _).le
  have hlim : Tendsto (fun n => ENNReal.ofReal (2 * (1 - η n ^ 2 / 4) / (2 + 10 * η n)) *
      poincareRate (str025_prob h)) atTop (𝓝 (poincareRate (str025_prob h))) := by
    have h1 : Tendsto (fun n => 2 * (1 - η n ^ 2 / 4) / (2 + 10 * η n)) atTop
        (𝓝 (2 * (1 - 0 ^ 2 / 4) / (2 + 10 * 0))) := by
      refine Tendsto.div (tendsto_const_nhds.mul (tendsto_const_nhds.sub
        ((hηt.pow 2).div_const 4))) (tendsto_const_nhds.add (hηt.const_mul 10)) (by norm_num)
    have e : (2 * (1 - 0 ^ 2 / 4) / (2 + 10 * 0) : ℝ) = 1 := by norm_num
    rw [e] at h1
    have h2 := ENNReal.Tendsto.mul_const (b := poincareRate (str025_prob h)) (ENNReal.tendsto_ofReal h1)
      (Or.inl (by simp : ENNReal.ofReal 1 ≠ 0))
    simpa using h2
  exact absurd (le_of_tendsto hlim hbound) (not_le.2 hc2)


/-- The ordinary quotient `I(ρ | μ_h) / (2 H(ρ | μ_h))`. -/
noncomputable def str025_quot (h : ℝ) (ρ : AbsoluteDensity 1) : ℝ≥0∞ :=
  ordinaryFisher h ρ / (2 * ordinaryEntropy h ρ)

theorem str025_entropy_ne_top (h : ℝ) (ρ : AbsoluteDensity 1) : ordinaryEntropy h ρ ≠ ⊤ := by
  rw [ordinaryEntropy_eq]; exact ENNReal.ofReal_ne_top

theorem str025_fisher_ne_top (h : ℝ) (ρ : AbsoluteDensity 1) : ordinaryFisher h ρ ≠ ⊤ := by
  rw [ordinaryFisher_eq]; exact ENNReal.ofReal_ne_top

theorem str025_attainment (h : ℝ) (ρ₀ : AbsoluteDensity 1) (h0 : 0 < ordinaryEntropy h ρ₀)
    (hlt : str025_quot h ρ₀ < poincareRate (str025_prob h)) :
    ∃ ρs : AbsoluteDensity 1, 0 < ordinaryEntropy h ρs ∧
      ∀ ρ : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ → str025_quot h ρs ≤ str025_quot h ρ := by
  set Lp := poincareRate (str025_prob h) with hLp
  set r : ℝ≥0∞ := ⨅ ρ : {ρ : AbsoluteDensity 1 // 0 < ordinaryEntropy h ρ}, str025_quot h ρ.1 with hr
  have hrle : ∀ ρ : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ → r ≤ str025_quot h ρ :=
    fun ρ hρ => iInf_le (fun ρ : {ρ : AbsoluteDensity 1 // 0 < ordinaryEntropy h ρ} =>
      str025_quot h ρ.1) ⟨ρ, hρ⟩
  have hr0 : r ≤ str025_quot h ρ₀ := hrle ρ₀ h0
  have hrlt : r < Lp := hr0.trans_lt hlt
  have hrne : r ≠ ⊤ := (hrlt.trans_le le_top).ne
  have hex : ∀ n : ℕ, ∃ ρ : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ ∧
      str025_quot h ρ < r + ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have : r < r + ((n : ℝ≥0∞) + 1)⁻¹ :=
      ENNReal.lt_add_right hrne (by simp)
    obtain ⟨⟨ρ, hρ⟩, hρq⟩ := iInf_lt_iff.1 this
    exact ⟨ρ, hρ, hρq⟩
  choose ρ hρpos hρq using hex
  have hδ : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    refine this.congr (fun n => ?_)
    simp [Function.comp]
  have hδ' : Tendsto (fun n : ℕ => r + ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 r) := by
    simpa using tendsto_const_nhds.add hδ
  have hM : ∀ n, str025_quot h (ρ n) ≤ ((r + 1).toNNReal : ℝ≥0∞) := by
    intro n
    rw [ENNReal.coe_toNNReal (ENNReal.add_ne_top.2 ⟨hrne, ENNReal.one_ne_top⟩)]
    refine (hρq n).le.trans (add_le_add le_rfl ?_)
    rw [ENNReal.inv_le_one]
    exact le_add_self
  obtain ⟨B, hB0, hBn, φ, ρL, ε, hφ, hε, hae, hcE, hoE, hlscF, hlscO⟩ :=
    circle_boundedQuotient_compactness (abs_nonneg h) (r + 1).toNNReal h le_rfl ρ hρpos
      (fun n => hM n)
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hδφ : Tendsto (fun n => r + (((φ n : ℕ) : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 r) := hδ'.comp hφt
  by_cases hL : ordinaryEntropy h ρL = 0
  · exfalso
    have hend := str025_endpoint_seq h (fun n => ρ (φ n)) (fun n => hρpos (φ n)) (hL ▸ hoE)
    have hle : liminf (fun n => str025_quot h (ρ (φ n))) atTop ≤
        liminf (fun n => r + (((φ n : ℕ) : ℝ≥0∞) + 1)⁻¹) atTop :=
      liminf_le_liminf (Eventually.of_forall fun n => (hρq (φ n)).le)
    rw [hδφ.liminf_eq] at hle
    exact absurd (hend.trans hle) (not_le.2 hrlt)
  · have hLpos : 0 < ordinaryEntropy h ρL := pos_iff_ne_zero.2 hL
    refine ⟨ρL, hLpos, fun ρ' hρ' => ?_⟩
    have hI : ∀ n, ordinaryFisher h (ρ (φ n)) ≤
        (r + (((φ n : ℕ) : ℝ≥0∞) + 1)⁻¹) * (2 * ordinaryEntropy h (ρ (φ n))) := by
      intro n
      have hp := hρpos (φ n)
      have h2 : (2 : ℝ≥0∞) * ordinaryEntropy h (ρ (φ n)) ≠ 0 :=
        mul_ne_zero (by norm_num) hp.ne'
      have h3 : (2 : ℝ≥0∞) * ordinaryEntropy h (ρ (φ n)) ≠ ⊤ :=
        ENNReal.mul_ne_top (by norm_num) (str025_entropy_ne_top h _)
      exact (ENNReal.div_le_iff h2 h3).1 (hρq (φ n)).le
    have htend : Tendsto (fun n => (r + (((φ n : ℕ) : ℝ≥0∞) + 1)⁻¹) *
        (2 * ordinaryEntropy h (ρ (φ n)))) atTop (𝓝 (r * (2 * ordinaryEntropy h ρL))) :=
      ENNReal.Tendsto.mul hδφ (Or.inr (ENNReal.mul_ne_top (by norm_num)
        (str025_entropy_ne_top h _)))
        (ENNReal.Tendsto.const_mul hoE (Or.inr (by norm_num))) (Or.inr hrne)
    have h1 : ordinaryFisher h ρL ≤ r * (2 * ordinaryEntropy h ρL) := by
      refine hlscO.trans ?_
      calc _ ≤ liminf (fun n => (r + (((φ n : ℕ) : ℝ≥0∞) + 1)⁻¹) *
            (2 * ordinaryEntropy h (ρ (φ n)))) atTop :=
            liminf_le_liminf (Eventually.of_forall hI)
        _ = _ := htend.liminf_eq
    have h2 : str025_quot h ρL ≤ r := ENNReal.div_le_of_le_mul h1
    exact h2.trans (hrle ρ' hρ')


/-- STR025, part 1: the ordinary Gaussian endpoint and conditional attainment.  The endpoint bound
holds for every `h` (no smallness and no bounded-quotient hypothesis is needed); the Poincare rate
is taken for the reference probability measure `threefoldReference h`. -/
theorem ordinaryQuotient_gaussianEndpoint (h : ℝ) :
    (∀ ρ : ℕ → AbsoluteDensity 1, (∀ n, 0 < ordinaryEntropy h (ρ n)) →
      Tendsto (fun n => ordinaryEntropy h (ρ n)) atTop (𝓝 0) →
      DGPS.poincareRate ⟨threefoldReference h, isProbabilityMeasure_threefoldReference h⟩ ≤
        liminf (fun n => ordinaryFisher h (ρ n) / (2 * ordinaryEntropy h (ρ n))) atTop) ∧
    (∀ ρ₀ : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ₀ →
      ordinaryFisher h ρ₀ / (2 * ordinaryEntropy h ρ₀) <
        DGPS.poincareRate ⟨threefoldReference h, isProbabilityMeasure_threefoldReference h⟩ →
      ∃ ρs : AbsoluteDensity 1, 0 < ordinaryEntropy h ρs ∧
        ∀ ρ : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ →
          ordinaryFisher h ρs / (2 * ordinaryEntropy h ρs) ≤
            ordinaryFisher h ρ / (2 * ordinaryEntropy h ρ)) :=
  ⟨fun ρ hpos hH => str025_endpoint_seq h ρ hpos hH,
    fun ρ₀ h0 hlt => str025_attainment h ρ₀ h0 hlt⟩

end DGPS.Examples.ThreeSpeciesCircle
