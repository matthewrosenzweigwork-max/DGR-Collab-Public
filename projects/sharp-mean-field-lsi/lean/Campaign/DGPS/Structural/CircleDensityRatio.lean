import DGPS.Foundations.CircleRegularity
import DGPS.Structural.FrozenGibbsInformation
import DGPS.Structural.FrozenGibbsIdentities
import DGPS.Structural.ImprovingFamilySmall

/-!
# Circle density ratio under small frozen information (STR019)

On the circle (`d = 1`): if the absolute dissipation of `ρ` is below `e^(-M)` (for the barycenter of
an improving family this is STR018), the relative square root `u = √(ρ/p)` against the frozen Gibbs
reference `p = P(ρ m)` has a continuous `H¹` representative `w` with `∫ w² p dm = 1` and
`osc w ≤ ∫ |w'| dm ≤ (1/2) e^(M/2) √D(ρ) < 1/2`; consequently `1/2 < w < 3/2` and
`1/4 < ρ/p < 9/4` pointwise for the representative.

R5 notes. Route change (permitted by the spec): self-contained proof. The `L¹` oscillation bound
`|w x - w y| ≤ ∫ |g|` for a continuous `H¹` function is proved by smoothing
(`smooth_osc_le_integral_abs`, `circle_osc_le_integral_norm`); Cauchy-Schwarz and `p ≥ e^(-M)` give
`∫ |g| ≤ e^(M/2) (∫ |g|² p)^(1/2)`; `D = 4 ∫ |g|² p` is STR002. The nonnegative continuous
representative is `|w₀|` for the Sobolev representative `w₀`. The generic statement
`circle_densityRatio_of_dissipation_lt` needs only `D(ρ) < e^(-M)`; the named output
`smallFrozenInformation_circle_densityRatio` feeds it with STR018.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace DGPS.Structural

/-- Cauchy–Schwarz for nonnegative `L²` functions. -/
theorem integral_mul_le_sqrt_mul_sqrt {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f h : α → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hh0 : ∀ x, 0 ≤ h x)
    (hf : MemLp f 2 μ) (hh : MemLp h 2 μ) :
    ∫ x, f x * h x ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, h x ^ 2 ∂μ) := by
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (Eventually.of_forall hf0) (Eventually.of_forall hh0)
    (by simpa using hf) (by simpa using hh)
  simpa [Real.sqrt_eq_rpow, Real.rpow_two] using key

/-- L¹ oscillation for smooth periodic functions on the circle. -/
theorem smooth_osc_le_integral_abs {φ : Torus 1 → ℝ} (hφ : IsSmoothPeriodic φ) (x y : Torus 1) :
    |φ x - φ y| ≤ ∫ z, |coordPartial 0 φ z| ∂haar 1 := by
  have hc : Continuous fun s : ℝ => |coordPartial 0 φ (torusLift fun _ : Fin 1 => s)| :=
    ((hφ.continuous_coordPartial 0).comp continuous_circleParam).abs
  have hper : Function.Periodic
      (fun s : ℝ => |coordPartial 0 φ (torusLift fun _ : Fin 1 => s)|) 1 := by
    intro s
    simp only [torusLift_one_add]
  have hfull : ∀ c : ℝ, ∫ z, |coordPartial 0 φ z| ∂haar 1 =
      ∫ s in c..(c + 1), |coordPartial 0 φ (torusLift fun _ : Fin 1 => s)| := by
    intro c
    rw [hper.intervalIntegral_add_eq c 0,
      integral_haar_one (fun z => |coordPartial 0 φ z|) ((hφ.continuous_coordPartial 0).abs)]
    simp
  have step : ∀ a b : ℝ, a ≤ b → b ≤ a + 1 →
      |φ (torusLift fun _ : Fin 1 => b) - φ (torusLift fun _ : Fin 1 => a)| ≤
        ∫ z, |coordPartial 0 φ z| ∂haar 1 := by
    intro a b hab hb
    rw [← circle_smooth_ftc hφ a b, hfull a]
    refine (intervalIntegral.abs_integral_le_integral_abs hab).trans ?_
    exact intervalIntegral.integral_mono_interval le_rfl hab hb
      (Eventually.of_forall fun s => abs_nonneg _) (hc.intervalIntegrable _ _)
  obtain ⟨a, b, ha, hb, hab, hd⟩ := exists_lifts_one x y
  rw [← ha, ← hb]
  rcases le_total a b with h | h
  · rw [abs_sub_comm]
    exact step a b h (by
      have : |a - b| = b - a := by rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.mpr h)
      linarith)
  · exact step b a h (by
      have : |a - b| = a - b := abs_of_nonneg (sub_nonneg.mpr h)
      linarith)

/-- On `Torus 1`, the tangent norm is the absolute value of the coordinate. -/
theorem norm_tangent_one (v : Tangent 1) : ‖v‖ = |v 0| := by
  simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]

/-- `L¹` is dominated by `L²` on the probability space `Torus 1`. -/
theorem integral_abs_le_sqrt {f : Torus 1 → ℝ} (hf : MemLp f 2 (haar 1)) :
    ∫ x, |f x| ∂haar 1 ≤ Real.sqrt (∫ x, f x ^ 2 ∂haar 1) := by
  have h1 : MemLp (fun _ : Torus 1 => (1 : ℝ)) 2 (haar 1) := memLp_const 1
  have := integral_mul_le_sqrt_mul_sqrt (μ := haar 1) (f := fun x => |f x|) (h := fun _ => 1)
    (fun x => abs_nonneg _) (fun _ => zero_le_one) hf.abs h1
  simpa using this

/-- The `L¹` oscillation bound for a continuous `H¹` function on the circle. -/
theorem circle_osc_le_integral_norm {w : Torus 1 → ℝ} {g : Torus 1 → Tangent 1}
    (hw : Continuous w) (hg : IsWeakGradient w g) (x y : Torus 1) :
    |w x - w y| ≤ ∫ z, ‖g z‖ ∂haar 1 := by
  obtain ⟨v, hv, hvw, h1, h2⟩ := exists_smooth_tendsto_H1 hg
  have hT : TendstoUniformly v w atTop :=
    circle_tendstoUniformly_of_coord hvw hg (fun n => (hv n).continuous_torus)
      (fun n => ae_eq_refl _) hw (ae_eq_refl _) (by simpa using h1) (by simpa using h2 0)
  set t : ℕ → ℝ := fun n => (eLpNorm (fun z => smoothGrad (v n) z 0 - g z 0) 2
      (haar 1)).toReal with ht
  have htt : Tendsto t atTop (𝓝 0) := by
    have e := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (h2 0)
    rwa [ENNReal.toReal_zero] at e
  have hgm : MemLp (fun z => g z 0) 2 (haar 1) := memLp_coord hg.memLp_grad 0
  have hgn : Integrable (fun z => ‖g z‖) (haar 1) :=
    (hg.memLp_grad.integrable one_le_two).norm
  have hbound : ∀ n, |v n x - v n y| ≤ ∫ z, ‖g z‖ ∂haar 1 + t n := by
    intro n
    have hdm : MemLp (fun z => smoothGrad (v n) z 0 - g z 0) 2 (haar 1) :=
      (memLp_two_of_continuous ((hv n).continuous_coordPartial 0)).sub hgm
    have hdi : Integrable (fun z => |smoothGrad (v n) z 0 - g z 0|) (haar 1) :=
      (hdm.integrable one_le_two).abs
    have hci : Integrable (fun z => |coordPartial 0 (v n) z|) (haar 1) :=
      ((memLp_two_of_continuous ((hv n).continuous_coordPartial 0)).integrable
        one_le_two).abs
    have h3 : ∫ z, |coordPartial 0 (v n) z| ∂haar 1 ≤
        ∫ z, ‖g z‖ ∂haar 1 + t n := by
      calc ∫ z, |coordPartial 0 (v n) z| ∂haar 1
          ≤ ∫ z, (‖g z‖ + |smoothGrad (v n) z 0 - g z 0|) ∂haar 1 := by
            refine integral_mono hci (hgn.add hdi) fun z => ?_
            rw [norm_tangent_one]
            simp only [smoothGrad_apply]
            have := abs_sub_abs_le_abs_sub (coordPartial 0 (v n) z) (g z 0)
            linarith [abs_sub_comm (coordPartial 0 (v n) z) (g z 0)]
        _ = ∫ z, ‖g z‖ ∂haar 1 + ∫ z, |smoothGrad (v n) z 0 - g z 0| ∂haar 1 :=
            integral_add hgn hdi
        _ ≤ _ := by
            have h4 : t n = Real.sqrt (∫ z, (smoothGrad (v n) z 0 - g z 0) ^ 2 ∂haar 1) :=
              toReal_eLpNorm_two hdm
            have h5 := integral_abs_le_sqrt hdm
            linarith
    exact (smooth_osc_le_integral_abs (hv n) x y).trans h3
  have hlim : Tendsto (fun n => |v n x - v n y|) atTop (𝓝 |w x - w y|) :=
    ((hT.tendsto_at x).sub (hT.tendsto_at y)).abs
  have hlim2 : Tendsto (fun n => ∫ z, ‖g z‖ ∂haar 1 + t n) atTop (𝓝 (∫ z, ‖g z‖ ∂haar 1 + 0)) :=
    tendsto_const_nhds.add htt
  rw [add_zero] at hlim2
  exact le_of_tendsto_of_tendsto hlim hlim2 (Eventually.of_forall hbound)

/-- Weighted `L²` bound for the gradient: if `c ≤ p ≤ C` and `g ∈ L²`, then
`∫ ‖g‖ ≤ c^(-1/2) (∫ ‖g‖² p)^(1/2)`, stated with `c = exp (-M)`. -/
theorem integral_norm_le_exp_mul_sqrt {M : ℝ} {p : Torus 1 → ℝ} {g : Torus 1 → Tangent 1}
    (hpm : Measurable p) (hlo : ∀ x, Real.exp (-M) ≤ p x) (hhi : ∀ x, p x ≤ Real.exp M)
    (hg : MemLp g 2 (haar 1)) :
    ∫ z, ‖g z‖ ∂haar 1 ≤ Real.exp (M / 2) * Real.sqrt (∫ z, ‖g z‖ ^ 2 * p z ∂haar 1) := by
  have hp0 : ∀ x, 0 < p x := fun x => lt_of_lt_of_le (Real.exp_pos _) (hlo x)
  have hsm : Measurable fun x => Real.sqrt (p x) := hpm.sqrt
  have hgn : MemLp (fun z => ‖g z‖) 2 (haar 1) := hg.norm
  have hf : MemLp (fun z => ‖g z‖ * Real.sqrt (p z)) 2 (haar 1) := by
    refine hgn.of_le_mul (c := Real.sqrt (Real.exp M)) ?_ (Eventually.of_forall fun z => ?_)
    · exact hgn.aestronglyMeasurable.mul hsm.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)),
        Real.norm_of_nonneg (norm_nonneg _), mul_comm]
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hhi z)) (norm_nonneg _)
  have hh : MemLp (fun z => (Real.sqrt (p z))⁻¹) 2 (haar 1) := by
    refine MemLp.of_bound (hsm.inv.aestronglyMeasurable) (Real.exp (M / 2))
      (Eventually.of_forall fun z => ?_)
    have h1 : Real.exp (-M / 2) ≤ Real.sqrt (p z) := by
      rw [Real.exp_half]; exact Real.sqrt_le_sqrt (hlo z)
    have h2 : (Real.sqrt (p z))⁻¹ ≤ (Real.exp (-M / 2))⁻¹ := inv_anti₀ (Real.exp_pos _) h1
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    have e : (Real.exp (-M / 2))⁻¹ = Real.exp (M / 2) := by
      rw [← Real.exp_neg]; congr 1; ring
    rwa [e] at h2
  have key := integral_mul_le_sqrt_mul_sqrt (μ := haar 1) (fun z => by positivity)
    (fun z => by have := hp0 z; positivity) hf hh
  have e1 : (fun z => ‖g z‖ * Real.sqrt (p z) * (Real.sqrt (p z))⁻¹) = fun z => ‖g z‖ := by
    funext z
    have := Real.sqrt_pos.mpr (hp0 z)
    field_simp
  have e2 : (fun z => (‖g z‖ * Real.sqrt (p z)) ^ 2) = fun z => ‖g z‖ ^ 2 * p z := by
    funext z
    rw [mul_pow, Real.sq_sqrt (hp0 z).le]
  have hint2 : Integrable (fun z => ((Real.sqrt (p z))⁻¹) ^ 2) (haar 1) := hh.integrable_sq
  have h3 : ∫ z, ((Real.sqrt (p z))⁻¹) ^ 2 ∂haar 1 ≤ Real.exp M := by
    have : ∫ z, ((Real.sqrt (p z))⁻¹) ^ 2 ∂haar 1 ≤ ∫ _z, Real.exp M ∂haar 1 := by
      refine integral_mono hint2 (integrable_const _) fun z => ?_
      rw [inv_pow, Real.sq_sqrt (hp0 z).le]
      have h := hlo z
      calc (p z)⁻¹ ≤ (Real.exp (-M))⁻¹ := inv_anti₀ (Real.exp_pos _) h
        _ = Real.exp M := by rw [← Real.exp_neg, neg_neg]
    simpa using this
  rw [e1, e2] at key
  refine key.trans ?_
  have h4 : Real.sqrt (∫ z, ((Real.sqrt (p z))⁻¹) ^ 2 ∂haar 1) ≤ Real.exp (M / 2) := by
    rw [Real.exp_half]; exact Real.sqrt_le_sqrt h3
  calc _ ≤ Real.sqrt (∫ z, ‖g z‖ ^ 2 * p z ∂haar 1) * Real.exp (M / 2) :=
        mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
    _ = _ := mul_comm _ _

/-- Integrability of the weighted gradient energy density. -/
theorem integrable_norm_sq_mul {p : Torus 1 → ℝ} {C : ℝ} {g : Torus 1 → Tangent 1}
    (hpm : Measurable p) (hp0 : ∀ x, 0 < p x) (hhi : ∀ x, p x ≤ C)
    (hg : MemLp g 2 (haar 1)) : Integrable (fun z => ‖g z‖ ^ 2 * p z) (haar 1) := by
  have h2 : Integrable (fun z => ‖g z‖ ^ 2) (haar 1) := hg.norm.integrable_sq
  refine (h2.const_mul C).mono' (h2.aestronglyMeasurable.mul hpm.aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  have := hp0 z
  rw [Real.norm_of_nonneg (by positivity), mul_comm C]
  exact mul_le_mul_of_nonneg_left (hhi z) (sq_nonneg _)

/-- `4 ∫ ‖g‖ₑ² dP` for `P = p m` as the real integral `4 ∫ ‖g‖² p dm`. -/
theorem four_lintegral_withDensity_eq {p : Torus 1 → ℝ} {C : ℝ} {g : Torus 1 → Tangent 1}
    (hpm : Measurable p) (hp0 : ∀ x, 0 < p x) (hhi : ∀ x, p x ≤ C)
    (hg : MemLp g 2 (haar 1)) :
    4 * ∫⁻ x, ‖g x‖ₑ ^ 2 ∂((haar 1).withDensity fun x => ENNReal.ofReal (p x)) =
      ENNReal.ofReal (4 * ∫ z, ‖g z‖ ^ 2 * p z ∂haar 1) := by
  have hint := integrable_norm_sq_mul hpm hp0 hhi hg
  have hnn : 0 ≤ᵐ[haar 1] fun z => ‖g z‖ ^ 2 * p z :=
    Eventually.of_forall fun z => by have := hp0 z; positivity
  have hmeas : AEMeasurable (fun x => ‖g x‖ₑ ^ 2) (haar 1) :=
    hg.aestronglyMeasurable.enorm.pow_const 2
  have e1 : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂((haar 1).withDensity fun x => ENNReal.ofReal (p x)) =
      ∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2 * p z) ∂haar 1 := by
    rw [lintegral_withDensity_eq_lintegral_mul₀ (hpm.ennreal_ofReal.aemeasurable) hmeas]
    refine lintegral_congr fun z => ?_
    simp only [Pi.mul_apply]
    rw [enorm_sq_eq_ofReal_norm_sq, ← ENNReal.ofReal_mul (hp0 z).le, mul_comm]
  rw [e1, ← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem rpow_neg_half_sq_mul {p : ℝ} (hp : 0 < p) : (p ^ (-(1 / 2 : ℝ))) ^ 2 * p = 1 := by
  rw [Real.rpow_neg hp.le, ← Real.sqrt_eq_rpow, inv_pow, Real.sq_sqrt hp.le]
  exact inv_mul_cancel₀ hp.ne'

/-- The conclusion of STR019 for a density `ρ` on the circle, relative to the frozen Gibbs reference
`P(ρ m)` with density `p`: a continuous `H¹` representative `w` of `√(ρ/p)` with weak gradient `g`,
`D(ρ) = 4 ∫ |g|² dP`, normalization `∫ w² p dm = 1`, the oscillation chain
`osc w ≤ ∫ |g| dm ≤ (1/2) e^(M/2) √D < 1/2`, and the pointwise bounds `1/2 < w < 3/2`,
`1/4 < w² < 9/4`, where `w² p = ρ` almost everywhere. -/
def CircleDensityRatio (A : InteractionData 1) (b : AbsoluteDrift A) (ρ : AbsoluteDensity 1) :
    Prop :=
  ∃ (w : Torus 1 → ℝ) (g : Torus 1 → Tangent 1),
      Continuous w ∧
      w =ᵐ[haar 1] relativeSqrt (densityMeasure ρ : Measure (Torus 1))
        (frozenGibbs A (densityMeasure ρ)) ∧
      IsWeakGradient w g ∧
      scalarDissipation A b ρ =
        4 * ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(frozenGibbs A (densityMeasure ρ)).measure ∧
      ∫ x, w x ^ 2 * (frozenGibbs A (densityMeasure ρ)).density x ∂haar 1 = 1 ∧
      (∀ x y, |w x - w y| ≤ ∫ z, ‖g z‖ ∂haar 1) ∧
      ∫ z, ‖g z‖ ∂haar 1 ≤
        1 / 2 * Real.exp (totalOscillation A / 2) *
          Real.sqrt (scalarDissipation A b ρ).toReal ∧
      1 / 2 * Real.exp (totalOscillation A / 2) *
          Real.sqrt (scalarDissipation A b ρ).toReal < 1 / 2 ∧
      (∀ x, 1 / 2 < w x ∧ w x < 3 / 2) ∧
      ρ.density =ᵐ[haar 1] (fun x => w x ^ 2 * (frozenGibbs A (densityMeasure ρ)).density x) ∧
      (∀ x, 1 / 4 < w x ^ 2 ∧ w x ^ 2 < 9 / 4)

/-- **STR019 (generic form).** On the circle, if the absolute dissipation of `ρ` is below
`e^(-M)`, the relative square root `√(ρ/p)` against the frozen Gibbs reference `p = P(ρ m)` has a
continuous `H¹` representative `w` with `∫ w² p dm = 1`, oscillation at most `∫ |w'| dm`, bounded by
`(1/2) e^(M/2) √D < 1/2`, hence `1/2 < w < 3/2` and `1/4 < ρ/p < 9/4` (for the representative
`w²` of the density ratio). -/
theorem circle_densityRatio_of_dissipation_lt (A : InteractionData 1) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) (ρ : AbsoluteDensity 1)
    (hD : scalarDissipation A b ρ < ENNReal.ofReal (Real.exp (-totalOscillation A))) :
    CircleDensityRatio A b ρ := by
  unfold CircleDensityRatio
  set M := totalOscillation A with hM
  set ν := densityMeasure ρ with hν
  set P := frozenGibbs A ν with hP
  have hub := (DGPS.Structural.frozenGibbs_uniform_bounds A hLip).1 ν
  have hlo : ∀ x, Real.exp (-M) ≤ P.density x := fun x => (hub x).1
  have hhi : ∀ x, P.density x ≤ Real.exp M := fun x => (hub x).2
  have hp0 : ∀ x, 0 < P.density x := fun x => lt_of_lt_of_le (Real.exp_pos _) (hlo x)
  have hpm : Measurable P.density := P.measurable_density
  obtain ⟨g, hg⟩ := (mem_weightedH1_iff P).1 (relativeSqrt_mem_weightedH1 A hLip ρ ρ)
  have hνac : (ν : Measure (Torus 1)) ≪ P.measure :=
    (withDensity_absolutelyContinuous _ _).trans P.haar_ac_measure
  have hDeq : scalarDissipation A b ρ = 4 * ∫⁻ x, ‖g x‖ₑ ^ 2 ∂P.measure := by
    rw [nonlinearDissipation_eq_frozenInformation A hLip b ρ]
    exact ordinaryRelativeFisher_eq hνac hg
  set J := ∫ z, ‖g z‖ ^ 2 * P.density z ∂haar 1 with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun z => by have := hp0 z; positivity
  have hDval : scalarDissipation A b ρ = ENNReal.ofReal (4 * J) := by
    rw [hDeq]
    exact four_lintegral_withDensity_eq hpm hp0 hhi hg.memLp_grad
  have hJlt : 4 * J < Real.exp (-M) := by
    rw [hDval] at hD
    exact (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).1 hD
  have hDtoReal : (scalarDissipation A b ρ).toReal = 4 * J := by
    rw [hDval, ENNReal.toReal_ofReal (by positivity)]
  have hsq4 : Real.sqrt (4 * J) = 2 * Real.sqrt J := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hcs := integral_norm_le_exp_mul_sqrt hpm hlo hhi hg.memLp_grad
  have hbound : ∫ z, ‖g z‖ ∂haar 1 ≤
      1 / 2 * Real.exp (M / 2) * Real.sqrt (scalarDissipation A b ρ).toReal := by
    rw [hDtoReal, hsq4]
    linarith
  have hstrict : 1 / 2 * Real.exp (M / 2) * Real.sqrt (scalarDissipation A b ρ).toReal < 1 / 2 := by
    rw [hDtoReal]
    have h1 : Real.sqrt (4 * J) < Real.exp (-M / 2) := by
      rw [Real.exp_half]
      exact Real.sqrt_lt_sqrt (by positivity) hJlt
    have h2 : Real.exp (M / 2) * Real.exp (-M / 2) = 1 := by
      rw [← Real.exp_add, show M / 2 + -M / 2 = 0 by ring, Real.exp_zero]
    have h3 := mul_lt_mul_of_pos_left h1 (Real.exp_pos (M / 2))
    rw [h2] at h3
    linarith
  -- continuous representative
  obtain ⟨w0, hw0c, hw0ae, -, -, -⟩ := sobolev_embedding_dim_one hg
  set W : Torus 1 → ℝ := fun x => |w0 x| with hW
  have hWc : Continuous W := hw0c.abs
  have hWae : W =ᵐ[haar 1] relativeSqrt (ν : Measure (Torus 1)) P := by
    filter_upwards [hw0ae] with x hx
    show |w0 x| = _
    rw [hx]
    exact abs_of_nonneg (Real.sqrt_nonneg _)
  have hgW : IsWeakGradient W g := hg.congr_ae hWae.symm (Filter.EventuallyEq.refl _ _)
  have hosc : ∀ x y, |W x - W y| ≤ ∫ z, ‖g z‖ ∂haar 1 := circle_osc_le_integral_norm hWc hgW
  have hlt12 : ∫ z, ‖g z‖ ∂haar 1 < 1 / 2 := lt_of_le_of_lt hbound hstrict
  -- the density ratio
  have habs : (fun x => Real.sqrt ((ν : Measure (Torus 1)).rnDeriv (haar 1) x).toReal) =ᵐ[haar 1]
      ρ.sqrt := by
    have h := Measure.rnDeriv_withDensity₀ (haar 1)
      (f := fun x => ENNReal.ofReal (ρ.sqrt x ^ 2))
      (by exact (ρ.memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal)
    filter_upwards [h, ρ.sqrt_nonneg] with x hx hx0
    rw [hν, densityMeasure_coe, hx, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq hx0]
  have hsq : (fun x => W x ^ 2 * P.density x) =ᵐ[haar 1] ρ.density := by
    filter_upwards [hWae, RelativeFisher.relativeSqrt_ae_eq P (ν : Measure (Torus 1)), habs]
      with x h1 h2 h3
    rw [h1, h2, h3, mul_pow, mul_assoc, rpow_neg_half_sq_mul (hp0 x)]
    simp [AbsoluteDensity.density]
  have hmass : ∫ x, W x ^ 2 * P.density x ∂haar 1 = 1 := by
    rw [integral_congr_ae hsq]
    exact ρ.mass_one
  have hWint : Integrable (fun x => W x ^ 2 * P.density x) (haar 1) :=
    Integrable.of_integral_ne_zero (by rw [hmass]; norm_num)
  have hpint : Integrable P.density (haar 1) :=
    Integrable.of_integral_ne_zero (by rw [P.mass_one]; norm_num)
  -- the maximum and minimum of `W` straddle `1`
  obtain ⟨x1, -, hx1'⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hWc.continuousOn
  obtain ⟨x2, -, hx2'⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hWc.continuousOn
  have hx1 : ∀ x, W x ≤ W x1 := fun x => hx1' (Set.mem_univ x)
  have hx2 : ∀ x, W x2 ≤ W x := fun x => hx2' (Set.mem_univ x)
  have hW0 : ∀ x, 0 ≤ W x := fun x => abs_nonneg _
  have hmax : 1 ≤ W x1 := by
    by_contra hlt
    replace hlt := not_le.mp hlt
    have h1 : ∫ x, W x ^ 2 * P.density x ∂haar 1 ≤ ∫ x, W x1 ^ 2 * P.density x ∂haar 1 :=
      integral_mono hWint (hpint.const_mul _) fun x =>
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hW0 x) (hx1 x) 2) (hp0 x).le
    rw [integral_const_mul, P.mass_one, hmass] at h1
    nlinarith [hW0 x1]
  have hmin : W x2 ≤ 1 := by
    by_contra hlt
    replace hlt := not_le.mp hlt
    have h1 : ∫ x, W x2 ^ 2 * P.density x ∂haar 1 ≤ ∫ x, W x ^ 2 * P.density x ∂haar 1 :=
      integral_mono (hpint.const_mul _) hWint fun x =>
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hW0 x2) (hx2 x) 2) (hp0 x).le
    rw [integral_const_mul, P.mass_one, hmass] at h1
    nlinarith [hW0 x2]
  have hrange : ∀ x, 1 / 2 < W x ∧ W x < 3 / 2 := by
    intro x
    have a1 := hosc x x2
    have a2 := hosc x1 x
    have b1 := le_abs_self (W x - W x2)
    have b2 := le_abs_self (W x1 - W x)
    constructor <;> linarith
  refine ⟨W, g, hWc, hWae, hgW, hDeq, hmass, hosc, hbound, hstrict, hrange, hsq.symm, fun x => ?_⟩
  obtain ⟨h1, h2⟩ := hrange x
  constructor <;> nlinarith

/-- **STR019.** Under the STR018 hypotheses (an improving family with small quotient `D/(2G)`),
the relative square root of the barycenter against its frozen Gibbs reference has a continuous
`H¹` circle representative `w` with `∫ w² p dm = 1`,
`osc w ≤ ∫ |w'| dm ≤ (1/2) e^(M/2) √D(ρ̄) < 1/2`, hence `1/2 < w < 3/2` and `1/4 < ρ̄/p < 9/4`
pointwise for the representative. -/
theorem smallFrozenInformation_circle_densityRatio (A : InteractionData 1)
    (hLip : LipschitzData A) (b : AbsoluteDrift A) (F : SpeciesFamily 1) (rs : ℝ)
    (hM : 0 < totalOscillation A) (hrs : 0 < rs)
    (h9 : rs ≤ (frozenLSRateInf A).toReal / 9)
    (hexp : rs ≤ Real.exp (-totalOscillation A) / (4 * totalOscillation A))
    (hG : 0 < speciesGap A F)
    (himp : speciesDissipation A b F / (2 * (speciesGap A F : ℝ≥0∞)) < ENNReal.ofReal rs) :
    CircleDensityRatio A b (barycenter F) :=
  circle_densityRatio_of_dissipation_lt A hLip b (barycenter F)
    (improvingFamily_gap_and_dissipation_small A hLip b F rs hM hrs h9 hexp hG himp).2.2.2.2.2.2.2

end DGPS.Structural
