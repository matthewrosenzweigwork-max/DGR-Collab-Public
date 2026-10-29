import DGPS.Circle.AngularNormalization
import DGPS.Model.Data

open MeasureTheory Real Set Filter Topology
open DGPS.Circle.AngularNormalization

/-!
# Engineered rank-one family definition (EX030)

SETUP-T10 in the angular variable `θ = 2π x` (`angEquiv`, EX001): `U = 1 - cos θ`,
`A_h = 1 + coth h`, `c_h = 1 + tanh h`, `Λ_h = h coth h`, the correction
`R_h(u) = ∫₀^u N_h(v) / (v (2 - v)) dv` with the integrand continuously extended by its removable
endpoint values (`integrand`), the positive normalization `Z_h`, density `q_h`, `E_h`, and the
potentials `V = hU + R_h(U) + E_h²/2`, `W = -(E_h(θ) - E_h(φ))²/2` (coupling one) packaged as
`DGPS.InteractionData 1` for `h ≥ 2`. Main output: `DGPS.Examples.engineered_rank_one_family_definition`.
-/

namespace DGPS.Examples.EngineeredRankOne

noncomputable def aH (h : ℝ) : ℝ := 1 + cosh h / sinh h
noncomputable def numer (h v : ℝ) : ℝ := aH h * (1 - exp (-h * v)) - v

theorem aH_mul (h : ℝ) (hh : 0 < h) : aH h * (1 - exp (-h * 2)) = 2 := by
  have hs : exp h - exp (-h) ≠ 0 := by
    have := Real.sinh_pos_iff.2 hh
    rw [Real.sinh_eq] at this; intro h0; rw [h0] at this; simp at this
  have e1 : exp (-h * 2) = exp (-h) * exp (-h) := by rw [← Real.exp_add]; ring_nf
  have e2 : exp h * exp (-h) = 1 := by rw [← Real.exp_add]; simp
  unfold aH
  rw [Real.sinh_eq, Real.cosh_eq, e1]
  have : (exp h - exp (-h)) / 2 ≠ 0 := by intro h0; apply hs; linarith
  field_simp
  linear_combination (-2 * exp (-h)) * e2

theorem numer_zero (h : ℝ) : numer h 0 = 0 := by simp [numer]
theorem numer_two (h : ℝ) (hh : 0 < h) : numer h 2 = 0 := by
  unfold numer; rw [aH_mul h hh]; ring

theorem hasDerivAt_numer (h v : ℝ) :
    HasDerivAt (numer h) (aH h * h * exp (-h * v) - 1) v := by
  have h1 : HasDerivAt (fun v : ℝ => -h * v) (-h) v := by
    simpa using (hasDerivAt_id v).const_mul (-h)
  have h2 := h1.exp
  have h3 : HasDerivAt (fun y : ℝ => aH h * (1 - exp (-h * y)))
      (aH h * (0 - exp (-h * v) * -h)) v :=
    ((hasDerivAt_const v (1:ℝ)).sub h2).const_mul (aH h)
  have h4 : HasDerivAt (fun y : ℝ => aH h * (1 - exp (-h * y)) - y)
      (aH h * (0 - exp (-h * v) * -h) - 1) v := h3.sub (hasDerivAt_id v)
  exact h4.congr_deriv (by ring)

noncomputable def integrand (h v : ℝ) : ℝ :=
  if v = 0 then (aH h * h - 1) / 2
  else if v = 2 then -(aH h * h * exp (-h * 2) - 1) / 2
  else numer h v / (v * (2 - v))

theorem integrand_of_ne (h : ℝ) {v : ℝ} (h0 : v ≠ 0) (h2 : v ≠ 2) :
    integrand h v = numer h v / (v * (2 - v)) := by
  simp [integrand, h0, h2]

theorem continuousAt_integrand_zero (h : ℝ) : ContinuousAt (integrand h) 0 := by
  rw [continuousAt_iff_punctured_nhds]
  have hd := (hasDerivAt_numer h 0).tendsto_slope
  have hc : Tendsto (fun v : ℝ => (2 - v)⁻¹) (𝓝[≠] 0) (𝓝 ((2 - 0)⁻¹)) :=
    (((continuous_const.sub continuous_id).continuousAt (x := 0)).inv₀ (by norm_num)).tendsto.mono_left
      nhdsWithin_le_nhds
  have hm := hd.mul hc
  have hv : integrand h 0 = (aH h * h * exp (-h * 0) - 1) * (2 - 0)⁻¹ := by
    simp [integrand]; ring
  rw [hv]
  refine hm.congr' ?_
  have h1 : ∀ᶠ v : ℝ in 𝓝[≠] 0, v ≠ 2 := by
    have : ∀ᶠ v : ℝ in 𝓝 0, v ≠ 2 := (isOpen_ne.mem_nhds (by norm_num))
    exact nhdsWithin_le_nhds this
  filter_upwards [h1, self_mem_nhdsWithin] with v hv2 hv0
  have hv0' : v ≠ 0 := hv0
  rw [integrand_of_ne h hv0' hv2, slope_def_field, numer_zero]
  have : (2 - v) ≠ 0 := sub_ne_zero.2 (Ne.symm hv2)
  field_simp
  ring

theorem continuousAt_integrand_two (h : ℝ) (hh : 0 < h) : ContinuousAt (integrand h) 2 := by
  rw [continuousAt_iff_punctured_nhds]
  have hd := (hasDerivAt_numer h 2).tendsto_slope
  have hc : Tendsto (fun v : ℝ => v⁻¹) (𝓝[≠] 2) (𝓝 ((2:ℝ)⁻¹)) :=
    ((continuousAt_id (x := (2:ℝ))).inv₀ (by norm_num)).tendsto.mono_left nhdsWithin_le_nhds
  have hm := (hd.mul hc).neg
  have hv : integrand h 2 = -((aH h * h * exp (-h * 2) - 1) * (2:ℝ)⁻¹) := by
    simp [integrand]; ring
  rw [hv]
  refine hm.congr' ?_
  have h1 : ∀ᶠ v : ℝ in 𝓝[≠] 2, v ≠ 0 := by
    have : ∀ᶠ v : ℝ in 𝓝 2, v ≠ 0 := (isOpen_ne.mem_nhds (by norm_num))
    exact nhdsWithin_le_nhds this
  filter_upwards [h1, self_mem_nhdsWithin] with v hv0 hv2
  have hv2' : v ≠ 2 := hv2
  rw [integrand_of_ne h hv0 hv2', slope_def_field, numer_two h hh]
  have : (v - 2) ≠ 0 := sub_ne_zero.2 hv2'
  have h3 : (2 - v) ≠ 0 := sub_ne_zero.2 (Ne.symm hv2')
  field_simp
  ring

theorem continuousOn_integrand (h : ℝ) (hh : 0 < h) : ContinuousOn (integrand h) (Icc 0 2) := by
  intro v hv
  by_cases h0 : v = 0
  · subst h0; exact (continuousAt_integrand_zero h).continuousWithinAt
  by_cases h2 : v = 2
  · subst h2; exact (continuousAt_integrand_two h hh).continuousWithinAt
  have ev : ∀ᶠ w : ℝ in 𝓝 v, w ≠ 0 ∧ w ≠ 2 :=
    Filter.Eventually.and (isOpen_ne.mem_nhds h0) (isOpen_ne.mem_nhds h2)
  have hc : ContinuousAt (fun w : ℝ => numer h w / (w * (2 - w))) v := by
    have hn : Continuous (numer h) := by
      unfold numer; fun_prop
    have h2' : v * (2 - v) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.2 (Ne.symm h2))
    exact hn.continuousAt.div (by fun_prop) h2'
  exact (hc.congr (by filter_upwards [ev] with w hw; exact (integrand_of_ne h hw.1 hw.2).symm)).continuousWithinAt

noncomputable def corr (h u : ℝ) : ℝ := ∫ v in (0:ℝ)..u, integrand h v

theorem continuousOn_corr (h : ℝ) (hh : 0 < h) : ContinuousOn (corr h) (Icc 0 2) := by
  have hint : IntervalIntegrable (integrand h) volume 0 2 :=
    (continuousOn_integrand h hh).intervalIntegrable_of_Icc (by norm_num)
  have := intervalIntegral.continuousOn_primitive_interval' hint (a := 0) (by simp)
  rw [uIcc_of_le (show (0:ℝ) ≤ 2 by norm_num)] at this
  exact this


noncomputable def cH (h : ℝ) : ℝ := 1 + tanh h
noncomputable def lamH (h : ℝ) : ℝ := h * (cosh h / sinh h)

/-- `U = 1 - cos θ` on the angular circle. -/
noncomputable def Uang (θ : AngCircle) : ℝ := 1 - Real.Angle.cos θ

theorem Uang_mem (θ : AngCircle) : Uang θ ∈ Icc (0:ℝ) 2 := by
  have h1 : Real.Angle.cos θ ≤ 1 := by
    induction θ using Real.Angle.induction_on with
    | _ x => rw [Real.Angle.cos_coe]; exact Real.cos_le_one x
  have h2 : -1 ≤ Real.Angle.cos θ := by
    induction θ using Real.Angle.induction_on with
    | _ x => rw [Real.Angle.cos_coe]; exact Real.neg_one_le_cos x
  unfold Uang
  constructor <;> linarith

theorem continuous_Uang : Continuous Uang := by
  unfold Uang
  exact continuous_const.sub Real.Angle.continuous_cos

noncomputable def Eang (h : ℝ) (θ : AngCircle) : ℝ := (exp (h * Uang θ) - cH h) / tanh h

noncomputable def logq (h : ℝ) (θ : AngCircle) : ℝ := -(h * Uang θ) - corr h (Uang θ)

theorem continuous_corrU (h : ℝ) (hh : 0 < h) : Continuous (fun θ : AngCircle => corr h (Uang θ)) :=
  (continuousOn_corr h hh).comp_continuous continuous_Uang Uang_mem

theorem continuous_logq (h : ℝ) (hh : 0 < h) : Continuous (logq h) := by
  unfold logq
  exact (continuous_const.mul continuous_Uang).neg.sub (continuous_corrU h hh)

/-- The normalizing constant `Z_h = ∫ exp(-hU - R_h(U)) dθ/(2π)`. -/
noncomputable def Zh (h : ℝ) : ℝ := ∫ θ, exp (logq h θ) ∂angHaar

theorem Zh_pos (h : ℝ) (hh : 0 < h) : 0 < Zh h := by
  have hi : Integrable (fun θ => exp (logq h θ)) angHaar :=
    (continuous_exp.comp (continuous_logq h hh)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact integral_exp_pos hi

/-- The reference density `q_h` with respect to the normalized angular Haar measure. -/
noncomputable def qAng (h : ℝ) (θ : AngCircle) : ℝ := (Zh h)⁻¹ * exp (logq h θ)

theorem qAng_pos (h : ℝ) (hh : 0 < h) (θ : AngCircle) : 0 < qAng h θ :=
  mul_pos (inv_pos.2 (Zh_pos h hh)) (exp_pos _)

theorem integral_qAng (h : ℝ) (hh : 0 < h) : ∫ θ, qAng h θ ∂angHaar = 1 := by
  unfold qAng
  rw [integral_const_mul]
  have := (Zh_pos h hh).ne'
  change (Zh h)⁻¹ * Zh h = 1
  field_simp

/-- One-body potential in the angular variable: `V = hU + R_h(U) + E_h²/2`. -/
noncomputable def Vang (h : ℝ) (θ : AngCircle) : ℝ :=
  h * Uang θ + corr h (Uang θ) + Eang h θ ^ 2 / 2

/-- Interaction in the angular variables: `W = -(E_h(θ) - E_h(φ))²/2`. -/
noncomputable def Wang (h : ℝ) (θ φ : AngCircle) : ℝ := -(Eang h θ - Eang h φ) ^ 2 / 2

theorem continuous_Eang (h : ℝ) : Continuous (Eang h) := by
  unfold Eang
  exact ((continuous_const.mul continuous_Uang).rexp.sub continuous_const).div_const _

theorem continuous_Vang (h : ℝ) (hh : 0 < h) : Continuous (Vang h) := by
  unfold Vang
  exact (((continuous_const.mul continuous_Uang).add (continuous_corrU h hh)).add
    ((continuous_Eang h).pow 2 |>.div_const 2))

theorem continuous_angEquiv : Continuous angEquiv := by
  have : (angEquiv : Torus 1 → AngCircle) = fun x => angHomeo (x 0) := rfl
  rw [this]
  exact angHomeo.continuous.comp (continuous_apply 0)

end DGPS.Examples.EngineeredRankOne

namespace DGPS.Models

open DGPS.Examples.EngineeredRankOne

/-- The engineered rank-one interaction data (SETUP-T10) for `h ≥ 2`, as `InteractionData 1`
on the unit-period torus through `θ = 2π x` (`angEquiv`). The coupling is exactly one. -/
noncomputable def engineeredRankOne (h : ℝ) (hh : 2 ≤ h) : InteractionData 1 where
  V := fun x => Vang h (angEquiv x)
  W := fun x y => Wang h (angEquiv x) (angEquiv y)
  V_continuous := (continuous_Vang h (by linarith)).comp continuous_angEquiv
  W_continuous := by
    unfold Wang
    have hE : Continuous fun x : Torus 1 => Eang h (angEquiv x) :=
      (continuous_Eang h).comp continuous_angEquiv
    have h1 : Continuous fun p : Torus 1 × Torus 1 => Eang h (angEquiv p.1) :=
      hE.comp continuous_fst
    have h2 : Continuous fun p : Torus 1 × Torus 1 => Eang h (angEquiv p.2) :=
      hE.comp continuous_snd
    exact (((h1.sub h2).pow 2).neg).div_const 2
  W_symm := fun x y => by unfold Wang; ring
  W_diag := fun x => by unfold Wang; ring

/-- The engineered reference measure `q_h m` on the unit-period torus. -/
noncomputable def engineeredReference (h : ℝ) : MeasureTheory.Measure (Torus 1) :=
  (angHaar.withDensity fun θ => ENNReal.ofReal (qAng h θ)).map angEquiv.symm

end DGPS.Models

namespace DGPS.Examples

open DGPS.Examples.EngineeredRankOne DGPS.Models

theorem engineeredReference_isProbability (h : ℝ) (hh : 0 < h) :
    IsProbabilityMeasure (engineeredReference h) := by
  constructor
  unfold engineeredReference
  rw [Measure.map_apply angEquiv.symm.measurable MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hi : Integrable (qAng h) angHaar := by
    unfold qAng
    exact ((continuous_exp.comp (continuous_logq h hh)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun θ => (qAng_pos h hh θ).le),
    integral_qAng h hh]
  simp

/-- EX030: the engineered rank-one family is fixed by the displayed formulas. -/
theorem engineered_rank_one_family_definition (h : ℝ) (hh : 2 ≤ h) :
    (aH h = 1 + cosh h / sinh h ∧ cH h = 1 + tanh h ∧ lamH h = h * (cosh h / sinh h)) ∧
    ContinuousOn (integrand h) (Icc 0 2) ∧
    (∀ v ∈ Ioo (0:ℝ) 2,
      integrand h v = (aH h * (1 - exp (-h * v)) - v) / (v * (2 - v))) ∧
    integrand h 0 = (aH h * h - 1) / 2 ∧
    integrand h 2 = -(aH h * h * exp (-h * 2) - 1) / 2 ∧
    (∀ u, corr h u = ∫ v in (0:ℝ)..u, integrand h v) ∧
    0 < Zh h ∧
    (∀ θ : AngCircle, qAng h θ =
      (Zh h)⁻¹ * exp (-(h * (1 - Real.Angle.cos θ)) - corr h (1 - Real.Angle.cos θ))) ∧
    ∫ θ, qAng h θ ∂angHaar = 1 ∧
    IsProbabilityMeasure (engineeredReference h) ∧
    (∀ x : Torus 1, (engineeredRankOne h hh).V x =
      h * (1 - Real.Angle.cos (angEquiv x)) + corr h (1 - Real.Angle.cos (angEquiv x)) +
        ((exp (h * (1 - Real.Angle.cos (angEquiv x))) - (1 + tanh h)) / tanh h) ^ 2 / 2) ∧
    (∀ x y : Torus 1, (engineeredRankOne h hh).W x y =
      -(((exp (h * (1 - Real.Angle.cos (angEquiv x))) - (1 + tanh h)) / tanh h) -
        ((exp (h * (1 - Real.Angle.cos (angEquiv y))) - (1 + tanh h)) / tanh h)) ^ 2 / 2) := by
  have hp : 0 < h := by linarith
  refine ⟨⟨rfl, rfl, rfl⟩, continuousOn_integrand h hp, ?_, ?_, ?_, fun u => rfl, Zh_pos h hp,
    fun θ => rfl, integral_qAng h hp, engineeredReference_isProbability h hp,
    fun x => rfl, fun x y => rfl⟩
  · intro v hv
    exact integrand_of_ne h hv.1.ne' hv.2.ne
  · simp [integrand]
  · simp [integrand]

end DGPS.Examples
