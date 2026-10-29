import DGPS.Examples.EngineeredRankOneTiltedMeasure

/-!
# Engineered antipodal tail cancellation (EX044)

For `h ≥ 2`, `Ω = {U ≥ 1/2}`, `Δ = h (2 - U)`, `g = f - 1`, `T ≤ 1` and `S = h e^{2h} T`:
`∫_Ω Δ g² dμ_h ≤ C T`, `∫_{Δ ≤ r} g² dμ_h ≤ C T e^r / √S`, `∫_Ω g² dμ_h ≤ C T / log S`
for `S ≥ 3`, and `∫_Ω Φ(f²) dμ_h ≤ C T` with `Φ(s) = s log s - s + 1`.
Main output: `DGPS.Examples.engineered_antipodal_tail_cancellation`.
-/

open MeasureTheory Real Set Filter Topology
open scoped ContDiff ENNReal
open DGPS.Circle.AngularNormalization
open DGPS.Circle.StationaryFlux

namespace DGPS.Examples.EngineeredRankOneEX044

open DGPS.Models DGPS.Examples.EngineeredRankOne DGPS.Examples.EngineeredGroundState
  DGPS.Examples.EngineeredHardy DGPS.Examples.EngineeredRankOneEX042

lemma sin_sq_Uang_ex044 (θ : AngCircle) :
    Real.Angle.sin θ ^ 2 = Uang θ * (2 - Uang θ) := by
  unfold Uang
  have := (by induction θ using Real.Angle.induction_on with
    | _ x => rw [Real.Angle.sin_coe, Real.Angle.cos_coe]; exact Real.sin_sq_add_cos_sq x :
    Real.Angle.sin θ ^ 2 + Real.Angle.cos θ ^ 2 = 1)
  nlinarith

lemma sin_angSec_ex044 (θ : AngCircle) : Real.sin (angSec θ) = Real.Angle.sin θ := by
  have h1 := Real.Angle.sin_coe (angSec θ)
  have h2 : ((angSec θ : ℝ) : Real.Angle) = θ := coe_angSec θ
  rw [h2] at h1
  exact h1.symm

lemma smooth_potential_ex044 {C : ℝ} (h : ℝ) (hh : 0 < h)
    (hV : ∀ t, h ^ 2 * Real.sin t ^ 2 / 4 - C * h ≤ groundPot h t) {g : AngCircle → ℝ}
    (hg : IsSmoothAngular g) :
    h ^ 2 / 4 * ∫ θ, (g θ * (Real.Angle.sin θ * sAng h θ)) ^ 2 ∂angHaar ≤
      ∫ θ, (angDeriv g θ * sAng h θ) ^ 2 ∂angHaar +
        C * h * ∫ θ, (g θ * sAng h θ) ^ 2 ∂angHaar := by
  obtain ⟨hsm, hid⟩ := periodic_part h hh hg
  have hs := isSmoothAngular_sAng h hh
  have hw : groundStateConj h g = fun θ => g θ * sAng h θ := by
    funext θ
    unfold groundStateConj
    rw [← sAng_sq h hh θ, Real.sqrt_sq (sAng_pos h hh θ).le]
  have cw : Continuous (groundStateConj h g) := continuous_of_smooth hsm
  have cdw : Continuous (angDeriv (groundStateConj h g)) :=
    continuous_of_smooth (smooth_angDeriv hsm)
  obtain ⟨B, hB⟩ := bounded_groundPot_angSec_ex042 h hh
  have hVm : AEStronglyMeasurable (fun θ => groundPot h (angSec θ)) angHaar :=
    ((continuous_groundPot h hh).measurable.comp
      DGPS.FiniteN.Tools.UniformVonMises.measurable_angSec).aestronglyMeasurable
  have i1 : Integrable (fun θ => angDeriv (groundStateConj h g) θ ^ 2) angHaar :=
    integrable_angHaar_of_continuous (cdw.pow 2)
  have i2 : Integrable (fun θ => groundStateConj h g θ ^ 2) angHaar :=
    integrable_angHaar_of_continuous (cw.pow 2)
  have i3 : Integrable (fun θ => groundStateConj h g θ ^ 2 * groundPot h (angSec θ)) angHaar :=
    i2.mul_bdd hVm (Eventually.of_forall fun θ => by simpa using hB θ)
  have i4 : Integrable (fun θ => angDeriv (groundStateConj h g) θ ^ 2 +
      groundPot h (angSec θ) * groundStateConj h g θ ^ 2) angHaar := by
    refine i1.add (i3.congr (Eventually.of_forall fun θ => ?_))
    simp only; ring
  have cσ : Continuous fun θ : AngCircle => Real.Angle.sin θ := Real.Angle.continuous_sin
  have i5 : Integrable (fun θ => (g θ * (Real.Angle.sin θ * sAng h θ)) ^ 2) angHaar :=
    integrable_angHaar_of_continuous
      (((continuous_of_smooth hg).mul (cσ.mul (continuous_of_smooth hs))).pow 2)
  have key : ∫ θ, (h ^ 2 / 4 * (g θ * (Real.Angle.sin θ * sAng h θ)) ^ 2 -
        C * h * groundStateConj h g θ ^ 2) ∂angHaar ≤
      ∫ θ, (angDeriv (groundStateConj h g) θ ^ 2 +
        groundPot h (angSec θ) * groundStateConj h g θ ^ 2) ∂angHaar := by
    refine integral_mono ((i5.const_mul _).sub (i2.const_mul _)) i4 fun θ => ?_
    have h1 := hV (angSec θ)
    rw [sin_angSec_ex044] at h1
    have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (groundStateConj h g θ))
    have h3 := sq_nonneg (angDeriv (groundStateConj h g) θ)
    have h4 : (g θ * (Real.Angle.sin θ * sAng h θ)) ^ 2 =
        Real.Angle.sin θ ^ 2 * groundStateConj h g θ ^ 2 := by
      rw [hw]; simp only; ring
    simp only
    rw [h4]
    nlinarith
  rw [integral_sub (i5.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul] at key
  rw [integral_circleReference h hh] at hid
  have e1 : ∫ θ, (angDeriv g θ * sAng h θ) ^ 2 ∂angHaar =
      ∫ θ, angDeriv g θ ^ 2 * qAng h θ ∂angHaar :=
    integral_congr_ae (Eventually.of_forall fun θ => by
      simp only; rw [mul_pow, sAng_sq h hh])
  have e2 : ∫ θ, groundStateConj h g θ ^ 2 ∂angHaar = ∫ θ, (g θ * sAng h θ) ^ 2 ∂angHaar :=
    integral_congr_ae (Eventually.of_forall fun θ => by rw [hw])
  rw [e2, ← hid] at key
  rw [e1]
  linarith

lemma weak_potential_ex044 {C : ℝ} (h : ℝ) (hh : 0 < h)
    (hV : ∀ t, h ^ 2 * Real.sin t ^ 2 / 4 - C * h ≤ groundPot h t) {g g' : AngCircle → ℝ}
    (hw : IsAngularWeakDeriv g g') :
    h ^ 2 / 4 * ∫ θ, qAng h θ * (Real.Angle.sin θ ^ 2 * g θ ^ 2) ∂angHaar ≤
      ∫ θ, qAng h θ * g' θ ^ 2 ∂angHaar + C * h * ∫ θ, qAng h θ * g θ ^ 2 ∂angHaar := by
  obtain ⟨ψ, hψs, hψ1, hψ2⟩ := smooth_approx_hardy hw
  have hs := isSmoothAngular_sAng h hh
  have cs := continuous_of_smooth hs
  have cσ : Continuous fun θ : AngCircle => Real.Angle.sin θ := Real.Angle.continuous_sin
  have hψc : ∀ n, Continuous (ψ n) := fun n => continuous_of_smooth (hψs n)
  have hdc : ∀ n, Continuous (angDeriv (ψ n)) := fun n =>
    continuous_of_smooth (smooth_angDeriv (hψs n))
  have mψ : ∀ n, MemLp (ψ n) 2 angHaar := fun n => memLp_of_cont_ex042 (hψc n)
  have mdψ : ∀ n, MemLp (angDeriv (ψ n)) 2 angHaar := fun n => memLp_of_cont_ex042 (hdc n)
  have hA := tendsto_mul_sq_ex042 (d := ψ) (u := g) (cσ.mul cs) mψ hw.memLp hψ1
  have hB := tendsto_mul_sq_ex042 (d := fun n => angDeriv (ψ n)) (u := g') cs mdψ
    hw.memLp_deriv hψ2
  have hC := tendsto_mul_sq_ex042 (d := ψ) (u := g) cs mψ hw.memLp hψ1
  have eq1 : ∀ F : AngCircle → ℝ, ∫ θ, qAng h θ * F θ ^ 2 ∂angHaar =
      ∫ θ, (F θ * sAng h θ) ^ 2 ∂angHaar := fun F =>
    integral_congr_ae (Eventually.of_forall fun θ => by
      simp only; rw [mul_pow, sAng_sq h hh]; ring)
  have eq2 : ∫ θ, qAng h θ * (Real.Angle.sin θ ^ 2 * g θ ^ 2) ∂angHaar =
      ∫ θ, (g θ * (Real.Angle.sin θ * sAng h θ)) ^ 2 ∂angHaar :=
    integral_congr_ae (Eventually.of_forall fun θ => by
      have := sAng_sq h hh θ
      calc qAng h θ * (Real.Angle.sin θ ^ 2 * g θ ^ 2)
          = Real.Angle.sin θ ^ 2 * g θ ^ 2 * sAng h θ ^ 2 := by rw [this]; ring
        _ = _ := by ring)
  rw [eq2, eq1 g', eq1 g]
  refine le_of_tendsto_of_tendsto' (hA.const_mul (h ^ 2 / 4))
    (hB.add (hC.const_mul (C * h))) fun n => ?_
  have := smooth_potential_ex044 (C := C) h hh hV (hψs n)
  simpa [Pi.mul_apply] using this

lemma integrable_w_g2_ex044 {W : AngCircle → ℝ} (hW : Continuous W) {g : AngCircle → ℝ}
    (hg : MemLp g 2 angHaar) : Integrable (fun θ => W θ * g θ ^ 2) angHaar := by
  obtain ⟨B, hB⟩ := exists_bound_of_continuous hW
  have := hg.integrable_sq.mul_bdd hW.aestronglyMeasurable (Eventually.of_forall hB)
  exact this.congr (Eventually.of_forall fun θ => by simp only; ring)

lemma measurableSet_omega_ex044 : MeasurableSet {θ : AngCircle | 1 / 2 ≤ Uang θ} :=
  measurableSet_le measurable_const continuous_Uang.measurable

lemma continuous_delta_ex044 (h : ℝ) : Continuous fun θ : AngCircle => h * (2 - Uang θ) :=
  continuous_const.mul (continuous_const.sub continuous_Uang)

lemma measurableSet_delta_ex044 (h r : ℝ) : MeasurableSet {θ : AngCircle | h * (2 - Uang θ) ≤ r} :=
  measurableSet_le (continuous_delta_ex044 h).measurable measurable_const

lemma set_ref_ex044 (h : ℝ) (hp : 0 < h) {A : Set AngCircle} (hA : MeasurableSet A)
    (G : AngCircle → ℝ) :
    ∫ x in {x : Torus 1 | angEquiv x ∈ A}, G (angEquiv x) ∂engineeredReference h =
      ∫ θ, A.indicator (fun θ => qAng h θ * G θ) θ ∂angHaar := by
  have hm : MeasurableSet {x : Torus 1 | angEquiv x ∈ A} := angEquiv.measurable hA
  rw [← integral_indicator hm]
  have e : {x : Torus 1 | angEquiv x ∈ A}.indicator (fun x => G (angEquiv x)) =
      fun x => A.indicator G (angEquiv x) := by
    funext x
    by_cases hx : angEquiv x ∈ A
    · simp [Set.indicator_of_mem, hx]
    · simp [hx]
  rw [e, integral_ref_ent h hp (A.indicator G)]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  by_cases hθ : θ ∈ A <;> simp [hθ]

lemma energy_omega_ex044 {C : ℝ} (h : ℝ) (hh : 0 < h)
    (hV : ∀ t, h ^ 2 * Real.sin t ^ 2 / 4 - C * h ≤ groundPot h t) {g g' : AngCircle → ℝ}
    (hw : IsAngularWeakDeriv g g') :
    ∫ θ, {θ : AngCircle | 1 / 2 ≤ Uang θ}.indicator
        (fun θ => qAng h θ * (h * (2 - Uang θ) * g θ ^ 2)) θ ∂angHaar ≤
      8 / h * (∫ θ, qAng h θ * g' θ ^ 2 ∂angHaar +
        C * h * ∫ θ, qAng h θ * g θ ^ 2 ∂angHaar) := by
  have hpot := weak_potential_ex044 h hh hV hw
  have cq : Continuous (qAng h) := EngineeredGroundState.continuous_qAng h hh
  have i1 : Integrable (fun θ => {θ : AngCircle | 1 / 2 ≤ Uang θ}.indicator
        (fun θ => qAng h θ * (h * (2 - Uang θ) * g θ ^ 2)) θ) angHaar := by
    have := (integrable_w_g2_ex044 (W := fun θ => qAng h θ * (h * (2 - Uang θ)))
      (cq.mul (continuous_delta_ex044 h)) hw.memLp).indicator
      measurableSet_omega_ex044
    refine this.congr (Eventually.of_forall fun θ => ?_)
    simp only [Set.indicator_apply]
    split_ifs <;> ring
  have i2 : Integrable (fun θ => qAng h θ * (Real.Angle.sin θ ^ 2 * g θ ^ 2)) angHaar := by
    have := integrable_w_g2_ex044 (W := fun θ => qAng h θ * Real.Angle.sin θ ^ 2)
      (cq.mul (Real.Angle.continuous_sin.pow 2)) hw.memLp
    exact this.congr (Eventually.of_forall fun θ => by simp only; ring)
  have hle : ∫ θ, {θ : AngCircle | 1 / 2 ≤ Uang θ}.indicator
        (fun θ => qAng h θ * (h * (2 - Uang θ) * g θ ^ 2)) θ ∂angHaar ≤
      2 * h * ∫ θ, qAng h θ * (Real.Angle.sin θ ^ 2 * g θ ^ 2) ∂angHaar := by
    rw [← integral_const_mul]
    refine integral_mono i1 (i2.const_mul _) fun θ => ?_
    have hq := (qAng_pos h hh θ).le
    have hU := Uang_mem θ
    have hs := sin_sq_Uang_ex044 θ
    have hg2 := sq_nonneg (g θ)
    by_cases hθ : θ ∈ {θ : AngCircle | 1 / 2 ≤ Uang θ}
    · rw [Set.indicator_of_mem hθ]
      have hθ' : 1 / 2 ≤ Uang θ := hθ
      have key : 2 * h * (qAng h θ * (Real.Angle.sin θ ^ 2 * g θ ^ 2)) -
          qAng h θ * (h * (2 - Uang θ) * g θ ^ 2) =
          qAng h θ * g θ ^ 2 * h * (2 - Uang θ) * (2 * Uang θ - 1) := by
        rw [hs]; ring
      have : 0 ≤ qAng h θ * g θ ^ 2 * h * (2 - Uang θ) * (2 * Uang θ - 1) := by
        have : 0 ≤ 2 - Uang θ := by linarith [hU.2]
        have : 0 ≤ 2 * Uang θ - 1 := by linarith
        positivity
      linarith
    · rw [Set.indicator_of_notMem hθ]
      have := sq_nonneg (Real.Angle.sin θ)
      positivity
  have hX : 2 * h * ∫ θ, qAng h θ * (Real.Angle.sin θ ^ 2 * g θ ^ 2) ∂angHaar =
      8 / h * (h ^ 2 / 4 * ∫ θ, qAng h θ * (Real.Angle.sin θ ^ 2 * g θ ^ 2) ∂angHaar) := by
    field_simp
    ring
  have h8 : 0 ≤ 8 / h := by positivity
  calc _ ≤ _ := hle
    _ = _ := hX
    _ ≤ _ := mul_le_mul_of_nonneg_left hpot h8

lemma integrable_omega_delta_ex044 (h : ℝ) (hh : 0 < h) {g : AngCircle → ℝ}
    (hg : MemLp g 2 angHaar) :
    Integrable (fun θ => {θ : AngCircle | 1 / 2 ≤ Uang θ}.indicator
        (fun θ => qAng h θ * (h * (2 - Uang θ) * g θ ^ 2)) θ) angHaar := by
  have cq : Continuous (qAng h) := EngineeredGroundState.continuous_qAng h hh
  have := (integrable_w_g2_ex044 (W := fun θ => qAng h θ * (h * (2 - Uang θ)))
      (cq.mul (continuous_delta_ex044 h)) hg).indicator measurableSet_omega_ex044
  refine this.congr (Eventually.of_forall fun θ => ?_)
  simp only [Set.indicator_apply]
  split_ifs <;> ring

lemma tail_tilt_ex044 (h : ℝ) (hp : 0 < h) {g : AngCircle → ℝ} (hg : MemLp g 2 angHaar)
    (r : ℝ) :
    ∫ θ, {θ : AngCircle | h * (2 - Uang θ) ≤ r}.indicator
        (fun θ => qAng h θ * g θ ^ 2) θ ∂angHaar ≤
      cH h * exp (r - 2 * h) *
        ∫ θ, qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ) * g θ ^ 2) ∂angHaar := by
  have cq : Continuous (qAng h) := EngineeredGroundState.continuous_qAng h hp
  have hc0 := cH_pos_ex043 hp
  have iD := (integrable_w_g2_ex044 cq hg).indicator (measurableSet_delta_ex044 h r)
  have iR : Integrable (fun θ => qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ) * g θ ^ 2))
      angHaar := by
    have := integrable_w_g2_ex044 (W := fun θ => qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ)))
      (cq.mul (continuous_const.mul (continuous_expU_ex043 h))) hg
    exact this.congr (Eventually.of_forall fun θ => by simp only; ring)
  rw [← integral_const_mul]
  refine integral_mono iD (iR.const_mul _) fun θ => ?_
  have hq := (qAng_pos h hp θ).le
  have hg2 := sq_nonneg (g θ)
  by_cases hθ : θ ∈ {θ : AngCircle | h * (2 - Uang θ) ≤ r}
  · rw [Set.indicator_of_mem hθ]
    have hθ' : h * (2 - Uang θ) ≤ r := hθ
    have h1 : 1 ≤ exp (r - 2 * h) * exp (h * Uang θ) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    have hcc : cH h * (cH h)⁻¹ = 1 := mul_inv_cancel₀ hc0.ne'
    have e : cH h * exp (r - 2 * h) * (qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ) * g θ ^ 2)) =
        qAng h θ * g θ ^ 2 * (exp (r - 2 * h) * exp (h * Uang θ)) := by
      calc _ = (cH h * (cH h)⁻¹) * (qAng h θ * g θ ^ 2 * (exp (r - 2 * h) * exp (h * Uang θ))) := by
            ring
        _ = _ := by rw [hcc, one_mul]
    rw [e]
    have : 0 ≤ qAng h θ * g θ ^ 2 := mul_nonneg hq hg2
    nlinarith
  · rw [Set.indicator_of_notMem hθ]
    have := (exp_pos (h * Uang θ)).le
    have := (exp_pos (r - 2 * h)).le
    have := (inv_pos.2 hc0).le
    positivity

lemma split_arith_ex044 {A D r : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hr : 0 < r) :
    A ≤ (if D ≤ r then A else 0) + r⁻¹ * (D * A) := by
  by_cases hd : D ≤ r
  · simp only [hd, ↓reduceIte]
    have := mul_nonneg (inv_nonneg.2 hr.le) (mul_nonneg hD hA)
    linarith
  · simp only [hd, ↓reduceIte]
    have hd' : r < D := not_le.1 hd
    have h1 : 1 ≤ r⁻¹ * D := by
      rw [← div_eq_inv_mul, le_div_iff₀ hr]; linarith
    have : r⁻¹ * (D * A) = (r⁻¹ * D) * A := by ring
    rw [this]
    nlinarith

lemma omega_split_ex044 (h : ℝ) (hp : 0 < h) {g : AngCircle → ℝ} (hg : MemLp g 2 angHaar)
    {r : ℝ} (hr : 0 < r) :
    ∫ θ, {θ : AngCircle | 1 / 2 ≤ Uang θ}.indicator (fun θ => qAng h θ * g θ ^ 2) θ ∂angHaar ≤
      ∫ θ, {θ : AngCircle | h * (2 - Uang θ) ≤ r}.indicator
        (fun θ => qAng h θ * g θ ^ 2) θ ∂angHaar +
      r⁻¹ * ∫ θ, {θ : AngCircle | 1 / 2 ≤ Uang θ}.indicator
        (fun θ => qAng h θ * (h * (2 - Uang θ) * g θ ^ 2)) θ ∂angHaar := by
  have cq : Continuous (qAng h) := EngineeredGroundState.continuous_qAng h hp
  have iO := (integrable_w_g2_ex044 cq hg).indicator measurableSet_omega_ex044
  have iD := (integrable_w_g2_ex044 cq hg).indicator (measurableSet_delta_ex044 h r)
  have iW := integrable_omega_delta_ex044 h hp hg
  rw [← integral_const_mul, ← integral_add iD (iW.const_mul _)]
  refine integral_mono iO (iD.add (iW.const_mul _)) fun θ => ?_
  have hq := (qAng_pos h hp θ).le
  have hg2 := sq_nonneg (g θ)
  have hU := Uang_mem θ
  have hΔ : 0 ≤ h * (2 - Uang θ) := mul_nonneg hp.le (by linarith [hU.2])
  have hqg : 0 ≤ qAng h θ * g θ ^ 2 := mul_nonneg hq hg2
  have key := split_arith_ex044 hqg hΔ hr
  have e : qAng h θ * (h * (2 - Uang θ) * g θ ^ 2) = h * (2 - Uang θ) * (qAng h θ * g θ ^ 2) := by
    ring
  have eD : {θ : AngCircle | h * (2 - Uang θ) ≤ r}.indicator
      (fun θ => qAng h θ * g θ ^ 2) θ =
      (if h * (2 - Uang θ) ≤ r then qAng h θ * g θ ^ 2 else 0) := by
    by_cases hd : h * (2 - Uang θ) ≤ r <;> simp [hd]
  by_cases hθ : 1 / 2 ≤ Uang θ
  · have hm : θ ∈ {θ : AngCircle | 1 / 2 ≤ Uang θ} := hθ
    rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, eD, e]
    exact key
  · have hm : θ ∉ {θ : AngCircle | 1 / 2 ≤ Uang θ} := hθ
    rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, eD]
    have : 0 ≤ (if h * (2 - Uang θ) ≤ r then qAng h θ * g θ ^ 2 else 0) := by
      split_ifs
      · exact hqg
      · exact le_rfl
    simpa using this

lemma phi_le_ex044 {f : ℝ} (hf : 0 ≤ f) :
    f ^ 2 * Real.log (f ^ 2) - f ^ 2 + 1 ≤
      9 * (f - 1) ^ 2 * (1 + Real.log (2 + (f - 1) ^ 2)) := by
  have hl : 0 ≤ Real.log (2 + (f - 1) ^ 2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg (f - 1)])
  have hg2 := sq_nonneg (f - 1)
  by_cases h2 : f ≤ 2
  · have h1 : f ^ 2 * Real.log (f ^ 2) ≤ f ^ 2 * (f ^ 2 - 1) := by
      by_cases h0 : f = 0
      · simp [h0]
      · apply mul_le_mul_of_nonneg_left _ (sq_nonneg f)
        have := Real.log_le_sub_one_of_pos (by positivity : 0 < f ^ 2)
        linarith
    have h3 : (f ^ 2 - 1) ^ 2 = (f - 1) ^ 2 * (f + 1) ^ 2 := by ring
    have h4 : (f + 1) ^ 2 ≤ 9 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h4 hg2, mul_nonneg hg2 hl]
  · have h2' : 2 < f := not_le.1 h2
    have h5 : Real.log (f ^ 2) = 2 * Real.log f := by
      rw [Real.log_pow]; norm_num
    have h6 : Real.log f ≤ Real.log (2 + (f - 1) ^ 2) :=
      Real.log_le_log (by linarith) (by nlinarith)
    have h7 : f ^ 2 ≤ 4 * (f - 1) ^ 2 := by nlinarith
    have h8 : 0 ≤ Real.log f := Real.log_nonneg (by linarith)
    have h9 : f ^ 2 * Real.log (f ^ 2) ≤ 8 * (f - 1) ^ 2 * Real.log (2 + (f - 1) ^ 2) := by
      rw [h5]
      calc f ^ 2 * (2 * Real.log f) ≤ (4 * (f - 1) ^ 2) * (2 * Real.log (2 + (f - 1) ^ 2)) :=
            mul_le_mul h7 (by linarith) (by positivity) (by positivity)
        _ = _ := by ring
    nlinarith [mul_nonneg hg2 hl, sq_nonneg f]

lemma phi_nonneg_ex044 {s : ℝ} (hs : 0 ≤ s) : 0 ≤ s * Real.log s - s + 1 := by
  rcases hs.eq_or_lt with h0 | h0
  · simp [← h0]
  · have := Real.log_le_sub_one_of_pos (inv_pos.2 h0)
    rw [Real.log_inv] at this
    have h1 : s * (-Real.log s) ≤ s * (s⁻¹ - 1) := mul_le_mul_of_nonneg_left this hs
    have h2 : s * (s⁻¹ - 1) = 1 - s := by field_simp
    nlinarith

lemma tail_alg_ex044 {h T c r : ℝ} (hp : 0 < h) (hT : 0 < T) :
    2 * Real.exp (r - 2 * h) * (c * Real.exp h * h ^ (-(1 / 2 : ℝ)) * Real.sqrt T) =
      2 * c * T * Real.exp r / Real.sqrt (h * Real.exp (2 * h) * T) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ T = s ^ 2 :=
    ⟨Real.sqrt T, Real.sqrt_pos.2 hT, (Real.sq_sqrt hT.le).symm⟩
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 < u ∧ h = u ^ 2 :=
    ⟨Real.sqrt h, Real.sqrt_pos.2 hp, (Real.sq_sqrt hp.le).symm⟩
  have e2h : Real.exp (2 * u ^ 2) = Real.exp (u ^ 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hrh : (u ^ 2) ^ (-(1 / 2 : ℝ)) = u⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hu.le]
  have hsq : Real.sqrt (u ^ 2 * Real.exp (2 * u ^ 2) * s ^ 2) = u * Real.exp (u ^ 2) * s := by
    rw [e2h, show u ^ 2 * Real.exp (u ^ 2) ^ 2 * s ^ 2 = (u * Real.exp (u ^ 2) * s) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [hrh, hsq, Real.sqrt_sq hs.le, Real.exp_sub, e2h]
  field_simp

lemma delta_bound_ex044 {C37 K N T : ℝ} (hC37 : 0 < C37) (h : ℝ) (hp : 0 < h)
    (hV : ∀ t, h ^ 2 * Real.sin t ^ 2 / 4 - C37 * h ≤ groundPot h t)
    {f f' : AngCircle → ℝ} (hg : IsAngularWeakDeriv (fun θ => f θ - 1) f')
    (hEq : ∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar ≤ h * T)
    (hNc : N = ∫ θ, qAng h θ * (f θ - 1) ^ 2 ∂angHaar) (hN3 : N ≤ K * T) :
    ∫ θ, {θ : AngCircle | 1 / 2 ≤ Uang θ}.indicator
      (fun θ => qAng h θ * (h * (2 - Uang θ) * (f θ - 1) ^ 2)) θ ∂angHaar ≤
      (8 + 8 * C37 * K) * T := by
  have h1 := energy_omega_ex044 (C := C37) h hp hV hg
  beta_reduce at h1
  rw [← hNc] at h1
  have h2 : 8 / h * (∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar + C37 * h * N) ≤
      8 / h * (h * T + C37 * h * N) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : 8 / h * (h * T + C37 * h * N) = 8 * T + 8 * C37 * N := by field_simp
  have h4 : 8 * C37 * N ≤ 8 * C37 * (K * T) :=
    mul_le_mul_of_nonneg_left hN3 (by positivity)
  nlinarith

lemma tail_bound_ex044 (h : ℝ) (hp : 0 < h) {g : AngCircle → ℝ} (hg : MemLp g 2 angHaar)
    {T C43 : ℝ} (hT0 : 0 < T)
    (hνc : ∫ x, (g (angEquiv x)) ^ 2 ∂tiltedMeasure_ex043 h ≤
      C43 * exp h * h ^ (-(1 / 2 : ℝ)) * Real.sqrt T) (r : ℝ) :
    ∫ θ, {θ : AngCircle | h * (2 - Uang θ) ≤ r}.indicator
      (fun θ => qAng h θ * g θ ^ 2) θ ∂angHaar ≤
      2 * C43 * T * Real.exp r / Real.sqrt (h * Real.exp (2 * h) * T) := by
  have hνp : ∫ x, (g (angEquiv x)) ^ 2 ∂tiltedMeasure_ex043 h =
      ∫ θ, qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ) * g θ ^ 2) ∂angHaar :=
    tilt_circle_ex043 hp (fun θ => g θ ^ 2)
  have hcH2 : cH h ≤ 2 := by unfold cH; linarith [Real.tanh_lt_one h]
  have h1 := tail_tilt_ex044 h hp hg r
  rw [← hνp] at h1
  have hν0 : 0 ≤ ∫ x, (g (angEquiv x)) ^ 2 ∂tiltedMeasure_ex043 h :=
    integral_nonneg fun _ => sq_nonneg _
  have h2 : cH h * exp (r - 2 * h) * ∫ x, (g (angEquiv x)) ^ 2 ∂tiltedMeasure_ex043 h ≤
      2 * exp (r - 2 * h) * (C43 * exp h * h ^ (-(1 / 2 : ℝ)) * Real.sqrt T) := by
    have := mul_le_mul hcH2 hνc hν0 (by norm_num)
    have e := exp_pos (r - 2 * h)
    calc _ = exp (r - 2 * h) * (cH h * ∫ x, (g (angEquiv x)) ^ 2 ∂tiltedMeasure_ex043 h) := by
          ring
      _ ≤ exp (r - 2 * h) * (2 * (C43 * exp h * h ^ (-(1 / 2 : ℝ)) * Real.sqrt T)) :=
          mul_le_mul_of_nonneg_left this e.le
      _ = _ := by ring
  rw [tail_alg_ex044 hp hT0] at h2
  exact h1.trans h2

lemma big_arith_ex044 {S T K c2 c3 c4 I W : ℝ} {D : ℝ → ℝ} (hS3 : 3 ≤ S) (hT : 0 ≤ T)
    (hK : 0 ≤ K) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3) (hc4 : c3 + 4 * c2 + 64 * K ≤ c4)
    (hsplit : ∀ r : ℝ, 0 < r → I ≤ D r + r⁻¹ * W)
    (htail : ∀ r : ℝ, D r ≤ c3 * T * Real.exp r / Real.sqrt S)
    (hW : W ≤ c2 * T) (hI : I ≤ K * T) :
    I ≤ c4 * T / Real.log S := by
  have hS0 : 0 < S := by linarith
  have hL : 1 < Real.log S := by
    rw [Real.lt_log_iff_exp_lt hS0]
    have := Real.exp_one_lt_d9
    linarith
  have hLp : 0 < Real.log S := by linarith
  by_cases hL64 : 64 ≤ Real.log S
  · obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log S := ⟨_, rfl⟩
    rw [← hLdef] at hL hL64 hLp ⊢
    have hlogL : Real.log L ≤ L / 4 := by
      have h64 : Real.log 64 = 6 * Real.log 2 := by
        rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
      have h2 := Real.log_two_lt_d9
      have := Real.log_le_sub_one_of_pos (show 0 < L / 64 by positivity)
      rw [Real.log_div (by positivity) (by norm_num), h64] at this
      linarith
    have hr : L / 4 ≤ L / 2 - Real.log L := by linarith
    have hrp : 0 < L / 2 - Real.log L := by linarith
    have hsp := hsplit _ hrp
    have ht := htail (L / 2 - Real.log L)
    have hexp : Real.exp (L / 2 - Real.log L) = Real.sqrt S / L := by
      rw [Real.exp_sub, Real.exp_log hLp, Real.exp_half, hLdef, Real.exp_log hS0]
    rw [hexp] at ht
    have hsS : 0 < Real.sqrt S := Real.sqrt_pos.2 hS0
    have ht' : c3 * T * (Real.sqrt S / L) / Real.sqrt S = c3 * T / L := by
      field_simp
    rw [ht'] at ht
    have hinv : (L / 2 - Real.log L)⁻¹ ≤ 4 / L := by
      rw [inv_eq_one_div, div_le_div_iff₀ hrp hLp]; nlinarith
    have hW' : (L / 2 - Real.log L)⁻¹ * W ≤ 4 / L * (c2 * T) := by
      calc _ ≤ (L / 2 - Real.log L)⁻¹ * (c2 * T) :=
            mul_le_mul_of_nonneg_left hW (inv_nonneg.2 hrp.le)
        _ ≤ 4 / L * (c2 * T) := mul_le_mul_of_nonneg_right hinv (by positivity)
    have h5 : c3 * T / L + 4 / L * (c2 * T) ≤ c4 * T / L := by
      have e : c3 * T / L + 4 / L * (c2 * T) = (c3 + 4 * c2) * T / L := by field_simp
      rw [e]
      apply div_le_div_of_nonneg_right _ hLp.le
      nlinarith
    linarith
  · have hlt : Real.log S < 64 := not_le.1 hL64
    rw [le_div_iff₀ hLp]
    have h2 : K * T * Real.log S ≤ K * T * 64 :=
      mul_le_mul_of_nonneg_left hlt.le (by positivity)
    have h3 : I * Real.log S ≤ (K * T) * Real.log S := mul_le_mul_of_nonneg_right hI hLp.le
    nlinarith [mul_nonneg hc3 hT, mul_nonneg hc2 hT, mul_le_mul_of_nonneg_right hc4 hT]

lemma phi_torus_ex044 (h : ℝ) (hp : 0 < h) {f : AngCircle → ℝ} (hfm0 : AEMeasurable f angHaar)
    (hf0 : ∀ θ, 0 ≤ f θ) {B : ℝ} (hB : 0 ≤ B)
    (hsup : ∀ᵐ x ∂engineeredReference h, (f (angEquiv x) - 1) ^ 2 ≤ B) :
    Integrable (fun x : Torus 1 => f (angEquiv x) ^ 2 * Real.log (f (angEquiv x) ^ 2)
      - f (angEquiv x) ^ 2 + 1) (engineeredReference h) ∧
    Integrable (fun x : Torus 1 => (f (angEquiv x) - 1) ^ 2) (engineeredReference h) ∧
    ∀ M2 : ℝ, 1 + Real.log (2 + B) ≤ M2 →
      ∫ x in {x : Torus 1 | 1 / 2 ≤ Uang (angEquiv x)},
        (f (angEquiv x) ^ 2 * Real.log (f (angEquiv x) ^ 2) - f (angEquiv x) ^ 2 + 1)
          ∂engineeredReference h ≤
      9 * M2 * ∫ x in {x : Torus 1 | 1 / 2 ≤ Uang (angEquiv x)},
        (f (angEquiv x) - 1) ^ 2 ∂engineeredReference h := by
  have : IsProbabilityMeasure (engineeredReference h) := engineeredReference_isProbability h hp
  have hfm : AEMeasurable (fun x : Torus 1 => f (angEquiv x)) (engineeredReference h) :=
    aemeasurable_ref h hfm0
  have hgT_meas : AEStronglyMeasurable (fun x : Torus 1 => (f (angEquiv x) - 1) ^ 2)
      (engineeredReference h) := ((hfm.sub_const 1).pow_const 2).aestronglyMeasurable
  have hΦ_meas : AEStronglyMeasurable (fun x : Torus 1 => f (angEquiv x) ^ 2 *
      Real.log (f (angEquiv x) ^ 2) - f (angEquiv x) ^ 2 + 1) (engineeredReference h) :=
    ((((hfm.pow_const 2).mul (hfm.pow_const 2).log).sub (hfm.pow_const 2)).add_const
      1).aestronglyMeasurable
  have hgT_int : Integrable (fun x : Torus 1 => (f (angEquiv x) - 1) ^ 2)
      (engineeredReference h) :=
    Integrable.of_bound hgT_meas B (by
      filter_upwards [hsup] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hx)
  have phi_ae : ∀ M2 : ℝ, 1 + Real.log (2 + B) ≤ M2 → ∀ᵐ x ∂(engineeredReference h),
      f (angEquiv x) ^ 2 * Real.log (f (angEquiv x) ^ 2) - f (angEquiv x) ^ 2 + 1 ≤
        9 * M2 * (f (angEquiv x) - 1) ^ 2 := by
    intro M2 hM2
    filter_upwards [hsup] with x hx
    have h1 := phi_le_ex044 (hf0 (angEquiv x))
    have h2 : Real.log (2 + (f (angEquiv x) - 1) ^ 2) ≤ Real.log (2 + B) :=
      Real.log_le_log (by positivity) (by linarith)
    have h3 := sq_nonneg (f (angEquiv x) - 1)
    calc _ ≤ _ := h1
      _ ≤ 9 * (f (angEquiv x) - 1) ^ 2 * M2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      _ = _ := by ring
  have hlogB : 0 ≤ Real.log (2 + B) := Real.log_nonneg (by linarith)
  have phi_int : Integrable (fun x : Torus 1 => f (angEquiv x) ^ 2 *
      Real.log (f (angEquiv x) ^ 2) - f (angEquiv x) ^ 2 + 1) (engineeredReference h) := by
    refine Integrable.mono' (hgT_int.const_mul (9 * (1 + Real.log (2 + B)))) hΦ_meas ?_
    filter_upwards [phi_ae _ le_rfl] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (phi_nonneg_ex044 (sq_nonneg _))]
    linarith
  refine ⟨phi_int, hgT_int, fun M2 hM2 => ?_⟩
  rw [← integral_const_mul]
  exact setIntegral_mono_ae phi_int.integrableOn (hgT_int.const_mul _).integrableOn
    (phi_ae M2 hM2)


lemma phi_final_ex044 {K T S c4 c5 I P : ℝ} (hK : 0 ≤ K) (hS0 : 0 < S) (hT : 0 < T)
    (hc4 : 0 ≤ c4)
    (hc5 : c5 = 9 * (2 + Real.log (2 + K)) * c4 + 9 * (1 + Real.log (2 + 3 * K)) * K)
    (hphi : ∀ M2 : ℝ, 1 + Real.log (2 + K * S) ≤ M2 → P ≤ 9 * M2 * I)
    (h4 : 3 ≤ S → I ≤ c4 * T / Real.log S) (hI : I ≤ K * T) :
    P ≤ c5 * T := by
  have hlogK : 0 ≤ Real.log (2 + K) := Real.log_nonneg (by linarith)
  have hlog3K : 0 ≤ Real.log (2 + 3 * K) := Real.log_nonneg (by linarith)
  by_cases hS3 : 3 ≤ S
  · have hL : 1 < Real.log S := by
      rw [Real.lt_log_iff_exp_lt hS0]
      have := Real.exp_one_lt_d9
      linarith
    have hLp : 0 < Real.log S := by linarith
    have hM : 1 + Real.log (2 + K * S) ≤ (2 + Real.log (2 + K)) * Real.log S := by
      have h1 : Real.log (2 + K * S) ≤ Real.log ((2 + K) * S) :=
        Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_mul (by positivity) hS0.ne'] at h1
      nlinarith
    have h1 := hphi _ hM
    have h2 := h4 hS3
    have h3 : 9 * ((2 + Real.log (2 + K)) * Real.log S) * I ≤
        9 * ((2 + Real.log (2 + K)) * Real.log S) * (c4 * T / Real.log S) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : 9 * ((2 + Real.log (2 + K)) * Real.log S) * (c4 * T / Real.log S) =
        9 * (2 + Real.log (2 + K)) * c4 * T := by field_simp
    have h5 : 0 ≤ 9 * (1 + Real.log (2 + 3 * K)) * K := by positivity
    have h6 : 9 * (2 + Real.log (2 + K)) * c4 * T ≤ c5 * T := by
      rw [hc5]; nlinarith [mul_nonneg hT.le h5]
    linarith
  · have hlt : S < 3 := not_le.1 hS3
    have hM : 1 + Real.log (2 + K * S) ≤ 1 + Real.log (2 + 3 * K) := by
      have : Real.log (2 + K * S) ≤ Real.log (2 + 3 * K) :=
        Real.log_le_log (by positivity) (by nlinarith)
      linarith
    have h1 := hphi _ hM
    have h3 : 9 * (1 + Real.log (2 + 3 * K)) * I ≤
        9 * (1 + Real.log (2 + 3 * K)) * (K * T) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    have h5 : 0 ≤ 9 * (2 + Real.log (2 + K)) * c4 := by positivity
    have h6 : 9 * (1 + Real.log (2 + 3 * K)) * (K * T) ≤ c5 * T := by
      rw [hc5]; nlinarith [mul_nonneg hT.le h5]
    linarith

end DGPS.Examples.EngineeredRankOneEX044


namespace DGPS.Examples

open MeasureTheory Real Set
open DGPS.Examples.EngineeredRankOne DGPS.Examples.EngineeredRankOneEX042
  DGPS.Examples.EngineeredRankOneEX044 DGPS.Models DGPS.Circle.AngularNormalization
  DGPS.Examples.EngineeredGroundState

/-- EX044: engineered antipodal tail cancellation. -/
theorem engineered_antipodal_tail_cancellation :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 2 ≤ h → ∀ f f' : AngCircle → ℝ,
      IsAngularWeakDeriv f f' → (∀ θ, 0 ≤ f θ) →
      ∫ x, f (angEquiv x) ^ 2 ∂engineeredReference h = 1 →
      ∀ T N : ℝ, 0 < T →
      T = (∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h) / h +
        (∫ x, Eang h (angEquiv x) ∂densityRef h f) ^ 2 →
      T ≤ 1 →
      N = ∫ x, (f (angEquiv x) - 1) ^ 2 ∂engineeredReference h →
      N ≤ C * T ∧
      ∫ x in {x : Torus 1 | 1 / 2 ≤ Uang (angEquiv x)},
          h * (2 - Uang (angEquiv x)) * (f (angEquiv x) - 1) ^ 2
          ∂engineeredReference h ≤ C * T ∧
      (∀ r : ℝ, ∫ x in {x : Torus 1 | h * (2 - Uang (angEquiv x)) ≤ r},
          (f (angEquiv x) - 1) ^ 2 ∂engineeredReference h ≤
        C * T * Real.exp r / Real.sqrt (h * Real.exp (2 * h) * T)) ∧
      (∀ S : ℝ, S = h * Real.exp (2 * h) * T → 3 ≤ S →
        ∫ x in {x : Torus 1 | 1 / 2 ≤ Uang (angEquiv x)},
          (f (angEquiv x) - 1) ^ 2 ∂engineeredReference h ≤ C * T / Real.log S) ∧
      (IntegrableOn (fun x : Torus 1 => f (angEquiv x) ^ 2 * Real.log (f (angEquiv x) ^ 2)
          - f (angEquiv x) ^ 2 + 1) {x : Torus 1 | 1 / 2 ≤ Uang (angEquiv x)}
          (engineeredReference h) ∧
        ∫ x in {x : Torus 1 | 1 / 2 ≤ Uang (angEquiv x)},
          (f (angEquiv x) ^ 2 * Real.log (f (angEquiv x) ^ 2) - f (angEquiv x) ^ 2 + 1)
          ∂engineeredReference h ≤ C * T) := by
  obtain ⟨C37, hC37, H37⟩ := engineered_drift_and_ground_potential
  obtain ⟨K, hK, H42⟩ := engineered_small_t_l2_and_sup_controls
  obtain ⟨C43, hC43, H43⟩ := engineered_tilted_measure_identity
  obtain ⟨c2, hc2⟩ : ∃ c : ℝ, c = 8 + 8 * C37 * K := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ c : ℝ, c = 2 * C43 := ⟨_, rfl⟩
  obtain ⟨c4, hc4⟩ : ∃ c : ℝ, c = c3 + 4 * c2 + 64 * K := ⟨_, rfl⟩
  have hlogK : 0 ≤ Real.log (2 + K) := Real.log_nonneg (by linarith)
  have hlog3K : 0 ≤ Real.log (2 + 3 * K) := Real.log_nonneg (by linarith)
  obtain ⟨c5, hc5⟩ : ∃ c : ℝ, c = 9 * (2 + Real.log (2 + K)) * c4 +
      9 * (1 + Real.log (2 + 3 * K)) * K := ⟨_, rfl⟩
  have hc2p : 0 < c2 := by rw [hc2]; positivity
  have hc3p : 0 < c3 := by rw [hc3]; positivity
  have hc4p : 0 < c4 := by rw [hc4]; positivity
  have hc5p : 0 < c5 := by rw [hc5]; positivity
  refine ⟨K + c2 + c3 + c4 + c5, by positivity, ?_⟩
  intro h hh f f' hw hf0 hnorm T N hT0 hT hT1 hN
  have hp : 0 < h := by linarith
  have hP : IsProbabilityMeasure (engineeredReference h) := engineeredReference_isProbability h hp
  obtain ⟨hN1, hN2, hN3, hsupR, hsupA⟩ := H42 h hh f f' hw hf0 hnorm T N hT hT1 hN
  have hV : ∀ t, h ^ 2 * Real.sin t ^ 2 / 4 - C37 * h ≤ groundPot h t := fun t => (H37 h hh t).2.2
  have hg : IsAngularWeakDeriv (fun θ => f θ - 1) f' := by
    have := isWeakDeriv_sub_ex042 hw (isWeakDeriv_const_ex042 1)
    simpa using this
  have hN0 : 0 ≤ N := by rw [hN]; exact integral_nonneg fun _ => sq_nonneg _
  have cq : Continuous (qAng h) := EngineeredGroundState.continuous_qAng h hp
  have hNc : N = ∫ θ, qAng h θ * (f θ - 1) ^ 2 ∂angHaar :=
    hN.trans (integral_ref_ent h hp (fun θ => (f θ - 1) ^ 2))
  have hE_ref : ∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h =
      ∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar := integral_ref_ent h hp (fun θ => f' θ ^ 2)
  have hEq : ∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar ≤ h * T := by
    have h1 : (∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar) / h ≤ T := by
      rw [← hE_ref]; rw [hT]
      nlinarith [sq_nonneg (∫ x, Eang h (angEquiv x) ∂densityRef h f)]
    rw [div_le_iff₀ hp] at h1
    linarith
  have hΔc : ∫ θ, {θ : AngCircle | 1 / 2 ≤ Uang θ}.indicator
      (fun θ => qAng h θ * (h * (2 - Uang θ) * (f θ - 1) ^ 2)) θ ∂angHaar ≤ c2 * T := by
    rw [hc2]; exact delta_bound_ex044 hC37 h hp hV hg hEq hNc hN3
  have hνc := (H43 h hh f f' hw hf0 hnorm T hT).2.2
  have tail : ∀ r : ℝ, ∫ θ, {θ : AngCircle | h * (2 - Uang θ) ≤ r}.indicator
      (fun θ => qAng h θ * (f θ - 1) ^ 2) θ ∂angHaar ≤
      c3 * T * Real.exp r / Real.sqrt (h * Real.exp (2 * h) * T) := by
    intro r
    rw [hc3]
    exact tail_bound_ex044 h hp (g := fun θ => f θ - 1) hg.memLp hT0 hνc r
  have hΩle : ∫ θ, {θ : AngCircle | 1 / 2 ≤ Uang θ}.indicator
          (fun θ => qAng h θ * (f θ - 1) ^ 2) θ ∂angHaar ≤ K * T := by
    refine le_trans ?_ hN3
    rw [integral_indicator measurableSet_omega_ex044, hNc]
    exact setIntegral_le_integral (integrable_w_g2_ex044 cq hg.memLp)
      (Eventually.of_forall fun θ => mul_nonneg (qAng_pos h hp θ).le (sq_nonneg _))
  have big : ∀ S : ℝ, S = h * Real.exp (2 * h) * T → 3 ≤ S →
      ∫ θ, {θ : AngCircle | 1 / 2 ≤ Uang θ}.indicator
        (fun θ => qAng h θ * (f θ - 1) ^ 2) θ ∂angHaar ≤ c4 * T / Real.log S := by
    intro S hS hS3
    refine big_arith_ex044 (D := fun r => ∫ θ, {θ : AngCircle | h * (2 - Uang θ) ≤ r}.indicator
      (fun θ => qAng h θ * (f θ - 1) ^ 2) θ ∂angHaar) hS3 hT0.le hK.le hc2p.le hc3p.le
      hc4.ge ?_ ?_ hΔc hΩle
    · intro r hr
      have := omega_split_ex044 h hp hg.memLp hr
      beta_reduce at this
      exact this
    · intro r
      rw [hS]
      exact tail r
  -- Torus conversions
  have eΩ : ∫ x in {x : Torus 1 | 1 / 2 ≤ Uang (angEquiv x)},
        (f (angEquiv x) - 1) ^ 2 ∂engineeredReference h =
      ∫ θ, {θ : AngCircle | 1 / 2 ≤ Uang θ}.indicator
        (fun θ => qAng h θ * (f θ - 1) ^ 2) θ ∂angHaar :=
    set_ref_ex044 h hp measurableSet_omega_ex044 (fun θ => (f θ - 1) ^ 2)
  have hT' : 0 ≤ T := hT0.le
  have hCc2 : c2 ≤ K + c2 + c3 + c4 + c5 := by linarith
  have hCc3 : c3 ≤ K + c2 + c3 + c4 + c5 := by linarith
  have hCc4 : c4 ≤ K + c2 + c3 + c4 + c5 := by linarith
  have part4 : ∀ S : ℝ, S = h * Real.exp (2 * h) * T → 3 ≤ S →
      ∫ x in {x : Torus 1 | 1 / 2 ≤ Uang (angEquiv x)},
        (f (angEquiv x) - 1) ^ 2 ∂engineeredReference h ≤ c4 * T / Real.log S := by
    intro S hS hS3
    rw [eΩ]; exact big S hS hS3
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = h * Real.exp (2 * h) * T := ⟨_, rfl⟩
  have hS0 : 0 < S := by rw [hS]; positivity
  have hsupS : ∀ᵐ x ∂(engineeredReference h), (f (angEquiv x) - 1) ^ 2 ≤ K * S := by
    filter_upwards [hsupR] with x hx
    rw [hS]; exact hx
  obtain ⟨phi_int, hgT_int, phi_set⟩ := phi_torus_ex044 h hp
    hw.memLp.aestronglyMeasurable.aemeasurable hf0 (mul_nonneg hK.le hS0.le) hsupS
  have hgΩ_le : ∫ x in {x : Torus 1 | 1 / 2 ≤ Uang (angEquiv x)},
        (f (angEquiv x) - 1) ^ 2 ∂engineeredReference h ≤ K * T := by
    rw [eΩ]; exact hΩle
  refine ⟨?_, ?_, ?_, ?_, phi_int.integrableOn, ?_⟩
  · exact hN3.trans (mul_le_mul_of_nonneg_right (by linarith) hT')
  · have : ∫ x in {x : Torus 1 | 1 / 2 ≤ Uang (angEquiv x)},
        h * (2 - Uang (angEquiv x)) * (f (angEquiv x) - 1) ^ 2 ∂engineeredReference h =
        ∫ θ, {θ : AngCircle | 1 / 2 ≤ Uang θ}.indicator
          (fun θ => qAng h θ * (h * (2 - Uang θ) * (f θ - 1) ^ 2)) θ ∂angHaar :=
      set_ref_ex044 h hp measurableSet_omega_ex044 (fun θ => h * (2 - Uang θ) * (f θ - 1) ^ 2)
    rw [this]
    exact hΔc.trans (mul_le_mul_of_nonneg_right hCc2 hT')
  · intro r
    have : ∫ x in {x : Torus 1 | h * (2 - Uang (angEquiv x)) ≤ r},
        (f (angEquiv x) - 1) ^ 2 ∂engineeredReference h =
        ∫ θ, {θ : AngCircle | h * (2 - Uang θ) ≤ r}.indicator
          (fun θ => qAng h θ * (f θ - 1) ^ 2) θ ∂angHaar :=
      set_ref_ex044 h hp (measurableSet_delta_ex044 h r) (fun θ => (f θ - 1) ^ 2)
    rw [this]
    refine (tail r).trans ?_
    have hsq : 0 ≤ Real.sqrt (h * Real.exp (2 * h) * T) := Real.sqrt_nonneg _
    have hnn : 0 ≤ T * Real.exp r := by positivity
    calc c3 * T * Real.exp r / Real.sqrt (h * Real.exp (2 * h) * T)
        = c3 * (T * Real.exp r) / Real.sqrt (h * Real.exp (2 * h) * T) := by ring
      _ ≤ (K + c2 + c3 + c4 + c5) * (T * Real.exp r) /
          Real.sqrt (h * Real.exp (2 * h) * T) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCc3 hnn) hsq
      _ = _ := by ring
  · intro S' hS' hS3
    have hLp : 0 < Real.log S' := Real.log_pos (by linarith)
    refine (part4 S' hS' hS3).trans ?_
    rw [div_le_div_iff_of_pos_right hLp]
    exact mul_le_mul_of_nonneg_right hCc4 hT'
  · exact (phi_final_ex044 hK.le hS0 hT0 hc4p.le hc5 phi_set (part4 S hS) hgΩ_le).trans
      (mul_le_mul_of_nonneg_right (by linarith) hT')

end DGPS.Examples
