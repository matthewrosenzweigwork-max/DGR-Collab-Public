import DGPS.Examples.EngineeredHardy
import DGPS.Examples.EngineeredGroundState
import DGPS.Examples.EngineeredRankOneDrift
import DGPS.Examples.EngineeredRankOneNormalization
import DGPS.Examples.EngineeredRankOneEntropy
import DGPS.FiniteN.Tools.UniformVonMises

/-!
# EX042: engineered small-`T` `L²` and sup controls

For the engineered reference measure `μ_h` and a nonnegative angular weak-`H¹` function `f` with
`μ_h(f²) = 1`, write `g = f - 1`, `N = μ_h(g²)` and `T = E/h + (μ_f(Eang))²`.
We prove `N = 2(1 - μ_h f)`, `Var_{μ_h}(f) ≥ N/2`, `N ≤ C T` and an almost-everywhere bound
`g² ≤ C h e^{2h} T`, uniformly for `h ≥ 2`.
-/

open MeasureTheory Real Set Filter Topology
open scoped ContDiff ENNReal
open DGPS.Circle.AngularNormalization
open DGPS.Circle.StationaryFlux

namespace DGPS.Examples.EngineeredRankOneEX042

open DGPS.Models DGPS.Examples.EngineeredRankOne DGPS.Examples.EngineeredGroundState
  DGPS.Examples.EngineeredHardy

lemma isWeakDeriv_sub_ex042 {u v u' v' : AngCircle → ℝ} (hu : IsAngularWeakDeriv u u')
    (hv : IsAngularWeakDeriv v v') :
    IsAngularWeakDeriv (fun θ => u θ - v θ) (fun θ => u' θ - v' θ) where
  memLp := hu.memLp.sub hv.memLp
  memLp_deriv := hu.memLp_deriv.sub hv.memLp_deriv
  ibp := by
    intro ψ hψ
    have h1 := hu.ibp ψ hψ
    have h2 := hv.ibp ψ hψ
    have cψ := continuous_of_smooth hψ
    have cdψ := continuous_of_smooth (smooth_angDeriv hψ)
    have i1 := integrable_cont_mul hu.memLp cdψ
    have i2 := integrable_cont_mul hv.memLp cdψ
    have i3 := integrable_cont_mul hu.memLp_deriv cψ
    have i4 := integrable_cont_mul hv.memLp_deriv cψ
    simp only [sub_mul]
    rw [integral_sub i1 i2, integral_sub i3 i4, h1, h2]
    ring

lemma isWeakDeriv_const_ex042 (c : ℝ) :
    IsAngularWeakDeriv (fun _ : AngCircle => c) (fun _ => 0) := by
  have := DGPS.FiniteN.Tools.UniformVonMises.smooth_isWeakDeriv (smooth_const c)
  rw [angDeriv_const] at this
  exact this

lemma isWeakDeriv_const_mul_ex042 {u u' : AngCircle → ℝ} (hu : IsAngularWeakDeriv u u') (c : ℝ) :
    IsAngularWeakDeriv (fun θ => c * u θ) (fun θ => c * u' θ) where
  memLp := hu.memLp.const_mul c
  memLp_deriv := hu.memLp_deriv.const_mul c
  ibp := by
    intro ψ hψ
    have h1 := hu.ibp ψ hψ
    have e1 : ∫ θ, c * u θ * angDeriv ψ θ ∂angHaar = c * ∫ θ, u θ * angDeriv ψ θ ∂angHaar := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun θ => by ring)
    have e2 : ∫ θ, c * u' θ * ψ θ ∂angHaar = c * ∫ θ, u' θ * ψ θ ∂angHaar := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun θ => by ring)
    rw [e1, e2, h1]
    ring


lemma tendsto_eLpNorm_mul_ex042 {d : ℕ → AngCircle → ℝ} {c : AngCircle → ℝ} (hc : Continuous c)
    (hd : ∀ n, MemLp (d n) 2 angHaar)
    (ht : Tendsto (fun n => eLpNorm (d n) 2 angHaar) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun θ => d n θ * c θ) 2 angHaar) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := exists_bound_of_continuous hc
  have h1 : Tendsto (fun n => ENNReal.ofReal C * eLpNorm (d n) 2 angHaar) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul ht (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun n => bot_le)
    (fun n => ?_)
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    ((hd n).aestronglyMeasurable.mul hc.aestronglyMeasurable) ?_ 2
  refine Eventually.of_forall fun θ => ?_
  simp only [Pi.mul_apply, norm_mul]
  nlinarith [hC θ, norm_nonneg (d n θ), norm_nonneg (c θ)]

lemma tendsto_integral_sq_ex042 {u : ℕ → AngCircle → ℝ} {v : AngCircle → ℝ}
    (hu : ∀ n, MemLp (u n) 2 angHaar) (hv : MemLp v 2 angHaar)
    (ht : Tendsto (fun n => eLpNorm (fun θ => u n θ - v θ) 2 angHaar) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ θ, u n θ ^ 2 ∂angHaar) atTop (𝓝 (∫ θ, v θ ^ 2 ∂angHaar)) := by
  have hδ : Tendsto (fun n => (eLpNorm (fun θ => u n θ - v θ) 2 angHaar).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
    simpa [Function.comp_def] using this
  have hfin : ∀ n, eLpNorm (fun θ => u n θ - v θ) 2 angHaar ≠ ⊤ := fun n =>
    ((hu n).sub hv).eLpNorm_ne_top
  have hbd : ∀ n, |(eLpNorm (u n) 2 angHaar).toReal - (eLpNorm v 2 angHaar).toReal| ≤
      (eLpNorm (fun θ => u n θ - v θ) 2 angHaar).toReal := by
    intro n
    have a1 : eLpNorm (u n) 2 angHaar ≤ eLpNorm v 2 angHaar +
        eLpNorm (fun θ => u n θ - v θ) 2 angHaar := by
      have e : u n = v + (fun θ => u n θ - v θ) := by funext θ; simp
      calc eLpNorm (u n) 2 angHaar = eLpNorm (v + (fun θ => u n θ - v θ)) 2 angHaar := by
            rw [← e]
        _ ≤ _ := eLpNorm_add_le (by norm_num)
    have a2 : eLpNorm v 2 angHaar ≤ eLpNorm (u n) 2 angHaar +
        eLpNorm (fun θ => u n θ - v θ) 2 angHaar := by
      have e : v = u n + (fun θ => -(u n θ - v θ)) := by funext θ; simp
      calc eLpNorm v 2 angHaar = eLpNorm (u n + (fun θ => -(u n θ - v θ))) 2 angHaar := by
            rw [← e]
        _ ≤ eLpNorm (u n) 2 angHaar + eLpNorm (fun θ => -(u n θ - v θ)) 2 angHaar :=
            eLpNorm_add_le (by norm_num)
        _ = _ := by
            rw [show (fun θ => -(u n θ - v θ)) = -(fun θ => u n θ - v θ) from rfl, eLpNorm_neg]
    have b1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hv.eLpNorm_ne_top, hfin n⟩) a1
    have b2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨(hu n).eLpNorm_ne_top, hfin n⟩) a2
    rw [ENNReal.toReal_add hv.eLpNorm_ne_top (hfin n)] at b1
    rw [ENNReal.toReal_add (hu n).eLpNorm_ne_top (hfin n)] at b2
    rw [abs_le]; constructor <;> linarith
  have hconv : Tendsto (fun n => (eLpNorm (u n) 2 angHaar).toReal) atTop
      (𝓝 (eLpNorm v 2 angHaar).toReal) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => by rw [Real.dist_eq]; exact hbd n) hδ
  have h2 := hconv.pow 2
  rw [← integral_sq_eq_hardy hv] at h2
  exact h2.congr fun n => (integral_sq_eq_hardy (hu n)).symm


lemma bounded_groundPot_angSec_ex042 (h : ℝ) (hh : 0 < h) :
    ∃ B : ℝ, ∀ θ : AngCircle, |groundPot h (angSec θ)| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    (continuous_groundPot h hh).continuousOn
  refine ⟨B, fun θ => ?_⟩
  have hmem : angSec θ ∈ Set.Ioc (0 : ℝ) (0 + 2 * π) := (AddCircle.equivIoc (2 * π) 0 θ).2
  have := hB (angSec θ) ⟨hmem.1.le, by linarith [hmem.2]⟩
  simpa using this

lemma smooth_energy_ex042 {CV : ℝ} (h : ℝ) (hh : 0 < h)
    (hV : ∀ t, -(CV * h) ≤ groundPot h t) {g : AngCircle → ℝ} (hg : IsSmoothAngular g) :
    ∫ θ, (angDeriv g θ * sAng h θ + g θ * angDeriv (sAng h) θ) ^ 2 ∂angHaar ≤
      ∫ θ, qAng h θ * angDeriv g θ ^ 2 ∂angHaar + CV * h * ∫ θ, qAng h θ * g θ ^ 2 ∂angHaar := by
  obtain ⟨hsm, hid⟩ := periodic_part h hh hg
  have hs := isSmoothAngular_sAng h hh
  have hw : groundStateConj h g = fun θ => g θ * sAng h θ := by
    funext θ
    unfold groundStateConj
    rw [← sAng_sq h hh θ, Real.sqrt_sq (sAng_pos h hh θ).le]
  have hdw : angDeriv (groundStateConj h g) =
      fun θ => angDeriv g θ * sAng h θ + g θ * angDeriv (sAng h) θ := by
    rw [hw]; exact angDeriv_mul hg hs
  have hw2 : ∀ θ, groundStateConj h g θ ^ 2 = qAng h θ * g θ ^ 2 := by
    intro θ
    rw [hw]
    show (g θ * sAng h θ) ^ 2 = _
    rw [mul_pow, sAng_sq h hh]; ring
  rw [integral_circleReference h hh] at hid
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
  have key : ∫ θ, (angDeriv (groundStateConj h g) θ ^ 2 - CV * h * groundStateConj h g θ ^ 2)
      ∂angHaar ≤ ∫ θ, (angDeriv (groundStateConj h g) θ ^ 2 +
        groundPot h (angSec θ) * groundStateConj h g θ ^ 2) ∂angHaar := by
    refine integral_mono (i1.sub (i2.const_mul _)) i4 fun θ => ?_
    have := hV (angSec θ)
    have h2 := sq_nonneg (groundStateConj h g θ)
    simp only
    nlinarith
  rw [integral_sub i1 (i2.const_mul _), integral_const_mul] at key
  have e1 : ∫ θ, angDeriv g θ ^ 2 * qAng h θ ∂angHaar = ∫ θ, qAng h θ * angDeriv g θ ^ 2 ∂angHaar :=
    integral_congr_ae (Eventually.of_forall fun θ => by simp only; ring)
  have e2 : ∫ θ, groundStateConj h g θ ^ 2 ∂angHaar = ∫ θ, qAng h θ * g θ ^ 2 ∂angHaar :=
    integral_congr_ae (Eventually.of_forall hw2)
  have e3 : (fun θ => (angDeriv g θ * sAng h θ + g θ * angDeriv (sAng h) θ) ^ 2) =
      fun θ => angDeriv (groundStateConj h g) θ ^ 2 := by
    funext θ; rw [hdw]
  rw [e3]
  rw [e2, ← hid, e1] at key
  linarith


lemma memLp_of_cont_ex042 {c : AngCircle → ℝ} (hc : Continuous c) : MemLp c 2 angHaar := by
  obtain ⟨C, hC⟩ := exists_bound_of_continuous hc
  exact MemLp.of_bound hc.aestronglyMeasurable C (Eventually.of_forall hC)

lemma tendsto_lin_sq_ex042 {a b : ℕ → AngCircle → ℝ} {a0 b0 c1 c2 : AngCircle → ℝ}
    (hc1 : Continuous c1) (hc2 : Continuous c2)
    (ha : ∀ n, MemLp (a n) 2 angHaar) (hb : ∀ n, MemLp (b n) 2 angHaar)
    (ha0 : MemLp a0 2 angHaar) (hb0 : MemLp b0 2 angHaar)
    (hta : Tendsto (fun n => eLpNorm (fun θ => a n θ - a0 θ) 2 angHaar) atTop (𝓝 0))
    (htb : Tendsto (fun n => eLpNorm (fun θ => b n θ - b0 θ) 2 angHaar) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ θ, (a n θ * c1 θ + b n θ * c2 θ) ^ 2 ∂angHaar) atTop
      (𝓝 (∫ θ, (a0 θ * c1 θ + b0 θ * c2 θ) ^ 2 ∂angHaar)) := by
  have m1 := fun n => memLp_mul_cont (ha n) hc1
  have m2 := fun n => memLp_mul_cont (hb n) hc2
  refine tendsto_integral_sq_ex042 (fun n => (m1 n).add (m2 n))
    ((memLp_mul_cont ha0 hc1).add (memLp_mul_cont hb0 hc2)) ?_
  have t1 := tendsto_eLpNorm_mul_ex042 hc1 (fun n => (ha n).sub ha0) hta
  have t2 := tendsto_eLpNorm_mul_ex042 hc2 (fun n => (hb n).sub hb0) htb
  have t3 := t1.add t2
  rw [add_zero] at t3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds t3 (fun n => bot_le)
    (fun n => ?_)
  have e : (fun θ => (a n θ * c1 θ + b n θ * c2 θ) - (a0 θ * c1 θ + b0 θ * c2 θ)) =
      (fun θ => (a n θ - a0 θ) * c1 θ) + (fun θ => (b n θ - b0 θ) * c2 θ) := by
    funext θ; simp only [Pi.add_apply]; ring
  rw [e]
  exact eLpNorm_add_le (by norm_num)

lemma tendsto_mul_sq_ex042 {d : ℕ → AngCircle → ℝ} {u c : AngCircle → ℝ} (hc : Continuous c)
    (hd : ∀ n, MemLp (d n) 2 angHaar) (hu : MemLp u 2 angHaar)
    (ht : Tendsto (fun n => eLpNorm (fun θ => d n θ - u θ) 2 angHaar) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ θ, (d n θ * c θ) ^ 2 ∂angHaar) atTop
      (𝓝 (∫ θ, (u θ * c θ) ^ 2 ∂angHaar)) := by
  refine tendsto_integral_sq_ex042 (fun n => memLp_mul_cont (hd n) hc) (memLp_mul_cont hu hc) ?_
  have t1 := tendsto_eLpNorm_mul_ex042 hc (fun n => (hd n).sub hu) ht
  refine t1.congr fun n => ?_
  congr 1; funext θ; simp only [Pi.sub_apply]; ring

lemma weak_energy_ex042 {CV : ℝ} (h : ℝ) (hh : 0 < h)
    (hV : ∀ t, -(CV * h) ≤ groundPot h t) {g g' : AngCircle → ℝ} (hw : IsAngularWeakDeriv g g') :
    ∫ θ, (g' θ * sAng h θ + g θ * angDeriv (sAng h) θ) ^ 2 ∂angHaar ≤
      ∫ θ, qAng h θ * g' θ ^ 2 ∂angHaar + CV * h * ∫ θ, qAng h θ * g θ ^ 2 ∂angHaar := by
  obtain ⟨ψ, hψs, hψ1, hψ2⟩ := smooth_approx_hardy hw
  have hs := isSmoothAngular_sAng h hh
  have cs := continuous_of_smooth hs
  have cds := continuous_of_smooth (smooth_angDeriv hs)
  have hψc : ∀ n, Continuous (ψ n) := fun n => continuous_of_smooth (hψs n)
  have hdc : ∀ n, Continuous (angDeriv (ψ n)) := fun n =>
    continuous_of_smooth (smooth_angDeriv (hψs n))
  have mψ : ∀ n, MemLp (ψ n) 2 angHaar := fun n => memLp_of_cont_ex042 (hψc n)
  have mdψ : ∀ n, MemLp (angDeriv (ψ n)) 2 angHaar := fun n => memLp_of_cont_ex042 (hdc n)
  have hA := tendsto_lin_sq_ex042 (a := fun n => angDeriv (ψ n)) (b := ψ)
    (a0 := g') (b0 := g) cs cds mdψ mψ hw.memLp_deriv hw.memLp hψ2 hψ1
  have hB := tendsto_mul_sq_ex042 (d := fun n => angDeriv (ψ n)) (u := g') cs mdψ
    hw.memLp_deriv hψ2
  have hC := tendsto_mul_sq_ex042 (d := ψ) (u := g) cs mψ hw.memLp hψ1
  have eq1 : ∀ F : AngCircle → ℝ, ∫ θ, qAng h θ * F θ ^ 2 ∂angHaar =
      ∫ θ, (F θ * sAng h θ) ^ 2 ∂angHaar := fun F =>
    integral_congr_ae (Eventually.of_forall fun θ => by
      simp only; rw [mul_pow, sAng_sq h hh]; ring)
  simp_rw [eq1]
  refine le_of_tendsto_of_tendsto' hA (hB.add (hC.const_mul (CV * h))) fun n => ?_
  have := smooth_energy_ex042 (CV := CV) h hh hV (hψs n)
  simp_rw [eq1] at this
  exact this


lemma agmon_scaled_ex042 {w w' : AngCircle → ℝ} (hw : IsAngularWeakDeriv w w') :
    ∀ᵐ θ ∂angHaar, w θ ^ 2 ≤ (∫ θ, w θ ^ 2 ∂angHaar) +
      2 * Real.sqrt (DGPS.Circle.AngularNormalization.a0 * (∫ θ, w θ ^ 2 ∂angHaar) * ∫ θ, w' θ ^ 2 ∂angHaar) := by
  set n : ℝ := ∫ θ, w θ ^ 2 ∂angHaar with hn
  set E : ℝ := ∫ θ, w' θ ^ 2 ∂angHaar with hE
  have hn0 : 0 ≤ n := integral_nonneg fun _ => sq_nonneg _
  have hE0 : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  rcases hn0.eq_or_lt with h0 | hpos
  · have hz : (fun θ => w θ ^ 2) =ᵐ[angHaar] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hw.memLp.integrable_sq).1 h0.symm
    filter_upwards [hz] with θ hθ
    simp only [Pi.zero_apply] at hθ
    rw [hθ, ← h0]; simp
  · set c : ℝ := (Real.sqrt n)⁻¹ with hc
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hpos
    have hc2 : c ^ 2 * n = 1 := by
      rw [hc, inv_pow, Real.sq_sqrt hn0]; field_simp
    have hw1 := isWeakDeriv_const_mul_ex042 hw c
    have hn1 : ∫ θ, (c * w θ) ^ 2 ∂angHaar = 1 := by
      have : ∫ θ, (c * w θ) ^ 2 ∂angHaar = c ^ 2 * n := by
        rw [hn, ← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun θ => by simp only; ring)
      rw [this, hc2]
    have hE1 : ∫ θ, (c * w' θ) ^ 2 ∂angHaar = c ^ 2 * E := by
      rw [hE, ← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun θ => by simp only; ring)
    have hag := agmon_ang hw1 hn1
    rw [hE1] at hag
    filter_upwards [hag] with θ hθ
    have hsq : Real.sqrt (DGPS.Circle.AngularNormalization.a0 * (c ^ 2 * E)) = c * Real.sqrt (DGPS.Circle.AngularNormalization.a0 * E) := by
      rw [show DGPS.Circle.AngularNormalization.a0 * (c ^ 2 * E) = c ^ 2 * (DGPS.Circle.AngularNormalization.a0 * E) by ring, Real.sqrt_mul (sq_nonneg c),
        Real.sqrt_sq (inv_nonneg.2 hsn.le)]
    rw [hsq] at hθ
    have hcn : c * Real.sqrt n = 1 := by rw [hc]; field_simp
    have hsq2 : Real.sqrt (DGPS.Circle.AngularNormalization.a0 * n * E) = Real.sqrt n * Real.sqrt (DGPS.Circle.AngularNormalization.a0 * E) := by
      rw [show DGPS.Circle.AngularNormalization.a0 * n * E = n * (DGPS.Circle.AngularNormalization.a0 * E) by ring, Real.sqrt_mul hn0]
    rw [hsq2]
    have hnn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0
    have : w θ ^ 2 = n * (c * w θ) ^ 2 := by
      have : n * c ^ 2 = 1 := by linarith [hc2]
      calc w θ ^ 2 = (n * c ^ 2) * w θ ^ 2 := by rw [this, one_mul]
        _ = n * (c * w θ) ^ 2 := by ring
    rw [this]
    calc n * (c * w θ) ^ 2 ≤ n * (1 + 2 * (c * Real.sqrt (DGPS.Circle.AngularNormalization.a0 * E))) :=
          mul_le_mul_of_nonneg_left hθ hn0
      _ = n + 2 * (Real.sqrt n * Real.sqrt (DGPS.Circle.AngularNormalization.a0 * E)) := by
          have : n * c = Real.sqrt n := by
            calc n * c = (Real.sqrt n * Real.sqrt n) * c := by rw [hnn]
              _ = Real.sqrt n * (c * Real.sqrt n) := by ring
              _ = Real.sqrt n := by rw [hcn, mul_one]
          calc n * (1 + 2 * (c * Real.sqrt (DGPS.Circle.AngularNormalization.a0 * E))) = n + 2 * ((n * c) * Real.sqrt (DGPS.Circle.AngularNormalization.a0 * E)) := by ring
            _ = _ := by rw [this]


lemma mass_ex042 {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    {f : α → ℝ} (hf : MemLp f 2 P) (hn : ∫ x, f x ^ 2 ∂P = 1) (h0 : ∀ x, 0 ≤ f x) :
    ∫ x, (f x - 1) ^ 2 ∂P = 2 * (1 - ∫ x, f x ∂P) ∧
      1 / 2 * ∫ x, (f x - 1) ^ 2 ∂P ≤ ∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P := by
  set m : ℝ := ∫ x, f x ∂P with hm
  have i1 : Integrable f P := hf.integrable (by norm_num)
  have i2 : Integrable (fun x => f x ^ 2) P := hf.integrable_sq
  have e1 : ∫ x, (f x - 1) ^ 2 ∂P = 2 * (1 - m) := by
    have : (fun x => (f x - 1) ^ 2) = fun x => (f x ^ 2 - 2 * f x) + 1 := by
      funext x; ring
    have j : Integrable (fun x => f x ^ 2 - 2 * f x) P := i2.sub (i1.const_mul 2)
    rw [this, integral_add j (integrable_const _),
      integral_sub i2 (i1.const_mul 2), integral_const_mul, hn]
    simp [hm]; ring
  have e2 : ∫ x, (f x - m) ^ 2 ∂P = 1 - m ^ 2 := by
    have : (fun x => (f x - m) ^ 2) = fun x => (f x ^ 2 - (2 * m) * f x) + m ^ 2 := by
      funext x; ring
    have j : Integrable (fun x => f x ^ 2 - (2 * m) * f x) P := i2.sub (i1.const_mul (2 * m))
    rw [this, integral_add j (integrable_const _),
      integral_sub i2 (i1.const_mul (2 * m)), integral_const_mul, hn]
    simp [hm]; ring
  have hm0 : 0 ≤ m := integral_nonneg h0
  have hv : 0 ≤ ∫ x, (f x - m) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
  rw [e2] at hv
  have hm1 : m ≤ 1 := by nlinarith
  refine ⟨e1, ?_⟩
  rw [e1, e2]
  nlinarith

lemma withDensity_le_ex042 (h : ℝ) {M : ℝ} (hM : ∀ θ, qAng h θ ≤ M) :
    (angHaar.withDensity fun θ => ENNReal.ofReal (qAng h θ)) ≤
      ENNReal.ofReal M • angHaar := by
  rw [Measure.le_iff']
  intro s
  rw [Measure.smul_apply, withDensity_apply' _ s, smul_eq_mul]
  calc ∫⁻ a in s, ENNReal.ofReal (qAng h a) ∂angHaar ≤ ∫⁻ _ in s, ENNReal.ofReal M ∂angHaar :=
        lintegral_mono fun a => ENNReal.ofReal_le_ofReal (hM a)
    _ = _ := by rw [setLIntegral_const]

lemma isAngMeasureWeakDeriv_ex042 (h : ℝ) (hh : 0 < h)
    (hP : IsProbabilityMeasure (engineeredReference h)) {f f' : AngCircle → ℝ}
    (hw : IsAngularWeakDeriv f f') :
    IsAngMeasureWeakDeriv (angMap ⟨engineeredReference h, hP⟩) f f' := by
  have hν := angMap_engineered_hardy hP
  obtain ⟨m, M, hm, hmM⟩ := exists_bounds_hardy (hardyData_qAng hh).cont (hardyData_qAng hh).pos
  have hle := withDensity_le_ex042 h (fun θ => (hmM θ).2)
  have hcne : ENNReal.ofReal M ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨?_, ?_, hw.memLp.integrable (by norm_num), hw.memLp_deriv.integrable (by norm_num),
    hw.ibp⟩
  · show MemLp f 2 ((angMap ⟨engineeredReference h, hP⟩ : ProbabilityMeasure AngCircle) :
      Measure AngCircle)
    rw [hν]; exact hw.memLp.of_measure_le_smul hcne hle
  · show MemLp f' 2 ((angMap ⟨engineeredReference h, hP⟩ : ProbabilityMeasure AngCircle) :
      Measure AngCircle)
    rw [hν]; exact hw.memLp_deriv.of_measure_le_smul hcne hle

lemma poincare_ex042 (h : ℝ) (hh : 0 < h) (hP : IsProbabilityMeasure (engineeredReference h))
    {f f' : AngCircle → ℝ} (hw : IsAngularWeakDeriv f f') :
    angVariance (angMap ⟨engineeredReference h, hP⟩) f ≤
      4 * (π / h) * ∫ θ, f' θ ^ 2
        ∂((angMap ⟨engineeredReference h, hP⟩ : ProbabilityMeasure AngCircle) :
          Measure AngCircle) :=
  weak_hardy_hardy (hardyData_qAng hh) _ (angMap_engineered_hardy hP)
    (isAngMeasureWeakDeriv_ex042 h hh hP hw)

lemma integral_ref_nu_ex042 (h : ℝ) (hP : IsProbabilityMeasure (engineeredReference h))
    (F : AngCircle → ℝ) :
    ∫ x, F (angEquiv x) ∂engineeredReference h =
      ∫ θ, F θ ∂((angMap ⟨engineeredReference h, hP⟩ : ProbabilityMeasure AngCircle) :
        Measure AngCircle) := by
  show _ = ∫ θ, F θ ∂((engineeredReference h).map angEquiv)
  rw [angEquiv.measurableEmbedding.integral_map]


/-- The constant in the Agmon-type sup bound for `w = g √q`. -/
noncomputable def supConst_ex042 (CV : ℝ) : ℝ :=
  8 * π + 2 * Real.sqrt (DGPS.Circle.AngularNormalization.a0 * (8 * π) * (1 + 8 * π * CV))

lemma supConst_nonneg_ex042 (CV : ℝ) : 0 ≤ supConst_ex042 CV := by
  unfold supConst_ex042
  have := Real.pi_pos
  positivity

lemma sup_core_ex042 (h : ℝ) (hh : 2 ≤ h) {CV c0 : ℝ} (hCV : 0 ≤ CV) (hc0 : 0 < c0)
    (hV : ∀ t, -(CV * h) ≤ groundPot h t)
    (hq : ∀ θ, c0 * h ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * h) ≤ qAng h θ)
    {f f' : AngCircle → ℝ} (hw : IsAngularWeakDeriv f f') {T : ℝ} (hT0 : 0 ≤ T)
    (hE : ∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar ≤ h * T)
    (hN : ∫ θ, qAng h θ * (f θ - 1) ^ 2 ∂angHaar ≤ 8 * π * T) :
    ∀ᵐ θ ∂angHaar, (f θ - 1) ^ 2 ≤
      supConst_ex042 CV / c0 * (h * Real.exp (2 * h) * T) := by
  have hp : 0 < h := by linarith
  have hpi := Real.pi_pos
  have ha0 := DGPS.Circle.AngularNormalization.a0_pos
  have hs := isSmoothAngular_sAng h hp
  have hg : IsAngularWeakDeriv (fun θ => f θ - 1) f' := by
    have := isWeakDeriv_sub_ex042 hw (isWeakDeriv_const_ex042 1)
    simpa using this
  have hwd := isAngularWeakDeriv_mul_smooth hg hs
  have hag := agmon_scaled_ex042 hwd
  have eq1 : ∫ θ, ((f θ - 1) * sAng h θ) ^ 2 ∂angHaar =
      ∫ θ, qAng h θ * (f θ - 1) ^ 2 ∂angHaar :=
    integral_congr_ae (Eventually.of_forall fun θ => by
      simp only; rw [mul_pow, sAng_sq h hp]; ring)
  have hen := weak_energy_ex042 (CV := CV) h hp hV hg
  have hn0 : 0 ≤ ∫ θ, qAng h θ * (f θ - 1) ^ 2 ∂angHaar :=
    integral_nonneg fun θ => q_sq_nonneg h hp (fun θ => f θ - 1) θ
  have hE0 : 0 ≤ ∫ θ, (f' θ * sAng h θ + (f θ - 1) * angDeriv (sAng h) θ) ^ 2 ∂angHaar :=
    integral_nonneg fun _ => sq_nonneg _
  set n : ℝ := ∫ θ, qAng h θ * (f θ - 1) ^ 2 ∂angHaar with hn
  set E2 : ℝ := ∫ θ, (f' θ * sAng h θ + (f θ - 1) * angDeriv (sAng h) θ) ^ 2 ∂angHaar
    with hE2
  have hE2b : E2 ≤ h * T + CV * h * (8 * π * T) := by
    have := mul_le_mul_of_nonneg_left hN (mul_nonneg hCV hp.le)
    linarith
  have hprod : DGPS.Circle.AngularNormalization.a0 * n * E2 ≤
      DGPS.Circle.AngularNormalization.a0 * (8 * π * T) * (h * T + CV * h * (8 * π * T)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hN ha0.le) hE2b hE0 (by positivity)
  have hsqrt := Real.sqrt_le_sqrt hprod
  have hsh : 1 ≤ √h := by
    rw [show (1:ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hshpos : 0 < √h := by linarith
  have hK : DGPS.Circle.AngularNormalization.a0 * (8 * π * T) *
      (h * T + CV * h * (8 * π * T)) =
      (DGPS.Circle.AngularNormalization.a0 * (8 * π) * (1 + 8 * π * CV)) * h * T ^ 2 := by ring
  have hK0 : 0 ≤ DGPS.Circle.AngularNormalization.a0 * (8 * π) * (1 + 8 * π * CV) := by
    positivity
  have hsq : Real.sqrt (DGPS.Circle.AngularNormalization.a0 * (8 * π * T) *
      (h * T + CV * h * (8 * π * T))) =
      Real.sqrt (DGPS.Circle.AngularNormalization.a0 * (8 * π) * (1 + 8 * π * CV)) * √h * T := by
    rw [hK, Real.sqrt_mul (by positivity), Real.sqrt_mul hK0, Real.sqrt_sq hT0]
  rw [hsq] at hsqrt
  have hSC : 0 ≤ Real.sqrt (DGPS.Circle.AngularNormalization.a0 * (8 * π) * (1 + 8 * π * CV)) :=
    Real.sqrt_nonneg _
  have hw2 : ∀ᵐ θ ∂angHaar, qAng h θ * (f θ - 1) ^ 2 ≤ supConst_ex042 CV * √h * T := by
    filter_upwards [hag] with θ hθ
    rw [eq1] at hθ
    have e : ((f θ - 1) * sAng h θ) ^ 2 = qAng h θ * (f θ - 1) ^ 2 := by
      rw [mul_pow, sAng_sq h hp]; ring
    have hθ' : ((f θ - 1) * sAng h θ) ^ 2 ≤ n + 2 *
        Real.sqrt (DGPS.Circle.AngularNormalization.a0 * n * E2) := hθ
    rw [e] at hθ'
    unfold supConst_ex042
    have h1 : 0 ≤ T * (√h - 1) := mul_nonneg hT0 (by linarith)
    have h2 : 0 ≤ Real.sqrt (DGPS.Circle.AngularNormalization.a0 * (8 * π) *
        (1 + 8 * π * CV)) * T * (√h - 1) := by
      have : 0 ≤ T * (√h - 1) := h1
      positivity
    nlinarith
  have hqpos : 0 < c0 * h ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * h) := by positivity
  have hrp : h ^ (-(1 / 2 : ℝ)) = (√h)⁻¹ := by
    rw [Real.rpow_neg hp.le, Real.sqrt_eq_rpow]
  have hexp : Real.exp (-2 * h) * Real.exp (2 * h) = 1 := by
    rw [← Real.exp_add]; simp
  filter_upwards [hw2] with θ hθ
  have h3 : c0 * h ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * h) * (f θ - 1) ^ 2 ≤
      supConst_ex042 CV * √h * T :=
    le_trans (mul_le_mul_of_nonneg_right (hq θ) (sq_nonneg _)) hθ
  rw [hrp] at h3
  have hE2pos := Real.exp_pos (2 * h)
  have hSC0 := supConst_nonneg_ex042 CV
  have hsqh : √h * √h = h := Real.mul_self_sqrt hp.le
  -- multiply both sides by √h * exp (2h) / c0
  have h4 : (f θ - 1) ^ 2 * c0 = (c0 * (√h)⁻¹ * Real.exp (-2 * h) * (f θ - 1) ^ 2) *
      (√h * Real.exp (2 * h)) := by
    calc (f θ - 1) ^ 2 * c0 = (f θ - 1) ^ 2 * c0 * (Real.exp (-2 * h) * Real.exp (2 * h)) *
          ((√h)⁻¹ * √h) := by
          rw [hexp, inv_mul_cancel₀ hshpos.ne']; ring
      _ = _ := by ring
  have h5 : (f θ - 1) ^ 2 * c0 ≤ supConst_ex042 CV * h * Real.exp (2 * h) * T := by
    rw [h4]
    calc _ ≤ (supConst_ex042 CV * √h * T) * (√h * Real.exp (2 * h)) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = supConst_ex042 CV * (√h * √h) * Real.exp (2 * h) * T := by ring
      _ = _ := by rw [hsqh]
  rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
  nlinarith


end DGPS.Examples.EngineeredRankOneEX042

namespace DGPS.Examples

open DGPS.Examples.EngineeredRankOne DGPS.Examples.EngineeredRankOneEX042 DGPS.Models
  DGPS.Examples.EngineeredHardy DGPS.Examples.EngineeredGroundState
  DGPS.Circle.AngularNormalization

/-- EX042: engineered small-`T` `L²` and sup controls.  For `ρ = f² μ_h` with `f ≥ 0`,
`μ_h(f²) = 1` and angular weak derivative `f'`, put `T = μ_h((f')²)/h + ρ(E_h)²` and `g = f - 1`,
`N = μ_h(g²)`, `S = h exp(2h) T`.  If `T ≤ 1` then `N = 2 (1 - μ_h f)`, `Var_μ(f) ≥ N/2`,
`N ≤ C T` and `‖g‖_∞² ≤ C S` (essential supremum, for `μ_h` and for angular Haar measure), with `C`
independent of `h ≥ 2` and `ρ`. -/
theorem engineered_small_t_l2_and_sup_controls :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 2 ≤ h → ∀ f f' : AngCircle → ℝ,
      IsAngularWeakDeriv f f' → (∀ θ, 0 ≤ f θ) →
      ∫ x, f (angEquiv x) ^ 2 ∂engineeredReference h = 1 →
      ∀ T N : ℝ,
      T = (∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h) / h +
        (∫ x, Eang h (angEquiv x) ∂densityRef h f) ^ 2 →
      T ≤ 1 →
      N = ∫ x, (f (angEquiv x) - 1) ^ 2 ∂engineeredReference h →
      N = 2 * (1 - ∫ x, f (angEquiv x) ∂engineeredReference h) ∧
      N / 2 ≤ ∫ x, (f (angEquiv x) - ∫ y, f (angEquiv y) ∂engineeredReference h) ^ 2
        ∂engineeredReference h ∧
      N ≤ C * T ∧
      (∀ᵐ x ∂engineeredReference h, (f (angEquiv x) - 1) ^ 2 ≤ C * (h * Real.exp (2 * h) * T)) ∧
      (∀ᵐ θ ∂angHaar, (f θ - 1) ^ 2 ≤ C * (h * Real.exp (2 * h) * T)) := by
  obtain ⟨c0, C36, hc0, hC36, H36⟩ := engineered_normalization_and_rare_mass_bounds
  obtain ⟨C37, hC37, H37⟩ := engineered_drift_and_ground_potential
  have hpi := Real.pi_pos
  refine ⟨max (8 * π) (supConst_ex042 C37 / c0), lt_max_of_lt_left (by positivity), ?_⟩
  intro h hh f f' hw hf0 hnorm T N hT hT1 hN
  have hp : 0 < h := by linarith
  have hP : IsProbabilityMeasure (engineeredReference h) := engineeredReference_isProbability h hp
  have hV : ∀ t, -(C37 * h) ≤ groundPot h t := fun t => by
    have := (H37 h hh t).2.2
    nlinarith [sq_nonneg (h * Real.sin t)]
  have hq := (H36 h hh).2.1
  -- translate to angular integrals
  have hE_ref : ∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h =
      ∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar := integral_ref_ent h hp (fun θ => f' θ ^ 2)
  have hT0 : 0 ≤ T := by
    rw [hT]
    have : 0 ≤ ∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h :=
      integral_nonneg fun _ => sq_nonneg _
    positivity
  have hEq : ∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar ≤ h * T := by
    have h1 : (∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar) / h ≤ T := by
      rw [← hE_ref]; rw [hT]
      nlinarith [sq_nonneg (∫ x, Eang h (angEquiv x) ∂densityRef h f)]
    rw [div_le_iff₀ hp] at h1
    linarith
  have hνp : IsProbabilityMeasure ((angMap ⟨engineeredReference h, hP⟩ : ProbabilityMeasure AngCircle) : Measure AngCircle) := inferInstance
  have hweak := isAngMeasureWeakDeriv_ex042 h hp hP hw
  have hnorm_ν : ∫ θ, f θ ^ 2 ∂((angMap ⟨engineeredReference h, hP⟩ : ProbabilityMeasure AngCircle) : Measure AngCircle) = 1 := by
    rw [← integral_ref_nu_ex042 h hP (fun θ => f θ ^ 2)]; exact hnorm
  obtain ⟨hm1, hm2⟩ := mass_ex042 hweak.memLp hnorm_ν hf0
  have hNν : N = ∫ θ, (f θ - 1) ^ 2 ∂((angMap ⟨engineeredReference h, hP⟩ : ProbabilityMeasure AngCircle) : Measure AngCircle) := by
    rw [hN]; exact integral_ref_nu_ex042 h hP (fun θ => (f θ - 1) ^ 2)
  have hmean : ∫ x, f (angEquiv x) ∂engineeredReference h = ∫ θ, f θ ∂((angMap ⟨engineeredReference h, hP⟩ : ProbabilityMeasure AngCircle) : Measure AngCircle) :=
    integral_ref_nu_ex042 h hP f
  have hvar_ref : ∫ x, (f (angEquiv x) - ∫ y, f (angEquiv y) ∂engineeredReference h) ^ 2
      ∂engineeredReference h = angVariance (angMap ⟨engineeredReference h, hP⟩) f := by
    unfold angVariance
    have := integral_ref_nu_ex042 h hP
      (fun θ => (f θ - ∫ φ, f φ ∂((angMap ⟨engineeredReference h, hP⟩ : ProbabilityMeasure AngCircle) : Measure AngCircle)) ^ 2)
    rw [hmean]
    exact this
  have hpc := poincare_ex042 h hp hP hw
  have hEν : ∫ θ, f' θ ^ 2 ∂((angMap ⟨engineeredReference h, hP⟩ : ProbabilityMeasure AngCircle) : Measure AngCircle) = ∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar := by
    show ∫ θ, f' θ ^ 2 ∂((angMap ⟨engineeredReference h, hP⟩ : ProbabilityMeasure AngCircle) :
      Measure AngCircle) = _
    rw [angMap_engineered_hardy hP]
    exact integral_nu_hardy (hardyData_qAng hp).cont (hardyData_qAng hp).pos _
  have hNq : ∫ θ, qAng h θ * (f θ - 1) ^ 2 ∂angHaar = N := by
    rw [hNν]
    show _ = ∫ θ, (f θ - 1) ^ 2 ∂((angMap ⟨engineeredReference h, hP⟩ : ProbabilityMeasure
      AngCircle) : Measure AngCircle)
    rw [angMap_engineered_hardy hP]
    exact (integral_nu_hardy (hardyData_qAng hp).cont (hardyData_qAng hp).pos _).symm
  have hNle : N ≤ 8 * π * T := by
    have h1 : angVariance (angMap ⟨engineeredReference h, hP⟩) f ≤ 4 * (π / h) * (h * T) := by
      refine hpc.trans ?_
      rw [hEν]
      exact mul_le_mul_of_nonneg_left hEq (by positivity)
    have h2 : 4 * (π / h) * (h * T) = 4 * π * T := by field_simp
    have h3 : N / 2 ≤ angVariance (angMap ⟨engineeredReference h, hP⟩) f := by
      unfold angVariance; rw [hNν]; linarith [hm2]
    linarith
  have hCmax1 : 8 * π ≤ max (8 * π) (supConst_ex042 C37 / c0) := le_max_left _ _
  have hCmax2 : supConst_ex042 C37 / c0 ≤ max (8 * π) (supConst_ex042 C37 / c0) :=
    le_max_right _ _
  have hsup : ∀ᵐ θ ∂angHaar, (f θ - 1) ^ 2 ≤
      max (8 * π) (supConst_ex042 C37 / c0) * (h * Real.exp (2 * h) * T) := by
    have hcore := sup_core_ex042 h hh hC37.le hc0 hV hq hw hT0 hEq (by rw [hNq]; exact hNle)
    filter_upwards [hcore] with θ hθ
    refine hθ.trans (mul_le_mul_of_nonneg_right hCmax2 (by positivity))
  refine ⟨?_, ?_, ?_, ?_, hsup⟩
  · rw [hNν, hm1, hmean]
  · rw [hvar_ref]
    rw [hNν]; unfold angVariance; linarith [hm2]
  · exact hNle.trans (mul_le_mul_of_nonneg_right hCmax1 hT0)
  · -- transfer the angular a.e. bound to the reference measure
    unfold engineeredReference
    rw [angEquiv.symm.measurableEmbedding.ae_map_iff]
    have hac := (withDensity_absolutelyContinuous angHaar
      (fun θ => ENNReal.ofReal (qAng h θ))).ae_le hsup
    filter_upwards [hac] with θ hθ
    simpa using hθ

end DGPS.Examples
