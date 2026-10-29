import DGPS.Examples.EngineeredRankOneEigen
import DGPS.Variational.PositiveRankOne

open MeasureTheory Real Set Filter Topology
open scoped ContDiff
open DGPS.Circle.AngularNormalization

/-!
# Engineered exact scalar gap and dissipation (EX033)

For `h ≥ 2` the engineered data of EX030 is a positive centered rank-one model
(`DGPS.Models.engineeredModel`, `q = q_h ∘ angEquiv`, `φ = E_h ∘ angEquiv`, `η = 1`) in the sense of
EX006. Its `V` is the engineered `V` of EX030 up to the additive constant `log Z_h` (so gap and
dissipation are unchanged). The EX006 identity with `η = 1` and `φ = E_h` and the eigen-equation of
EX032 (`Aq = a₀ Λ_h E_h`, `φ' = 2π E_h'`) give, for every absolute-admissible density `ρ`,
`G = H + M²/2` and `D / a₀ = I / a₀ + 2 Λ_h M² + M² J` (`a₀ = 4π²`; division by `a₀` is the
angular normalization of EX001), all quantities being finite.
Main output: `DGPS.Examples.engineered_exact_scalar_gap_and_dissipation`.
-/

namespace DGPS.Examples.EngineeredRankOne

/-- Angular derivative `E_h'` of the feature, as a function on the angular circle. -/
noncomputable def dEang (h : ℝ) (θ : AngCircle) : ℝ :=
  h * Real.Angle.sin θ * exp (h * (1 - Real.Angle.cos θ)) / tanh h

/-- Angular second derivative `E_h''` of the feature. -/
noncomputable def ddEang (h : ℝ) (θ : AngCircle) : ℝ :=
  h / tanh h * exp (h * (1 - Real.Angle.cos θ)) *
    (Real.Angle.cos θ + h * Real.Angle.sin θ ^ 2)

/-- Angular score `(log q_h)'`. -/
noncomputable def dlogqAng (h : ℝ) (θ : AngCircle) : ℝ :=
  -(h + integrand h (1 - Real.Angle.cos θ)) * Real.Angle.sin θ

theorem Uang_coe' (t : ℝ) : Uang ((t : ℝ) : AngCircle) = 1 - Real.cos t := Uang_coe t

theorem dEang_coe (h t : ℝ) : dEang h ((t : ℝ) : AngCircle) = dE h t := by
  have e : dEang h (t : Real.Angle) = dE h t := by
    simp [dEang, dE, Real.Angle.sin_coe, Real.Angle.cos_coe]
  exact e

theorem ddEang_coe (h t : ℝ) : ddEang h ((t : ℝ) : AngCircle) =
    h / tanh h * exp (h * (1 - Real.cos t)) * (Real.cos t + h * Real.sin t ^ 2) := by
  have e : ddEang h (t : Real.Angle) =
      h / tanh h * exp (h * (1 - Real.cos t)) * (Real.cos t + h * Real.sin t ^ 2) := by
    simp [ddEang, Real.Angle.sin_coe, Real.Angle.cos_coe]
  exact e

theorem dlogqAng_coe (h t : ℝ) : dlogqAng h ((t : ℝ) : AngCircle) =
    -(h + integrand h (1 - Real.cos t)) * Real.sin t := by
  have e : dlogqAng h (t : Real.Angle) =
      -(h + integrand h (1 - Real.cos t)) * Real.sin t := by
    simp [dlogqAng, Real.Angle.sin_coe, Real.Angle.cos_coe]
  exact e

theorem angDeriv_of {ψ G : AngCircle → ℝ}
    (hG : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ψ (s : AngCircle)) (G (t : AngCircle)) t)
    (θ : AngCircle) : angDeriv ψ θ = G θ := by
  unfold angDeriv
  rw [(hG _).deriv]
  have : ((angSec θ : ℝ) : AngCircle) = θ := by
    unfold angSec; exact AddCircle.coe_equivIoc
  rw [this]

theorem coordPartial_of {ψ G : AngCircle → ℝ}
    (hψ : IsSmoothAngular ψ)
    (hG : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ψ (s : AngCircle)) (G (t : AngCircle)) t)
    (x : Torus 1) : coordPartial 0 (ψ ∘ angEquiv) x = 2 * π * G (angEquiv x) := by
  rw [coordPartial_comp_angEquiv hψ, angDeriv_of hG]

theorem isSmoothAngular_Eang (h : ℝ) : IsSmoothAngular (Eang h) := by
  have hUs : ContDiff ℝ ∞ (fun t : ℝ => Uang ((t : ℝ) : AngCircle)) := by
    have : (fun t : ℝ => Uang ((t : ℝ) : AngCircle)) = fun t => 1 - Real.cos t := funext Uang_coe
    rw [this]; exact contDiff_const.sub Real.contDiff_cos
  unfold IsSmoothAngular Eang
  exact ((Real.contDiff_exp.comp (contDiff_const.mul hUs)).sub contDiff_const).div_const _

theorem isSmoothAngular_dEang (h : ℝ) : IsSmoothAngular (dEang h) := by
  unfold IsSmoothAngular
  have : (fun s : ℝ => dEang h (s : AngCircle)) = dE h := funext (dEang_coe h)
  rw [this]
  unfold dE
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => h * (1 - Real.cos t)) :=
    contDiff_const.mul (contDiff_const.sub Real.contDiff_cos)
  exact (((contDiff_const.mul Real.contDiff_sin).mul (Real.contDiff_exp.comp h1))).div_const _

theorem isSmoothAngular_qAng (h : ℝ) (hh : 0 < h) : IsSmoothAngular (qAng h) := by
  have hUs : ContDiff ℝ ∞ (fun t : ℝ => 1 - Real.cos t) :=
    contDiff_const.sub Real.contDiff_cos
  have hL : ContDiff ℝ ∞ (fun t : ℝ => logq h ((t : ℝ) : AngCircle)) := by
    have : (fun t : ℝ => logq h ((t : ℝ) : AngCircle)) =
        fun t => -(h * (1 - Real.cos t)) - corr h (1 - Real.cos t) := by
      funext t; unfold logq; rw [Uang_coe']
    rw [this]
    exact (contDiff_const.mul hUs).neg.sub ((contDiff_corr h hh).comp hUs)
  unfold IsSmoothAngular qAng
  exact contDiff_const.mul (Real.contDiff_exp.comp hL)

theorem log_qAng (h : ℝ) (hh : 0 < h) (θ : AngCircle) :
    Real.log (qAng h θ) = logq h θ - Real.log (Zh h) := by
  unfold qAng
  rw [Real.log_mul (inv_pos.2 (Zh_pos h hh)).ne' (exp_pos _).ne', Real.log_inv, Real.log_exp]
  ring

theorem isSmoothAngular_log_qAng (h : ℝ) (hh : 0 < h) :
    IsSmoothAngular (fun θ => Real.log (qAng h θ)) := by
  have hUs : ContDiff ℝ ∞ (fun t : ℝ => 1 - Real.cos t) :=
    contDiff_const.sub Real.contDiff_cos
  unfold IsSmoothAngular
  have : (fun s : ℝ => Real.log (qAng h (s : AngCircle))) =
      fun t => -(h * (1 - Real.cos t)) - corr h (1 - Real.cos t) - Real.log (Zh h) := by
    funext t; rw [log_qAng h hh]; unfold logq; rw [Uang_coe']
  rw [this]
  exact ((contDiff_const.mul hUs).neg.sub ((contDiff_corr h hh).comp hUs)).sub contDiff_const

theorem hasDerivAt_log_qAng (h : ℝ) (hh : 0 < h) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.log (qAng h (s : AngCircle))) (dlogqAng h (t : AngCircle)) t := by
  have : (fun s : ℝ => Real.log (qAng h (s : AngCircle))) =
      fun s => logq h ((s : ℝ) : AngCircle) - Real.log (Zh h) := funext fun s => log_qAng h hh _
  rw [this, dlogqAng_coe]
  exact (hasDerivAt_logq h hh t).sub_const _

theorem hasDerivAt_dEang (h : ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => dEang h (s : AngCircle)) (ddEang h (t : AngCircle)) t := by
  have : (fun s : ℝ => dEang h (s : AngCircle)) = dE h := funext (dEang_coe h)
  rw [this, ddEang_coe]
  exact hasDerivAt_dE h t

theorem hasDerivAt_Eang' (h : ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Eang h (s : AngCircle)) (dEang h (t : AngCircle)) t := by
  rw [dEang_coe]; exact hasDerivAt_Eang h t

theorem isSmoothAngular_two_pi_dEang (h : ℝ) :
    IsSmoothAngular (fun θ => 2 * π * dEang h θ) := by
  unfold IsSmoothAngular
  exact contDiff_const.mul (isSmoothAngular_dEang h)

theorem hasDerivAt_two_pi_dEang (h : ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => 2 * π * dEang h (s : AngCircle))
      (2 * π * ddEang h (t : AngCircle)) t :=
  (hasDerivAt_dEang h t).const_mul _

/-- Pointwise eigen-equation in angular form. -/
theorem eigen_ang (h : ℝ) (hh : 0 < h) (θ : AngCircle) :
    -(ddEang h θ + dlogqAng h θ * dEang h θ) = lamH h * Eang h θ := by
  induction θ using Real.Angle.induction_on with
  | _ t =>
    have e1 := ddEang_coe h t
    have e2 := dlogqAng_coe h t
    have e3 := dEang_coe h t
    have e4 := eigen_explicit h hh t
    have e5 : (t : Real.Angle) = ((t : ℝ) : AngCircle) := rfl
    rw [e5]
    rw [e1, e2, e3]
    exact e4

end DGPS.Examples.EngineeredRankOne

namespace DGPS.Models

open DGPS.Examples.EngineeredRankOne DGPS.PositiveRankOne

/-- The engineered rank-one model as an EX006 `RankOneModel`: `q = q_h ∘ angEquiv`,
`φ = E_h ∘ angEquiv`, `η = 1`. -/
noncomputable def engineeredModel (h : ℝ) (hh : 2 ≤ h) : RankOneModel where
  q := fun x => qAng h (angEquiv x)
  φ := fun x => Eang h (angEquiv x)
  η := 1
  q_smooth := (isSmoothPeriodic_comp_iff (qAng h)).2 (isSmoothAngular_qAng h (by linarith))
  q_pos := fun x => qAng_pos h (by linarith) _
  q_mass := by
    rw [integral_comp_angEquiv (qAng h)]
    exact integral_qAng h (by linarith)
  φ_smooth := (isSmoothPeriodic_comp_iff (Eang h)).2 (isSmoothAngular_Eang h)
  φ_centered := by
    have := integral_comp_angEquiv (fun θ => Eang h θ * qAng h θ)
    rw [this]
    have h0 := integral_qAng_mul_Eang h (by linarith)
    rw [← h0]
    exact integral_congr_ae (Eventually.of_forall fun θ => mul_comm _ _)
  η_nonneg := zero_le_one

end DGPS.Models

namespace DGPS.Examples.EngineeredRankOne

open DGPS.Models DGPS.PositiveRankOne

theorem engineeredModel_ref_measure (h : ℝ) (hh : 2 ≤ h) :
    (engineeredModel h hh).ref.measure = engineeredReference h := by
  have hp : 0 < h := by linarith
  unfold engineeredReference
  have hm : MeasurableEmbedding (angEquiv.symm : AngCircle → Torus 1) := angEquiv.symm.measurableEmbedding
  ext s hs
  rw [Measure.map_apply angEquiv.symm.measurable hs]
  unfold BoundedPositiveReference.measure
  rw [withDensity_apply _ hs, withDensity_apply _ (angEquiv.symm.measurable hs)]
  have := (measurePreserving_angEquiv.setLIntegral_comp_preimage_emb angEquiv.measurableEmbedding
    (fun θ => ENNReal.ofReal (qAng h θ)) (angEquiv.symm ⁻¹' s))
  have hs' : angEquiv ⁻¹' (angEquiv.symm ⁻¹' s) = s := by
    ext x; simp
  rw [hs'] at this
  exact this

end DGPS.Examples.EngineeredRankOne

namespace DGPS.Examples.EngineeredRankOne

open DGPS.Models DGPS.PositiveRankOne

theorem engineeredModel_dφ (h : ℝ) (hh : 2 ≤ h) (x : Torus 1) :
    (engineeredModel h hh).dφ x = 2 * π * dEang h (angEquiv x) :=
  coordPartial_of (ψ := Eang h) (isSmoothAngular_Eang h) (hasDerivAt_Eang' h) x

theorem engineeredModel_dlogq (h : ℝ) (hh : 2 ≤ h) (x : Torus 1) :
    (engineeredModel h hh).dlogq x = 2 * π * dlogqAng h (angEquiv x) :=
  coordPartial_of (ψ := fun θ => Real.log (qAng h θ)) (isSmoothAngular_log_qAng h (by linarith))
    (hasDerivAt_log_qAng h (by linarith)) x

theorem engineeredModel_Aq (h : ℝ) (hh : 2 ≤ h) (x : Torus 1) :
    (engineeredModel h hh).Aq x = a0 * lamH h * Eang h (angEquiv x) := by
  have hp : 0 < h := by linarith
  have h1 : coordPartial 0 (engineeredModel h hh).φ = (fun θ => 2 * π * dEang h θ) ∘ angEquiv :=
    funext (engineeredModel_dφ h hh)
  have h2 : coordPartial 0 (coordPartial 0 (engineeredModel h hh).φ) x =
      2 * π * (2 * π * ddEang h (angEquiv x)) := by
    rw [h1]
    exact coordPartial_of (G := fun θ => 2 * π * ddEang h θ)
      (isSmoothAngular_two_pi_dEang h) (hasDerivAt_two_pi_dEang h) x
  unfold RankOneModel.Aq
  rw [h2, engineeredModel_dlogq h hh, engineeredModel_dφ h hh]
  have := eigen_ang h hp (angEquiv x)
  unfold a0
  linear_combination (2 * π) ^ 2 * this

theorem engineeredModel_dφ_sq (h : ℝ) (hh : 2 ≤ h) (x : Torus 1) :
    (engineeredModel h hh).dφ x ^ 2 = a0 * dEang h (angEquiv x) ^ 2 := by
  rw [engineeredModel_dφ]; unfold a0; ring

end DGPS.Examples.EngineeredRankOne

namespace DGPS.Examples

open DGPS.Examples.EngineeredRankOne DGPS.Models DGPS.PositiveRankOne

/-- EX033: engineered exact scalar gap and dissipation. -/
theorem engineered_exact_scalar_gap_and_dissipation (h : ℝ) (hh : 2 ≤ h)
    (b : AbsoluteDrift (engineeredModel h hh).data) (ρ : AbsoluteDensity 1) :
    ((∀ x : Torus 1, (engineeredModel h hh).data.V x =
        (engineeredRankOne h hh).V x + Real.log (Zh h)) ∧
      (∀ x y : Torus 1, (engineeredModel h hh).data.W x y = (engineeredRankOne h hh).W x y)) ∧
    (engineeredModel h hh).ref.measure = engineeredReference h ∧
    (∀ t : ℝ, dEang h (t : AngCircle) = deriv (fun s : ℝ => Eang h (s : AngCircle)) t) ∧
    relativeEntropy (densityMeasure ρ : Measure (Torus 1)) (engineeredReference h) ≠ ⊤ ∧
    (speciesGap (engineeredModel h hh).data (SpeciesFamily.single ρ) : ℝ) =
      (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) (engineeredReference h)).toReal +
        (∫ x, Eang h (angEquiv x) ∂(densityMeasure ρ : Measure (Torus 1))) ^ 2 / 2 ∧
    ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) (engineeredModel h hh).ref ≠ ⊤ ∧
    speciesDissipation (engineeredModel h hh).data b (SpeciesFamily.single ρ) ≠ ⊤ ∧
    (speciesDissipation (engineeredModel h hh).data b (SpeciesFamily.single ρ)).toReal / a0 =
      (ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1))
          (engineeredModel h hh).ref).toReal / a0 +
        2 * lamH h * (∫ x, Eang h (angEquiv x) ∂(densityMeasure ρ : Measure (Torus 1))) ^ 2 +
        (∫ x, Eang h (angEquiv x) ∂(densityMeasure ρ : Measure (Torus 1))) ^ 2 *
          ∫ x, dEang h (angEquiv x) ^ 2 ∂(densityMeasure ρ : Measure (Torus 1)) := by
  have hp : 0 < h := by linarith
  obtain ⟨hG, hI, hD, hDe⟩ := positive_rank_one_scalar_case (engineeredModel h hh) b ρ
  have hq : ∀ x, (engineeredModel h hh).data.V x = (engineeredRankOne h hh).V x + Real.log (Zh h) := by
    intro x
    show (engineeredModel h hh).V x = _
    unfold RankOneModel.V
    show -Real.log (qAng h (angEquiv x)) + 1 / 2 * Eang h (angEquiv x) ^ 2 =
      Vang h (angEquiv x) + Real.log (Zh h)
    rw [log_qAng h hp]
    unfold Vang logq
    ring
  have hW : ∀ x y : Torus 1, (engineeredModel h hh).data.W x y = (engineeredRankOne h hh).W x y := by
    intro x y
    show (engineeredModel h hh).W x y = Wang h (angEquiv x) (angEquiv y)
    unfold RankOneModel.W Wang
    show 1 * (Eang h (angEquiv x) * Eang h (angEquiv y) - Eang h (angEquiv x) ^ 2 / 2 -
      Eang h (angEquiv y) ^ 2 / 2) = _
    ring
  have hHfin : relativeEntropy (densityMeasure ρ : Measure (Torus 1))
      (engineeredModel h hh).ref.measure ≠ ⊤ :=
    ((engineeredModel h hh).free_energy_identity (densityMeasure ρ)
      (absoluteDensity_entropy_finite ρ).2.2.1).1
  have hrefm : (engineeredModel h hh).ref.measure = engineeredReference h :=
    engineeredModel_ref_measure h hh
  have ha0 : 0 < a0 := a0_pos
  have hAint : ∫ x, (engineeredModel h hh).Aq x ∂(densityMeasure ρ : Measure (Torus 1)) =
      a0 * lamH h * ∫ x, Eang h (angEquiv x) ∂(densityMeasure ρ : Measure (Torus 1)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => engineeredModel_Aq h hh x)
  have hJint : ∫ x, (engineeredModel h hh).dφ x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1)) =
      a0 * ∫ x, dEang h (angEquiv x) ^ 2 ∂(densityMeasure ρ : Measure (Torus 1)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => engineeredModel_dφ_sq h hh x)
  have hη : (engineeredModel h hh).η = 1 := rfl
  have hm : ∫ x, (engineeredModel h hh).φ x ∂(densityMeasure ρ : Measure (Torus 1)) =
      ∫ x, Eang h (angEquiv x) ∂(densityMeasure ρ : Measure (Torus 1)) := rfl
  rw [hη, hm, hrefm] at hG
  rw [hη, hm, hAint, hJint] at hDe
  refine ⟨⟨hq, hW⟩, hrefm, ?_, hrefm ▸ hHfin, ?_, hI, hD, ?_⟩
  · intro t; rw [dEang_coe]; exact ((hasDerivAt_Eang h t).deriv).symm
  · rw [hG]; ring
  · rw [hDe]
    field_simp

end DGPS.Examples
