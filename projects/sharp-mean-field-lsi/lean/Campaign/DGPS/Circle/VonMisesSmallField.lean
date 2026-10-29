import DGPS.Examples.ThreeSpeciesCircle.OrdinaryOptimizers
import DGPS.Circle.VonMisesParity
import DGPS.Variational.PositiveRankOne

/-!
# EX010: the one-site von Mises ground functional

The square-root domain is `AbsoluteDensity 1`, including its zero sets. All information
quantities in the ground functional use angular normalization, obtained by division by
`a₀ = 4π²`. Compactness is the previously proved uniform circle compactness theorem;
the quantitative Haar remainder gives coercivity without an additional domain assumption.
-/

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace DGPS.Circle.VonMisesSmallField

open DGPS.Examples.ThreeSpeciesCircle DGPS.Circle.AngularNormalization
open DGPS.Circle.BesselMoments DGPS.Circle.VonMisesParity

/-- Angular Haar Fisher information, for the complete absolute square-root domain. -/
noncomputable def ex010_haarFisher (ρ : AbsoluteDensity 1) : ℝ :=
  DGPS.Analysis.circleFisherInformation ρ / DGPS.Circle.AngularNormalization.a0

/-- The bounded angular potential moment. -/
noncomputable def ex010_potential (ρ : AbsoluteDensity 1) : ℝ :=
  ∫ x, ρ.density x * sinHarm 1 x ^ 2 ∂haar 1

/-- `I_m - 2 H_m + h² ρ(sin² θ)`, with angular information. -/
noncomputable def ex010_ground (h : ℝ) (ρ : AbsoluteDensity 1) : ℝ :=
  ex010_haarFisher ρ - 2 * DGPS.Analysis.circleEntropy ρ + h ^ 2 * ex010_potential ρ

theorem ex010_potential_nonneg (ρ : AbsoluteDensity 1) : 0 ≤ ex010_potential ρ :=
  integral_nonneg fun x => mul_nonneg (ρ.density_nonneg x) (sq_nonneg _)

theorem ex010_sin_bound (x : Torus 1) : |sinHarm 1 x| ≤ 1 := by
  unfold sinHarm
  exact (Complex.abs_im_le_norm _).trans (by simp)

theorem ex010_remainder (ρ : AbsoluteDensity 1) :
    DGPS.Analysis.circleEntropy ρ ^ 2 / 6 ≤
      ex010_haarFisher ρ - 2 * DGPS.Analysis.circleEntropy ρ := by
  have hr := (DGPS.Analysis.circle_quantitative_lsi_on_the_absolute_domain ρ).2.2.1
  have hp := DGPS.Circle.AngularNormalization.a0_pos
  unfold ex010_haarFisher
  rw [le_sub_iff_add_le, le_div_iff₀ hp]
  dsimp [DGPS.Circle.AngularNormalization.a0] at *
  nlinarith

theorem ex010_ground_nonneg (h : ℝ) (ρ : AbsoluteDensity 1) : 0 ≤ ex010_ground h ρ := by
  have := ex010_remainder ρ
  have := mul_nonneg (sq_nonneg h) (ex010_potential_nonneg ρ)
  unfold ex010_ground
  nlinarith [sq_nonneg (DGPS.Analysis.circleEntropy ρ)]

/-- An energy sublevel bounds the full Haar information, uniformly over all competitors. -/
theorem ex010_coercivity (h : ℝ) (ρ : AbsoluteDensity 1) {M : ℝ}
    (hM : ex010_ground h ρ ≤ M) :
    DGPS.Analysis.circleFisherInformation ρ ≤
      DGPS.Circle.AngularNormalization.a0 * (M + 2 * Real.sqrt (6 * M)) := by
  have hr := ex010_remainder ρ
  have hP := mul_nonneg (sq_nonneg h) (ex010_potential_nonneg ρ)
  have hs : DGPS.Analysis.circleEntropy ρ ^ 2 ≤ 6 * M := by
    unfold ex010_ground at hM
    nlinarith
  have hHb : DGPS.Analysis.circleEntropy ρ ≤ Real.sqrt (6 * M) := Real.le_sqrt_of_sq_le hs
  have hI : ex010_haarFisher ρ ≤ M + 2 * Real.sqrt (6 * M) := by
    unfold ex010_ground at hM
    linarith
  exact (div_le_iff₀ DGPS.Circle.AngularNormalization.a0_pos).mp hI |>.trans_eq (mul_comm _ _)

/-- Full-domain uniform compactness preserves the potential, including at zeros of the limit. -/
theorem ex010_potential_tendsto {ρ : ℕ → AbsoluteDensity 1} {ρL : AbsoluteDensity 1} {R : ℝ}
    (hub : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x| ≤ R)
    (hpt : ∀ᵐ x ∂haar 1, Tendsto (fun n => (ρ n).sqrt x) atTop (𝓝 (ρL.sqrt x))) :
    Tendsto (fun n => ex010_potential (ρ n)) atTop (𝓝 (ex010_potential ρL)) := by
  exact tendsto_integral_comp_mul (T := fun t : ℝ => t ^ 2) (continuous_pow 2)
    ((continuous_sinHarm 1).pow 2) (Cc := 1)
    (fun x => by simpa [abs_pow] using pow_le_one₀ (abs_nonneg _) (ex010_sin_bound x) (n := 2))
    (fun n => (ρ n).memLp_sqrt.aestronglyMeasurable) hub hpt

/-- Genuine existence of an absolute-admissible ground minimizer; no compactness premise. -/
theorem ex010_minimum_exists (h : ℝ) :
    ∃ ρs : AbsoluteDensity 1, ∀ ρ : AbsoluteDensity 1, ex010_ground h ρs ≤ ex010_ground h ρ := by
  let ρ0 : AbsoluteDensity 1 :=
    ⟨fun _ => 1, ⟨fun _ => 0, isWeakGradient_const 1⟩, ae_of_all _ (fun _ => zero_le_one), by simp⟩
  let S : Set ℝ := Set.range (ex010_ground h)
  have hSne : S.Nonempty := ⟨ex010_ground h ρ0, ⟨ρ0, rfl⟩⟩
  have hSb : BddBelow S := ⟨0, by rintro _ ⟨ρ, rfl⟩; exact ex010_ground_nonneg h ρ⟩
  obtain ⟨e, heanti, het, hem⟩ := exists_seq_tendsto_sInf hSne hSb
  choose ρ hρ using hem
  have hE : ∀ n, ex010_ground h (ρ n) = e n := hρ
  have hB : ∀ n, DGPS.Analysis.circleFisherInformation (ρ n) ≤
      DGPS.Circle.AngularNormalization.a0 * (e 0 + 2 * Real.sqrt (6 * e 0)) := by
    intro n
    exact ex010_coercivity h (ρ n) (by rw [hE]; exact heanti (Nat.zero_le n))
  obtain ⟨φ, ρL, ε, R, hφ, hε, hae, hub, -, hlsc⟩ := exists_limit_of_bounded_fisher ρ hB
  have hpt : ∀ᵐ x ∂haar 1, Tendsto (fun n => (ρ (φ n)).sqrt x) atTop (𝓝 (ρL.sqrt x)) := by
    filter_upwards [ae_all_iff.mpr hae] with x hx
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by simpa [Real.norm_eq_abs] using hx n) hε
  have hH := tendsto_circleEntropy hub hpt
  have hP := ex010_potential_tendsto hub hpt
  have hEt := het.comp hφ.tendsto_atTop
  have hupper : Tendsto (fun n => DGPS.Circle.AngularNormalization.a0 *
      (e (φ n) + 2 * DGPS.Analysis.circleEntropy (ρ (φ n)) - h ^ 2 * ex010_potential (ρ (φ n))))
      atTop (𝓝 (DGPS.Circle.AngularNormalization.a0 *
      (sInf S + 2 * DGPS.Analysis.circleEntropy ρL - h ^ 2 * ex010_potential ρL))) :=
    (hEt.add (hH.const_mul 2) |>.sub (hP.const_mul (h ^ 2))).const_mul _
  have hId : ∀ n, DGPS.Analysis.circleFisherInformation (ρ (φ n)) =
      DGPS.Circle.AngularNormalization.a0 *
      (e (φ n) + 2 * DGPS.Analysis.circleEntropy (ρ (φ n)) - h ^ 2 * ex010_potential (ρ (φ n))) := by
    intro n
    rw [← hE]
    unfold ex010_ground ex010_haarFisher
    field_simp [DGPS.Circle.AngularNormalization.a0_pos.ne']
    ring
  have hIt : Tendsto (fun n => DGPS.Analysis.circleFisherInformation (ρ (φ n))) atTop
      (𝓝 (DGPS.Circle.AngularNormalization.a0 *
      (sInf S + 2 * DGPS.Analysis.circleEntropy ρL - h ^ 2 * ex010_potential ρL))) :=
    hupper.congr fun n => (hId n).symm
  have hnn : 0 ≤ DGPS.Circle.AngularNormalization.a0 *
      (sInf S + 2 * DGPS.Analysis.circleEntropy ρL - h ^ 2 * ex010_potential ρL) :=
    ge_of_tendsto' hIt fun n => circleFisherInformation_nonneg _
  have hlim := ENNReal.tendsto_ofReal hIt
  rw [hlim.liminf_eq] at hlsc
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlsc
  rw [ENNReal.toReal_ofReal (circleFisherInformation_nonneg ρL), ENNReal.toReal_ofReal hnn] at hreal
  refine ⟨ρL, fun ρ' => ?_⟩
  have hbound : ex010_haarFisher ρL ≤
      sInf S + 2 * DGPS.Analysis.circleEntropy ρL - h ^ 2 * ex010_potential ρL :=
    (div_le_iff₀ DGPS.Circle.AngularNormalization.a0_pos).mpr (hreal.trans_eq (mul_comm _ _))
  have hinf : sInf S ≤ ex010_ground h ρ' := csInf_le hSb ⟨ρ', rfl⟩
  unfold ex010_ground at hinf ⊢
  linarith

end DGPS.Circle.VonMisesSmallField

namespace DGPS.Circle.VonMisesSmallField

open DGPS.Examples.ThreeSpeciesCircle DGPS.Circle.AngularNormalization
open DGPS.Circle.BesselMoments DGPS.Circle.VonMisesParity
open DGPS.PositiveRankOne DGPS.PositiveRankOne.RankOneModel

theorem ex010_smooth_cos : IsSmoothPeriodic (cosHarm 1) := by
  unfold IsSmoothPeriodic
  have e : (cosHarm 1 ∘ torusLift) = fun y : Fin 1 → ℝ => Real.cos (2 * Real.pi * y 0) := by
    funext y
    simp only [Function.comp_apply, cosHarm_lift, Nat.cast_one, mul_one]
  rw [e]; fun_prop

theorem ex010_smooth_sin : IsSmoothPeriodic (sinHarm 1) := by
  unfold IsSmoothPeriodic
  have e : (sinHarm 1 ∘ torusLift) = fun y : Fin 1 → ℝ => Real.sin (2 * Real.pi * y 0) := by
    funext y
    simp only [Function.comp_apply, sinHarm_lift, Nat.cast_one, mul_one]
  rw [e]; fun_prop

theorem ex010_exists_pt (x : Torus 1) : ∃ t : ℝ, pt t = x := by
  refine ⟨SharpLSI.secT x 0, ?_⟩
  have e : (fun _ : Fin 1 => SharpLSI.secT x 0) = SharpLSI.secT x := by
    funext i; fin_cases i; rfl
  show SharpLSI.liftT (fun _ : Fin 1 => SharpLSI.secT x 0) = x
  rw [e]; exact SharpLSI.liftT_secT x

theorem ex010_coord_cos (x : Torus 1) :
    coordPartial 0 (cosHarm 1) x = -(2 * Real.pi) * sinHarm 1 x := by
  obtain ⟨t, rfl⟩ := ex010_exists_pt x
  have hd := hasDerivAt_smooth_one ex010_smooth_cos t
  have he : (fun s : ℝ => cosHarm 1 (pt s)) = fun s => Real.cos (2 * Real.pi * s) := by
    funext s; simp [cosHarm_pt]
  rw [he] at hd
  have ht := ((hasDerivAt_id t).const_mul (2 * Real.pi)).cos
  have hh := hd.unique ht
  simpa [sinHarm_pt, mul_comm] using hh

theorem ex010_coord_sin (x : Torus 1) :
    coordPartial 0 (sinHarm 1) x = 2 * Real.pi * cosHarm 1 x := by
  obtain ⟨t, rfl⟩ := ex010_exists_pt x
  have hd := hasDerivAt_smooth_one ex010_smooth_sin t
  have he : (fun s : ℝ => sinHarm 1 (pt s)) = fun s => Real.sin (2 * Real.pi * s) := by
    funext s; simp [sinHarm_pt]
  rw [he] at hd
  have ht := ((hasDerivAt_id t).const_mul (2 * Real.pi)).sin
  have hh := hd.unique ht
  simpa [cosHarm_pt, mul_comm] using hh

theorem ex010_angCos (x : Torus 1) : angCos (angEquiv x) = cosHarm 1 x := by
  obtain ⟨t, rfl⟩ := ex010_exists_pt x
  rw [angEquiv_apply]
  change angMode 1 (angRescale ((t : ℝ) : UnitAddCircle)) = cosHarm 1 (pt t)
  rw [angRescale_mk, angMode_coe, cosHarm_pt]
  simp

theorem ex010_weight_eq (h : ℝ) (x : Torus 1) :
    vmWeight h x = Real.exp (h * cosHarm 1 x) / DGPS.Circle.BesselMoments.besselI 0 h := by
  simp only [vmWeight, besselDensity, ex010_angCos]

theorem ex010_smooth_weight (h : ℝ) : IsSmoothPeriodic (vmWeight h) := by
  have he : vmWeight h = fun x => Real.exp (h * cosHarm 1 x) /
      DGPS.Circle.BesselMoments.besselI 0 h := funext (ex010_weight_eq h)
  rw [he]
  unfold IsSmoothPeriodic
  exact (Real.contDiff_exp.comp (contDiff_const.mul ex010_smooth_cos)).div_const _

/-- A reference with the exact density `exp(h cos θ) / I₀(h)`; zero auxiliary feature. -/
noncomputable def ex010_model (h : ℝ) : RankOneModel where
  q := vmWeight h
  φ := fun _ => 0
  η := 0
  q_smooth := ex010_smooth_weight h
  q_pos x := div_pos (Real.exp_pos _) (DGPS.Circle.BesselMoments.besselI_zero_pos h)
  q_mass := integral_vmWeight h
  φ_smooth := contDiff_const
  φ_centered := by simp
  η_nonneg := le_rfl

theorem ex010_log_weight (h : ℝ) (x : Torus 1) :
    Real.log ((ex010_model h).q x) =
      h * cosHarm 1 x - Real.log (DGPS.Circle.BesselMoments.besselI 0 h) := by
  change Real.log (vmWeight h x) = _
  rw [ex010_weight_eq, Real.log_div (Real.exp_pos _).ne'
    (DGPS.Circle.BesselMoments.besselI_zero_pos h).ne', Real.log_exp]

theorem ex010_log_score (h : ℝ) (x : Torus 1) :
    (ex010_model h).dlogq x = -(2 * Real.pi * h) * sinHarm 1 x := by
  have he : (fun x => Real.log ((ex010_model h).q x)) = fun x =>
      h * cosHarm 1 x + 0 * (0 : ℝ) - Real.log (DGPS.Circle.BesselMoments.besselI 0 h) := by
    funext x; simp [ex010_log_weight]
  unfold dlogq
  rw [he]
  rw [show (fun x : Torus 1 => h * cosHarm 1 x + 0 * (0 : ℝ) -
      Real.log (DGPS.Circle.BesselMoments.besselI 0 h)) = fun x =>
      h * cosHarm 1 x + 0 * (fun _ : Torus 1 => (0 : ℝ)) x +
      (-Real.log (DGPS.Circle.BesselMoments.besselI 0 h)) by rfl,
    coordPartial_lin ex010_smooth_cos (show IsSmoothPeriodic (fun _ : Torus 1 => (0 : ℝ)) from contDiff_const),
    ex010_coord_cos]
  ring

/-- The Haar cosine moment of an arbitrary absolute-admissible density. -/
noncomputable def ex010_cosMoment (ρ : AbsoluteDensity 1) : ℝ :=
  ∫ x, ρ.density x * cosHarm 1 x ∂haar 1

theorem ex010_fisher_integral (h : ℝ) (ρ : AbsoluteDensity 1) :
    (∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 -
      ρ.sqrt x * (ex010_model h).dlogq x) ^ 2 ∂haar 1) =
      DGPS.Analysis.circleFisherInformation ρ -
        2 * DGPS.Circle.AngularNormalization.a0 * h * ex010_cosMoment ρ +
        DGPS.Circle.AngularNormalization.a0 * h ^ 2 * ex010_potential ρ := by
  let g := weakGradient ρ.sqrt ρ.sqrt_mem
  have hg := isWeakGradient_weakGradient ρ.sqrt_mem
  have ig : Integrable (fun x => g x 0 ^ 2) (haar 1) :=
    (memLp_coord hg.memLp_grad 0).integrable_sq
  have ip : Integrable (fun x => ρ.density x * sinHarm 1 x ^ 2) (haar 1) :=
    (integrable_cont_mul ((continuous_sinHarm 1).pow 2) ρ.integrable_density).congr
      (ae_of_all _ fun x => mul_comm _ _)
  have ix : Integrable (fun x => (2 * ρ.sqrt x * g x 0) * sinHarm 1 x) (haar 1) := by
    have hi := ρ.memLp_sqrt.integrable_mul (memLp_mul_cont (continuous_sinHarm 1)
      (memLp_coord hg.memLp_grad 0))
    exact (hi.const_mul 2).congr (ae_of_all _ fun x => by dsimp [g]; ring)
  have hibp := (density_gradient ρ).1.ibp (sinHarm 1) ex010_smooth_sin 0
  have hx : ∫ x, (2 * ρ.sqrt x * g x 0) * sinHarm 1 x ∂haar 1 =
      -(2 * Real.pi * ex010_cosMoment ρ) := by
    simp only [ex010_coord_sin, PiLp.smul_apply, smul_eq_mul] at hibp
    have he : ∫ x, ρ.density x * (2 * Real.pi * cosHarm 1 x) ∂haar 1 =
        2 * Real.pi * ex010_cosMoment ρ := by
      unfold ex010_cosMoment
      rw [← integral_const_mul]; congr 1; funext x; ring
    rw [he] at hibp
    dsimp [g]
    linarith
  have hI : DGPS.Analysis.circleFisherInformation ρ = 4 * ∫ x, g x 0 ^ 2 ∂haar 1 := by
    unfold DGPS.Analysis.circleFisherInformation
    simp_rw [norm_sq_tangent]
    rfl
  have he : (fun x => (2 * g x 0 - ρ.sqrt x * (ex010_model h).dlogq x) ^ 2) = fun x =>
      4 * g x 0 ^ 2 + (4 * Real.pi * h) * ((2 * ρ.sqrt x * g x 0) * sinHarm 1 x) +
      (DGPS.Circle.AngularNormalization.a0 * h ^ 2) * (ρ.density x * sinHarm 1 x ^ 2) := by
    funext x
    rw [ex010_log_score]
    dsimp [DGPS.Circle.AngularNormalization.a0, AbsoluteDensity.density]
    ring
  change (∫ x, (2 * g x 0 - ρ.sqrt x * (ex010_model h).dlogq x) ^ 2 ∂haar 1) = _
  rw [he]
  have hs1 := integral_add ((ig.const_mul 4).add (ix.const_mul (4 * Real.pi * h)))
    (ip.const_mul (DGPS.Circle.AngularNormalization.a0 * h ^ 2))
  have hs2 := integral_add (ig.const_mul 4) (ix.const_mul (4 * Real.pi * h))
  simp only [Pi.add_apply] at hs1 hs2
  rw [hs1, hs2, integral_const_mul, integral_const_mul, integral_const_mul, hx]
  rw [hI]
  dsimp [ex010_potential, DGPS.Circle.AngularNormalization.a0]
  ring

theorem ex010_fisher_identity (h : ℝ) (ρ : AbsoluteDensity 1) :
    ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) (ex010_model h).ref =
      ENNReal.ofReal (DGPS.Analysis.circleFisherInformation ρ -
        2 * DGPS.Circle.AngularNormalization.a0 * h * ex010_cosMoment ρ +
        DGPS.Circle.AngularNormalization.a0 * h ^ 2 * ex010_potential ρ) := by
  rw [(ex010_model h).fisher_eq ρ, ex010_fisher_integral]

/-- Exact entropy conversion for every absolute competitor, including vanishing densities. -/
theorem ex010_entropy_identity (h : ℝ) (ρ : AbsoluteDensity 1) :
    (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) (ex010_model h).ref.measure).toReal =
      DGPS.Analysis.circleEntropy ρ - h * ex010_cosMoment ρ +
        Real.log (DGPS.Circle.BesselMoments.besselI 0 h) := by
  rw [(ex010_model h).entropy_ref_eq (densityMeasure ρ) (absoluteDensity_entropy_finite ρ).2.2.1,
    (absoluteDensity_entropy_finite ρ).2.2.2, ← DGPS.Examples.ThreeSpeciesCircle.circleEntropy_eq ρ,
    integral_densityMeasure]
  have ic := integrable_cont_mul (continuous_cosHarm 1) ρ.integrable_density
  have he : (fun x => ρ.density x * Real.log ((ex010_model h).q x)) =
      fun x => h * (ρ.density x * cosHarm 1 x) -
        Real.log (DGPS.Circle.BesselMoments.besselI 0 h) * ρ.density x := by
    funext x; rw [ex010_log_weight]; ring
  rw [he, integral_sub (by simpa [mul_comm] using ic.const_mul h)
    (ρ.integrable_density.const_mul _), integral_const_mul, integral_const_mul, ρ.integral_density]
  dsimp [ex010_cosMoment]
  ring

/-- Both extended quantities are finite on the complete absolute domain. -/
theorem ex010_relative_finite (h : ℝ) (ρ : AbsoluteDensity 1) :
    ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) (ex010_model h).ref ≠ ⊤ ∧
      relativeEntropy (densityMeasure ρ : Measure (Torus 1)) (ex010_model h).ref.measure ≠ ⊤ := by
  constructor
  · rw [ex010_fisher_identity]; exact ENNReal.ofReal_ne_top
  · exact ((ex010_model h).free_energy_identity (densityMeasure ρ)
      (absoluteDensity_entropy_finite ρ).2.2.1).1

end DGPS.Circle.VonMisesSmallField

namespace DGPS.Examples

open DGPS.Circle.VonMisesSmallField DGPS.Circle.AngularNormalization

/-- EX010, in angular normalization: exact cancellation and a minimizer on the full
absolute square-root Haar Sobolev domain, for every real field (including zero). -/
theorem small_field_one_site_ground_functional (h : ℝ) :
    (∀ ρ : AbsoluteDensity 1,
      (ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) (ex010_model h).ref).toReal /
          DGPS.Circle.AngularNormalization.a0 -
        2 * (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) (ex010_model h).ref.measure).toReal =
      ex010_ground h ρ - 2 * Real.log (DGPS.Circle.BesselMoments.besselI 0 h)) ∧
    (∃ ρs : AbsoluteDensity 1, ∀ ρ : AbsoluteDensity 1, ex010_ground h ρs ≤ ex010_ground h ρ) := by
  refine ⟨fun ρ => ?_, ex010_minimum_exists h⟩
  have hnn : 0 ≤ DGPS.Analysis.circleFisherInformation ρ -
      2 * DGPS.Circle.AngularNormalization.a0 * h * ex010_cosMoment ρ +
      DGPS.Circle.AngularNormalization.a0 * h ^ 2 * ex010_potential ρ := by
    rw [← ex010_fisher_integral]
    exact integral_nonneg fun _ => sq_nonneg _
  rw [ex010_fisher_identity, ENNReal.toReal_ofReal hnn, ex010_entropy_identity]
  unfold ex010_ground ex010_haarFisher
  field_simp [DGPS.Circle.AngularNormalization.a0_pos.ne']
  ring

end DGPS.Examples
