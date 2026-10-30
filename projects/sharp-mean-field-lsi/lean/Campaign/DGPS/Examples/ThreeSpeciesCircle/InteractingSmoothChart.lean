import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarSmooth

/-! Genuine normalized mean-zero C2 Holder charts of positive smooth AE roots.
This constructs the represented density, rather than assuming a chart or its
regularity in the actual minimizer factory. No chart-neighborhood claim is made. -/

noncomputable section
open MeasureTheory Filter Topology Function
open scoped ContDiff
open DGPS.Analysis.PeriodicHolder DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem smooth_periodic_isPH {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f 1) : IsPH (1 / 2) 2 f := by
  have h1 := (contDiff_infty_iff_deriv.mp hf).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  have h3 := (contDiff_infty_iff_deriv.mp h2).2
  have hp1 := DGPS.Analysis.PeriodicHolder.periodic_deriv hp
  have hp2 := DGPS.Analysis.PeriodicHolder.periodic_deriv hp1
  have hp3 := DGPS.Analysis.PeriodicHolder.periodic_deriv hp2
  have hb2 := periodic_bdd hp2 h2.continuous
  have hb3 := periodic_bdd hp3 h3.continuous
  have hhold : HolderBdd (1 / 2) (deriv (deriv f)) := by
    refine ⟨supNorm (deriv (deriv (deriv f))) + 2 * supNorm (deriv (deriv f)),
      add_nonneg (supNorm_nonneg _) (mul_nonneg (by norm_num) (supNorm_nonneg _)), ?_⟩
    exact holder_of_lip (supNorm_nonneg _) (supNorm_nonneg _) (by norm_num) (by norm_num)
      (lip_bound (h2.differentiable (by simp)) hb3) hb2.abs_le_supNorm
  exact ⟨hp, hf.differentiable (by simp), hp1, h1.differentiable (by simp),
    hp2, h2.continuous, hhold⟩

private theorem angular_point (t : ℝ) :
    angEquiv.symm (t : AngCircle) = pt (t / (2 * Real.pi)) := by
  rw [MeasurableEquiv.symm_apply_eq, angEquiv_apply]
  change (t : AngCircle) = angRescale ((t / (2 * Real.pi) : ℝ) : UnitAddCircle)
  rw [angRescale_mk]
  congr 1
  field_simp

/-- Every genuinely smooth positive AE root yields an actual normalized
mean-zero C2 Holder chart on the original absolute-density law. -/
theorem positiveSmoothRoot_exists_meanZero_chart (h : ℝ) (ρ : AbsoluteDensity 1)
    {v : Torus 1 → ℝ} (hv : IsSmoothPeriodic v) (hvpos : ∀ x, 0 < v x)
    (hvrep : ρ.sqrt =ᵐ[haar 1] v) :
    ∃ u : PeriodicC2_STR02969, meanT_STR02901 u.val = 0 ∧
      ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ) := by
  letI : HolderExponent (1 / 2 : ℝ) := holderExponent_half_STR02901
  let F := fun s : ℝ => Real.log (v (pt s) ^ 2) - h * cosHarm 3 (pt s)
  have hcos : ContDiff ℝ ∞ (fun s : ℝ => cosHarm 3 (pt s)) := by
    simp_rw [cosHarm_pt]
    fun_prop
  have hF : ContDiff ℝ ∞ F :=
    ((circ_smooth_pt hv).pow 2 |>.log (fun s => (pow_pos (hvpos (pt s)) 2).ne')).sub
      (contDiff_const.mul hcos)
  have hper : Periodic F 1 := circ_periodic_pt
    (fun x => Real.log (v x ^ 2) - h * cosHarm 3 x)
  let Φ : PH (1 / 2) 2 := PH.mk F (smooth_periodic_isPH hF hper)
  let c := PH.integral 2 Φ
  let Ψ : PH (1 / 2) 2 := Φ - c • 1
  let u := PeriodicC2_STR02969.mk (wT_STR02901 Ψ) (isC2Alpha_wT_STR02901 Ψ)
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  have hu (t : ℝ) : u.val t = Real.log (v (pt (t / (2 * Real.pi))) ^ 2) -
      h * Real.cos (3 * t) - c := by
    dsimp only [u, PeriodicC2_STR02969.val, PeriodicC2_STR02969.mk, wT_STR02901,
      Ψ, PH.val_sub, PH.val_smul, PH.val_one, Φ, PH.val_mk, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.one_apply, F]
    rw [cosHarm_pt]
    have he : 2 * Real.pi * ((3 : ℕ) : ℝ) * (t / (2 * Real.pi)) = 3 * t := by
      field_simp
      <;> ring
    rw [he]
    ring
  have hunit (s : ℝ) : u.val (2 * Real.pi * s) = F s - c := by
    dsimp only [u, PeriodicC2_STR02969.val, PeriodicC2_STR02969.mk, wT_STR02901]
    have he : (2 * Real.pi * s) / (2 * Real.pi) = s := by field_simp
    rw [he]
    simp [Ψ, Φ, PH.val_sub, PH.val_smul, PH.val_one, PH.val_mk]
  have hmean : meanT_STR02901 u.val = 0 := by
    rw [← meanT_eq_unit_STR02901]
    simp_rw [hunit]
    rw [intervalIntegral.integral_sub (hF.continuous.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const]
    change c - (1 - 0) • c = 0
    simp
  have hmass : (∫ x, v x ^ 2 ∂haar 1) = 1 := by
    calc
      _ = ∫ x, ρ.sqrt x ^ 2 ∂haar 1 := integral_congr_ae
        (hvrep.mono fun x hx => by change v x ^ 2 = ρ.sqrt x ^ 2; rw [hx])
      _ = 1 := ρ.mass_one
  have hmassUnit : (∫ s in (0 : ℝ)..1, v (pt s) ^ 2) = 1 :=
    (integral_haar_one _ (hv.continuous_torus.pow 2)).symm.trans hmass
  have hexp (t : ℝ) : Real.exp (h * Real.cos (3 * t) + u.val t) =
      Real.exp (-c) * v (pt (t / (2 * Real.pi))) ^ 2 := by
    rw [hu]
    have he : h * Real.cos (3 * t) +
        (Real.log (v (pt (t / (2 * Real.pi))) ^ 2) - h * Real.cos (3 * t) - c) =
          -c + Real.log (v (pt (t / (2 * Real.pi))) ^ 2) := by ring
    rw [he, Real.exp_add, Real.exp_log (pow_pos (hvpos _) 2)]
  have hZ : meanT_STR02901 (fun t => Real.exp (h * Real.cos (3 * t) + u.val t)) =
      Real.exp (-c) := by
    rw [← meanT_eq_unit_STR02901]
    simp_rw [hexp]
    have he : (fun s : ℝ => v (pt ((2 * Real.pi * s) / (2 * Real.pi))) ^ 2) =
        fun s => v (pt s) ^ 2 := by
      funext s
      congr 2
      field_simp
    rw [intervalIntegral.integral_const_mul, he, hmassUnit, mul_one]
  have hrho (t : ℝ) : rhoT_STR02901 h u.val t = v (pt (t / (2 * Real.pi))) ^ 2 := by
    unfold rhoT_STR02901
    rw [hZ, hexp]
    field_simp [(Real.exp_pos (-c)).ne']
  refine ⟨u, hmean, ?_⟩
  apply (ae_comp_angEquiv_iff (p := fun θ =>
    ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ))).1
  filter_upwards [hvrep] with x hx
  change ρ.density (angEquiv.symm (angEquiv x)) =
    rhoT_STR02901 h u.val (angSec (angEquiv x))
  rw [MeasurableEquiv.symm_apply_apply, hrho]
  have he : pt (angSec (angEquiv x) / (2 * Real.pi)) = x := by
    rw [← angular_point, coe_angSec_STR02962, MeasurableEquiv.symm_apply_apply]
  rw [he]
  change ρ.sqrt x ^ 2 = v x ^ 2
  rw [hx]

/-- Every actual original-H1 minimizer admits a genuine normalized mean-zero
C2 Holder chart. No chart or regularity assumption is supplied. -/
theorem elementaryModel_scalarMinimizer_exists_meanZero_chart (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ →
            scalarQuotient (modelData h ε) b ρ = scalarRate (modelData h ε) b →
            ∃ u : PeriodicC2_STR02969, meanT_STR02901 u.val = 0 ∧
              ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ) := by
  obtain ⟨δ, hδ, hδr, hsmooth⟩ := elementaryModel_scalarMinimizer_smooth_representative D
  refine ⟨δ, hδ, hδr, fun h hh hsmall => ?_⟩
  obtain ⟨ε0, m, hε0, hεmax, hm, hminimizer⟩ := hsmooth h hh hsmall
  refine ⟨ε0, hε0, hεmax, fun ε hε he b ρ hG hmin => ?_⟩
  obtain ⟨v, hv, hvrep, hvmin, _⟩ := hminimizer ε hε he b ρ hG hmin
  exact positiveSmoothRoot_exists_meanZero_chart h ρ hv (fun x => hm.trans_le (hvmin x)) hvrep

end DGPS.Examples.ThreeSpeciesCircle
