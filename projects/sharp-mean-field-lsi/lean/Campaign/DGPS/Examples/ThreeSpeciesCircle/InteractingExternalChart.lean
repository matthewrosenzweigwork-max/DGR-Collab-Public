import DGPS.Examples.ThreeSpeciesCircle.InteractingChartNative

/-! Independent common feedback field V and scalar value c on the actual
periodic chart. These are parameters, not self-density feedback or optimizer
hypotheses. Physical rate r=a0*(1+gamma); all functionals are divided by a0. -/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The exact normalized angular expectation of an independent common field. -/
def externalChartMean (h : ℝ) (u : PeriodicC2_STR02969) (V : PeriodicHolder_STR02968) : ℝ :=
  meanCLM_STR02954 (rho_STR02954 (h, e0_STR02955 u) * V)

/-- Normalized one-body functional I-2rH+E[V]-c in the retained chart. -/
def externalChartDeficit (h : ℝ)
    (x : (PeriodicHolder_STR02968 × ℝ) × (ℝ × PeriodicC2_STR02969)) : ℝ :=
  JC2_STR02956 h x.2.1 x.2.2 + (externalChartMean h x.2.2 x.1.1 - x.1.2) / a0

/-- The normalized density-centered external-field gradient. Constant changes in
V disappear from the density equation, while c enters the scalar value equation. -/
def externalChartGradient (h : ℝ)
    (x : PeriodicHolder_STR02968 × (ℝ × PeriodicC2_STR02969)) : PeriodicHolder_STR02968 :=
  Gfun_STR02955 h x.2.1 x.2.2 + a0⁻¹ •
    (rho_STR02954 (h, e0_STR02955 x.2.2) *
      (x.1 - externalChartMean h x.2.2 x.1 • (1 : PeriodicHolder_STR02968)))

theorem externalChartGradient_smooth (h : ℝ) : ContDiff ℝ ∞ (externalChartGradient h) := by
  have hu : ContDiff ℝ ∞ (fun x : PeriodicHolder_STR02968 × (ℝ × PeriodicC2_STR02969) => x.2.2) :=
    contDiff_snd.comp contDiff_snd
  have hγ : ContDiff ℝ ∞ (fun x : PeriodicHolder_STR02968 × (ℝ × PeriodicC2_STR02969) => x.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hV : ContDiff ℝ ∞ (fun x : PeriodicHolder_STR02968 × (ℝ × PeriodicC2_STR02969) => x.1) :=
    contDiff_fst
  have hr := rho_smooth_STR02954.comp
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : PeriodicHolder_STR02968 × (ℝ × PeriodicC2_STR02969) => h)).prodMk
      (e0_STR02955.contDiff.comp hu))
  have hm := meanCLM_STR02954.contDiff.comp (hr.mul hV)
  unfold externalChartGradient externalChartMean
  exact (Gmap_smooth_STR02955.comp (contDiff_const.prodMk (hγ.prodMk hu))).add
    ((contDiff_const (c := (a0⁻¹ : ℝ))).smul (hr.mul (hV.sub (hm.smul (contDiff_const (c := (1 : PeriodicHolder_STR02968)))))))

theorem externalChartDeficit_smooth (h : ℝ) : ContDiff ℝ ∞ (externalChartDeficit h) := by
  have hu : ContDiff ℝ ∞ (fun x : (PeriodicHolder_STR02968 × ℝ) × (ℝ × PeriodicC2_STR02969) => x.2.2) :=
    contDiff_snd.comp contDiff_snd
  have hγ : ContDiff ℝ ∞ (fun x : (PeriodicHolder_STR02968 × ℝ) × (ℝ × PeriodicC2_STR02969) => x.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hV : ContDiff ℝ ∞ (fun x : (PeriodicHolder_STR02968 × ℝ) × (ℝ × PeriodicC2_STR02969) => x.1.1) :=
    contDiff_fst.comp contDiff_fst
  have hc : ContDiff ℝ ∞ (fun x : (PeriodicHolder_STR02968 × ℝ) × (ℝ × PeriodicC2_STR02969) => x.1.2) :=
    contDiff_snd.comp contDiff_fst
  have h0 := e0_STR02955.contDiff.comp hu
  have h1 := e1_STR02955.contDiff.comp hu
  have hr := rho_smooth_STR02954.comp
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : (PeriodicHolder_STR02968 × ℝ) × (ℝ × PeriodicC2_STR02969) => h)).prodMk h0)
  have hZ := logZ_smooth_STR02954.comp
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : (PeriodicHolder_STR02968 × ℝ) × (ℝ × PeriodicC2_STR02969) => h)).prodMk h0)
  have hI := meanCLM_STR02954.contDiff.comp ((h1.mul h1).mul hr)
  have hE := meanCLM_STR02954.contDiff.comp (h0.mul hr)
  have hJ := hI.sub (((contDiff_const (c := (2 : ℝ))).mul ((contDiff_const (c := (1 : ℝ))).add hγ)).mul
    ((hE.sub hZ).add (contDiff_const (c := Real.log (meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s))))))))
  unfold externalChartDeficit JC2_STR02956 externalChartMean
  exact hJ.add (((meanCLM_STR02954.contDiff.comp (hr.mul hV)).sub hc).div_const a0)

theorem externalChartGradient_zero (h γ : ℝ) (u : PeriodicC2_STR02969) :
    externalChartGradient h (0, γ, u) = Gfun_STR02955 h γ u := by
  simp [externalChartGradient, externalChartMean]

theorem externalChartDeficit_zero (h γ : ℝ) (u : PeriodicC2_STR02969) :
    externalChartDeficit h ((0, 0), γ, u) = JC2_STR02956 h γ u := by
  simp [externalChartDeficit, externalChartMean]

/-- Exact binding to the physical normalized one-body functional. The original
absolute H1 record needs only an AE chart; V is an independent actual field. -/
theorem externalChartDeficit_native (h γ c : ℝ) (u : PeriodicC2_STR02969)
    (V : PeriodicHolder_STR02968) (ρ : AbsoluteDensity 1)
    (hρ : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ)) :
    a0 * externalChartDeficit h ((V, c), γ, u) =
      (ordinaryFisher h ρ).toReal - 2 * (a0 * (1 + γ)) * (ordinaryEntropy h ρ).toReal +
        (∫ x, V.val (angSec (angEquiv x)) ∂(densityMeasure ρ : Measure (Torus 1))) - c := by
  obtain ⟨hH, hI⟩ := interactingChart_native_ordinary_terms h u ρ hρ
  have hV : externalChartMean h u V =
      ∫ x, V.val (angSec (angEquiv x)) ∂(densityMeasure ρ : Measure (Torus 1)) := by
    rw [interactingChartIntegral_native_ae h u ρ hρ]
    unfold externalChartMean
    rw [meanCLM_apply_STR02954]
    congr 1
    funext t
    rw [val_mul_STR02954, Pi.mul_apply, rho_val_STR02954, angEquiv.apply_symm_apply]
    have he : V.val (angSec (t : AngCircle)) = V.val t :=
      eq_of_circDist_eq_zero_STR02968 V.isPerHolder.1 (by
        unfold circDist_STR02968
        rw [coe_angSec_STR02962]
        exact dist_self _)
    rw [he]
    rfl
  unfold externalChartDeficit
  rw [JC2_eq_STR02956, hH, hI, hV]
  unfold Jchart_STR02950
  have ha : a0 ≠ 0 := by unfold a0; positivity
  field_simp [ha]
  ring

end DGPS.Examples.ThreeSpeciesCircle
