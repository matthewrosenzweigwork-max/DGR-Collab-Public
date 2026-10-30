import DGPS.Examples.ThreeSpeciesCircle.InteractingChartNative
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarCompactness
import DGPS.Examples.ThreeSpeciesCircle.InteractingReferenceBarrier

/-! Genuine probability facts needed before promoting local stationary curves
to actual global scalar optimizers: original-law invariance, canonical positive
continuous roots, chart entropy continuity, and positive candidate gaps. -/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Scalar gap, dissipation and quotient preserve the original probability
law. Dissipation is proved finite BEFORE using its real identity. -/
theorem elementaryModel_scalar_measure_congr (h ε : ℝ) (b : AbsoluteDrift (modelData h ε))
    (ρ σ : AbsoluteDensity 1)
    (hμ : (densityMeasure ρ : Measure (Torus 1))=densityMeasure σ) :
    scalarGap (modelData h ε) ρ=scalarGap (modelData h ε) σ ∧
    scalarDissipation (modelData h ε) b ρ=scalarDissipation (modelData h ε) b σ ∧
    scalarQuotient (modelData h ε) b ρ=scalarQuotient (modelData h ε) b σ := by
  have hprob : densityMeasure ρ=densityMeasure σ := Subtype.ext hμ
  have hdens := (densityMeasure_eq_iff_STR02901 ρ σ).1 hμ
  have hgap : scalarGap (modelData h ε) ρ=scalarGap (modelData h ε) σ := by
    apply NNReal.coe_injective
    change densityFreeEnergy (modelData h ε) ρ-freeEnergyMinimumReal (modelData h ε)=
      densityFreeEnergy (modelData h ε) σ-freeEnergyMinimumReal (modelData h ε)
    unfold densityFreeEnergy
    simp only [hprob]
  have hI : ordinaryFisher h ρ=ordinaryFisher h σ := by unfold ordinaryFisher; rw [hμ]
  have hC : elementaryC h 0 ρ=elementaryC h 0 σ := by
    unfold elementaryC
    rw [hμ]
    congr 1
    apply congrArg (fun x : ℝ => 2 * x)
    apply integral_congr_ae
    exact hdens.mono fun x hx => by dsimp only; rw [hx]
  have hJ : elementaryJ h ρ=elementaryJ h σ := by
    unfold elementaryJ
    rw [hμ]
    apply integral_congr_ae
    exact hdens.mono fun x hx => by dsimp only; rw [hx]
  have hD := elementaryModel_scalarDissipation_real h ε b ρ
  have hD' := elementaryModel_scalarDissipation_real h ε b σ
  have hreal : (scalarDissipation (modelData h ε) b ρ).toReal=
      (scalarDissipation (modelData h ε) b σ).toReal := by rw [hD.2,hD'.2,hI,hC,hJ]
  have hd : scalarDissipation (modelData h ε) b ρ=scalarDissipation (modelData h ε) b σ := by
    rw [←ENNReal.ofReal_toReal hD.1,←ENNReal.ofReal_toReal hD'.1,hreal]
  exact ⟨hgap,hd,by unfold scalarQuotient; rw [hgap,hd]⟩

/-- Canonical chart roots themselves are continuous and strictly positive;
this concerns their actual constructed values, not arbitrary stored roots. -/
theorem interactingChartAbsolute_positive_continuous (h : ℝ) (u : PeriodicC2_STR02969) :
    Continuous (interactingChartAbsolute h u).sqrt ∧ ∀ x, 0<(interactingChartAbsolute h u).sqrt x := by
  let F := fun t => Real.exp ((u.val t-logZ_STR02962 h u.val+logZh_STR02962 h)/2)
  have hu : Continuous u.val := u.isC2.2.1.continuous
  have hF : Continuous F := by dsimp only [F]; fun_prop
  have hp : Function.Periodic F (2*Real.pi) := by
    intro t
    dsimp only [F]
    rw [u.isC2.1 t]
  have hg : Continuous (gLift_STR02962 h u.val) := by
    change Continuous (AddCircle.liftIoc (2*Real.pi) 0 F)
    exact AddCircle.liftIoc_zero_continuous (by simpa using (hp 0).symm) hF.continuousOn
  have ha : Continuous (angEquiv : Torus 1 → AngCircle) := by
    change Continuous (fun x : Torus 1 => angHomeo (x 0))
    exact angHomeo.continuous.comp (continuous_apply 0)
  refine ⟨(hg.comp ha).mul (continuous_referenceDensity h).sqrt,fun x => ?_⟩
  change 0<gLift_STR02962 h u.val (angEquiv x)*Real.sqrt (referenceDensity h x)
  exact mul_pos (Real.exp_pos _) (Real.sqrt_pos.mpr (referenceDensity_pos (h:=h) x))

/-- The exact native chart entropy is continuous in the actual retained full
Holder topology. Two existing smooth functionals eliminate the Fisher term. -/
theorem continuous_interactingChart_entropy (h : ℝ) :
    Continuous (fun u : PeriodicC2_STR02969 => entropyChart_STR02949 h u.val) := by
  have he : (fun u : PeriodicC2_STR02969 => entropyChart_STR02949 h u.val)=
      fun u => (JC2_STR02956 h (-1) u-JC2_STR02956 h 0 u)/2 := by
    funext u
    rw [JC2_eq_STR02956,JC2_eq_STR02956]
    unfold Jchart_STR02950
    ring
  rw [he]
  exact (((JC2_smooth_STR02956 h (-1)).continuous).sub
    (JC2_smooth_STR02956 h 0).continuous).div_const 2

/-- Positive seed entropy and a genuine continuous chart curve imply positive
actual interacting gaps on ONE coupling interval. The interval precedes all
competitors/drifts; no candidate-gap or candidate-minimum premise is assumed. -/
theorem interactingChart_curve_positive_gap {h : ℝ} (hh : 0<h)
    (σ : AbsoluteDensity 1) (hσpos : 0<ordinaryEntropy h σ)
    (u : ℝ → PeriodicC2_STR02969) (hu : ContinuousAt u 0)
    (hseed : ∀ᵐ θ ∂angHaar, σ.density (angEquiv.symm θ)=rhoT_STR02901 h (u 0).val (angSec θ)) :
    ∃ ε0 : ℝ, 0<ε0 ∧ ε0≤epsMax h ∧ ∀ ε : ℝ, 0<ε → ε<ε0 →
      0<scalarGap (modelData h ε) (interactingChartAbsolute h (u ε)) := by
  have hs := (interactingChart_native_ordinary_terms h (u 0) σ hseed).1
  have hp : 0<entropyChart_STR02949 h (u 0).val := by
    rw [←hs]
    exact ENNReal.toReal_pos hσpos.ne' (str025_entropy_ne_top h σ)
  have he : ∀ᶠ ε in 𝓝 (0:ℝ), 0<entropyChart_STR02949 h (u ε).val :=
    ((continuous_interactingChart_entropy h).continuousAt.comp hu).eventually (lt_mem_nhds hp)
  obtain ⟨d,hd,htail⟩ := Metric.eventually_nhds_iff.1 he
  obtain ⟨εG,hεG,hεGmax,hgap⟩ := elementaryModel_speciesGap_entropy_comparable hh
  refine ⟨min d εG,lt_min hd hεG,(min_le_right _ _).trans hεGmax,
    fun ε hε heps => ?_⟩
  have hsmall : dist ε 0<d := by
    rw [Real.dist_eq,sub_zero,abs_of_pos hε]
    exact heps.trans_le (min_le_left _ _)
  have hHpos := htail hsmall
  let ρ := interactingChartAbsolute h (u ε)
  have hH : (ordinaryEntropy h ρ).toReal=entropyChart_STR02949 h (u ε).val :=
    (interactingChart_native_ordinary_terms h (u ε) ρ
      (Eventually.of_forall (interactingChartAbsolute_density h (u ε)))).1
  have hg : (1/2:ℝ)*(ordinaryEntropy h ρ).toReal≤(scalarGap (modelData h ε) ρ:ℝ) := by
    have ht := (hgap ε hε (heps.trans_le (min_le_right _ _)) (SpeciesFamily.single ρ)).1
    simpa only [speciesGap_single,sum_single_count,SpeciesFamily.single_weight,
      SpeciesFamily.single_density,one_mul] using ht
  have hGreal : (0:ℝ)<(scalarGap (modelData h ε) ρ:ℝ) := by rw [hH] at hg; linarith
  exact_mod_cast hGreal

end DGPS.Examples.ThreeSpeciesCircle
