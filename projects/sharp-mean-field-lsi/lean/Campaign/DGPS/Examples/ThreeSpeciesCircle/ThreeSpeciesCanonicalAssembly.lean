import DGPS.Examples.ThreeSpeciesCircle.ElementaryRateChain
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesSmoothClassification
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarClassificationFactory
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarSplitUphill
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryCompensatingSequence
import DGPS.Model.SpeciesFamily
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! Canonical T08 assembly. The species measure below is a measure ON the
native space of probability laws with its weak Borel sigma-algebra; it is not
the per-label physical-measure helper in Particle.ProductRecovery. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

local instance speciesProbabilityMeasurableSpace : MeasurableSpace (ProbabilityMeasure (DGPS.Torus 1)) :=
  borel (ProbabilityMeasure (DGPS.Torus 1))
local instance speciesProbabilityDecidableEq : DecidableEq (ProbabilityMeasure (DGPS.Torus 1)) :=
  Classical.decEq _
local instance speciesProbabilityBorelSpace : BorelSpace (ProbabilityMeasure (DGPS.Torus 1)) := ⟨rfl⟩

namespace DGPS

/-- The actual finite atomic measure on species probability laws. Identical
laws add their original positive weights; no species count bound is imposed. -/
def speciesLaw (F : SpeciesFamily 1) : Measure (ProbabilityMeasure (Torus 1)) :=
  ∑ s, ENNReal.ofReal (F.weight s) • Measure.dirac (densityMeasure (F.density s))

end DGPS

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The canonical equally weighted measure on three actual probability laws. -/
def ternarySpeciesLaw (η : Fin 3 → AbsoluteDensity 1) : Measure (ProbabilityMeasure (Torus 1)) :=
  (1 / 3 : ℝ≥0∞) • ∑ j : Fin 3, Measure.dirac (densityMeasure (η j))

private theorem speciesLaw_singleton (F : SpeciesFamily 1) (ν : ProbabilityMeasure (Torus 1)) :
    speciesLaw F {ν} = ENNReal.ofReal (∑ s, if densityMeasure (F.density s) = ν then F.weight s else 0) := by
  classical
  rw [speciesLaw, Measure.finsetSum_apply]
  rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => by
    split_ifs
    · exact F.weight_nonneg s
    · exact le_rfl)]
  apply Finset.sum_congr rfl
  intro s _
  by_cases he : densityMeasure (F.density s) = ν
  · simp [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton _), he]
  · simp [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton _), he]

private theorem ternarySpeciesLaw_singleton (η : Fin 3 → AbsoluteDensity 1)
    (hη : Function.Injective (fun j => densityMeasure (η j))) (j : Fin 3) :
    ternarySpeciesLaw η {densityMeasure (η j)} = 1 / 3 := by
  classical
  simp [ternarySpeciesLaw, Measure.smul_apply, Measure.finsetSum_apply,
    Measure.dirac_apply' _ (measurableSet_singleton _), Pi.single_apply, hη.eq_iff]

/-- Exact atom equality is equivalent to genuine grouping of ALL original
positive weights and laws. Both directions are proved, not assumed. -/
theorem speciesLaw_eq_ternary_iff (F : SpeciesFamily 1) (η : Fin 3 → AbsoluteDensity 1)
    (hη : Function.Injective (fun j => densityMeasure (η j))) :
    speciesLaw F = ternarySpeciesLaw η ↔
      ∃ label : Fin F.count → Fin 3,
        (∀ j, (∑ s, if label s = j then F.weight s else 0) = 1 / 3) ∧
        ∀ s, densityMeasure (F.density s) = densityMeasure (η (label s)) := by
  classical
  constructor
  · intro he
    have hSupport (s : Fin F.count) : ∃ j : Fin 3, densityMeasure (F.density s) = densityMeasure (η j) := by
      by_contra hn
      have hNone : ∀ j : Fin 3, densityMeasure (η j) ≠ densityMeasure (F.density s) :=
        fun j hj => hn ⟨j, hj.symm⟩
      have hMass := congrArg (fun μ : Measure (ProbabilityMeasure (Torus 1)) => μ {densityMeasure (F.density s)}) he
      have hZero : ternarySpeciesLaw η {densityMeasure (F.density s)} = 0 := by
        simp [ternarySpeciesLaw, Measure.smul_apply, Measure.finsetSum_apply,
          Measure.dirac_apply' _ (measurableSet_singleton _), hNone]
      rw [hZero, speciesLaw_singleton] at hMass
      have hpos : 0 < ∑ t, if densityMeasure (F.density t) = densityMeasure (F.density s) then F.weight t else 0 := by
        apply (F.weight_pos s).trans_le
        have ht := Finset.single_le_sum (f := fun t =>
          if densityMeasure (F.density t) = densityMeasure (F.density s) then F.weight t else 0)
          (fun t _ => by split_ifs; exact F.weight_nonneg t; exact le_rfl) (Finset.mem_univ s)
        simpa only [if_pos rfl, ite_true] using ht
      exact (ENNReal.ofReal_pos.mpr hpos).ne' hMass
    choose label hLaw using hSupport
    refine ⟨label, fun j => ?_, hLaw⟩
    have hMass := congrArg (fun μ : Measure (ProbabilityMeasure (Torus 1)) => μ {densityMeasure (η j)}) he
    rw [speciesLaw_singleton, ternarySpeciesLaw_singleton η hη j] at hMass
    have hCond (s : Fin F.count) : densityMeasure (F.density s) = densityMeasure (η j) ↔ label s = j := by
      rw [hLaw s]
      exact hη.eq_iff
    simp_rw [hCond] at hMass
    have hNonneg : 0 ≤ (∑ s, if label s = j then F.weight s else 0) :=
      Finset.sum_nonneg fun s _ => by split_ifs; exact F.weight_nonneg s; exact le_rfl
    have ht := congrArg ENNReal.toReal hMass
    change (ENNReal.ofReal ((∑ s, if label s = j then F.weight s else 0))).toReal = _ at ht
    rw [ENNReal.toReal_ofReal hNonneg] at ht
    norm_num at ht
    exact ht
  · rintro ⟨label, hMass, hLaw⟩
    have hCoefficient (j : Fin 3) :
        (∑ s, if label s = j then ENNReal.ofReal (F.weight s) else 0) = (1 / 3 : ℝ≥0∞) := by
      have he := ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (f := fun s => if label s = j then F.weight s else 0)
        (fun s _ => by split_ifs; exact F.weight_nonneg s; exact le_rfl)
      simp only [apply_ite, ENNReal.ofReal_zero] at he
      rw [← he]
      change ENNReal.ofReal ((∑ s, if label s = j then F.weight s else 0)) = _
      rw [hMass j]
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
      norm_num
    have hGroup : speciesLaw F = ∑ j : Fin 3,
        (∑ s, if label s = j then ENNReal.ofReal (F.weight s) else 0) • Measure.dirac (densityMeasure (η j)) := by
      unfold speciesLaw
      simp_rw [hLaw]
      symm
      simp_rw [Finset.sum_smul, ite_smul, zero_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      simp [eq_comm]
    rw [hGroup]
    simp_rw [hCoefficient]
    exact Finset.smul_sum.symm


private theorem canonical_pt_add (s t : ℝ) : pt s + pt t = pt (s + t) :=
  (SharpLSI.liftT_add (fun _ : Fin 1 => s) (fun _ : Fin 1 => t)).symm

/-- Native translation is the positive physical pushforward by the indicated
circle rotation, as an equality of probability measures. -/
theorem interactingDensityTranslate_pushforward (a : Torus 1) (ρ : AbsoluteDensity 1) :
    (densityMeasure (interactingDensityTranslate a ρ) : Measure (Torus 1)) =
      Measure.map (fun x => x + a) (densityMeasure ρ : Measure (Torus 1)) := by
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [interactingDensityTranslate_integral]
  exact (integral_map (φ := fun x : Torus 1 => x + a) (continuous_id.add continuous_const).measurable.aemeasurable
    f.continuous.aestronglyMeasurable).symm

private theorem canonical_cyclic_root (η : Fin 3 → AbsoluteDensity 1)
    (hcyc : ∀ (j : Fin 3) x, (η (j + 1)).sqrt x = (η j).sqrt (x - pt (1 / 3))) :
    ∀ (j : Fin 3) x, (η j).density x = (η 0).density (x - pt ((j : ℕ) / 3)) := by
  intro j x
  have h0 := hcyc 0
  have h1 := hcyc 1
  fin_cases j
  · simp only [Fin.val_zero, Nat.cast_zero, zero_div]
    rw [show pt (0 : ℝ) = 0 by ext i; rfl, sub_zero]
    rfl
  · simpa [AbsoluteDensity.density] using congrArg (fun z : ℝ => z ^ 2) (h0 x)
  · have he : (η 2).sqrt x = (η 0).sqrt (x - pt (2 / 3)) := by
      calc
        (η 2).sqrt x = (η 1).sqrt (x - pt (1 / 3)) := by simpa using h1 x
        _ = (η 0).sqrt ((x - pt (1 / 3)) - pt (1 / 3)) := h0 _
        _ = (η 0).sqrt (x - pt (2 / 3)) := by
          rw [sub_sub, canonical_pt_add]
          norm_num
    exact congrArg (fun z : ℝ => z ^ 2) he

private theorem canonical_law_rotation (η : Fin 3 → AbsoluteDensity 1)
    (hd : ∀ (j : Fin 3) x, (η j).density x = (η 0).density (x - pt ((j : ℕ) / 3))) :
    ∀ j : Fin 3, densityMeasure (η j) =
      densityMeasure (interactingDensityTranslate (pt ((j : ℕ) / 3)) (η 0)) := by
  intro j
  apply Subtype.ext
  apply (DGPS.Frontier.STR029.densityMeasure_eq_iff_STR02901 _ _).2
  exact Filter.Eventually.of_forall (hd j)

end DGPS.Examples.ThreeSpeciesCircle

namespace DGPS

/-- Smooth positive representative of the actual probability density. -/
def SmoothPositiveDensity (ρ : AbsoluteDensity 1) : Prop :=
  ∃ v : Torus 1 → ℝ, IsSmoothPeriodic v ∧ (∀ x, 0 < v x) ∧
    ρ.density =ᵐ[haar 1] v

/-- Positive H1 density means a continuous H1 density representative bounded
below by a positive constant. It does not assert smoothness. -/
def PositiveH1Density (ρ : AbsoluteDensity 1) : Prop :=
  ∃ v : Torus 1 → ℝ, Continuous v ∧ MemH1 v ∧
    (∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ v x) ∧ ρ.density =ᵐ[haar 1] v

def IsSpeciesOptimizer (A : InteractionData 1) (b : AbsoluteDrift A) (F : SpeciesFamily 1) : Prop :=
  0 < speciesGap A F ∧ speciesQuotient A b F = speciesRate A b

def IsScalarOptimizer (A : InteractionData 1) (b : AbsoluteDrift A) (ρ : AbsoluteDensity 1) : Prop :=
  0 < scalarGap A ρ ∧ scalarQuotient A b ρ = scalarRate A b

def AttainsAtMostRate (A : InteractionData 1) (b : AbsoluteDrift A) (k : ℕ+)
    (F : SpeciesFamily 1) : Prop :=
  (F.count : ℕ) ≤ k ∧ 0 < speciesGap A F ∧ speciesQuotient A b F = speciesRateAtMost A b k

/-- The smooth circle distributional equation, on all probability measures. -/
abbrev IsDistributionalStationary := Examples.ThreeSpeciesCircle.IsCircleDistributionalStationary

/-- Strict mixture convexity on the actual finite-free-energy domain. -/
abbrev StrictMixtureConvexFreeEnergy := Examples.ThreeSpeciesCircle.CircleStrictMixtureConvexFreeEnergy

/-- A bounded positive continuous H1 square root gives a positive H1 density.
The one-dimensional H1 algebra proves the density-domain claim. -/
theorem positiveH1Density_of_bounded_root (ρ : AbsoluteDensity 1)
    (v : Torus 1 → ℝ) (hv : Continuous v) (hrep : ρ.sqrt =ᵐ[haar 1] v)
    (hH : MemH1 v) (m : ℝ) (hm : 0 < m) (hlo : ∀ x, m ≤ v x) :
    PositiveH1Density ρ := by
  obtain ⟨g, hg⟩ := hH
  refine ⟨fun x => v x ^ 2, hv.pow 2, ?_, ⟨m ^ 2, sq_pos_of_pos hm, ?_⟩, ?_⟩
  · exact ⟨_, by simpa only [pow_two] using hg.mul_one_dim hg⟩
  · intro x
    have hp := mul_nonneg (sub_nonneg.mpr (hlo x)) (add_nonneg (hm.le.trans (hlo x)) hm.le)
    nlinarith
  · filter_upwards [hrep] with x hx
    exact congrArg (fun z : ℝ => z ^ 2) hx

end DGPS

namespace DGPS.Models

/-- The explicit frozen circle interaction; no model coefficients are changed. -/
abbrev threeSpeciesCircle := DGPS.Examples.ThreeSpeciesCircle.modelData

/-- The actual ordinary reference probability, defined for every real field. -/
def threeSpeciesReference (h : ℝ) : ProbabilityMeasure (DGPS.Torus 1) :=
  ⟨(DGPS.Examples.ThreeSpeciesCircle.ordinaryReference h).measure,
    (DGPS.Examples.ThreeSpeciesCircle.ordinaryReference h).isProbabilityMeasure⟩

private theorem threeSpeciesPotential_smooth (h ε : ℝ) (ρ : DGPS.AbsoluteDensity 1) :
    DGPS.IsSmoothPeriodic (DGPS.interactionPotential (threeSpeciesCircle h ε) ρ) := by
  have he : DGPS.interactionPotential (threeSpeciesCircle h ε) ρ = fun x =>
      DGPS.Examples.ThreeSpeciesCircle.driftPot h ε (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) x -
        ε / 2 * ∫ y, DGPS.Examples.ThreeSpeciesCircle.kernelK h y y
          ∂(DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) := by
    funext x
    exact DGPS.Examples.ThreeSpeciesCircle.elementary_equilibriumPotential h ε _ x
  rw [he]
  exact (DGPS.Examples.ThreeSpeciesCircle.isSmooth_driftPot h ε _).sub contDiff_const

/-- A genuine drift provider for the actual frozen model, including its Gibbs
diagonal gauge. The spatially constant gauge has zero derivative. -/
def threeSpeciesCircleDrift (h ε : ℝ) : DGPS.AbsoluteDrift (threeSpeciesCircle h ε) where
  force := fun ρ => DGPS.smoothGrad (DGPS.interactionPotential (threeSpeciesCircle h ε) ρ)
  measurable_force := fun ρ => (threeSpeciesPotential_smooth h ε ρ).continuous_smoothGrad.measurable
  weak_gradient := fun ρ => by
    have hg := (threeSpeciesPotential_smooth h ε ρ).isWeakGradient
    exact ⟨hg.memLp.mono_exponent (by norm_num),
      hg.memLp_grad.mono_exponent (by norm_num), hg.ibp⟩

end DGPS.Models

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Exactly one optimal atomic measure on species laws. This classifies every
original finite positive-weight family, including arbitrary duplicate labels. -/
theorem unrestrictedOptimizer_unique_ternaryRotationOrbit :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ b : AbsoluteDrift (modelData h ε), ∃ η : Fin 3 → AbsoluteDensity 1,
          (∀ j, SmoothPositiveDensity (η j)) ∧
          Function.Injective (fun j => densityMeasure (η j)) ∧
          (∀ j : Fin 3, densityMeasure (η j) =
            densityMeasure (interactingDensityTranslate (pt ((j : ℕ) / 3)) (η 0))) ∧
          (∃ F : SpeciesFamily 1, IsSpeciesOptimizer (modelData h ε) b F) ∧
          ∀ F : SpeciesFamily 1, IsSpeciesOptimizer (modelData h ε) b F ↔
            (0 < speciesGap (modelData h ε) F ∧ speciesLaw F = ternarySpeciesLaw η) := by
  obtain ⟨δ, hδ, hmain⟩ := elementaryModel_speciesRate_smooth_orbit_classification
  refine ⟨δ, hδ, fun h hh hhd => ?_⟩
  obtain ⟨ε0, m, hε0, hεmax, hm, hM⟩ := hmain h hh hhd
  refine ⟨ε0, hε0, hεmax, fun ε hε hεsmall b => ?_⟩
  obtain ⟨p, hp, hps, η, hG, hQ, hη, hthird, hsm, hds, hlog, hlo, hrot, hclass⟩ :=
    hM ε hε hεsmall b
  refine ⟨η, fun j => ⟨(η j).density, hds j, ?_, Filter.EventuallyEq.rfl⟩,
    hη, canonical_law_rotation η (canonical_cyclic_root η hrot),
    ⟨SpeciesFamily.ofData 3 p hp hps η, hG, hQ⟩, fun F => ?_⟩
  · intro x
    exact sq_pos_of_pos (hm.trans_le (hlo j x))
  · have hgroup := speciesLaw_eq_ternary_iff F η hη
    change IsSpeciesOptimizer (modelData h ε) b F ↔ _
    constructor
    · intro hF
      refine ⟨hF.1, hgroup.mpr ?_⟩
      obtain ⟨label, hmass, hlaw⟩ := (hclass F).mp hF
      exact ⟨label, hmass, hlaw⟩
    · rintro ⟨_, hatom⟩
      exact (hclass F).mpr (hgroup.mp hatom)

/-- Full native weighted-H1 tangent statement, with original chosen weak
gradients, AE cancellation, both parameter signs, and the exact remainder.
Continuous positive H1 densities are asserted; no smooth tangent restriction. -/
def EveryH1SplitUphill (h ε : ℝ) (b : AbsoluteDrift (modelData h ε))
    (σ : AbsoluteDensity 1) : Prop :=
  ∀ (q : ℕ+) (θ : Fin q → ℝ) (hθ : ∀ s, 0 < θ s) (hθsum : ∑ s, θ s = 1),
    ∀ f : Fin q → WeakH1Test (densityMeasure σ),
      (∀ s, ∫ x, (f s).fn x ∂(densityMeasure σ : Measure (Torus 1)) = 0) →
      (∀ᵐ x ∂(densityMeasure σ : Measure (Torus 1)), ∑ s, θ s * (f s).fn x = 0) →
      let B := ∑ s, θ s * ∫ x, (f s).fn x ^ 2 ∂(densityMeasure σ : Measure (Torus 1))
      let r := (scalarRate (modelData h ε) b).toReal
      let c := ((∑ s, θ s * ∫ x, ((f s).grad x 0) ^ 2
          ∂(densityMeasure σ : Measure (Torus 1))) - r * B) /
        (2 * (scalarGap (modelData h ε) σ : ℝ))
      0 < B → 0 < c ∧
      ∃ (g : Fin q → Torus 1 → ℝ)
        (hg : ∀ s, IsWeakGradient (g s) (f s).grad)
        (hgc : ∀ s, Continuous (g s))
        (hm : ∀ s, ∫ x, g s x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
        (hcancel : ∀ x, ∑ s, θ s * g s x = 0),
        (∀ s, g s =ᵐ[haar 1] (f s).fn) ∧
        ∃ t0 : ℝ, 0 < t0 ∧ ∃ rem : ℝ → ℝ,
          Tendsto (fun t => rem t / t ^ 2) (𝓝[{t : ℝ | t ≠ 0}] 0) (𝓝 0) ∧
          ∀ t : ℝ, 0 < |t| → |t| < t0 →
            ∃ hp : ∀ s x, 0 < 1 + t * g s x,
              let F := finiteH1Split σ q θ hθ hθsum g (fun s => (f s).grad) hg hgc hm t hp
              (∀ s, (densityMeasure (F.density s) : Measure (Torus 1)) =
                (densityMeasure σ : Measure (Torus 1)).withDensity
                  (fun x => ENNReal.ofReal (1 + t * (f s).fn x))) ∧
              (∀ s, ∃ v : Torus 1 → ℝ, Continuous v ∧
                (F.density s).sqrt =ᵐ[haar 1] v ∧ MemH1 v ∧
                  ∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ v x) ∧
              (∀ s, PositiveH1Density (F.density s)) ∧
              densityMeasure (barycenter F) = densityMeasure σ ∧
              0 < speciesGap (modelData h ε) F ∧
              speciesQuotient (modelData h ε) b F ≠ ⊤ ∧
              speciesQuotient (modelData h ε) b F = ENNReal.ofReal (r + c * t ^ 2 + rem t) ∧
              scalarRate (modelData h ε) b < speciesQuotient (modelData h ε) b F

private theorem canonical_uphill_factory :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ b : AbsoluteDrift (modelData h ε), ∀ σ : AbsoluteDensity 1,
          IsScalarOptimizer (modelData h ε) b σ → EveryH1SplitUphill h ε b σ := by
  obtain ⟨δ, hδ, hM⟩ := scalarOptimizer_everyInfinitesimalFixedBarycenterSplit_uphill
  refine ⟨δ, hδ, fun h hh hhd => ?_⟩
  obtain ⟨ε0, hε0, hεmax, hU⟩ := hM h hh hhd
  refine ⟨ε0, hε0, hεmax, fun ε hε hεsmall b σ hσ => ?_⟩
  intro q θ hθ hθsum f hmean hcancel
  dsimp only
  intro hB
  obtain ⟨hc, g, hg, hgc, hm, hcg, hae, t0, ht0, rem, hrem, hsplit⟩ :=
    hU ε hε hεsmall b σ hσ.1 hσ.2 q θ hθ hθsum f hmean hcancel hB
  refine ⟨hc, g, hg, hgc, hm, hcg, hae, t0, ht0, rem, hrem, fun t ht hsmall => ?_⟩
  obtain ⟨hp, hLaw, hPos, hbar, hGap, hFin, hQ, hStrict⟩ := hsplit t ht hsmall
  refine ⟨hp, hLaw, hPos, ?_, hbar, hGap, hFin, hQ, hStrict⟩
  intro s
  obtain ⟨v, hv, hrep, hH, m, hm, hlo⟩ := hPos s
  exact positiveH1Density_of_bounded_root _ v hv hrep hH m hm hlo

/-- The complete necessary-species conclusion, using actual native objects.
The law rotation is the physical pushforward by the preceding translation
identity. Every original family and full weighted-H1 tangent is retained. -/
def CanonicalThreeSpeciesConclusion (h ε : ℝ) (b : AbsoluteDrift (modelData h ε)) : Prop :=
  ∃ hH : IsCoerciveDensityHessian (modelData h ε) (Models.threeSpeciesReference h),
  ∃ hs : FiniteRate (scalarRate (modelData h ε) b),
    (∀ r ∈ [speciesRate (modelData h ε) b, speciesRateAtMost (modelData h ε) b 2,
      scalarRate (modelData h ε) b, ordinaryLSRate (ordinaryReference h),
      poincareRate (Models.threeSpeciesReference h),
      gaussianRate (modelData h ε) (Models.threeSpeciesReference h) hH,
      min (gaussianRate (modelData h ε) (Models.threeSpeciesReference h) hH)
        (poincareRate (Models.threeSpeciesReference h))], FiniteRate r) ∧
    0 < speciesRate (modelData h ε) b ∧
    speciesRate (modelData h ε) b < speciesRateAtMost (modelData h ε) b 2 ∧
    speciesRateAtMost (modelData h ε) b 2 = ordinaryLSRate (ordinaryReference h) ∧
    ordinaryLSRate (ordinaryReference h) < scalarRate (modelData h ε) b ∧
    scalarRate (modelData h ε) b <
      min (gaussianRate (modelData h ε) (Models.threeSpeciesReference h) hH)
        (poincareRate (Models.threeSpeciesReference h)) ∧
    min (gaussianRate (modelData h ε) (Models.threeSpeciesReference h) hH)
      (poincareRate (Models.threeSpeciesReference h)) = poincareRate (Models.threeSpeciesReference h) ∧
    poincareRate (Models.threeSpeciesReference h) <
      gaussianRate (modelData h ε) (Models.threeSpeciesReference h) hH ∧
    (∀ ν : ProbabilityMeasure (Torus 1), IsDistributionalStationary (modelData h ε) ν ↔
      ν = Models.threeSpeciesReference h) ∧
    StrictMixtureConvexFreeEnergy (modelData h ε) ∧
    (∃ η : Fin 3 → AbsoluteDensity 1,
      (∀ j, SmoothPositiveDensity (η j)) ∧
      Pairwise (fun i j => densityMeasure (η i) ≠ densityMeasure (η j)) ∧
      (∀ j : Fin 3, densityMeasure (η j) =
        densityMeasure (interactingDensityTranslate (pt ((j : ℕ) / 3)) (η 0))) ∧
      (∃ F : SpeciesFamily 1, IsSpeciesOptimizer (modelData h ε) b F) ∧
      ∀ F : SpeciesFamily 1, IsSpeciesOptimizer (modelData h ε) b F ↔
        (0 < speciesGap (modelData h ε) F ∧ speciesLaw F = ternarySpeciesLaw η)) ∧
    (¬ ∃ F : SpeciesFamily 1, AttainsAtMostRate (modelData h ε) b 2 F) ∧
    (∃ ξ : Fin 3 → AbsoluteDensity 1,
      (∀ j, SmoothPositiveDensity (ξ j)) ∧
      Pairwise (fun i j => densityMeasure (ξ i) ≠ densityMeasure (ξ j)) ∧
      (∀ j : Fin 3, densityMeasure (ξ j) =
        densityMeasure (interactingDensityTranslate (pt ((j : ℕ) / 3)) (ξ 0))) ∧
      (∀ ρ : AbsoluteDensity 1, IsScalarOptimizer (modelData h ε) b ρ ↔
        ∃ j : Fin 3, densityMeasure ρ = densityMeasure (ξ j)) ∧
      ∀ j : Fin 3, EveryH1SplitUphill h ε b (ξ j))

/-- All clauses of the frozen T08 primary theorem on one common field/coupling
interval. Stronger provider-independence is retained: the interval precedes ALL
actual drift providers, including the explicit canonical drift below. -/
theorem elementaryCircle_exactlyThreeSpeciesNecessary_allDrifts :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ h : ℝ, 0 < h → h < h0 →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ b : AbsoluteDrift (modelData h ε), CanonicalThreeSpeciesConclusion h ε b := by
  obtain ⟨δR, hδR, hRate⟩ := elementaryModel_full_rate_chain
  obtain ⟨δF, hδF, hFamily⟩ := unrestrictedOptimizer_unique_ternaryRotationOrbit
  obtain ⟨δS, hδS, hScalar⟩ := scalarOptimizer_exact_three_rotationBranches
  obtain ⟨δU, hδU, hUphill⟩ := canonical_uphill_factory
  let h0 := min δR (min δF (min δS δU))
  refine ⟨h0, lt_min hδR (lt_min hδF (lt_min hδS hδU)), fun h hh hhd => ?_⟩
  have hhR : h < δR := hhd.trans_le (min_le_left _ _)
  have hh1 : h < min δF (min δS δU) := hhd.trans_le (min_le_right _ _)
  have hhF : h < δF := hh1.trans_le (min_le_left _ _)
  have hh2 : h < min δS δU := hh1.trans_le (min_le_right _ _)
  have hhS : h < δS := hh2.trans_le (min_le_left _ _)
  have hhU : h < δU := hh2.trans_le (min_le_right _ _)
  obtain ⟨εR, heR, heRm, hR⟩ := hRate h hh hhR
  obtain ⟨εF, heF, _, hF⟩ := hFamily h hh hhF
  obtain ⟨εS, heS, _, hS⟩ := hScalar h hh hhS
  obtain ⟨εU, heU, _, hU⟩ := hUphill h hh hhU
  let ε0 := min εR (min εF (min εS εU))
  refine ⟨ε0, lt_min heR (lt_min heF (lt_min heS heU)),
    (min_le_left _ _).trans heRm, fun ε hε he b => ?_⟩
  have hεR : ε < εR := he.trans_le (min_le_left _ _)
  have hε1 : ε < min εF (min εS εU) := he.trans_le (min_le_right _ _)
  have hεF : ε < εF := hε1.trans_le (min_le_left _ _)
  have hε2 : ε < min εS εU := hε1.trans_le (min_le_right _ _)
  have hεS : ε < εS := hε2.trans_le (min_le_left _ _)
  have hεU : ε < εU := hε2.trans_le (min_le_right _ _)
  have hεmax : ε < epsMax h := hεR.trans_le heRm
  obtain ⟨hH, hRates⟩ := hR ε hε hεR
  obtain ⟨hFinite, hPositive, hMs, hBinary, hOrdinary, hScalarTwo, hTwo, hGauss, hNoBinary⟩ := hRates b
  have hs : FiniteRate (scalarRate (modelData h ε) b) := hFinite _ (by simp)
  obtain ⟨η, hηsm, hηdistinct, hηrot, hAttain, hAtomic⟩ := hF ε hε hεF b
  obtain ⟨ξ, hξsm, hξdistinct, hξrot, hξmin, hξclass⟩ := hS ε hε hεS b
  refine ⟨hH, hs, hFinite, hPositive, hMs, hBinary, hOrdinary,
    hScalarTwo, hTwo, hGauss, ?_, elementaryModel_strictConvexity hε hεmax,
    ⟨η, hηsm, fun i j hij he => hij (hηdistinct he), hηrot, hAttain, hAtomic⟩, ?_,
    ⟨ξ, ?_, hξdistinct, canonical_law_rotation ξ hξrot, hξclass, ?_⟩⟩
  · intro ν
    exact elementaryModel_uniqueStationary hh hε hεmax ν
  · rintro ⟨F, hcount, hG, hQ⟩
    exact (hNoBinary F hcount hG).ne' hQ
  · intro j
    refine ⟨(ξ j).density, (hξsm j).1.pow 2, ?_, Filter.EventuallyEq.rfl⟩
    intro x
    exact sq_pos_of_pos ((hξsm j).2 x)
  · intro j
    exact hU ε hε hεU b (ξ j) (hξmin j)

/-- The complete canonical T08 export for the explicit model, canonical drift
and reference. All seven rate guards, full atomic-law uniqueness, every scalar
minimizer and the full H1 tangent statement are part of its expanded conclusion. -/
theorem elementaryCircle_exactlyThreeSpeciesNecessary :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ h : ℝ, 0 < h → h < h0 →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        CanonicalThreeSpeciesConclusion h ε (Models.threeSpeciesCircleDrift h ε) := by
  obtain ⟨h0, hh0, hM⟩ := elementaryCircle_exactlyThreeSpeciesNecessary_allDrifts
  refine ⟨h0, hh0, fun h hh hhd => ?_⟩
  obtain ⟨ε0, he0, _, hε⟩ := hM h hh hhd
  exact ⟨ε0, he0, fun ε he heSmall => hε ε he heSmall (Models.threeSpeciesCircleDrift h ε)⟩

/-- A genuine increasing reindexing makes any strictly positive null sequence
strictly decrease. All original family facts can be composed with this SAME
cofinal index map; no selected laws or limits are replaced. -/
private theorem canonical_decreasing_reindex (w : ℕ → ℝ) (hw : ∀ n, 0 < w n)
    (ht : Tendsto w atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictAnti (fun n => w (φ n)) := by
  classical
  have hnext (k : ℕ) : ∃ n : ℕ, k < n ∧ w n < w k / 2 := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      (ht.eventually (gt_mem_nhds (half_pos (hw k))))
    refine ⟨max N (k + 1), ?_, hN _ (le_max_left _ _)⟩
    omega
  let φ : ℕ → ℕ := Nat.rec 0 (fun _ k => Classical.choose (hnext k))
  have hstep (n : ℕ) : φ n < φ (n + 1) ∧ w (φ (n + 1)) < w (φ n) / 2 := by
    exact Classical.choose_spec (hnext (φ n))
  refine ⟨φ, strictMono_nat_of_lt_succ (fun n => (hstep n).1),
    strictAnti_nat_of_succ_lt (fun n => ?_)⟩
  exact (hstep n).2.trans (half_lt_self (hw (φ n)))

/-- The actual compensating sequence, retaining the SAME ordinary equality
law and strict positivity of every compensation density. Passing to a tail
only removes finitely many parameters; the original two-species objectives
and exact reference barycenter are preserved. -/
private theorem canonical_compensating_sequence (D : OrdinaryRootGraphData)
    {h ε : ℝ} (hh : 0 < h) (hhd : h < D.radius)
    (hε : 0 < ε) (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε)) :
    ∃ σ : AbsoluteDensity 1, 0 < ordinaryEntropy h σ ∧
      str025_quot h σ = ordinaryLSRate (ordinaryReference h) ∧
      ∃ (w : ℕ → ℝ) (F : ℕ → SpeciesFamily 1) (hcount : ∀ n, (F n).count = 2),
        (∀ n, 0 < w n ∧ w n < 1) ∧ StrictAnti w ∧ Tendsto w atTop (𝓝 0) ∧
        (∀ n, (F n).weight ⟨0, by rw [hcount n]; decide⟩ = w n ∧
          (F n).weight ⟨1, by rw [hcount n]; decide⟩ = 1 - w n ∧
          densityMeasure ((F n).density ⟨0, by rw [hcount n]; decide⟩) = densityMeasure σ ∧
          ((F n).density ⟨1, by rw [hcount n]; decide⟩).density =ᵐ[haar 1]
            (fun x => (referenceDensity h x - w n * σ.density x) / (1 - w n)) ∧
          (∃ v : Torus 1 → ℝ, Continuous v ∧ (∀ x, 0 < v x) ∧
            ((F n).density ⟨1, by rw [hcount n]; decide⟩).density =ᵐ[haar 1] v) ∧
          (densityMeasure (barycenter (F n)) : Measure (Torus 1)) = threefoldReference h ∧
          0 < speciesGap (modelData h ε) (F n) ∧
          FiniteRate (speciesQuotient (modelData h ε) b (F n))) ∧
        Tendsto (fun n => speciesQuotient (modelData h ε) b (F n)) atTop
          (𝓝 (ordinaryLSRate (ordinaryReference h))) := by
  obtain ⟨σ, hpos, hquot, hdata⟩ := ordinaryRoots_compensating_data D hh hhd
  obtain ⟨g, hg, hg0, hmass, M, hgc, hM, hgM, hμ⟩ := hdata 0
  let τ := DGPS.Lipschitz.t01RelativeAbsoluteDensity (ordinaryReference h)
    (ordinaryReference_lip h) g hg hg0 hmass
  have hH : 0 < ordinaryEntropy h τ := by
    unfold ordinaryEntropy
    rw [hμ]
    exact hpos 0
  have hEquality : str025_quot h τ = ordinaryLSRate (ordinaryReference h) := by
    change ordinaryFisher h τ / (2 * ordinaryEntropy h τ) = _
    unfold ordinaryFisher ordinaryEntropy
    rw [hμ]
    exact hquot 0
  obtain ⟨w, F, hcount, hw, hwlim, hFn, hlim⟩ := ordinary_relative_compensating_sequence
    hh hε hεmax b g hg hg0 hmass M hgM hH
  have hwM : Tendsto (fun n => w n * M ^ 2) atTop (𝓝 0) := by
    simpa using hwlim.mul_const (M ^ 2)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (hwM.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  have hτ (x : Torus 1) : τ.density x = referenceDensity h x * g x ^ 2 :=
    DGPS.Lipschitz.t01RelativeAbsoluteDensity_density _ _ _ _ _ _ x
  have hτc : Continuous τ.density := by
    have he : τ.density = fun x => referenceDensity h x * g x ^ 2 := funext hτ
    rw [he]
    exact (continuous_referenceDensity h).mul (hgc.pow 2)
  have hwt := hwlim.comp (tendsto_add_atTop_nat N)
  obtain ⟨φ, hφ, hAnti⟩ := canonical_decreasing_reindex (fun n => w (n + N))
    (fun n => (hw (n + N)).1) hwt
  refine ⟨τ, hH, hEquality, (fun n => w (φ n + N)), (fun n => F (φ n + N)),
    (fun n => hcount (φ n + N)), (fun n => hw (φ n + N)), hAnti,
    hwt.comp hφ.tendsto_atTop, fun n => ?_, ?_⟩
  · obtain ⟨hw0, hw1, hfirst, hsecond, hbar, hGap, hFin⟩ := hFn (φ n + N)
    refine ⟨hw0, hw1, hfirst, hsecond, ?_, hbar, hGap, hFin⟩
    refine ⟨fun x => (referenceDensity h x - w (φ n + N) * τ.density x) / (1 - w (φ n + N)),
      ((continuous_referenceDensity h).sub (continuous_const.mul hτc)).div_const _,
      fun x => ?_, hsecond⟩
    have hsq : g x ^ 2 ≤ M ^ 2 := by
      have hb := (abs_le.mp (hgM x)).2
      have hp := mul_nonneg (sub_nonneg.mpr hb) (add_nonneg hM.le (hg0 x))
      nlinarith
    have hsmall : w (φ n + N) * g x ^ 2 < 1 := by
      have hbound := mul_le_mul_of_nonneg_left hsq (hw (φ n + N)).1.le
      have htail := hN (φ n + N) (by omega)
      linarith
    apply div_pos _ (sub_pos.mpr (hw (φ n + N)).2)
    rw [hτ]
    have hp := mul_pos (referenceDensity_pos (h := h) x) (sub_pos.mpr hsmall)
    nlinarith
  · change Tendsto (fun n => speciesQuotient (modelData h ε) b (F n)) atTop (𝓝 (str025_quot h τ)) at hlim
    rw [hEquality] at hlim
    exact hlim.comp ((tendsto_add_atTop_nat N).comp hφ.tendsto_atTop)

/-- The required public binary export includes equality, strict nonattainment,
and an actual compensating minimizing sequence at an ordinary equality law.
All original H1 competitors and arbitrary positive binary weights are admitted. -/
theorem binaryRate_eq_ordinaryLSRate :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ h : ℝ, 0 < h → h < h0 →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ b : AbsoluteDrift (modelData h ε),
        speciesRateAtMost (modelData h ε) b 2 = ordinaryLSRate (ordinaryReference h) ∧
        (¬ ∃ F : SpeciesFamily 1, AttainsAtMostRate (modelData h ε) b 2 F) ∧
        ∃ σ : AbsoluteDensity 1, 0 < ordinaryEntropy h σ ∧
          str025_quot h σ = ordinaryLSRate (ordinaryReference h) ∧
          ∃ (w : ℕ → ℝ) (F : ℕ → SpeciesFamily 1) (hcount : ∀ n, (F n).count = 2),
            (∀ n, 0 < w n ∧ w n < 1) ∧ StrictAnti w ∧ Tendsto w atTop (𝓝 0) ∧
            (∀ n, (F n).weight ⟨0, by rw [hcount n]; decide⟩ = w n ∧
              (F n).weight ⟨1, by rw [hcount n]; decide⟩ = 1 - w n ∧
              densityMeasure ((F n).density ⟨0, by rw [hcount n]; decide⟩) = densityMeasure σ ∧
              ((F n).density ⟨1, by rw [hcount n]; decide⟩).density =ᵐ[haar 1]
                (fun x => (referenceDensity h x - w n * σ.density x) / (1 - w n)) ∧
              (∃ v : Torus 1 → ℝ, Continuous v ∧ (∀ x, 0 < v x) ∧
                ((F n).density ⟨1, by rw [hcount n]; decide⟩).density =ᵐ[haar 1] v) ∧
              (densityMeasure (barycenter (F n)) : Measure (Torus 1)) = threefoldReference h ∧
              0 < speciesGap (modelData h ε) (F n) ∧
              FiniteRate (speciesQuotient (modelData h ε) b (F n))) ∧
            Tendsto (fun n => speciesQuotient (modelData h ε) b (F n)) atTop
              (𝓝 (ordinaryLSRate (ordinaryReference h))) := by
  let D := Classical.choice exists_ordinaryRootGraphData
  obtain ⟨δ, hδ, hBinary⟩ := elementaryModel_binary_rate_eq_and_strict
  refine ⟨min δ D.radius, lt_min hδ D.radius_pos, fun h hh hhd => ?_⟩
  obtain ⟨ε0, he0, heMax, hB⟩ := hBinary h hh (hhd.trans_le (min_le_left _ _))
  refine ⟨ε0, he0, heMax, fun ε hε hεsmall b => ?_⟩
  obtain ⟨hEq, hStrict⟩ := hB ε hε hεsmall b
  refine ⟨hEq, ?_, canonical_compensating_sequence D hh
    (hhd.trans_le (min_le_right _ _)) hε (hεsmall.trans_le heMax) b⟩
  rintro ⟨F, hcount, hGap, hQ⟩
  exact (hStrict F hcount hGap).ne' hQ

end DGPS.Examples.ThreeSpeciesCircle
