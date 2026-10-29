import LeanResearch.PeriodicAttractiveLogGas.CollectiveSecondMoment
import LeanResearch.PeriodicAttractiveLogGas.CollectiveExponential
import LeanResearch.PeriodicAttractiveLogGas.LocalizedVirialPairs

/-! Coercivity on the actual separated region, source Proposition
`prop:separated-coercivity`, lines 1323--1340. The region assumptions are
literal inequalities for the constructed mass and hard shell count. The
conclusion uses the original attractive Gibbs measure and the existing
ambient closed-form energy of each physical Lipschitz observable.
Development and central checks are recorded in
`research/reviews/separated-coercivity-development.md`.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace PeriodicAttractiveLogGas.SeparatedCoercivity

open CollectiveIntegrationByParts CollectiveSecondMoment CollectiveExponential
  SeparatedRadius HeavyScales

theorem four_le_threshold {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hN : 4 / δ ≤ (N : ℝ)) : 4 ≤ δ * N := by
  simpa only [mul_comm] using (div_le_iff₀ hδ).mp hN

/-- The source particle threshold supplies the genuine N>=2 needed by the
global attractive integration-by-parts theorem. -/
theorem two_le_particle_number {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hN : 4 / δ ≤ (N : ℝ)) : 2 ≤ N := by
  have ht := four_le_threshold hδ hN
  have hb : δ * (N : ℝ) ≤ N := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hδ1.le (Nat.cast_nonneg N)
  have hn : (4 : ℝ) ≤ N := ht.trans hb
  have hn' : 4 ≤ N := by exact_mod_cast hn
  omega

theorem four_le_mass {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (hN : 4 / δ ≤ (N : ℝ))
    (ξ : Torus) (s : ℝ) {X : Configuration N} (hM : δ * N < mass ξ s X) :
    4 ≤ mass ξ s X := (four_le_threshold hδ hN).trans hM.le

/-- Collision nullity is transferred to the genuine restricted Gibbs law.
No vanishing or trace condition is imposed on the observable at collisions. -/
theorem ae_noncollision_restrict (N : ℕ) (β : ℝ) (U : Set (Configuration N)) :
    ∀ᵐ X ∂(gibbsMeasure greenRealRepresentative N β).restrict U,
      X ∉ collisionSet N := by
  have h : ∀ᵐ X ∂gibbsMeasure greenRealRepresentative N β, X ∉ collisionSet N := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using
      gibbs_collisionSet_null greenRealRepresentative N β
  exact ae_restrict_of_ae h

/-- The earlier physical gradient estimate is global, hence applies to the
restriction without any collision deletion or additional analytic premise. -/
theorem QFunction_gradient_bound_ae_restrict {N : ℕ} (hN : 0 < N) {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (ξ : Torus) (β : ℝ)
    (U : Set (Configuration N)) :
    ∀ᵐ X ∂(gibbsMeasure greenRealRepresentative N β).restrict U,
      ‖(QFunction ξ hs hsmall).gradient X‖ ^ 2 ≤ 6400 * N * s ^ 2 :=
  Eventually.of_forall (fun X ↦ QFunction_norm_gradient_sq_le hN hs hsmall ξ X)

/-- Actual separated positivity supplies ell0 almost everywhere on U.
The exceptional set is the already proved Gibbs-null collision set. -/
theorem QFunction_generator_bound_ae_restrict {N : ℕ} (hN : 0 < N)
    {β β₀ s K δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hβ4 : β₀ < 4)
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (hK : separationRadius β₀ ≤ K)
    (hscale : 16 * β₀ * remainderGradientBound * s ≤ 4 - β₀)
    (hδ : 0 < δ) (hthreshold : 4 / δ ≤ (N : ℝ))
    (ξ : Torus) (U : Set (Configuration N)) (hU : IsOpen U)
    (hmass : ∀ X ∈ U, δ * N < mass ξ s X)
    (hshell : ∀ X ∈ U, (shellCount ξ s K X : ℝ) <
      2 * separationConstant β₀ * (4 - β₀) * mass ξ s X) :
    ∀ᵐ X ∂(gibbsMeasure greenRealRepresentative N β).restrict U,
      (4 - β₀) * δ ^ 2 * N / 4 ≤ (QFunction ξ hs hsmall).generator β X := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hgap : 0 ≤ 4 - β₀ := sub_nonneg.mpr hβ4.le
  filter_upwards [ae_restrict_mem hU.measurableSet, ae_noncollision_restrict N β U]
    with X hXU hX
  have hM := hmass X hXU
  have hM4 := four_le_mass hδ hthreshold ξ s hM
  have hgen := LocalizedVirialPairs.QFunction_generator_separated_lower
    hN hβ hβ₀ hβ4 hs hsmall hK hscale ξ hM4 (hshell X hXU) hX
  have hm2 : (δ * (N : ℝ)) ^ 2 ≤ mass ξ s X ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hδ.le hNr.le) hM.le 2
  calc
    _ = (4 - β₀) / (4 * (N : ℝ)) * (δ * (N : ℝ)) ^ 2 := by
      field_simp [hNr.ne']
    _ ≤ (4 - β₀) / (4 * (N : ℝ)) * mass ξ s X ^ 2 :=
      mul_le_mul_of_nonneg_left hm2 (div_nonneg hgap (by positivity))
    _ ≤ _ := hgen

/-- Source Proposition `prop:separated-coercivity`, with every original
local hypothesis and the actual ambient energy. The outer-scale hypothesis
is retained from the source; the previously proved Q estimates only need
the stated smaller-ball bound. No condition is imposed inside U on F at
collisions, and no symmetry of F or U is required. -/
theorem separated_coercivity {N : ℕ} {β β₀ s K δ₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hβ4 : β₀ < 4)
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (_houter : 2 * K * s ≤ 1 / 4)
    (hscale : 16 * β₀ * remainderGradientBound * s ≤ 4 - β₀)
    (hK : separationRadius β₀ ≤ K) (hδ₁ : 0 < δ₁) (hδ₁1 : δ₁ < 1)
    (hthreshold : 4 / δ₁ ≤ (N : ℝ))
    (ξ : Torus) (U : Set (Configuration N)) (hU : IsOpen U)
    (hmass : ∀ X ∈ U, δ₁ * N < mass ξ s X)
    (hshell : ∀ X ∈ U, (shellCount ξ s K X : ℝ) <
      2 * separationConstant β₀ * (4 - β₀) * mass ξ s X)
    (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y)))
    (hsupport : ∀ X, X ∉ U → F X = 0) :
    (∫ X, F X ^ 2 ∂gibbsMeasure greenRealRepresentative N β) ≤
      (409600 * s ^ 2 / ((4 - β₀) ^ 2 * δ₁ ^ 4 * N)) *
      ambientEnergy (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
        (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF) := by
  have hN₂ : 2 ≤ N := two_le_particle_number hδ₁ hδ₁1 hthreshold
  have hN : 0 < N := lt_of_lt_of_le (by norm_num) hN₂
  have hpair : (QFunction (N := N) ξ hs hsmall).PairGradientBound 162 :=
    QFunction_pairGradientBound hN hs hsmall ξ
  have hQ : ∀ X : Configuration N, 0 ≤ (QFunction ξ hs hsmall).value X :=
    fun X ↦ Q_nonneg ξ s X
  have hLQ := QFunction_generator_bound_ae_restrict hN hβ hβ₀ hβ4 hs hsmall
    hK hscale hδ₁ hthreshold ξ U hU hmass hshell
  have hgrad := QFunction_gradient_bound_ae_restrict hN hs hsmall ξ β U
  exact separated_coercivity_from_generator (QFunction ξ hs hsmall) hN₂
    hβ hβ₀ hβ4 hδ₁ hs hpair hQ U hU hLQ hgrad F hF hsupport

end PeriodicAttractiveLogGas.SeparatedCoercivity
