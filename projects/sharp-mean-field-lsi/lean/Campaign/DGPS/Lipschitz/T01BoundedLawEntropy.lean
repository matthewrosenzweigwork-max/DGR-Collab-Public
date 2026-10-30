import DGPS.FiniteN.Tools.Rothaus
import SharpSymmetricLSI.Paper.R7Positive

/-!
# Entropy convergence for bounded observables from their laws and second moments

The second-moment limit and the clipped-square test identify the bound of the
limiting observable almost everywhere. The clipped entropy test then gives the
actual entropy limit, including zero mass.
-/

open MeasureTheory Filter Topology SharpLSI
open scoped ENNReal BoundedContinuousFunction

namespace DGPS.Lipschitz

/-- A bounded prelimit family with convergent laws and second moments has the same
almost-everywhere bound at the limit. -/
theorem ae_abs_le_of_bounded_law_and_mass
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    {Ω' : Type*} [MeasurableSpace Ω'] (γ : Measure Ω') [IsProbabilityMeasure γ]
    (f : ∀ k, Ω k → ℝ) {F : Ω' → ℝ} (hF : MemLp F 2 γ)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ k x, |f k x| ≤ B)
    (hlaw : ∀ g : ℝ →ᵇ ℝ,
      Tendsto (fun k => ∫ x, g (f k x) ∂P k) atTop (𝓝 (∫ x, g (F x) ∂γ)))
    (hmass : Tendsto (fun k => ∫ x, f k x ^ 2 ∂P k) atTop (𝓝 (∫ x, F x ^ 2 ∂γ))) :
    ∀ᵐ x ∂γ, |F x| ≤ B := by
  have hclip : AEStronglyMeasurable (fun x => min |F x| B) γ :=
    (continuous_abs.min continuous_const).comp_aestronglyMeasurable hF.aestronglyMeasurable
  have hclipi : Integrable (fun x => min |F x| B ^ 2) γ :=
    Integrable.of_bound (hclip.pow 2) (B ^ 2) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (le_min (abs_nonneg _) hB0) (min_le_right _ _) 2)
  have ht := hlaw (psiSq B hB0)
  simp only [psiSq_apply] at ht
  have ht' : Tendsto (fun k => ∫ x, f k x ^ 2 ∂P k) atTop
      (𝓝 (∫ x, min |F x| B ^ 2 ∂γ)) := by
    refine ht.congr fun k => integral_congr_ae (Eventually.of_forall fun x => ?_)
    rw [min_eq_left (hB k x), sq_abs]
  have heq := tendsto_nhds_unique hmass ht'
  have hnonneg : ∀ x, 0 ≤ F x ^ 2 - min |F x| B ^ 2 := by
    intro x
    have h := pow_le_pow_left₀ (le_min (abs_nonneg (F x)) hB0) (min_le_left |F x| B) 2
    rw [sq_abs] at h
    linarith
  have hz : (∫ x, F x ^ 2 - min |F x| B ^ 2 ∂γ) = 0 := by
    rw [integral_sub hF.integrable_sq hclipi, heq, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hnonneg)
    (hF.integrable_sq.sub hclipi)).mp hz
  filter_upwards [hae] with x hx
  by_contra hn
  have hgt : B < |F x| := lt_of_not_ge hn
  have hs : F x ^ 2 = B ^ 2 := by
    rw [min_eq_right hgt.le] at hx
    exact sub_eq_zero.mp hx
  have ha : |F x| ^ 2 = B ^ 2 := by rw [sq_abs, hs]
  nlinarith [abs_nonneg (F x)]

/-- Under the same hypotheses, homogeneous entropy converges in its finite real
value. No entropy inequality or positive lower bound on the observable is used. -/
theorem homogeneousEntropy_tendsto_of_bounded_law_and_mass
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    {Ω' : Type*} [MeasurableSpace Ω'] (γ : Measure Ω') [IsProbabilityMeasure γ]
    (f : ∀ k, Ω k → ℝ) (hf : ∀ k, MemLp (f k) 2 (P k))
    {F : Ω' → ℝ} (hF : MemLp F 2 γ)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ k x, |f k x| ≤ B)
    (hlaw : ∀ g : ℝ →ᵇ ℝ,
      Tendsto (fun k => ∫ x, g (f k x) ∂P k) atTop (𝓝 (∫ x, g (F x) ∂γ)))
    (hmass : Tendsto (fun k => ∫ x, f k x ^ 2 ∂P k) atTop (𝓝 (∫ x, F x ^ 2 ∂γ))) :
    DGPS.homogeneousEntropy γ (fun x => F x ^ 2) ≠ ⊤ ∧
      Tendsto (fun k => (DGPS.homogeneousEntropy (P k) (fun x => f k x ^ 2)).toReal) atTop
        (𝓝 (DGPS.homogeneousEntropy γ (fun x => F x ^ 2)).toReal) := by
  have hFB := ae_abs_le_of_bounded_law_and_mass P γ f hF hB0 hB hlaw hmass
  let M := max B 1
  have hM : 1 ≤ M := le_max_right _ _
  have hMB : B ≤ M := le_max_left _ _
  have hsF : (fun x => min |F x| M ^ 2) =ᵐ[γ] fun x => F x ^ 2 := by
    filter_upwards [hFB] with x hx
    rw [min_eq_left (hx.trans hMB), sq_abs]
  have hsf : ∀ k, (fun x => min |f k x| M ^ 2) = fun x => f k x ^ 2 := by
    intro k
    funext x
    rw [min_eq_left ((hB k x).trans hMB), sq_abs]
  have hlog : Integrable (fun x => F x ^ 2 * Real.log (F x ^ 2)) γ := by
    have hi : Integrable (fun x => psiEnt M hM (F x)) γ :=
      Integrable.of_bound ((psiEnt M hM).continuous.comp_aestronglyMeasurable
        hF.aestronglyMeasurable) ‖psiEnt M hM‖
          (Eventually.of_forall fun x => (psiEnt M hM).norm_coe_le_norm _)
    exact hi.congr (hFB.mono fun x hx => by
      simp only [psiEnt_apply, min_eq_left (hx.trans hMB), sq_abs])
  have hfinite : DGPS.homogeneousEntropy γ (fun x => F x ^ 2) ≠ ⊤ := by
    rw [DGPS.FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent hF.integrable_sq,
      ent_eq_formula γ _ (fun x => sq_nonneg _) hF.integrable_sq hlog]
    exact ENNReal.ofReal_ne_top
  refine ⟨hfinite, ?_⟩
  have hE := hlaw (psiEnt M hM)
  have hS := hlaw (psiSq M (by linarith))
  have ht := (hE.sub ((Real.continuous_mul_log.tendsto _).comp hS)).max (tendsto_const_nhds (x := (0 : ℝ)))
  have hpre : ∀ k, (DGPS.homogeneousEntropy (P k) (fun x => f k x ^ 2)).toReal =
      max ((∫ x, psiEnt M hM (f k x) ∂P k) -
        (∫ x, psiSq M (by linarith) (f k x) ∂P k) *
          Real.log (∫ x, psiSq M (by linarith) (f k x) ∂P k)) 0 := by
    intro k
    rw [DGPS.FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent (hf k).integrable_sq,
      ← hsf k]
    exact ent_trunc_toReal (P k) (hf k).aestronglyMeasurable hM
  have hlim : (DGPS.homogeneousEntropy γ (fun x => F x ^ 2)).toReal =
      max ((∫ x, psiEnt M hM (F x) ∂γ) -
        (∫ x, psiSq M (by linarith) (F x) ∂γ) *
          Real.log (∫ x, psiSq M (by linarith) (F x) ∂γ)) 0 := by
    rw [DGPS.FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent hF.integrable_sq,
      ← ent_congr_ae hsF]
    exact ent_trunc_toReal γ hF.aestronglyMeasurable hM
  rw [hlim]
  exact ht.congr fun k => (hpre k).symm

end DGPS.Lipschitz
