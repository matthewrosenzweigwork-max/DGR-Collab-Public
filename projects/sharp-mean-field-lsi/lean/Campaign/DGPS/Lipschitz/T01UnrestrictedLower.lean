import DGPS.Foundations.Torus
import DGPS.Analysis.RelativeFisher
import FullLabeledLSI.Infra.HypercontrHybrid6
import FullLabeledLSI.Infra.SpectralSetup
import FullLabeledLSI.Paper.Lindeberg7

/-!
# Labeled replacement from reference form data

The legacy replacement engines only need a reference eigenbasis, its C¹ representatives,
mutual absolute continuity with Haar measure, and a positive ordinary LSI subrate. Their
semiconvex equilibrium wrappers are unnecessary here. These lemmas retain those exact
structural inputs; constructing them for the campaign equilibrium remains a separate bridge.
No particle-rate lower bound is asserted in this file.
-/

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace DGPS.Lipschitz

open SharpLSI.FL

/-- Every campaign bounded positive reference has a positive legacy ordinary LSI subrate.
Clamping a density on its null exceptional set supplies the legacy pointwise bounds. -/
theorem legacy_reference_lsi_lower_bound {d : ℕ} (P : BoundedPositiveReference d) :
    ENNReal.ofReal (P.lower / P.upper) ≤ rLS P.measure := by
  obtain ⟨x, hx, hy⟩ := (P.lower_le.and P.le_upper).exists
  have horder : P.lower ≤ P.upper := hx.trans hy
  let ρ : Torus d → ℝ := fun x => max P.lower (min P.upper (P.density x))
  have hae : ρ =ᵐ[haar d] P.density := by
    filter_upwards [P.lower_le, P.le_upper] with x hx hy
    simp only [ρ, min_eq_right hy, max_eq_right hx]
  have hρ : SharpLSI.GoodDens ρ P.lower P.upper :=
    { meas := measurable_const.max (measurable_const.min P.measurable_density)
      pos := P.lower_pos
      lower := fun x => le_max_left _ _
      upper := fun x => max_le horder (min_le_left _ _)
      one := (integral_congr_ae hae).trans P.mass_one }
  have hmeasure : SharpLSI.densMeasure ρ = P.measure := by
    apply withDensity_congr_ae
    exact hae.mono fun x hx => congrArg ENNReal.ofReal hx
  rw [← hmeasure]
  exact Gross.rLS_ge_of_goodDens hρ

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}

/-- Hybrid moments are available from the reference form and one-body LSI alone. -/
theorem hybrid_moments_of_reference_form
    (hac : μ ≪ volume) (hca : volume ≪ μ)
    (he : SharpLSI.IsRefEigenbasis μ e lam)
    (hC1 : ∀ j, Gross.C1T (e j)) {a : ℝ} (ha : 0 < a)
    (hrls : ENNReal.ofReal a ≤ rLS μ) (hlam0 : lam 0 = 0)
    (hpos : 0 < lam 1) (J : ℕ) : HybridPolyMoment μ e lam J := by
  have hnn : ∀ j, 0 ≤ lam j := fun j => by
    simpa only [hlam0] using he.mono (Nat.zero_le j)
  intro L q
  exact Hyb.hybrid_poly_moment hac hca he hC1
    (fun _ => Filter.EventuallyEq.refl _ _) ha hrls hlam0 hnn hpos
    (fun j hj => he.mono hj) J L q

/-- The hybrid moment input for a campaign reference; its LSI subrate and absolute continuity
are proved from that reference's defining density bounds. -/
theorem hybrid_moments_of_campaign_reference
    (P : BoundedPositiveReference d)
    (he : SharpLSI.IsRefEigenbasis P.measure e lam)
    (hC1 : ∀ j, Gross.C1T (e j)) (hlam0 : lam 0 = 0)
    (hpos : 0 < lam 1) (J : ℕ) : HybridPolyMoment P.measure e lam J := by
  obtain ⟨x, hx, hy⟩ := (P.lower_le.and P.le_upper).exists
  have hupper : 0 < P.upper := P.lower_pos.trans_le (hx.trans hy)
  exact hybrid_moments_of_reference_form P.measure_ac_haar P.haar_ac_measure he hC1
    (div_pos P.lower_pos hupper) (legacy_reference_lsi_lower_bound P) hlam0 hpos J

/-- Quantitative third-order replacement, uniform in the number of labels and coefficient
arrays at fixed spectral level. Only positive fluctuation modes enter `IP`. -/
theorem third_order_joint_replacement_of_reference_form
    (hac : μ ≪ volume) (hca : volume ≪ μ)
    (he : SharpLSI.IsRefEigenbasis μ e lam)
    (hC1 : ∀ j, Gross.C1T (e j)) {a : ℝ} (ha : 0 < a)
    (hrls : ENNReal.ofReal a ≤ rLS μ) (hlam0 : lam 0 = 0)
    (hpos : 0 < lam 1) {J JR : ℕ} (hJ : JR ≤ J)
    {Φ : ℝ × (Fin JR → ℝ) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hΦc : HasCompactSupport Φ) (L B : ℝ) :
    ∃ C : ℝ, ∀ (N : ℕ) (c : (Fin N → Fin (J + 1)) → ℝ),
      SpectralCoeff lam L c → ∑ j, c j ^ 2 ≤ B ^ 2 →
      ∀ δ : ℝ, 0 < δ → 0 < lowCount c δ →
        |IP μ e c δ hJ Φ Finset.univ - IP μ e c δ hJ Φ (retained c δ)| ≤
          C * (Real.sqrt δ + (Real.sqrt (lowCount c δ))⁻¹) := by
  have hG : GoodBasis μ e :=
    ⟨he.zero, fun j => (hC1 j).measurable, fun j => (hC1 j).bounded, he.orthonormal⟩
  have hnn : ∀ j, 0 ≤ lam j := fun j => by
    simpa only [hlam0] using he.mono (Nat.zero_le j)
  exact joint_rate_good hG
    (hybrid_moments_of_reference_form hac hca he hC1 ha hrls hlam0 hpos J)
    hlam0 hnn he.mono hpos hJ hΦ hΦc L B

/-- Continuous polynomial-growth replacement with the cutoff, influence, and particle-number
quantifiers in the order used by the unrestricted lower-bound proof. -/
theorem polynomial_growth_joint_replacement_of_reference_form
    (hac : μ ≪ volume) (hca : volume ≪ μ)
    (he : SharpLSI.IsRefEigenbasis μ e lam)
    (hC1 : ∀ j, Gross.C1T (e j)) {a : ℝ} (ha : 0 < a)
    (hrls : ENNReal.ofReal a ≤ rLS μ) (hlam0 : lam 0 = 0)
    (hpos : 0 < lam 1) {J JR : ℕ} (hJ : JR ≤ J)
    {Φ : ℝ × (Fin JR → ℝ) → ℝ} (hΦ : Continuous Φ)
    (hgrowth : ∃ (K : ℝ) (k : ℕ), ∀ p, |Φ p| ≤ K * (1 + ‖p‖) ^ k)
    (L B : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ᶠ N in atTop,
        ∀ c : (Fin N → Fin (J + 1)) → ℝ, SpectralCoeff lam L c →
          ∑ j, c j ^ 2 ≤ B ^ 2 →
            |IP μ e c δ hJ Φ Finset.univ - IP μ e c δ hJ Φ (retained c δ)| ≤ ε := by
  have hG : GoodBasis μ e :=
    ⟨he.zero, fun j => (hC1 j).measurable, fun j => (hC1 j).bounded, he.orthonormal⟩
  have hnn : ∀ j, 0 ≤ lam j := fun j => by
    simpa only [hlam0] using he.mono (Nat.zero_le j)
  exact joint_replace_good hG
    (hybrid_moments_of_reference_form hac hca he hC1 ha hrls hlam0 hpos J)
    hlam0 hnn he.mono hpos hJ hΦ hgrowth L B

end DGPS.Lipschitz
