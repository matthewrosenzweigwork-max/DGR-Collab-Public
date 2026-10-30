import DGPS.Lipschitz.T01SymmetricConditionalRate

/-!
# The scalar subrate for a family with one common conditional law

This reduction is for exchangeable conditional families: equality of their measures is
proved by symmetry before this theorem is applied. No species-rate lower bound is used.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- Equality of absolute probability laws determines their densities a.e. -/
theorem t01_density_ae_eq_of_measure_eq {ρ σ : AbsoluteDensity d}
    (h : densityMeasure ρ = densityMeasure σ) : ρ.density =ᵐ[haar d] σ.density := by
  have hm : (haar d).withDensity (fun x => ENNReal.ofReal (ρ.density x)) =
      (haar d).withDensity (fun x => ENNReal.ofReal (σ.density x)) := congrArg Subtype.val h
  have he := (withDensity_eq_iff_of_sigmaFinite
    (ρ.integrable_density.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    (σ.integrable_density.aestronglyMeasurable.aemeasurable.ennreal_ofReal)).mp hm
  filter_upwards [he] with x hx
  have hh := congrArg ENNReal.toReal hx
  simpa only [ENNReal.toReal_ofReal (ρ.density_nonneg x),
    ENNReal.toReal_ofReal (σ.density_nonneg x)] using hh

/-- A family whose species laws all equal one law has that same barycenter law. -/
theorem t01_barycenter_measure_eq_of_common_measure (F : SpeciesFamily d)
    (ρ : AbsoluteDensity d) (h : ∀ s, densityMeasure (F.density s) = densityMeasure ρ) :
    densityMeasure (barycenter F) = densityMeasure ρ := by
  apply Subtype.ext
  apply withDensity_congr_ae
  have he := ae_all_iff.mpr (fun s => t01_density_ae_eq_of_measure_eq (h s))
  filter_upwards [he] with x hx
  congr 1
  rw [F.barycenter_density_apply]
  change (∑ s, F.weight s * (F.density s).density x) = ρ.density x
  simp_rw [hx]
  rw [← Finset.sum_mul, F.weight_sum, one_mul]

/-- The gap of a common-law family is exactly the scalar gap. -/
theorem t01_speciesGap_eq_scalar_of_common_measure (A : InteractionData d)
    (F : SpeciesFamily d) (ρ : AbsoluteDensity d)
    (h : ∀ s, densityMeasure (F.density s) = densityMeasure ρ) :
    speciesGap A F = scalarGap A ρ := by
  rw [← speciesGap_single A ρ]
  apply NNReal.eq
  rw [coe_speciesGap, coe_speciesGap, speciesRawGap, speciesRawGap,
    t01_barycenter_measure_eq_of_common_measure F ρ h, densityMeasure_barycenter_single]
  simp_rw [h]
  rw [← Finset.sum_mul, F.weight_sum, one_mul, sum_single_count]
  simp [SpeciesFamily.single]

/-- The dissipation also equals the scalar dissipation, including an infinite value. -/
theorem t01_speciesDissipation_eq_scalar_of_common_measure (A : InteractionData d)
    (b : AbsoluteDrift A) (F : SpeciesFamily d) (ρ : AbsoluteDensity d)
    (h : ∀ s, densityMeasure (F.density s) = densityMeasure ρ) :
    speciesDissipation A b F = scalarDissipation A b ρ := by
  have hbar := t01_barycenter_measure_eq_of_common_measure F ρ h
  have hforce : b.force (barycenter F) =ᵐ[haar d] b.force ρ :=
    b.ae_eq_of_isWeakGradient _ (by
      have hp : interactionPotential A (barycenter F) = interactionPotential A ρ := by
        unfold interactionPotential
        rw [hbar]
      rw [hp]
      exact b.weak_gradient ρ)
  have hI : ∀ s, (∫⁻ x, ENNReal.ofReal
      (‖(2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • b.force (barycenter F) x‖ ^ 2)
      ∂haar d) = scalarDissipation A b ρ := by
    intro s
    have hroot := AbsoluteDensity.sqrt_ae_eq_of_density_ae_eq
      (t01_density_ae_eq_of_measure_eq (h s))
    have hgrad := ((F.isWeakGradient_sqrtGradient s).congr_ae hroot
      (EventuallyEq.refl _ _)).ae_eq (isWeakGradient_weakGradient ρ.sqrt_mem)
    unfold scalarDissipation scalarScore
    apply lintegral_congr_ae
    filter_upwards [hroot, hgrad, hforce] with x hx hg hf
    rw [hx, hg, hf]
  unfold speciesDissipation
  simp_rw [hI]
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun s _ => F.weight_nonneg s),
    F.weight_sum, ENNReal.ofReal_one, one_mul]

/-- The scalar subrate controls the actual conditional family when symmetry has identified
all its species laws. The conclusion has exactly the species-gap/force interface used by
the common conditional integration engine, without assuming a species subrate. -/
theorem two_subrate_family_of_common_measure (A : InteractionData d) (b : AbsoluteDrift A)
    {r : ℝ} (hr : 0 ≤ r) (hrr : ENNReal.ofReal r ≤ scalarRate A b)
    (F : SpeciesFamily d) (ρ : AbsoluteDensity d)
    (h : ∀ s, densityMeasure (F.density s) = densityMeasure ρ) :
    ENNReal.ofReal (2 * r * (speciesGap A F : ℝ)) ≤ speciesDissipation A b F := by
  rw [t01_speciesGap_eq_scalar_of_common_measure A F ρ h,
    t01_speciesDissipation_eq_scalar_of_common_measure A b F ρ h]
  exact two_subrate_scalarGap_le A b hr hrr ρ

/-- At almost every revealed configuration, symmetry supplies the common-law hypothesis
for every actual finite conditional family. This leaves only the absolute-domain construction
to the conditional Sobolev theorem, without a choice of measurable density representatives. -/
theorem ae_conditional_scalar_family {N : ℕ} (A : InteractionData d) (b : AbsoluteDrift A)
    {r : ℝ} (hr : 0 ≤ r) (hrr : ENNReal.ofReal r ≤ scalarRate A b)
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ}
    (hQ : SharpLSI.FL.IsBddDens Q c C)
    (ν : Measure (SharpLSI.Config N d)) [IsProbabilityMeasure ν]
    (hν : ν = SharpLSI.FL.qMeasure Q) (hsym : SharpLSI.IsSymmetricMeasure ν)
    (S : Finset (Fin N)) (q : ℕ+) (label : Fin q → Fin N)
    (hlabel : ∀ s, label s ∉ S) :
    ∀ᵐ a ∂ν.map (SharpLSI.FL.restrictS S), ∀ ρ : Fin q → AbsoluteDensity d,
      (∀ s x, (ρ s).density x = SharpLSI.FL.condDensS Q S (label s) a x) →
      ENNReal.ofReal (2 * r * (speciesGap A (SpeciesFamily.uniform q ρ) : ℝ)) ≤
        speciesDissipation A b (SpeciesFamily.uniform q ρ) := by
  let s0 : Fin q := ⟨0, q.pos⟩
  have he : ∀ᵐ a ∂ν.map (SharpLSI.FL.restrictS S), ∀ s : Fin q,
      SharpLSI.densMeasure (SharpLSI.FL.condDensS Q S (label s) a) =
        SharpLSI.densMeasure (SharpLSI.FL.condDensS Q S (label s0) a) := by
    rw [ae_all_iff]
    intro s
    filter_upwards [t01_condLawS_eq_of_symmetric ν hsym S (hlabel s) (hlabel s0),
      SharpLSI.FL.condLawS_ae_eq hQ (hlabel s) hν,
      SharpLSI.FL.condLawS_ae_eq hQ (hlabel s0) hν] with a hEq hi hj
    exact hi.symm.trans (hEq.trans hj)
  filter_upwards [he] with a ha
  intro ρ hρ
  apply two_subrate_family_of_common_measure A b hr hrr (SpeciesFamily.uniform q ρ) (ρ s0)
  intro s
  apply Subtype.ext
  change (haar d).withDensity (fun x => ENNReal.ofReal ((ρ s).density x)) =
    (haar d).withDensity (fun x => ENNReal.ofReal ((ρ s0).density x))
  have hs : (ρ s).density = SharpLSI.FL.condDensS Q S (label s) a := funext (hρ s)
  have hs0 : (ρ s0).density = SharpLSI.FL.condDensS Q S (label s0) a := funext (hρ s0)
  rw [hs, hs0]
  exact ha s

end DGPS.Lipschitz
