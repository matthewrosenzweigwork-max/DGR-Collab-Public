import DGPS.Lipschitz.T01ConditionalSpecies
import DGPS.Lipschitz.T01ConditionalInformation
import DGPS.Lipschitz.T01SymmetricFamilyRate

/-!
# Actual conditional species in explicit score coordinates

A bijective enumeration of the unrevealed labels gives the genuine uniform absolute family.
Its barycenter is the actual conditional barycenter density. The common algebra below converts
any proved subrate inequality for that family to the pointwise input of conditional integration.
The unrestricted theorem obtains that inequality from the actual species rate.
-/

open MeasureTheory InformationTheory Filter
open scoped ENNReal

namespace DGPS.Lipschitz

open KernelApproximation

theorem t01_centeredCorrection_eq_Jfun {d : ℕ} (A : InteractionData d)
    (μ ρ : ProbabilityMeasure (Torus d)) :
    t01CenteredCorrection A μ ρ = SharpLSI.Jfun A.W (μ : Measure (Torus d)) ρ := by
  unfold t01CenteredCorrection SharpLSI.Jfun SharpLSI.interE
  simp only [t01_legacy_centeredKernel_eq, DGPS.Structural.centeredKernel_eq_lipschitz]
  rw [integral_prod_symm _ ((centeredKernel_continuous A (μ : Measure (Torus d))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))]
  ring

/-- Conversion of an actual uniform conditional family's gap and dissipation. The subrate
premise is the current family rate inequality, allowing the scalar and species lanes to share
the density, barycenter and force identifications without exchanging their rates. -/
theorem t01_conditional_family_explicit_score {d N : ℕ} (A : InteractionData d)
    (b : AbsoluteDrift A) (μ : ProbabilityMeasure (Torus d))
    (hμ : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A)
    (D : KData d) (hD : D.K = centeredKernel A (μ : Measure (Torus d)))
    {v : Torus d → Tangent d}
    (hv : IsWeakGradient (frozenPotential A (μ : Measure (Torus d))) v)
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ} (hQ : SharpLSI.FL.IsBddDens Q c C)
    {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    (S : Finset (Fin N)) (a : S → Torus d) (q : ℕ+) (e : Fin q ≃ ↥(Sᶜ))
    (ρ : Fin q → AbsoluteDensity d)
    (hρ : ∀ s x, (ρ s).density x = SharpLSI.FL.condDensS Q S (e s) a x)
    (hgrad : ∀ s, IsWeakGradient (ρ s).density
      (fun x => WithLp.toLp 2 (SharpLSI.FL.gradCondS Q GQ S (e s) a x)))
    {r : ℝ}
    (hsubrate : ENNReal.ofReal (2 * r * (speciesGap A (SpeciesFamily.uniform q ρ) : ℝ)) ≤
      speciesDissipation A b (SpeciesFamily.uniform q ρ)) :
    ENNReal.ofReal (2 * r * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ,
      (klDiv (SharpLSI.densMeasure (SharpLSI.FL.condDensS Q S i a))
        (μ : Measure (Torus d))).toReal +
      SharpLSI.Jfun A.W (μ : Measure (Torus d))
        (SharpLSI.densMeasure (SharpLSI.FL.barDensS Q S a)))) ≤
      ENNReal.ofReal ((Sᶜ.card : ℝ)⁻¹) * ∑ i ∈ Sᶜ,
        ∫⁻ x, ENNReal.ofReal (SharpLSI.FL.condDensS Q S i a x) *
          ENNReal.ofReal (‖(SharpLSI.FL.condDensS Q S i a x)⁻¹ •
            WithLp.toLp 2 (SharpLSI.FL.gradCondS Q GQ S i a x) +
            (v x + ∫ y, SharpLSI.FL.barDensS Q S a y • D.G1 x y ∂haar d)‖ ^ 2) ∂haar d := by
  classical
  let F := SpeciesFamily.uniform q ρ
  have hq : (q : ℕ) = Sᶜ.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_congr e
  have hqR : (q : ℝ) = Sᶜ.card := by exact_mod_cast hq
  have hsumR (f : Fin N → ℝ) :
      (∑ s : Fin q, f (e s)) = ∑ i ∈ Sᶜ, f i := by
    rw [Equiv.sum_comp e (fun i : ↥(Sᶜ) => f i)]
    exact Finset.sum_coe_sort Sᶜ f
  have hsumE (f : Fin N → ℝ≥0∞) :
      (∑ s : Fin q, f (e s)) = ∑ i ∈ Sᶜ, f i := by
    rw [Equiv.sum_comp e (fun i : ↥(Sᶜ) => f i)]
    exact Finset.sum_coe_sort Sᶜ f
  have hb : ∀ x, (barycenter F).density x = SharpLSI.FL.barDensS Q S a x := by
    intro x
    rw [F.barycenter_density_apply]
    change (∑ s : Fin q, (1 / (q : ℝ)) * (ρ s).density x) = _
    simp_rw [hρ]
    rw [← Finset.mul_sum, hsumR (fun i => SharpLSI.FL.condDensS Q S i a x)]
    simp only [hqR, one_div, SharpLSI.FL.barDensS]
  have hmρ : ∀ s, (densityMeasure (ρ s) : Measure (Torus d)) =
      SharpLSI.densMeasure (SharpLSI.FL.condDensS Q S (e s) a) := by
    intro s
    change (haar d).withDensity (fun x => ENNReal.ofReal ((ρ s).density x)) = _
    simp_rw [hρ]
    rfl
  have hmb : (densityMeasure (barycenter F) : Measure (Torus d)) =
      SharpLSI.densMeasure (SharpLSI.FL.barDensS Q S a) := by
    change (haar d).withDensity (fun x => ENNReal.ofReal ((barycenter F).density x)) = _
    simp_rw [hb]
    rfl
  have hH : (∑ s, F.weight s * (relativeEntropy
      (densityMeasure (F.density s) : Measure (Torus d)) (μ : Measure (Torus d))).toReal) =
      (Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ,
        (klDiv (SharpLSI.densMeasure (SharpLSI.FL.condDensS Q S i a))
          (μ : Measure (Torus d))).toReal := by
    change (∑ s : Fin q, (1 / (q : ℝ)) *
      (relativeEntropy (densityMeasure (ρ s) : Measure (Torus d))
        (μ : Measure (Torus d))).toReal) = _
    simp_rw [DGPS.Analysis.relativeEntropy_eq_klDiv, hmρ]
    rw [← Finset.mul_sum, hsumR (fun i =>
      (klDiv (SharpLSI.densMeasure (SharpLSI.FL.condDensS Q S i a)) (μ : Measure (Torus d))).toReal)]
    rw [hqR, one_div]
  have hgap : (speciesGap A F : ℝ) =
      (Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ,
        (klDiv (SharpLSI.densMeasure (SharpLSI.FL.condDensS Q S i a))
          (μ : Measure (Torus d))).toReal +
      SharpLSI.Jfun A.W (μ : Measure (Torus d))
        (SharpLSI.densMeasure (SharpLSI.FL.barDensS Q S a)) := by
    rw [(speciesGap_eq_reference_entropy_correction A hμ F).2, hH,
      t01_centeredCorrection_eq_Jfun, hmb]
  have hforce : b.force (barycenter F) =ᵐ[haar d]
      fun x => v x + ∫ y, SharpLSI.FL.barDensS Q S a y • D.G1 x y ∂haar d := by
    simpa only [hb] using absoluteDrift_centered_ae A b μ D hD hv (barycenter F)
  have hC : 0 < C := hQ.pos.trans_le ((hQ.lower 0).trans (hQ.upper 0))
  have hpos : ∀ s x, 0 < (ρ s).density x := by
    intro s x
    rw [hρ]
    exact (div_pos hQ.pos hC).trans_le (SharpLSI.FL.condDensS_bounds hQ S (e s) a x).1
  let T : Fin N → ℝ≥0∞ := fun i => ∫⁻ x,
    ENNReal.ofReal (SharpLSI.FL.condDensS Q S i a x) *
      ENNReal.ofReal (‖(SharpLSI.FL.condDensS Q S i a x)⁻¹ •
        WithLp.toLp 2 (SharpLSI.FL.gradCondS Q GQ S i a x) +
        (v x + ∫ y, SharpLSI.FL.barDensS Q S a y • D.G1 x y ∂haar d)‖ ^ 2) ∂haar d
  have hI : ∀ s : Fin q,
      (∫⁻ x, ENNReal.ofReal ((ρ s).density x *
        ‖((ρ s).density x)⁻¹ • WithLp.toLp 2 (SharpLSI.FL.gradCondS Q GQ S (e s) a x) +
          b.force (barycenter F) x‖ ^ 2) ∂haar d) =
      T (e s) := by
    intro s
    apply lintegral_congr_ae
    filter_upwards [hforce] with x hx
    rw [ENNReal.ofReal_mul (hpos s x).le, hρ, hx]
  have hDiss : speciesDissipation A b F =
      ENNReal.ofReal ((Sᶜ.card : ℝ)⁻¹) * ∑ i ∈ Sᶜ,
        ∫⁻ x, ENNReal.ofReal (SharpLSI.FL.condDensS Q S i a x) *
          ENNReal.ofReal (‖(SharpLSI.FL.condDensS Q S i a x)⁻¹ •
            WithLp.toLp 2 (SharpLSI.FL.gradCondS Q GQ S i a x) +
            (v x + ∫ y, SharpLSI.FL.barDensS Q S a y • D.G1 x y ∂haar d)‖ ^ 2) ∂haar d := by
    change speciesDissipation A b (SpeciesFamily.uniform q ρ) = _
    rw [positive_speciesDissipation_eq A b (SpeciesFamily.uniform q ρ)
      (fun s x => WithLp.toLp 2 (SharpLSI.FL.gradCondS Q GQ S (e s) a x)) hgrad hpos]
    change (∑ s : Fin q, ENNReal.ofReal (1 / (q : ℝ)) *
      (∫⁻ x, ENNReal.ofReal ((ρ s).density x *
        ‖((ρ s).density x)⁻¹ • WithLp.toLp 2 (SharpLSI.FL.gradCondS Q GQ S (e s) a x) +
          b.force (barycenter F) x‖ ^ 2) ∂haar d)) =
      ENNReal.ofReal ((Sᶜ.card : ℝ)⁻¹) * ∑ i ∈ Sᶜ, T i
    simp_rw [hI]
    rw [← Finset.mul_sum, hsumE T, hqR, one_div]
  rw [← hgap, ← hDiss]
  exact hsubrate

/-- The actual species subrate gives the pointwise conditional bound for the entire
unrevealed family. The enumeration is constructed, and no exchangeability is required. -/
theorem ae_conditional_species_explicit_score {d N : ℕ} (A : InteractionData d)
    (b : AbsoluteDrift A) (μ : ProbabilityMeasure (Torus d))
    (hμ : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A)
    (D : KData d) (hD : D.K = centeredKernel A (μ : Measure (Torus d)))
    {v : Torus d → Tangent d}
    (hv : IsWeakGradient (frozenPotential A (μ : Measure (Torus d))) v)
    {r : ℝ} (hr : 0 ≤ r) (hrr : ENNReal.ofReal r ≤ speciesRate A b)
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ} (hQ : SharpLSI.FL.IsBddDens Q c C)
    {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    (hQw : SharpLSI.IsWeakGrad (Q ∘ SharpLSI.unflat) GQ)
    (hGm : ∀ p, Measurable (fun y => GQ y p))
    (hG2 : ∀ p, MemLp (fun y => GQ y p) 2 volume)
    (ν : Measure (SharpLSI.Config N d)) [IsProbabilityMeasure ν]
    (hν : ν = SharpLSI.FL.qMeasure Q) (S : Finset (Fin N)) (hS : Sᶜ.Nonempty) :
    ∀ᵐ X ∂ν,
      ENNReal.ofReal (2 * r * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ,
        (klDiv (SharpLSI.densMeasure (SharpLSI.FL.condDensS Q S i
          (SharpLSI.FL.restrictS S X))) (μ : Measure (Torus d))).toReal +
        SharpLSI.Jfun A.W (μ : Measure (Torus d))
          (SharpLSI.densMeasure (SharpLSI.FL.barDensS Q S (SharpLSI.FL.restrictS S X))))) ≤
      ENNReal.ofReal ((Sᶜ.card : ℝ)⁻¹) * ∑ i ∈ Sᶜ, ∫⁻ x,
        ENNReal.ofReal (SharpLSI.FL.condDensS Q S i (SharpLSI.FL.restrictS S X) x) *
        ENNReal.ofReal (‖(SharpLSI.FL.condDensS Q S i (SharpLSI.FL.restrictS S X) x)⁻¹ •
          WithLp.toLp 2 (SharpLSI.FL.gradCondS Q GQ S i (SharpLSI.FL.restrictS S X) x) +
          (v x + ∫ y, SharpLSI.FL.barDensS Q S (SharpLSI.FL.restrictS S X) y • D.G1 x y
            ∂haar d)‖ ^ 2) ∂haar d := by
  classical
  let q : ℕ+ := ⟨Sᶜ.card, Finset.card_pos.mpr hS⟩
  let e : Fin q ≃ ↥(Sᶜ) := (Sᶜ).equivFin.symm
  have ha := ae_conditional_absolute_density_gradient hQ.meas hQ.pos hQ.lower hQ.upper
    hQw hGm hG2 ν hν S
  have haX := SharpLSI.FL.ae_restrictS_of_ae_volume S hQ.meas ha
  rw [← hν] at haX
  filter_upwards [haX] with X hgradX
  choose ρ hρ using fun s : Fin q => hgradX (e s) (Finset.mem_compl.mp (e s).property)
  exact t01_conditional_family_explicit_score A b μ hμ D hD hv hQ S
    (SharpLSI.FL.restrictS S X) q e ρ (fun s => (hρ s).1) (fun s => (hρ s).2)
    (two_subrate_speciesGap_le A b hr hrr (SpeciesFamily.uniform q ρ))

/-- For a symmetric joint law, the scalar subrate supplies the same explicit pointwise
bound. Symmetry identifies the conditional species laws before the family conversion is used;
there is no replacement of the scalar subrate by a species subrate. -/
theorem ae_conditional_scalar_explicit_score {d N : ℕ} (A : InteractionData d)
    (b : AbsoluteDrift A) (μ : ProbabilityMeasure (Torus d))
    (hμ : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A)
    (D : KData d) (hD : D.K = centeredKernel A (μ : Measure (Torus d)))
    {v : Torus d → Tangent d}
    (hv : IsWeakGradient (frozenPotential A (μ : Measure (Torus d))) v)
    {r : ℝ} (hr : 0 ≤ r) (hrr : ENNReal.ofReal r ≤ scalarRate A b)
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ} (hQ : SharpLSI.FL.IsBddDens Q c C)
    {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    (hQw : SharpLSI.IsWeakGrad (Q ∘ SharpLSI.unflat) GQ)
    (hGm : ∀ p, Measurable (fun y => GQ y p))
    (hG2 : ∀ p, MemLp (fun y => GQ y p) 2 volume)
    (ν : Measure (SharpLSI.Config N d)) [IsProbabilityMeasure ν]
    (hν : ν = SharpLSI.FL.qMeasure Q) (hsym : SharpLSI.IsSymmetricMeasure ν)
    (S : Finset (Fin N)) (hS : Sᶜ.Nonempty) :
    ∀ᵐ X ∂ν,
      ENNReal.ofReal (2 * r * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ,
        (klDiv (SharpLSI.densMeasure (SharpLSI.FL.condDensS Q S i
          (SharpLSI.FL.restrictS S X))) (μ : Measure (Torus d))).toReal +
        SharpLSI.Jfun A.W (μ : Measure (Torus d))
          (SharpLSI.densMeasure (SharpLSI.FL.barDensS Q S (SharpLSI.FL.restrictS S X))))) ≤
      ENNReal.ofReal ((Sᶜ.card : ℝ)⁻¹) * ∑ i ∈ Sᶜ, ∫⁻ x,
        ENNReal.ofReal (SharpLSI.FL.condDensS Q S i (SharpLSI.FL.restrictS S X) x) *
        ENNReal.ofReal (‖(SharpLSI.FL.condDensS Q S i (SharpLSI.FL.restrictS S X) x)⁻¹ •
          WithLp.toLp 2 (SharpLSI.FL.gradCondS Q GQ S i (SharpLSI.FL.restrictS S X) x) +
          (v x + ∫ y, SharpLSI.FL.barDensS Q S (SharpLSI.FL.restrictS S X) y • D.G1 x y
            ∂haar d)‖ ^ 2) ∂haar d := by
  classical
  let q : ℕ+ := ⟨Sᶜ.card, Finset.card_pos.mpr hS⟩
  let e : Fin q ≃ ↥(Sᶜ) := (Sᶜ).equivFin.symm
  have hlabel : ∀ s : Fin q, (e s : Fin N) ∉ S :=
    fun s => Finset.mem_compl.mp (e s).property
  have ha := ae_conditional_absolute_density_gradient hQ.meas hQ.pos hQ.lower hQ.upper
    hQw hGm hG2 ν hν S
  have haX := SharpLSI.FL.ae_restrictS_of_ae_volume S hQ.meas ha
  rw [← hν] at haX
  have hs := ae_of_ae_map (SharpLSI.FL.measurable_restrictS S).aemeasurable
    (ae_conditional_scalar_family A b hr hrr hQ ν hν hsym S q
      (fun s => (e s : Fin N)) hlabel)
  filter_upwards [haX, hs] with X hgradX hscalar
  choose ρ hρ using fun s : Fin q => hgradX (e s) (hlabel s)
  exact t01_conditional_family_explicit_score A b μ hμ D hD hv hQ S
    (SharpLSI.FL.restrictS S X) q e ρ (fun s => (hρ s).1) (fun s => (hρ s).2)
    (hscalar ρ (fun s => (hρ s).1))

end DGPS.Lipschitz
