import DGRHS.Gaussian.PeriodicMeanFieldMoving
import DGRHS.Gaussian.PeriodicRieszNamedDynamicCLT

/-!
Packet P11e, unit 1 (part 4): the static `C²` class implies the time-tested mean-field identity.

`periodicStaticWeak_timeTested`: let `μ^r = periodicCappedDensityMeasure (ρ r)` be a narrowly continuous
path of probability measures with `ρ^r ≤ M` satisfying the integrated static weak formulation against
every `C²` torus test (`PeriodicStaticWeakMeanFieldC2`).  For a classical backward solution `f` of
`-∂_r f = L_{β,μ^r} f` with terminal value `φ` (`PeriodicClassicalBackwardSolution`),
`∫ f^t dμ^t - ∫ f^0 dμ^0 = ∫_{(0,t]} periodicMeanTestDrift (ρ r) f r dr`.  This is the one-sentence step of
TeX 3922-3924, written out through `two_parameter_chain_rule`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal RealInnerProductSpace ENNReal Topology Classical Interval
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Time continuity of a classical solution at a fixed torus point. -/
lemma PeriodicClassicalBackwardSolution.continuousOn_time {F : PeriodicTorus ι → E} {β : ℝ}
    {ρ : ℝ → PeriodicTorus ι → ℝ} {t : ℝ≥0} {φ : PeriodicTorus ι → ℝ} {f : ℝ → PeriodicTorus ι → ℝ}
    (hf : PeriodicClassicalBackwardSolution F β ρ t φ f) (z : PeriodicTorus ι) :
    ContinuousOn (fun r => f r z) (Icc 0 (t : ℝ)) := by
  have h := hf.value_continuous.comp
    (f := fun r : ℝ => (r, periodicCenteredLift z)) (s := Icc 0 (t : ℝ))
    (by fun_prop) (fun r hr => ⟨hr, mem_univ _⟩)
  simpa [Function.comp_def, periodicLiftFn_centeredLift] using h

/-- Slices of a classical solution are bounded measurable, hence integrable. -/
lemma PeriodicClassicalBackwardSolution.integrable_slice {F : PeriodicTorus ι → E} {β : ℝ}
    {ρ : ℝ → PeriodicTorus ι → ℝ} {t : ℝ≥0} {φ : PeriodicTorus ι → ℝ} {f : ℝ → PeriodicTorus ι → ℝ}
    (hf : PeriodicClassicalBackwardSolution F β ρ t φ f) (μ : Measure (PeriodicTorus ι))
    [IsFiniteMeasure μ] {r : ℝ} (hr : r ∈ Icc 0 (t : ℝ)) : Integrable (f r) μ := by
  obtain ⟨C, hC, hb⟩ := hf.bounded
  refine (integrable_const C).mono'
    (measurable_of_contDiff_lift ((hf.spatial_contdiff r hr).of_le (by norm_num))).aestronglyMeasurable
    (ae_of_all _ fun z => ?_)
  have := (hb r hr (periodicCenteredLift z)).1
  simpa only [Real.norm_eq_abs, periodicLiftFn_centeredLift] using this

/-- Fundamental theorem of calculus in time for a classical solution at a fixed torus point. -/
lemma periodic_slice_ftc {F : PeriodicTorus ι → E} {β : ℝ} {ρ : ℝ → PeriodicTorus ι → ℝ} {t : ℝ≥0}
    {φ : PeriodicTorus ι → ℝ} {f : ℝ → PeriodicTorus ι → ℝ}
    (hf : PeriodicClassicalBackwardSolution F β ρ t φ f) (δ : ℝ → PeriodicTorus ι → ℝ)
    (hδc : ContinuousOn (fun p : ℝ × E => δ p.1 (periodicLift p.2)) (Icc 0 (t : ℝ) ×ˢ univ))
    (hδ : ∀ r ∈ Ioo 0 (t : ℝ), ∀ z, HasDerivAt (fun u => f u z) (δ r z) r)
    (z : PeriodicTorus ι) {s s' : ℝ} (hs : s ∈ Icc 0 (t : ℝ)) (hs' : s' ∈ Icc 0 (t : ℝ))
    (hle : s' ≤ s) : f s z - f s' z = ∫ v in s'..s, δ (periodicClamp t v) z := by
  have hcont : ContinuousOn (fun r => f r z) (Icc s' s) :=
    (hf.continuousOn_time z).mono (Icc_subset_Icc hs'.1 hs.2)
  have hint : IntervalIntegrable (fun v => δ (periodicClamp t v) z) volume s' s :=
    (((continuous_clamped_of_continuousOn_lift t δ hδc).comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont (fun x hx => ?_) hint).symm
  have hx' : x ∈ Ioo 0 (t : ℝ) := ⟨lt_of_le_of_lt hs'.1 hx.1, lt_of_lt_of_le hx.2 hs.2⟩
  rw [periodicClamp_eq ⟨hx'.1.le, hx'.2.le⟩]
  exact hδ x hx' z

/-- Fubini on a time interval for a bounded continuous integrand. -/
lemma periodic_integral_swap (μ' : Measure (PeriodicTorus ι)) [IsFiniteMeasure μ']
    (G : ℝ × PeriodicTorus ι → ℝ) (hG : Continuous G) (C : ℝ) (hC : ∀ p, |G p| ≤ C) {a b : ℝ}
    (hab : a ≤ b) :
    ∫ z, (∫ v in a..b, G (v, z)) ∂μ' = ∫ v in a..b, ∫ z, G (v, z) ∂μ' := by
  simp only [intervalIntegral.integral_of_le hab]
  haveI : IsFiniteMeasure (volume.restrict (Ioc a b)) := ⟨by simp⟩
  refine integral_integral_swap (f := fun z v => G (v, z)) ?_
  refine (integrable_const C).mono'
    ((hG.comp (continuous_snd.prodMk continuous_fst)).measurable.aestronglyMeasurable)
    (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs]
  exact hC (p.2, p.1)

/-- Pairing difference of two slices against a fixed law. -/
lemma periodic_pairing_slice {F : PeriodicTorus ι → E} {β : ℝ} {ρ : ℝ → PeriodicTorus ι → ℝ}
    {t : ℝ≥0} {φ : PeriodicTorus ι → ℝ} {f : ℝ → PeriodicTorus ι → ℝ}
    (hf : PeriodicClassicalBackwardSolution F β ρ t φ f) (δ : ℝ → PeriodicTorus ι → ℝ)
    (hδc : ContinuousOn (fun p : ℝ × E => δ p.1 (periodicLift p.2)) (Icc 0 (t : ℝ) ×ˢ univ))
    (Cδ : ℝ) (hCδ : ∀ r ∈ Icc 0 (t : ℝ), ∀ z, |δ r z| ≤ Cδ)
    (hδ : ∀ r ∈ Ioo 0 (t : ℝ), ∀ z, HasDerivAt (fun u => f u z) (δ r z) r)
    (μ' : Measure (PeriodicTorus ι)) [IsFiniteMeasure μ'] {s s' : ℝ} (hs : s ∈ Icc 0 (t : ℝ))
    (hs' : s' ∈ Icc 0 (t : ℝ)) (hle : s' ≤ s) :
    (∫ z, f s z ∂μ') - ∫ z, f s' z ∂μ' = ∫ v in s'..s, ∫ z, δ (periodicClamp t v) z ∂μ' := by
  rw [← integral_sub (hf.integrable_slice μ' hs) (hf.integrable_slice μ' hs')]
  rw [integral_congr_ae (ae_of_all _ fun z => periodic_slice_ftc hf δ hδc hδ z hs hs' hle)]
  exact periodic_integral_swap μ' (fun p => δ (periodicClamp t p.1) p.2)
    (continuous_clamped_of_continuousOn_lift t δ hδc) Cδ
    (fun p => hCδ _ (periodicClamp_mem t.coe_nonneg _) _) hle


/-- **The static `C²` class implies the time-tested mean-field identity.** -/
theorem periodicStaticWeak_timeTested (D : PeriodicForceData ι) (β : ℝ) (T : ℝ≥0)
    (ρ : ℝ → PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hprob : ∀ r ∈ Icc 0 (T : ℝ), IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r)))
    (hρ : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ z ∂periodicHaar ι, ρ r z ≤ M)
    (μ : ℝ → ProbabilityMeasure (PeriodicTorus ι)) (hμ : ContinuousOn μ (Icc 0 (T : ℝ)))
    (hρμ : ∀ r ∈ Icc 0 (T : ℝ),
      (μ r : Measure (PeriodicTorus ι)) = periodicCappedDensityMeasure (ρ r))
    (hstat : PeriodicStaticWeakMeanFieldC2 D.F β (T : ℝ) ρ)
    (t : ℝ≥0) (ht : t ≤ T) (φ : PeriodicTorus ι → ℝ) (f : ℝ → PeriodicTorus ι → ℝ)
    (hf : PeriodicClassicalBackwardSolution D.F β ρ t φ f) :
    (∫ z, f (t : ℝ) z ∂periodicCappedDensityMeasure (ρ (t : ℝ))) -
        (∫ z, f 0 z ∂periodicCappedDensityMeasure (ρ 0)) =
      ∫ r in Ioc 0 (t : ℝ), periodicMeanTestDrift D.F β (ρ r) f r := by
  have htR : (t : ℝ) ≤ T := by exact_mod_cast ht
  have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
  have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
  have hIcc : ∀ r ∈ Icc 0 (t : ℝ), r ∈ Icc 0 (T : ℝ) := fun r hr => ⟨hr.1, hr.2.trans htR⟩
  obtain ⟨C, hC0, hb⟩ := hf.bounded
  obtain ⟨δ, hδc, ⟨Cδ, hCδ⟩, hδ, hEq⟩ := hf.time_equation
  have hδcont := continuous_clamped_of_continuousOn_lift t δ hδc
  have hδbd : ∀ p : ℝ × PeriodicTorus ι, |δ (periodicClamp t p.1) p.2| ≤ Cδ := fun p =>
    hCδ _ (periodicClamp_mem ht0 _) _
  -- the clamped narrowly continuous path
  let μ' : ℝ → ProbabilityMeasure (PeriodicTorus ι) := fun r => μ (periodicClamp t r)
  have hμ' : Continuous μ' :=
    hμ.comp_continuous (continuous_periodicClamp t) (fun r => hIcc _ (periodicClamp_mem ht0 r))
  have hμ'e : ∀ r ∈ Icc 0 (t : ℝ),
      (μ' r : Measure (PeriodicTorus ι)) = periodicCappedDensityMeasure (ρ r) := by
    intro r hr
    show (μ (periodicClamp t r) : Measure (PeriodicTorus ι)) = _
    rw [periodicClamp_eq hr]
    exact hρμ r (hIcc r hr)
  obtain ⟨Cs, hCs0, hCs⟩ := periodicStaticMeanTestDrift_bound D β M hM
  obtain ⟨Cs', hCs'0, hCs'⟩ := periodicStaticMeanTestDrift_sub_le D β M hM
  let H : ℝ → ℝ → ℝ := fun r s => ∫ z, f s z ∂periodicCappedDensityMeasure (ρ r)
  let a : ℝ → ℝ → ℝ := fun u s => periodicStaticMeanTestDrift D.F β (ρ u) (f s)
  let b : ℝ → ℝ → ℝ := fun r v => ∫ z, δ (periodicClamp t v) z ∂(μ' r : Measure (PeriodicTorus ι))
  have ha_int : ∀ s ∈ Icc 0 (t : ℝ), IntervalIntegrable (fun u => a u s) volume 0 (t : ℝ) := by
    intro s hs
    refine ((hstat (f s) (hf.spatial_contdiff s hs)).1).mono_set ?_
    rw [uIcc_of_le ht0, uIcc_of_le hT0]
    exact Icc_subset_Icc le_rfl htR
  have hHr : ∀ s ∈ Icc 0 (t : ℝ), ∀ r ∈ Icc 0 (t : ℝ), ∀ r' ∈ Icc 0 (t : ℝ),
      H r s - H r' s = ∫ u in r'..r, a u s := by
    intro s hs r hr r' hr'
    obtain ⟨hi, he⟩ := hstat (f s) (hf.spatial_contdiff s hs)
    have e1 := he r (hIcc r hr)
    have e2 := he r' (hIcc r' hr')
    have hsub : ∀ x ∈ Icc 0 (t : ℝ), IntervalIntegrable (fun u => a u s) volume 0 x := by
      intro x hx
      refine hi.mono_set ?_
      rw [uIcc_of_le hx.1, uIcc_of_le hT0]
      exact Icc_subset_Icc le_rfl (hx.2.trans htR)
    have := intervalIntegral.integral_interval_sub_left (hsub r hr) (hsub r' hr')
    change (∫ z, f s z ∂periodicCappedDensityMeasure (ρ r)) -
      (∫ z, f s z ∂periodicCappedDensityMeasure (ρ r')) = _
    linarith
  have hb' : ContinuousOn (fun p : ℝ × ℝ => b p.1 p.2) (Icc 0 (t : ℝ) ×ˢ Icc 0 (t : ℝ)) :=
    (continuous_integral_moving_probability (fun p : ℝ × ℝ => p.2) continuous_snd
      (fun p : ℝ × ℝ => μ' p.1) (hμ'.comp continuous_fst)
      (fun q : ℝ × PeriodicTorus ι => δ (periodicClamp t q.1) q.2) hδcont Cδ hδbd).continuousOn
  have hHs_le : ∀ r ∈ Icc 0 (t : ℝ), ∀ s ∈ Icc 0 (t : ℝ), ∀ s' ∈ Icc 0 (t : ℝ), s' ≤ s →
      H r s - H r s' = ∫ v in s'..s, b r v := by
    intro r hr s hs s' hs' hle
    haveI := hprob r (hIcc r hr)
    have := periodic_pairing_slice hf δ hδc Cδ hCδ hδ (periodicCappedDensityMeasure (ρ r)) hs hs' hle
    change (∫ z, f s z ∂periodicCappedDensityMeasure (ρ r)) -
      (∫ z, f s' z ∂periodicCappedDensityMeasure (ρ r)) = _
    rw [this]
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    show _ = ∫ z, δ (periodicClamp t v) z ∂(μ' r : Measure (PeriodicTorus ι))
    rw [hμ'e r hr]
  have hHs : ∀ r ∈ Icc 0 (t : ℝ), ∀ s ∈ Icc 0 (t : ℝ), ∀ s' ∈ Icc 0 (t : ℝ),
      H r s - H r s' = ∫ v in s'..s, b r v := by
    intro r hr s hs s' hs'
    rcases le_total s' s with h | h
    · exact hHs_le r hr s hs s' hs' h
    · have := hHs_le r hr s' hs' s hs h
      rw [intervalIntegral.integral_symm]
      linarith
  have haA : ∀ u ∈ Icc 0 (t : ℝ), ∀ s ∈ Icc 0 (t : ℝ), |a u s| ≤ Cs * C := by
    intro u hu s hs
    exact hCs (ρ u) (hρ u (hIcc u hu)) (hprob u (hIcc u hu)) (f s) (hf.spatial_contdiff s hs) C hC0
      (fun x => (hb s hs x).2.2)
  have hauc : ∀ ε > 0, ∃ η > 0, ∀ u ∈ Icc 0 (t : ℝ), ∀ s ∈ Icc 0 (t : ℝ), ∀ s' ∈ Icc 0 (t : ℝ),
      |s - s'| < η → |a u s - a u s'| ≤ ε := by
    intro ε hε
    have hpos : 0 < ε / (Cs' + 1) := by positivity
    obtain ⟨η, hη, hH⟩ := hessian_uniformly_continuous_in_time t f hf.hessian_continuous _ hpos
    refine ⟨η, hη, fun u hu s hs s' hs' hss => ?_⟩
    have h1 := hCs' (ρ u) (hρ u (hIcc u hu)) (hprob u (hIcc u hu)) (f s) (f s')
      (hf.spatial_contdiff s hs) (hf.spatial_contdiff s' hs') _ hpos.le
      (fun x => (hH s hs s' hs' hss x).le)
    refine h1.trans ?_
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨hI, hE⟩ := two_parameter_chain_rule (t : ℝ) ht0 H a b (Cs * C) ha_int hHr hb' hHs haA hauc
  -- identification of the integrand
  have hdiag : ∀ u ∈ Ioo 0 (t : ℝ),
      periodicMeanTestDrift D.F β (ρ u) f u = a u u + b u u := by
    intro u hu
    have hu' : u ∈ Icc 0 (t : ℝ) := ⟨hu.1.le, hu.2.le⟩
    haveI := hprob u (hIcc u hu')
    have hder : ∀ z, deriv (fun s => f s z) u = δ (periodicClamp t u) z := fun z => by
      rw [periodicClamp_eq hu', (hδ u hu z).deriv]
    have hδi : Integrable (fun z => δ (periodicClamp t u) z) (periodicCappedDensityMeasure (ρ u)) := by
      refine (integrable_const Cδ).mono' ?_ (ae_of_all _ fun z => ?_)
      · exact (hδcont.comp (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable
      · simpa only [Real.norm_eq_abs] using hδbd (u, z)
    have hlap := periodic_lap_integrable (hf.spatial_contdiff u hu') (periodicCappedDensityMeasure (ρ u))
    have hbu : b u u = ∫ z, δ (periodicClamp t u) z ∂periodicCappedDensityMeasure (ρ u) := by
      show ∫ z, δ (periodicClamp t u) z ∂(μ' u : Measure (PeriodicTorus ι)) = _
      rw [hμ'e u hu']
    unfold periodicMeanTestDrift
    simp only [hder]
    rw [integral_add hδi (hlap.const_mul β⁻¹), integral_const_mul]
    change _ = periodicStaticMeanTestDrift D.F β (ρ u) (f u) + b u u
    rw [hbu]
    unfold periodicStaticMeanTestDrift
    ring
  have hrhs : ∫ r in Ioc 0 (t : ℝ), periodicMeanTestDrift D.F β (ρ r) f r =
      ∫ u in (0 : ℝ)..t, (a u u + b u u) := by
    rw [intervalIntegral.integral_of_le ht0]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne (t : ℝ))] with r hr hrt
    exact hdiag r ⟨hr.1, lt_of_le_of_ne hr.2 hrt⟩
  rw [hrhs]
  exact hE

end DGRHS.Periodic
