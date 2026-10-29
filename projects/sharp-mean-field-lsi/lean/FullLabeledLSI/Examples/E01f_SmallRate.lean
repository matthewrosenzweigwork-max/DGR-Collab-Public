import FullLabeledLSI.Examples.Paper.Sec9SmallRateA
import FullLabeledLSI.Examples.Paper.Sec9SmallRateB
import FullLabeledLSI.Examples.Paper.Sec9SmallRateC

/-!
# Lemma 9.6 (`harmonic_small_rate_uniqueness`), lane C

Assembly.  `sMin_unique_of_small`: two minimizers of `S_{r,A}` with `|A| ≤ R`, `0 ≤ r ≤ 1` and
`r M² < 4π² c²` agree a.e. (`c = exp(-(1+R))`, `M = 1 + √R + R`).  `harmonic_small_rate_uniqueness`
(namespace `SharpLSI.FL.Ex.LaneC`, same statement as E01) follows since a compact set of continuous
potentials is bounded, and minimizers exist by `exists_sMin`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI.FL.Ex.LaneC

open SharpLSI FL.Ex.Reg FL.Ex.SR

theorem periodic_le_of_ae {F : ℝ → ℝ} (hc : Continuous F) (hp : Function.Periodic F 1)
    {u : Torus 1 → ℝ} (hae : (fun y => F (secT y 0)) =ᵐ[haar 1] u) {K : ℝ}
    (hu : ∀ᵐ y ∂haar 1, u y ≤ K) : ∀ x, F x ≤ K := by
  have h1 : ∀ᵐ y ∂haar 1, F (secT y 0) ≤ K := by
    filter_upwards [hae, hu] with y h1 h2
    rw [h1]; exact h2
  have h2 := ae_real_of_ae_torus h1
  have h3 : ∀ᵐ s : ℝ, 0 ≤ K - F s := by
    filter_upwards [h2] with s hs
    rw [F_secT_lineT hp] at hs
    linarith
  intro x
  have := nonneg_of_continuous_ae (f := fun x => K - F x) (continuous_const.sub hc) h3 x
  linarith

/-- Regular representative data of a minimizer, in the form needed for uniqueness. -/
theorem sMin_ode_data {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {A : Torus 1 → ℝ} (hA : Continuous A)
    {R : ℝ} (hR : ∀ x, |A x| ≤ R) {f : Torus 1 → ℝ} (hf : IsSMin r A f) :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ Function.Periodic F 1 ∧ (∀ x, 0 < F x) ∧
      (∀ x, deriv (deriv F) x =
        F x * ((A (lineT x) - sFunctional r A f) / 4 - r * Real.log (F x))) ∧
      (∫ x in (0 : ℝ)..1, F x ^ 2 = 1) ∧
      (∀ x, F x ≤ 1 + (Real.sqrt R + R)) ∧ (fun y => F (secT y 0)) =ᵐ[haar 1] f := by
  obtain ⟨hlo, hhi, hW, hsup⟩ := sMin_bounds hr0 hr1 hA hR hf
  obtain ⟨u, hu, hu0, huH, hu1, hweak⟩ := sMin_weakEL hA hf
  obtain ⟨F, hF2, hp, hpos, hode, -, hae⟩ := weakEL_master hr0 hA hu0 huH hu1 hweak
  have hFc : Continuous F := (hF2.continuous)
  refine ⟨F, hF2, hp, hpos, hode, ?_, ?_, hae.trans hu⟩
  · rw [← integral_torus_eq (G := fun t => F t ^ 2) (hFc.pow 2) (fun t => by simp [hp t])]
    refine Eq.trans ?_ hu1
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    simp only [hy]
  · refine periodic_le_of_ae hFc hp hae ?_
    filter_upwards [hsup, hu] with y h1 h2
    rw [h2]; exact h1

theorem sMin_unique_of_small {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {A : Torus 1 → ℝ}
    (hA : Continuous A) {R : ℝ} (hR : ∀ x, |A x| ≤ R)
    (hsmall : r * (1 + (Real.sqrt R + R)) ^ 2 < 4 * π ^ 2 * (Real.exp (-(1 + R))) ^ 2)
    {f g : Torus 1 → ℝ} (hf : IsSMin r A f) (hg : IsSMin r A g) : g =ᵐ[haar 1] f := by
  have hηeq : sFunctional r A g = sFunctional r A f :=
    le_antisymm (hg.2.2.2 f hf.1 hf.2.1 hf.2.2.1) (hf.2.2.2 g hg.1 hg.2.1 hg.2.2.1)
  obtain ⟨hlo, -, -, -⟩ := sMin_bounds hr0 hr1 hA hR hf
  obtain ⟨F, hF2, hFp, hFpos, hFode, hFm, hFM, hFae⟩ := sMin_ode_data hr0 hr1 hA hR hf
  obtain ⟨G, hG2, hGp, hGpos, hGode, hGm, hGM, hGae⟩ := sMin_ode_data hr0 hr1 hA hR hg
  rw [hηeq] at hGode
  set η := sFunctional r A f with hη
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR (0 : Torus 1))
  have hB : ∀ x, (A (lineT x) - η) / 4 ≤ R / 2 := fun x => by
    have := (abs_le.1 (hR (lineT x))).2
    linarith
  have hd1 : ∀ {H : ℝ → ℝ}, ContDiff ℝ 2 H → ∀ x, HasDerivAt H (deriv H x) x :=
    fun hH x => ((hH.differentiable (by norm_num)) x).hasDerivAt
  have hd2 : ∀ {H : ℝ → ℝ}, ContDiff ℝ 2 H → ∀ x, HasDerivAt (deriv H) (deriv (deriv H) x) x :=
    fun hH x => (((contDiff_one_deriv_of_two hH).differentiable one_ne_zero) x).hasDerivAt
  have hd2c : ∀ {H : ℝ → ℝ}, ContDiff ℝ 2 H → Continuous (deriv (deriv H)) :=
    fun hH => (contDiff_one_iff_deriv.1 (contDiff_one_deriv_of_two hH)).2
  have hFlow := min_lower_bound hR0 hr0 hr1 (hd1 hF2) (hd2 hF2) hFpos hFp hFode hB hFm
  have hGlow := min_lower_bound hR0 hr0 hr1 (hd1 hG2) (hd2 hG2) hGpos hGp hGode hB hGm
  have hc : 0 < Real.exp (-(1 + R)) := Real.exp_pos _
  have hFG := periodic_unique hc hr0 hsmall (hd1 hF2) (hd2 hF2) (hd1 hG2) (hd2 hG2)
    (hd2c hF2) (hd2c hG2) hFp hGp hFlow hGlow hFM hGM hFode hGode hFm hGm
  have h1 : (fun y => F (secT y 0)) =ᵐ[haar 1] (fun y => G (secT y 0)) := by
    rw [hFG]
  exact (hGae.symm.trans (h1.symm.trans hFae))

/-- **Lemma 9.6** (statement identical to `SharpLSI.FL.Ex.harmonic_small_rate_uniqueness` of E01). -/
theorem harmonic_small_rate_uniqueness (𝒜 : Set C(Torus 1, ℝ)) (h𝒜 : IsCompact 𝒜) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ A ∈ 𝒜, ∀ r : ℝ, 0 ≤ r → r < ε →
      ∃ f : Torus 1 → ℝ, IsSMin r (fun x => A x) f ∧
        ∀ g : Torus 1 → ℝ, IsSMin r (fun x => A x) g → g =ᵐ[haar 1] f := by
  obtain ⟨R0, hR0⟩ := isBounded_iff_forall_norm_le.1 h𝒜.isBounded
  set R : ℝ := max R0 0 with hRdef
  have hR : ∀ A ∈ 𝒜, ∀ x, |A x| ≤ R := fun A hA x => by
    have h1 : ‖A x‖ ≤ ‖A‖ := A.norm_coe_le_norm x
    have h2 := hR0 A hA
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (h2.trans (le_max_left _ _))
  have hR0' : 0 ≤ R := le_max_right _ _
  set c : ℝ := Real.exp (-(1 + R)) with hc
  set M : ℝ := 1 + (Real.sqrt R + R) with hM
  have hcpos : 0 < c := Real.exp_pos _
  set δ : ℝ := 4 * π ^ 2 * c ^ 2 / (M ^ 2 + 1) with hδ
  have hδpos : 0 < δ := by positivity
  refine ⟨min 1 δ, lt_min one_pos hδpos, fun A hA r hr0 hr => ?_⟩
  have hr1 : r < 1 := lt_of_lt_of_le hr (min_le_left _ _)
  have hrδ : r < δ := lt_of_lt_of_le hr (min_le_right _ _)
  have hAc : Continuous (fun x => A x) := A.continuous
  have hsmall : r * M ^ 2 < 4 * π ^ 2 * c ^ 2 := by
    rw [hδ, lt_div_iff₀ (by positivity)] at hrδ
    nlinarith [sq_nonneg M]
  obtain ⟨f, hf⟩ := exists_sMin hr0 hr1.le hAc
  exact ⟨f, hf, fun g hg => sMin_unique_of_small hr0 hr1.le hAc (hR A hA) hsmall hf hg⟩

end SharpLSI.FL.Ex.LaneC
