import DGPS.Lipschitz.T01BoundedDilution
import FullLabeledLSI.Paper.Sec3DiluteD
import DGPS.Analysis.LSITensorization

/-!
# The species rate below the minimizing reference's ordinary LSI rate

Only the assumption-clean truncation, entropy Fatou, and weighted Sobolev lemmas from the
legacy library are used. The actual binary family is constructed in the campaign domain.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- Every minimizing positive-Lipschitz Gibbs reference bounds the species rate from above. -/
theorem t01_speciesRate_le_ordinaryLSRate (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) {μ : ProbabilityMeasure (Torus d)}
    (hμ : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A) :
    speciesRate A b ≤ ordinaryLSRate (frozenGibbs A μ) := by
  classical
  let P := frozenGibbs A μ
  have hP := frozenGibbs_hasPositiveLipschitzDensity A hLip μ
  have hbd : ∀ x, Real.exp (-(2 * frozenSupBound A)) ≤ P.density x ∧
      P.density x ≤ Real.exp (2 * frozenSupBound A) := frozenDensity_bounds A _
  have legacyH1 {f : Torus d → ℝ} (hf : f ∈ WeightedH1 P) : SharpLSI.MemH1 P.measure f := by
    obtain ⟨G, hG⟩ := hf
    obtain ⟨hHaar, -⟩ := Analysis.legacy_memH1 ((isWeightedWeakGradient_iff P).mp hG)
    exact ⟨hHaar.1, P.memLp_measure_iff.mpr hHaar.2.1, P.memLp_measure_iff.mpr hHaar.2.2⟩
  have entFinite {f : Torus d → ℝ} (hf : f ∈ WeightedH1 P) :
      homogeneousEntropy P.measure (fun x => f x ^ 2) ≠ ⊤ := by
    rw [FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent hf.choose_spec.memLp.integrable_sq]
    exact SharpLSI.FL.ent_sq_ne_top (Real.exp_pos _) hbd P.mass_one P.measurable_density (legacyH1 hf)
  unfold ordinaryLSRate
  refine le_iInf fun f => ?_
  have hf := f.2.1
  have hw := (isWeightedWeakGradient_iff P).mp
    (isWeightedWeakGradient_weightedGradient P hf)
  obtain ⟨hhaar, hlegacyGrad⟩ := Analysis.legacy_memH1 hw
  let E := ∫ x, ‖weightedGradient P f.1 hf x‖ ^ 2 ∂P.measure
  let H := (homogeneousEntropy P.measure (fun x => f.1 x ^ 2)).toReal
  have hHfin := entFinite hf
  have hHe : homogeneousEntropy P.measure (fun x => f.1 x ^ 2) = ENNReal.ofReal H :=
    (ENNReal.ofReal_toReal hHfin).symm
  have hH0 : 0 < H := ENNReal.toReal_pos f.2.2.ne' hHfin
  have hE0 : 0 ≤ E := integral_nonneg fun x => sq_nonneg _
  have hEe : (∫⁻ x, ‖weightedGradient P f.1 hf x‖ₑ ^ 2 ∂P.measure) = ENNReal.ofReal E := by
    dsimp only [E]
    symm
    rw [ofReal_integral_eq_lintegral_ofReal
      (isWeightedWeakGradient_weightedGradient P hf).memLp_grad.norm.integrable_sq
      (Eventually.of_forall fun x => sq_nonneg _)]
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [hEe, hHe, show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_div_of_pos hH0]
  let t := 2 * E / H
  have ht0 : 0 ≤ t := by positivity
  refine ENNReal.le_of_forall_pos_le_add fun η' hη' _ => ?_
  let η : ℝ := η'
  have hη : 0 < η := by exact_mod_cast hη'
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add ht0 hη.le]
  let κ := η / (2 * (t + 1))
  have hκ0 : 0 < κ := by positivity
  have hthreshold : ENNReal.ofReal (H / (1 + κ)) <
      SharpLSI.ent P.measure (fun x => f.1 x ^ 2) := by
    rw [← FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent hf.choose_spec.memLp.integrable_sq, hHe,
      ENNReal.ofReal_lt_ofReal_iff hH0]
    exact div_lt_self hH0 (by linarith)
  have hev := Filter.eventually_lt_of_lt_liminf
    (hthreshold.trans_le (SharpLSI.FL.ent_le_liminf_trunc (P := P.measure) hf.choose_spec.memLp))
  obtain ⟨n, hn1, hn⟩ := ((eventually_ge_atTop 1).and hev).exists
  let M : ℝ := n
  have hM0 : 0 < M := by change (0 : ℝ) < (n : ℝ); exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  obtain ⟨G, hG, hGj, hGbound⟩ := SharpLSI.FL.exists_trunc_grad hhaar M
  let g : Torus d → ℝ := fun x => min |f.1 x| M
  have hg0 : ∀ x, 0 ≤ g x := fun x => le_min (abs_nonneg _) hM0.le
  have hgM : ∀ x, |g x| ≤ M := fun x => by
    rw [abs_of_nonneg (hg0 x)]
    exact min_le_right _ _
  have hgL2 : MemLp g 2 (haar d) := MemLp.of_bound hG.aestronglyMeasurable_fun M
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hgM x)
  have hgW := isWeakGradient_of_legacy_pair hG hgL2 (memLp_piLp_iff.mpr hGj)
  have hg : g ∈ WeightedH1 P := (mem_weightedH1_iff P).mpr ⟨_, hgW⟩
  have hgnfin := entFinite hg
  let Hn := (homogeneousEntropy P.measure (fun x => g x ^ 2)).toReal
  have hHne : homogeneousEntropy P.measure (fun x => g x ^ 2) = ENNReal.ofReal Hn :=
    (ENNReal.ofReal_toReal hgnfin).symm
  have hn' : H / (1 + κ) < Hn ∧ 0 < Hn := by
    rw [← FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent hg.choose_spec.memLp.integrable_sq,
      hHne, ENNReal.ofReal_lt_ofReal_iff'] at hn
    exact hn
  have hEg : ∫ x, ‖weightedGradient P g hg x‖ ^ 2 ∂P.measure ≤ E := by
    have hrep : weightedGradient P g hg =ᵐ[P.measure] (fun x => WithLp.toLp 2 (G x)) :=
      P.measure_ac_haar.ae_le (weightedGradient_ae_eq P hg hgW)
    have hFrep : SharpLSI.weakGrad f.1 =ᵐ[P.measure]
        (fun x j => weightedGradient P f.1 hf x j) := P.measure_ac_haar.ae_le hlegacyGrad
    apply integral_mono_ae
      (isWeightedWeakGradient_weightedGradient P hg).memLp_grad.norm.integrable_sq
      (isWeightedWeakGradient_weightedGradient P hf).memLp_grad.norm.integrable_sq
    filter_upwards [hrep, hFrep] with x hx hfx
    rw [hx, Analysis.norm_sq_eq_sqNorm]
    have hb := hGbound x
    rw [hfx, ← Analysis.norm_sq_eq_sqNorm] at hb
    exact hb
  let Z := ∫ x, g x ^ 2 ∂P.measure
  have hZ0 : 0 < Z := by
    by_contra hz
    have hz0 : Z = 0 := le_antisymm (not_lt.mp hz) (integral_nonneg fun x => sq_nonneg _)
    have hEnt0 := homogeneousEntropy_of_integral_eq_zero (P := P.measure) (v := fun x => g x ^ 2) hz0
    rw [hEnt0] at hHne
    exact (not_le_of_gt hn'.2) (by simpa using hHne.symm)
  have hrate := t01_speciesRate_le_bounded_test A hLip b hμ hg hg0 hgM
    (a := 1 / Z) (by positivity) (by change 1 / Z * Z = 1; field_simp)
    hHne hn'.2
  refine hrate.trans (ENNReal.ofReal_le_ofReal ?_)
  have hcmp : 2 * E / Hn ≤ (1 + κ) * t := by
    calc 2 * E / Hn ≤ 2 * E / (H / (1 + κ)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hn'.1.le
      _ = (1 + κ) * t := by dsimp only [t]; field_simp
  have hκt : κ * t ≤ η / 2 := by
    dsimp only [κ]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hη.le ht0]
  have hcmpg : 2 * (∫ x, ‖weightedGradient P g hg x‖ ^ 2 ∂P.measure) / Hn ≤ 2 * E / Hn :=
    div_le_div_of_nonneg_right (by linarith) hn'.2.le
  nlinarith

end DGPS.Lipschitz
