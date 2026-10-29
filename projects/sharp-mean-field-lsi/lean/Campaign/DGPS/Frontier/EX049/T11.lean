import DGPS.Frontier.EX049.T04
import DGPS.Frontier.EX049.T10

/-!
# EX049.11: Haar entropy with a small energy coefficient

Task id: EX049.11. Title: Haar entropy with a small energy coefficient.

For every real angular `H^1` function `w` on the circle `AngCircle`, with Haar probability
measure `angHaar`, and every `0 < δ ≤ 1`, the Haar entropy `entEX04910 angHaar (fun x => w x ^ 2)`
is at most `δ ∫ g ^ 2 ∂angHaar + [log (2 + 8π²) + log (1 / δ)] ∫ w ^ 2 ∂angHaar`, for every
angular weak derivative `g` of `w`.

Provides:
* `DGPS.Frontier.EX049.ex049_11_haar_entropy_small_energy_coefficient`: the main estimate.
* `DGPS.Frontier.EX049.log_one_add_le_EX04911`: `log (1 + x) ≤ δ x + log (1 / δ)` for `x ≥ 0`
  and `0 < δ ≤ 1`.
* `DGPS.Frontier.EX049.ent_congr_EX04911`: the entropy of the square depends only on the almost
  everywhere class of the function.
* `DGPS.Frontier.EX049.core_EX04911`: the unnormalized entropy bound for a measurable function
  whose square is bounded pointwise by `2M + 8π² T`, where `M` is its mass and `T` an energy.

R5 notes:
* Angular `H^1` is the campaign predicate `AngularH1`, and the weak derivative is the campaign
  predicate `IsAngularWeakDeriv`, both from `DGPS.Circle.AngularNormalization`. Their binding to
  the source objects is the open task EX049.25; this file does not claim it.
* The conclusion is quantified over every weak derivative `g` of `w`, not over one chosen
  derivative. This is at least as strong as the specification's `∫ (w')^2` read for any single
  derivative, so it does not weaken the statement.
* `δ` is an explicit real argument with the hypotheses `0 < δ` and `δ ≤ 1`, matching `0 < δ ≤ 1`.
* `Ent_m` is `entEX04910 angHaar`, with `0 log 0 = 0` realized by `Real.log 0 = 0` as in EX049.10.
  The constant `log D` with `D = 2 + 8π²` is written `Real.log (2 + 8 * π ^ 2)`.
* Non-literal reading (route): the specification's proof divides `w` by the square root of its
  mass. This file does not normalize. It uses the unnormalized bound
  `Ent ≤ M log ((2M + 8π² T) / M)` from EX049.10 with `T` the energy, and the inequality
  `log (1 + x) ≤ δ x + log (1 / δ)` at `x = T / M`. Both routes give the same estimate.
* Non-literal reading (representative): the pointwise bound is proved for the continuous
  representative `v` of `w` supplied by EX049.04. Entropy and mass are invariant under almost
  everywhere equality (`ent_congr_EX04911`), so the conclusion transfers to `w`.
* The pointwise bound uses `⨆ θ, |v θ|`, which is finite because the range of the continuous
  function `|v|` on the compact circle is bounded above.
* Zero mass is a separate branch, handled by the zero-mass clause of EX049.10, as in the
  specification's proof.
-/

namespace DGPS.Frontier.EX049

open MeasureTheory Real
open DGPS.Circle.AngularNormalization

/-- The scalar bound `log (1 + x) ≤ δ x + log (1 / δ)` for `x ≥ 0` and `0 < δ ≤ 1`, from the
tangent inequality `log t ≤ t - 1` at `t = δ (1 + x)`. -/
lemma log_one_add_le_EX04911 {x δ : ℝ} (hx : 0 ≤ x) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.log (1 + x) ≤ δ * x + Real.log (1 / δ) := by
  have hpos : 0 < δ * (1 + x) := mul_pos hδ0 (by linarith)
  have h1 : Real.log (δ * (1 + x)) ≤ δ * (1 + x) - 1 := Real.log_le_sub_one_of_pos hpos
  have h2 : Real.log (δ * (1 + x)) = Real.log δ + Real.log (1 + x) :=
    Real.log_mul hδ0.ne' (by linarith : (0 : ℝ) < 1 + x).ne'
  have h3 : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
  linarith

/-- The entropy of the square depends only on the almost everywhere class of the function. -/
lemma ent_congr_EX04911 (ν : Measure AngCircle) {v w : AngCircle → ℝ} (h : v =ᵐ[ν] w) :
    entEX04910 ν (fun x => v x ^ 2) = entEX04910 ν (fun x => w x ^ 2) := by
  have h1 : ∫ x, v x ^ 2 ∂ν = ∫ x, w x ^ 2 ∂ν :=
    integral_congr_ae (by filter_upwards [h] with x hx; simp only [hx])
  have h2 : ∫ x, v x ^ 2 * Real.log (v x ^ 2) ∂ν = ∫ x, w x ^ 2 * Real.log (w x ^ 2) ∂ν :=
    integral_congr_ae (by filter_upwards [h] with x hx; simp only [hx])
  simp only [entEX04910]
  rw [h1, h2]

/-- The entropy bound for a measurable `v` with mass `∫ v ^ 2 = M` and pointwise bound
`v ^ 2 ≤ 2M + 8π² T`: the entropy of `v ^ 2` is at most `δ T + [log (2 + 8π²) + log (1 / δ)] M`.
The zero-mass branch uses EX049.10; the positive-mass branch uses EX049.10 and the scalar bound. -/
lemma core_EX04911 (ν : Measure AngCircle) [IsProbabilityMeasure ν] {v : AngCircle → ℝ}
    (hv : Measurable v) {M T δ : ℝ} (hM0 : 0 ≤ M) (hT : 0 ≤ T)
    (hM : ∫ x, v x ^ 2 ∂ν = M) (hS : ∀ x, v x ^ 2 ≤ 2 * M + 8 * π ^ 2 * T)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    entEX04910 ν (fun x => v x ^ 2) ≤
      δ * T + (Real.log (2 + 8 * π ^ 2) + Real.log (1 / δ)) * M := by
  rcases hM0.eq_or_lt with h0 | hpos
  · subst h0
    rw [ent_eq_zero_EX04910 ν hv hS hM, mul_zero, add_zero]
    exact mul_nonneg hδ0.le hT
  · have hpos' : 0 < ∫ x, v x ^ 2 ∂ν := by rw [hM]; exact hpos
    obtain ⟨-, hent⟩ := ent_le_EX04910 ν hv hS hpos'
    rw [hM] at hent
    have hMne : M ≠ 0 := hpos.ne'
    have hratio : (2 * M + 8 * π ^ 2 * T) / M = 2 + 8 * π ^ 2 * (T / M) := by
      field_simp
    have hTM : 0 ≤ T / M := div_nonneg hT hM0
    have hle : 2 + 8 * π ^ 2 * (T / M) ≤ (2 + 8 * π ^ 2) * (1 + T / M) := by
      nlinarith [sq_nonneg π]
    have hposL : 0 < 2 + 8 * π ^ 2 * (T / M) := by
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ 8 * π ^ 2) hTM
      linarith
    have hlog1 : Real.log (2 + 8 * π ^ 2 * (T / M)) ≤ Real.log ((2 + 8 * π ^ 2) * (1 + T / M)) :=
      Real.log_le_log hposL hle
    have hlog2 : Real.log ((2 + 8 * π ^ 2) * (1 + T / M))
        = Real.log (2 + 8 * π ^ 2) + Real.log (1 + T / M) :=
      Real.log_mul (by positivity) (by linarith : (0 : ℝ) < 1 + T / M).ne'
    have hlog3 : Real.log (1 + T / M) ≤ δ * (T / M) + Real.log (1 / δ) :=
      log_one_add_le_EX04911 hTM hδ0 hδ1
    have hfinal : M * Real.log ((2 * M + 8 * π ^ 2 * T) / M)
        ≤ M * (Real.log (2 + 8 * π ^ 2) + (δ * (T / M) + Real.log (1 / δ))) := by
      rw [hratio]
      refine mul_le_mul_of_nonneg_left ?_ hM0
      linarith
    have hkey : M * (δ * (T / M)) = δ * T := by
      field_simp
    linarith [hent, hfinal, hkey]

/-- The main estimate: for every real angular `H^1` function `w`, every weak angular derivative `g`
of `w`, and every `0 < δ ≤ 1`, the Haar entropy of `w ^ 2` is at most
`δ ∫ g ^ 2 + [log (2 + 8π²) + log (1 / δ)] ∫ w ^ 2`. -/
theorem ex049_11_haar_entropy_small_energy_coefficient (w : AngCircle → ℝ) (hw : AngularH1 w)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ g : AngCircle → ℝ, IsAngularWeakDeriv w g →
      entEX04910 angHaar (fun x => w x ^ 2) ≤
        δ * (∫ θ, g θ ^ 2 ∂angHaar) +
          (Real.log (2 + 8 * π ^ 2) + Real.log (1 / δ)) * (∫ θ, w θ ^ 2 ∂angHaar) := by
  intro g hg
  obtain ⟨v, hvc, hvw, -, hall⟩ := ex049_04_explicit_angular_sobolev_supremum_estimate w hw
  obtain ⟨hsup, -⟩ := hall g hg
  have hbdd : BddAbove (Set.range fun θ => |v θ|) := (isCompact_range hvc.abs).bddAbove
  have hpt : ∀ x, v x ^ 2 ≤ 2 * (∫ θ, w θ ^ 2 ∂angHaar) + 8 * π ^ 2 * (∫ θ, g θ ^ 2 ∂angHaar) := by
    intro x
    have h1 : |v x| ≤ ⨆ θ, |v θ| := le_ciSup hbdd x
    have h2 : |v x| ^ 2 ≤ (⨆ θ, |v θ|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs] at h2
    linarith
  have hMnn : 0 ≤ ∫ θ, w θ ^ 2 ∂angHaar := integral_nonneg fun θ => sq_nonneg _
  have hTnn : 0 ≤ ∫ θ, g θ ^ 2 ∂angHaar := integral_nonneg fun θ => sq_nonneg _
  have hMv : ∫ x, v x ^ 2 ∂angHaar = ∫ θ, w θ ^ 2 ∂angHaar :=
    integral_congr_ae (by filter_upwards [hvw] with x hx; simp only [hx])
  rw [← ent_congr_EX04911 angHaar hvw]
  exact core_EX04911 angHaar hvc.measurable hMnn hTnn hMv hpt hδ0 hδ1

end DGPS.Frontier.EX049
