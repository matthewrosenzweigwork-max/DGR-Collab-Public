import DGPS.Foundations.AbsoluteDensity
import DGPS.Foundations.RelativeEntropy
import DGPS.Foundations.SobolevEmbedding
import DGPS.Foundations.Torus

/-!
# Finite entropy on every absolute Sobolev competitor (DEF006)

For every absolute-admissible density `ρ = u²` (`u ∈ H¹(m)`), `ρ log ρ` is `m`-integrable (so
is `|ρ log ρ|`), `H(ρ m | m)` is finite, and `(H(ρ m | m)).toReal = ∫ ρ log ρ dm`. The same
holds for every finite species family. The integrability is the FOU006 entropy-integrability
clause, valid in every dimension; no hypothesis `1 ≤ d` is needed.
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS

variable {d : ℕ}

/-- `ρ log ρ = u² log u²` is integrable for an absolute-admissible `ρ = u²` (FOU006 adapter). -/
theorem AbsoluteDensity.integrable_density_mul_log (ρ : AbsoluteDensity d) :
    Integrable (fun x => ρ.density x * Real.log (ρ.density x)) (haar d) :=
  Analysis.periodic_sobolev_embeddings_and_entropy_integrability.2.2.2.1 d ρ.sqrt ρ.sqrt_mem

/-- Finite entropy: `ρ log ρ` is integrable and `H(ρ m | m)` is finite and equals `∫ ρ log ρ`. -/
theorem absoluteDensity_entropy_finite (ρ : AbsoluteDensity d) :
    Integrable (fun x => ρ.density x * Real.log (ρ.density x)) (haar d) ∧
    Integrable (fun x => |ρ.density x * Real.log (ρ.density x)|) (haar d) ∧
    relativeEntropy (densityMeasure ρ) (haar d) ≠ ⊤ ∧
    (relativeEntropy (densityMeasure ρ) (haar d)).toReal =
      ∫ x, ρ.density x * Real.log (ρ.density x) ∂haar d := by
  have hlog := ρ.integrable_density_mul_log
  have hint := ρ.integrable_density
  have hF : Integrable (fun x => ρ.density x * Real.log (ρ.density x) - ρ.density x + 1)
      (haar d) := (hlog.sub hint).add (integrable_const 1)
  have hnn : 0 ≤ᵐ[haar d] fun x => ρ.density x * Real.log (ρ.density x) - ρ.density x + 1 :=
    Filter.Eventually.of_forall fun x => self_mul_log_sub_add_one_nonneg (ρ.density_nonneg x)
  have hE : ∫ x, (ρ.density x * Real.log (ρ.density x) - ρ.density x + 1) ∂haar d =
      ∫ x, ρ.density x * Real.log (ρ.density x) ∂haar d := by
    have h2 : Integrable (fun x => ρ.density x * Real.log (ρ.density x) - ρ.density x)
        (haar d) := hlog.sub hint
    rw [integral_add h2 (integrable_const (1 : ℝ)), integral_sub hlog hint,
      ρ.integral_density]
    simp
  have hH : relativeEntropy (densityMeasure ρ) (haar d) =
      ENNReal.ofReal (∫ x, ρ.density x * Real.log (ρ.density x) ∂haar d) := by
    have h1 : relativeEntropy (densityMeasure ρ) (haar d) = homogeneousEntropy (haar d) ρ.density :=
      relativeEntropy_withDensity (Filter.Eventually.of_forall ρ.density_nonneg)
        hint.aestronglyMeasurable.aemeasurable
    rw [h1, entropy_mass_one ρ.integral_density,
      ← ofReal_integral_eq_lintegral_ofReal hF hnn]
    rw [hE]
  have hnn' : 0 ≤ ∫ x, ρ.density x * Real.log (ρ.density x) ∂haar d := by
    have := integral_nonneg_of_ae hnn
    rwa [hE] at this
  refine ⟨hlog, hlog.abs, ?_, ?_⟩
  · rw [hH]; exact ENNReal.ofReal_ne_top
  · rw [hH, ENNReal.toReal_ofReal hnn']

/-- Finite species entropy sums: every finite family of absolute-admissible densities has a
finite entropy sum, and every real-weighted sum of the entropies equals the integral of the
weighted sum of `ρ_s log ρ_s`. -/
theorem absoluteDensity_entropy_sum_finite {ι : Type*} (s : Finset ι)
    (ρ : ι → AbsoluteDensity d) :
    (∑ i ∈ s, relativeEntropy (densityMeasure (ρ i)) (haar d)) ≠ ⊤ ∧
    ∀ θ : ι → ℝ,
      Integrable (fun x => ∑ i ∈ s, θ i * (((ρ i).density x) * Real.log ((ρ i).density x)))
        (haar d) ∧
      ∑ i ∈ s, θ i * (relativeEntropy (densityMeasure (ρ i)) (haar d)).toReal =
        ∫ x, ∑ i ∈ s, θ i * (((ρ i).density x) * Real.log ((ρ i).density x)) ∂haar d := by
  refine ⟨?_, fun θ => ?_⟩
  · exact ENNReal.sum_ne_top.mpr fun i _ => (absoluteDensity_entropy_finite (ρ i)).2.2.1
  · have hi : ∀ i ∈ s, Integrable
        (fun x => θ i * (((ρ i).density x) * Real.log ((ρ i).density x))) (haar d) :=
      fun i _ => (ρ i).integrable_density_mul_log.const_mul (θ i)
    refine ⟨integrable_finsetSum s hi, ?_⟩
    rw [integral_finsetSum s hi]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, (absoluteDensity_entropy_finite (ρ i)).2.2.2]

end DGPS
