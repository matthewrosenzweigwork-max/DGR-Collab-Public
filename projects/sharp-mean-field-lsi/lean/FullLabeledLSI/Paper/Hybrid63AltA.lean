import FullLabeledLSI.Infra.HypercontrTorus7
import FullLabeledLSI.Infra.SpectralSetup
import FullLabeledLSI.Paper.HybridRLS
import FullLabeledLSI.Paper.HybridMatrix
import FullLabeledLSI.Defs.F05_FiniteRank
import SharpSymmetricLSI.Paper.EntFinite

/-!
# Proposition 6.3: finiteness of the `toReal` terms of `Jexpr` (`Jexpr_terms_finite`)

* `bRate < ⊤` from `rLS ≤ ofReal λ₁` and `min_le_left`.
* On the spectral range, `refEnergy = ofReal (finite sum)` (`torus_energy_formula`) and the entropy
  of `F²` is finite because `F` is a.e. equal to a bounded `C¹` function.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace SharpLSI.FL

variable {d : ℕ}

theorem Jexpr_terms_finite_alt {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    (∀ C : ℕ → ℕ → ℝ, bRate (μ : Measure (Torus d)) lam C < ⊤) ∧
    ∀ (L : ℝ) (N : ℕ) (F : Config N d → ℝ), InSpectralRange e lam L F →
      refEnergy (μ : Measure (Torus d)) F < ⊤ ∧
      ent (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) (fun X => F X ^ 2) < ⊤ := by
  refine ⟨fun C => lt_top_iff_ne_top.2 (bRate_ne_top (rLS_le_lam_one hyp hμ he)), ?_⟩
  intro L N F hF
  obtain ⟨eC, a, hac, hca, hC1, hae, -⟩ :=
    Gross.torus_standing hd hyp hr μ hμ e lam he
  obtain ⟨T, c, hT, hFe⟩ := hF
  refine ⟨?_, ?_⟩
  · rw [(Gross.torus_energy_formula hac hca he hC1 hae T c hFe).2]
    exact ENNReal.ofReal_lt_top
  · set Q : Measure (Config N d) := Measure.pi fun _ : Fin N => (μ : Measure (Torus d)) with hQ
    set u := Gross.uFun (Gross.MT eC T) (fun k : T => c k.1) with hu
    have hu1 : Gross.C1C u := Gross.C1C_uFun_MT T hC1 _
    obtain ⟨K, hK⟩ := hu1.bounded
    have hFu : F =ᵐ[Q] u := by
      filter_upwards [Gross.ae_poly_eq hae T c] with X hX
      rw [hFe X, hX]
    have hmeas : Measurable fun X => u X ^ 2 := hu1.measurable.pow_const 2
    have hb : ∀ X, ‖u X ^ 2‖ ≤ K ^ 2 := fun X => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hK X) 2
    have hint : Integrable (fun X => u X ^ 2) Q :=
      Integrable.of_bound hmeas.aestronglyMeasurable (K ^ 2) (Filter.Eventually.of_forall hb)
    have heq : (fun X => F X ^ 2) =ᵐ[Q] fun X => u X ^ 2 :=
      hFu.mono fun X hX => by simp [hX]
    rw [SharpLSI.ent_congr_ae heq]
    refine SharpLSI.ent_lt_top_of_lintegral_rpow (p := 2) (fun X => sq_nonneg _) hint
      (by norm_num) ?_
    have hle : ∀ X, ‖u X ^ 2‖ₑ ^ (2 : ℝ) ≤ (ENNReal.ofReal (K ^ 2)) ^ (2 : ℝ) := fun X => by
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hb X)
    calc ∫⁻ X, ‖u X ^ 2‖ₑ ^ (2 : ℝ) ∂Q ≤ ∫⁻ _, (ENNReal.ofReal (K ^ 2)) ^ (2 : ℝ) ∂Q :=
          lintegral_mono hle
      _ < ⊤ := by
        rw [lintegral_const, measure_univ, mul_one]
        exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top

end SharpLSI.FL

end
