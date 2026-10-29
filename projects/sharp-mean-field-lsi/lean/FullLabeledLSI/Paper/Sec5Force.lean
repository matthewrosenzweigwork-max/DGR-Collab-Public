import FullLabeledLSI.Paper.Sec5ForceSum
import FullLabeledLSI.Paper.Sec5ForceRep
import FullLabeledLSI.Paper.Sec5ForceAE
import FullLabeledLSI.Paper.Sec5ForceJensen

/-!
# Lemma 5.5: the bridge from `forceDefect` to `forceDelta` and the final statement
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- `forceDefect` of S22, unfolded (same expression). -/
noncomputable def forceDefect' {N : ℕ} (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (ν : Measure (Config N d)) [IsFiniteMeasure ν] (j : ℕ) : ℝ :=
  ((Nat.choose N j : ℝ)⁻¹) * ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
    ((Sᶜ.card : ℝ)⁻¹) * ∑ i ∈ Sᶜ, ∫ X, ∑ k : Fin d,
      (condForceS W μ ν S X (X i) k -
        condExp (MeasurableSpace.comap (fun X : Config N d => (restrictS S X, X i)) inferInstance)
          ν (fun Y => SharpLSI.weakGradC (SharpLSI.Ucentered W μ N) Y i k) X) ^ 2 ∂ν

/-- The bridge: `forceDefect ≤ forceDelta` level by level, for the representatives of
`exists_force_rep`. -/
theorem forceDefect_le_forceDelta {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : SharpLSI.Hyp V W KV KW) (μ : ProbabilityMeasure (Torus d))
    (hμ : SharpLSI.IsMinimizer V W μ) :
    ∃ (bF : Torus d → Torus d → Fin d → ℝ) (bΔ : Torus d → Fin d → ℝ) (Bb : ℝ),
      ForceRep bF bΔ Bb ∧
      ∀ (N : ℕ) (ν : Measure (Config N d)) [IsProbabilityMeasure ν], HasSmoothPosDensity ν →
        ∀ j, j < N →
          forceDefect' W (μ : Measure (Torus d)) ν j ≤ forceDelta bF bΔ ν j := by
  obtain ⟨bF, bΔ, Bb, hB, hF, hG⟩ := exists_force_rep hd hyp μ hμ
  refine ⟨bF, bΔ, Bb, hB, ?_⟩
  intro N ν _ hν j hj
  have hN : 1 ≤ N := by omega
  have hacs := ac_of_smooth hν
  have hGae : ∀ᵐ X ∂ν, ∀ i k, SharpLSI.weakGradC
      (SharpLSI.Ucentered W (μ : Measure (Torus d)) N) X i k = Gpart bF bΔ N X i k :=
    hacs.1.ae_le (hG N hN)
  unfold forceDefect' forceDelta avg1R
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum fun S hS => ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum fun i hi => ?_
  have hiS : i ∉ S := Finset.mem_compl.mp hi
  have hcard : 1 ≤ Sᶜ.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hcond := condForce_ae_eq (bg := fun x y k => SharpLSI.bForce W (μ : Measure (Torus d)) x y k)
    hF ν hν S i hiS
  have hce : ∀ k : Fin d, (condExp (MeasurableSpace.comap
        (fun X : Config N d => (restrictS S X, X i)) inferInstance) ν
        (fun Y => SharpLSI.weakGradC (SharpLSI.Ucentered W (μ : Measure (Torus d)) N) Y i k)) =ᵐ[ν]
      condExp (MeasurableSpace.comap
        (fun X : Config N d => (restrictS S X, X i)) inferInstance) ν
        (fun Y => Gpart bF bΔ N Y i k) := fun k =>
    condExp_congr_ae (hGae.mono fun X hX => hX i k)
  refine (integral_congr_ae ?_).le.trans (jensen_force hB ν S hcard i)
  filter_upwards [hcond, ae_all_iff.2 hce] with X h1 h2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h2 k]
  have := h1 k
  simp only [condForceS, BS]
  rw [this]

/-- Lemma 5.5 (explicit form of S22). -/
theorem random_force_aux {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : SharpLSI.Hyp V W KV KW) (hr : 0 < SharpLSI.rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : SharpLSI.IsMinimizer V W μ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, ∀ (N M : ℕ), 3 ≤ M → M ≤ N → τ ≤ (M : ℝ) / N →
      ∀ (ν : Measure (Config N d)) [IsProbabilityMeasure ν], HasSmoothPosDensity ν →
        klDiv ν (Measure.pi fun _ => (μ : Measure (Torus d))) ≠ ⊤ →
        ∑ j ∈ Finset.range (N - M), forceDefect' W (μ : Measure (Torus d)) ν j ≤
          C * (1 + Real.sqrt
            (klDiv ν (Measure.pi fun _ => (μ : Measure (Torus d)))).toReal) := by
  obtain ⟨bF, bΔ, Bb, hB, hle⟩ := forceDefect_le_forceDelta hd hyp μ hμ
  obtain ⟨C, hC⟩ := abstract_force_sum hB τ hτ
  refine ⟨C, fun N M hM hMN hτM ν _ hsm hkl => ?_⟩
  calc ∑ j ∈ Finset.range (N - M), forceDefect' W (μ : Measure (Torus d)) ν j
      ≤ ∑ j ∈ Finset.range (N - M), forceDelta bF bΔ ν j :=
        Finset.sum_le_sum fun j hj => hle N ν hsm j (by
          have := Finset.mem_range.mp hj
          omega)
    _ ≤ _ := hC N M hM hMN hτM (μ : Measure (Torus d)) ν hkl

end SharpLSI.FL
