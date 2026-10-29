import SharpSymmetricLSI.Paper.ProductDissipation

/-!
# (2.11): the Fisher-information identity and its limit (Phase 3, lane D; R6)
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem tendsto_fisherComp (μ : Measure (Torus d)) (a : Torus d → ℝ) (B : Torus d → Torus d → ℝ) :
    Tendsto (fun N : ℕ => fisherComp μ a B N) atTop
      (𝓝 ((∫ x, a x ^ 2 ∂μ) + 2 * (∫ x, a x * ∫ y, B x y ∂μ ∂μ) +
        (∫ x, (∫ y, B x y ∂μ) ^ 2 ∂μ))) := by
  set A := ∫ x, a x ^ 2 ∂μ
  set X := ∫ x, a x * ∫ y, B x y ∂μ ∂μ
  set Y := ∫ x, ∫ y, B x y ^ 2 ∂μ ∂μ
  set Z := ∫ x, (∫ y, B x y ∂μ) ^ 2 ∂μ
  set g : ℝ → ℝ := fun t => A + 2 * (1 - t) * X + (t - t ^ 2) * Y + (1 - 3 * t + 2 * t ^ 2) * Z
  have hg : Continuous g := by fun_prop
  have ht : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hlim := (hg.tendsto 0).comp ht
  have h0 : g 0 = A + 2 * X + Z := by simp [g]
  rw [h0] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by have : (0 : ℝ) < N := by exact_mod_cast hN
                               exact this.ne'
  simp only [Function.comp, g, fisherComp]
  field_simp
  ring

/-- **(2.11)**. -/
theorem product_state_fisher_aux (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hs : IsSmoothT ρ)
    (hpos : ∀ x, 0 < ρ x) (h1 : ∫ x, ρ x ∂haar d = 1) :
    (∀ N : ℕ, 1 ≤ N →
      fisherInfoC (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N) ≠ ⊤ ∧
      (fisherInfoC (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N)).toReal / N =
        (∫ x, sqNorm (fun k => weakGrad (fun y => Real.log (ρ y)) x k + weakGrad V x k +
            ((N : ℝ) - 1) / N * fDens W ρ x k) ∂densMeasure ρ) +
          ((N : ℝ) - 1) / (N : ℝ) ^ 2 *
            ∫ x, ((∫ y, sqNorm (g1W W x y) ∂densMeasure ρ) - sqNorm (fDens W ρ x))
              ∂densMeasure ρ ∧
      4 * energy V W N
          (fun X => Real.sqrt ((Measure.pi fun _ : Fin N => densMeasure ρ).rnDeriv
            (gibbs V W N) X).toReal) =
        fisherInfoC (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N)) ∧
    dissipation V W ρ ≠ ⊤ ∧
    Tendsto (fun N : ℕ => (fisherInfoC (Measure.pi fun _ : Fin N => densMeasure ρ)
      (gibbs V W N)).toReal / N) atTop (𝓝 (dissipation V W ρ).toReal) := by
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hpos x).le
  haveI := isProbabilityMeasure_densMeasure' hρ0 h1
  refine ⟨fun N hN => ?_, ?_, ?_⟩
  · obtain ⟨-, h4, hF⟩ := fisher_productState (N := N) hyp hs hpos h1
    refine ⟨by rw [hF]; exact ENNReal.ofReal_ne_top, ?_, h4.symm⟩
    rw [fisher_div_eq_sum hyp hs hpos h1 hN, rhs_eq_sum hyp hs hpos h1 hN]
  · rw [dissipation_eq hyp hs hpos h1]; exact ENNReal.ofReal_ne_top
  · obtain ⟨Ca, hCa⟩ := aGrad_bdd hyp hs hpos
    obtain ⟨Cb, hCb⟩ := bGrad_bdd hyp (W := W)
    have hD : (dissipation V W ρ).toReal = ∑ k, ((∫ x, aGrad V ρ x k ^ 2 ∂densMeasure ρ) +
        2 * (∫ x, aGrad V ρ x k * ∫ y, bGrad W x y k ∂densMeasure ρ ∂densMeasure ρ) +
        (∫ x, (∫ y, bGrad W x y k ∂densMeasure ρ) ^ 2 ∂densMeasure ρ)) := by
      rw [dissipation_eq hyp hs hpos h1, ENNReal.toReal_ofReal (integral_nonneg fun x =>
        Finset.sum_nonneg fun k _ => sq_nonneg _)]
      simp_rw [bForce_eq hρ0 h1]
      have := rhs_generic (μ := densMeasure ρ) (fun k => measurable_aGrad hyp hs hpos k)
        (fun k => measurable_bGrad hyp (W := W) k) hCa hCb 1 0
      simp only [one_mul, zero_mul, add_zero, one_pow, mul_one] at this
      rw [this]
    rw [hD]
    refine (tendsto_finset_sum _ fun k _ => tendsto_fisherComp (densMeasure ρ)
      (fun x => aGrad V ρ x k) (fun x y => bGrad W x y k)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (fisher_div_eq_sum hyp hs hpos h1 hN).symm

end SharpLSI
