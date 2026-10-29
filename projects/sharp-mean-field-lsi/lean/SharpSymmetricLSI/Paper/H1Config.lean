import SharpSymmetricLSI.Paper.Gibbs
import SharpSymmetricLSI.Defs.D09_ParticleRates
import SharpSymmetricLSI.Infra.ChainRule

/-!
# `H¹(P_N)` on configuration spaces: truncations and energy identities (Phase 2, I1, milestone 3)

Under (1.2) the density of `P_N` is bounded below, so `L²(P_N)` functions are Haar-integrable on
the flattened torus `𝕋^{N×d}` (`integrable_haar_of_memLp`). The torus chain rule therefore applies
to `f ∘ unflat` for every `f ∈ H¹(P_N)`. Main results:
* `memH1C_min`, `memH1C_posPart_sub`, `memH1C_abs`: `H¹(P_N)` is stable under truncations;
* `energy_eq_min_add_posPart`: `ℰ_N(f) = ℰ_N(f ∧ M) + ℰ_N((f - M)₊)`;
* `energy_abs`: `ℰ_N(|f|) = ℰ_N(f)`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- Stability of `H¹(P_N)` under a pointwise operation with a dominated weak gradient. -/
theorem memH1C_of_comp (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) {T : ℝ → ℝ} (hT : Continuous T) (A : ℝ)
    (hTb : ∀ t, |T t| ≤ |t| + A) {gT : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    (hgT : IsWeakGrad (fun y => T ((f ∘ unflat) y)) gT)
    (hgb : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin N × Fin d))),
      sqNorm (gT y) ≤ sqNorm (weakGrad (f ∘ unflat) y)) :
    MemH1C (gibbs V W N) (fun X => T (f X)) := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  have hac := (gibbs_map_flat_ac hyp N).1
  have hw := isWeakGrad_weakGrad hf.1
  have hwT := isWeakGrad_weakGrad (⟨gT, hgT⟩ : HasWeakGrad fun y => T ((f ∘ unflat) y))
  refine ⟨⟨gT, hgT⟩, ?_, ?_⟩
  · refine (hf.2.1.norm.add (memLp_const A)).of_le
      (hT.comp_aestronglyMeasurable hf.2.1.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
    simp only [Function.comp_apply, Real.norm_eq_abs, Pi.add_apply]
    have := hTb (f (unflat y))
    have hA : 0 ≤ |f (unflat y)| + A := le_trans (abs_nonneg _) this
    rw [abs_of_nonneg hA]; exact this
  · have hm : AEStronglyMeasurable (fun y => Real.sqrt (sqNorm (weakGrad
        (fun y => T (f (unflat y))) y))) ((gibbs V W N).map flat) :=
      (Real.continuous_sqrt.comp_aestronglyMeasurable hwT.aestronglyMeasurable_sqNorm).mono_ac hac
    refine hf.2.2.of_le hm ?_
    filter_upwards [hac.ae_le (weakGrad_ae_eq hgT), hac.ae_le hgb] with y hy1 hy2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (by
      change sqNorm (weakGrad (fun y => T ((f ∘ unflat) y)) y) ≤ _
      rw [hy1]; exact hy2)

/-! ### Truncations in `H¹(P_N)` -/

theorem memH1C_posPart_sub (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) (M : ℝ) : MemH1C (gibbs V W N) (fun X => max (f X - M) 0) := by
  obtain ⟨hw, hi, hgi⟩ := memH1C_data hyp hf
  refine memH1C_of_comp hyp hf (T := fun t => max (t - M) 0)
    ((continuous_id.sub continuous_const).max continuous_const) |M| (fun t => ?_)
    (isWeakGrad_posPart_sub hw hi hgi M) (Eventually.of_forall fun y => ?_)
  · rcases le_total (t - M) 0 with h | h
    · rw [max_eq_right h, abs_zero]; positivity
    · rw [max_eq_left h, abs_of_nonneg h]
      linarith [le_abs_self t, neg_abs_le M]
  · rw [sqNorm_ite_left]; split_ifs
    · exact le_rfl
    · exact sqNorm_nonneg _

theorem memH1C_min (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) (M : ℝ) : MemH1C (gibbs V W N) (fun X => min (f X) M) := by
  obtain ⟨hw, hi, hgi⟩ := memH1C_data hyp hf
  refine memH1C_of_comp hyp hf (T := fun t => min t M) (continuous_id.min continuous_const) |M|
    (fun t => ?_) (isWeakGrad_min hw hi hgi M) (Eventually.of_forall fun y => ?_)
  · rcases le_total t M with h | h
    · rw [min_eq_left h]; linarith [abs_nonneg M]
    · rw [min_eq_right h]; linarith [abs_nonneg t]
  · rw [sqNorm_ite_right]; split_ifs
    · exact sqNorm_nonneg _
    · exact le_rfl

theorem memH1C_abs (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) : MemH1C (gibbs V W N) (fun X => |f X|) := by
  obtain ⟨hw, hi, hgi⟩ := memH1C_data hyp hf
  refine memH1C_of_comp hyp hf (T := fun t => |t|) continuous_abs 0
    (fun t => by simp) (isWeakGrad_abs hw hi hgi) (Eventually.of_forall fun y => ?_)
  by_cases h1 : 0 < (f ∘ unflat) y
  · simp only [h1, ↓reduceIte]; exact le_rfl
  · by_cases h2 : (f ∘ unflat) y < 0
    · simp only [h1, h2, ↓reduceIte]; rw [sqNorm_neg]
    · simp only [h1, h2, ↓reduceIte]
      rw [show (fun _ : Fin N × Fin d => (0 : ℝ)) = 0 from rfl]
      simp only [sqNorm, Pi.zero_apply]; simp only [ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, Finset.sum_const_zero]
      exact sqNorm_nonneg _

/-! ### Energy identities -/

theorem gradSqC_eq {N : ℕ} (f : Config N d → ℝ) (X : Config N d) :
    gradSqC f X = sqNorm (weakGrad (f ∘ unflat) (flat X)) := by
  simp only [gradSqC, weakGradC, sqNorm]
  rw [← Fintype.sum_prod_type']

theorem energy_eq (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : HasWeakGrad (f ∘ unflat)) :
    energy V W N f = ∫⁻ y, ENNReal.ofReal (sqNorm (weakGrad (f ∘ unflat) y))
      ∂((gibbs V W N).map flat) := by
  have hm : AEMeasurable (fun y => ENNReal.ofReal (sqNorm (weakGrad (f ∘ unflat) y)))
      ((gibbs V W N).map flat) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (isWeakGrad_weakGrad hf).aestronglyMeasurable_sqNorm.aemeasurable).mono_ac
      (gibbs_map_flat_ac hyp N).1
  rw [lintegral_map' hm measurable_flat.aemeasurable]
  unfold energy
  simp_rw [gradSqC_eq]

/-- `ℰ_N(f) = ℰ_N(f ∧ M) + ℰ_N((f - M)₊)` (manuscript (2.17)). -/
theorem energy_eq_min_add_posPart (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) (M : ℝ) :
    energy V W N f = energy V W N (fun X => min (f X) M) +
      energy V W N (fun X => max (f X - M) 0) := by
  obtain ⟨hw, hi, hgi⟩ := memH1C_data hyp hf
  have hac := (gibbs_map_flat_ac hyp N).1
  have hmin := isWeakGrad_min hw hi hgi M
  have hpos := isWeakGrad_posPart_sub hw hi hgi M
  rw [energy_eq hyp hf.1, energy_eq hyp ⟨_, hmin⟩, energy_eq hyp ⟨_, hpos⟩]
  have hm : AEMeasurable (fun y => ENNReal.ofReal (sqNorm (weakGrad
      ((fun X => min (f X) M) ∘ unflat) y))) ((gibbs V W N).map flat) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (isWeakGrad_weakGrad ⟨_, hmin⟩).aestronglyMeasurable_sqNorm.aemeasurable).mono_ac hac
  rw [← lintegral_add_left' hm]
  refine lintegral_congr_ae ?_
  filter_upwards [hac.ae_le (weakGrad_ae_eq hmin), hac.ae_le (weakGrad_ae_eq hpos)] with y h1 h2
  change _ = ENNReal.ofReal (sqNorm (weakGrad (fun y => min ((f ∘ unflat) y) M) y)) +
    ENNReal.ofReal (sqNorm (weakGrad (fun y => max ((f ∘ unflat) y - M) 0) y))
  rw [h1, h2, sqNorm_ite_right, sqNorm_ite_left]
  split_ifs
  · rw [ENNReal.ofReal_zero, zero_add]
  · rw [ENNReal.ofReal_zero, add_zero]

/-- `ℰ_N(|f|) = ℰ_N(f)`. -/
theorem energy_abs (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) : energy V W N (fun X => |f X|) = energy V W N f := by
  obtain ⟨hw, hi, hgi⟩ := memH1C_data hyp hf
  have hac := (gibbs_map_flat_ac hyp N).1
  have habs := isWeakGrad_abs hw hi hgi
  rw [energy_eq hyp ⟨_, habs⟩, energy_eq hyp hf.1]
  refine lintegral_congr_ae ?_
  filter_upwards [hac.ae_le (weakGrad_ae_eq habs), hac.ae_le (ae_grad_eq_zero_of_eq hw hi hgi 0)]
    with y h1 h0
  change ENNReal.ofReal (sqNorm (weakGrad (fun y => |(f ∘ unflat) y|) y)) = _
  rw [h1]
  congr 1
  by_cases hp : 0 < (f ∘ unflat) y
  · simp only [hp, ↓reduceIte]
  · by_cases hn : (f ∘ unflat) y < 0
    · simp only [hp, hn, ↓reduceIte]; rw [sqNorm_neg]
    · have hz : (f ∘ unflat) y = 0 := by linarith [not_lt.mp hp, not_lt.mp hn]
      have := h0 hz
      simp only [hp, hn, ↓reduceIte]
      simp [sqNorm, this]

end SharpLSI
