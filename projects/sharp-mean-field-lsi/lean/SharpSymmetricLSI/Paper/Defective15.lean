import SharpSymmetricLSI.Paper.Defective14
import SharpSymmetricLSI.Paper.Defective10

/-!
# R03 (Proposition 2.2), part 15: integrability of the regularized density and its gradient

* `volume_le_smul_gibbs_flat`: Lebesgue measure on `𝕋^{N×d}` is dominated by `C · P_N ∘ flat⁻¹`;
* `integrable_Qreg`, `memLp_GQreg`: `Q ∘ unflat ∈ L¹`, `∇Q ∈ L²(Leb)`;
* `lintegral_sq_integral_le`: `(∫ h)² ≤ ∫ h²` in `ℝ≥0∞` form on a probability space.
-/

open MeasureTheory Filter Topology InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem volume_le_smul_gibbs_flat (hyp : Hyp V W KV KW) (N : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ (volume : Measure (UnitAddTorus (Fin N × Fin d))) ≤
      C • (gibbs V W N).map flat := by
  obtain ⟨c, hc0, hct, hc⟩ := exists_gibbsDensity_lower hyp N
  refine ⟨c⁻¹, ENNReal.inv_ne_top.mpr hc0, ?_⟩
  rw [← map_flat_volume N, ← Measure.map_smul]
  refine Measure.map_mono ?_ measurable_flat
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.smul_apply, smul_eq_mul,
    show gibbs V W N = (volume : Measure (Config N d)).withDensity
      (gibbsDensity volume (hamiltonian V W N)) from rfl, withDensity_apply _ hs]
  calc volume s = c⁻¹ * (c * volume s) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
    _ ≤ c⁻¹ * ∫⁻ X in s, gibbsDensity volume (hamiltonian V W N) X := by
        gcongr
        rw [← setLIntegral_const]
        exact lintegral_mono fun X => hc X
  exact measurable_flat.aemeasurable

theorem memLp_volume_of_gibbs (hyp : Hyp V W KV KW) {N : ℕ} {u : UnitAddTorus (Fin N × Fin d) → ℝ}
    (hu : MemLp u 2 ((gibbs V W N).map flat)) : MemLp u 2 volume := by
  obtain ⟨C, hC, hle⟩ := volume_le_smul_gibbs_flat hyp (d := d) N
  exact hu.of_measure_le_smul hC hle

/-- `(∫ h)² ≤ ∫ h²` on a probability space, in `ℝ≥0∞`. -/
theorem ofReal_sq_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {h : α → ℝ} (hm : AEStronglyMeasurable h μ) :
    ENNReal.ofReal ((∫ x, h x ∂μ) ^ 2) ≤ ∫⁻ x, ENNReal.ofReal (h x ^ 2) ∂μ := by
  by_cases hfin : ∫⁻ x, ENNReal.ofReal (h x ^ 2) ∂μ = ⊤
  · rw [hfin]; exact le_top
  have h2 : Integrable (fun x => h x ^ 2) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hm.pow 2) (Eventually.of_forall fun x => sq_nonneg _)).mp
      hfin
  have hL2 : MemLp h 2 μ := (memLp_two_iff_integrable_sq hm).mpr h2
  have hi : Integrable h μ := hL2.integrable one_le_two
  set m := ∫ x, h x ∂μ
  have h0 : 0 ≤ ∫ x, (h x - m) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have e : ∫ x, (h x - m) ^ 2 ∂μ = (∫ x, h x ^ 2 ∂μ) - m ^ 2 := by
    have : ∀ x, (h x - m) ^ 2 = h x ^ 2 - 2 * m * h x + m ^ 2 := fun x => by ring
    simp_rw [this]
    rw [integral_add (f := fun x => h x ^ 2 - 2 * m * h x) (h2.sub (hi.const_mul _))
        (integrable_const _),
      integral_sub (f := fun x => h x ^ 2) (g := fun x => 2 * m * h x) h2 (hi.const_mul _),
      integral_const_mul]
    first | (simp; done) | (simp; ring)
  rw [← ofReal_integral_eq_lintegral_ofReal h2 (Eventually.of_forall fun x => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

theorem IsWeakGrad.congr_grad {ι : Type*} [Fintype ι] [DecidableEq ι] {f : UnitAddTorus ι → ℝ}
    {g g' : UnitAddTorus ι → ι → ℝ} (h : IsWeakGrad f g)
    (hgg : ∀ k, (fun y => g y k) =ᵐ[volume] fun y => g' y k) : IsWeakGrad f g' := by
  have hl : ∀ k, (fun x => g (liftT x) k) =ᵐ[volume] fun x => g' (liftT x) k := fun k =>
    quasiMeasurePreserving_liftT.ae_eq (hgg k)
  refine ⟨h.locInt, fun k => (h.locInt_grad k).congr (hl k), fun φ hφ hφc k => ?_⟩
  rw [h.ibp φ hφ hφc k]
  congr 1
  exact integral_congr_ae ((hl k).mono fun x hx => by simp only at hx ⊢; rw [hx])

/-- A measurable `L²(Leb)` weak gradient of an `H¹(P_N)` function. -/
theorem exists_measurable_grad (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) :
    ∃ g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ, IsWeakGrad (f ∘ unflat) g ∧
      (∀ p, Measurable fun y => g y p) ∧ (∀ p, MemLp (fun y => g y p) 2 volume) ∧
      (∀ p, Integrable (fun y => g y p) volume) := by
  obtain ⟨hw, -, -⟩ := memH1C_data hyp hf
  have ham : ∀ p, AEStronglyMeasurable (fun y => weakGrad (f ∘ unflat) y p) volume := fun p =>
    hw.aestronglyMeasurable_grad p
  refine ⟨fun y p => (ham p).mk _ y, hw.congr_grad fun p => (ham p).ae_eq_mk,
    fun p => (ham p).stronglyMeasurable_mk.measurable, fun p => ?_, fun p => ?_⟩
  · have h2 : MemLp (fun y => weakGrad (f ∘ unflat) y p) 2 volume := by
      refine memLp_volume_of_gibbs hyp ?_
      refine hf.2.2.of_le ((ham p).mono_ac (gibbs_map_flat_ac hyp N).1)
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact abs_le_sqrt_sqNorm _ p
    exact h2.ae_eq (ham p).ae_eq_mk
  · have h2 : MemLp (fun y => weakGrad (f ∘ unflat) y p) 2 volume := by
      refine memLp_volume_of_gibbs hyp ?_
      refine hf.2.2.of_le ((ham p).mono_ac (gibbs_map_flat_ac hyp N).1)
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact abs_le_sqrt_sqNorm _ p
    exact (h2.ae_eq (ham p).ae_eq_mk).integrable one_le_two

section regInt
variable (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
  {N : ℕ} (hN : 1 ≤ N) {f : Config N d → ℝ} (hfm : Measurable f) (hf : MemH1C (gibbs V W N) f)
  (n : ℕ)
include hyp hac hN hfm hf

theorem integrable_Qreg : Integrable (Qreg V W n f ∘ unflat) volume := by
  obtain ⟨c, C, hc, hb⟩ := Qreg_bounds hyp hf hfm n
  exact Integrable.of_bound ((measurable_Qreg hyp hf hfm n).comp measurable_unflat).aestronglyMeasurable
    C (Eventually.of_forall fun y => by
      simp only [Real.norm_eq_abs, Function.comp_apply]
      rw [abs_of_pos (hc.trans_le (hb _).1)]; exact (hb _).2)

theorem memLp_GQreg {g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    (hg2 : ∀ p, MemLp (fun y => g y p) 2 volume) (p : Fin N × Fin d) :
    MemLp (fun y => GQreg V W μ n f g y p) 2 volume := by
  have hg2 := hg2 p
  obtain ⟨c1, C1, hc1, h1⟩ := gibbsDensR_bounds hyp (N := N)
  obtain ⟨C, hC0, hC⟩ := exists_bound_gradH hyp hac hN (μ := μ)
  have hZ0 : 0 < Zreg V W n f := lt_of_lt_of_le (by positivity) (Zreg_bounds hyp hf n).1
  have hmℓ : Measurable fun y : UnitAddTorus (Fin N × Fin d) => gibbsDensR V W N (unflat y) :=
    (measurable_gibbsDensR hyp).comp measurable_unflat
  have hmf : Measurable fun y : UnitAddTorus (Fin N × Fin d) => f (unflat y) := hfm.comp measurable_unflat
  have t1 : MemLp (fun y => deriv (psiSqR n) (f (unflat y)) * g y p *
      gibbsDensR V W N (unflat y)) 2 volume := by
    have := (hg2.const_mul ((n : ℝ) + 1) |>.const_mul C1)
    refine this.of_le ((((contDiff_psiSqR n).continuous_deriv le_rfl).measurable.comp hmf |>.aestronglyMeasurable.mul
      hg2.aestronglyMeasurable).mul hmℓ.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    have a1 := abs_deriv_psiSqR_le n (f (unflat y))
    have a2 : |gibbsDensR V W N (unflat y)| ≤ C1 := by
      rw [abs_of_pos (hc1.trans_le (h1 _).1)]; exact (h1 _).2
    have a3 := abs_nonneg (g y p)
    have a4 : |((n : ℝ) + 1)| = (n : ℝ) + 1 := abs_of_pos (by positivity)
    rw [a4, abs_of_pos (hc1.trans_le ((h1 (unflat y)).1.trans (h1 (unflat y)).2))]
    calc |deriv (psiSqR n) (f (unflat y))| * |g y p| * |gibbsDensR V W N (unflat y)|
        ≤ ((n : ℝ) + 1) * |g y p| * C1 := by gcongr
      _ = C1 * (((n : ℝ) + 1) * |g y p|) := by ring
  have t2 : MemLp (fun y => uReg n f (unflat y) * (-(gibbsDensR V W N (unflat y) *
      (gsG W μ N y p + lipGrad (PhiMF V W μ) (projBlock p.1 y) p.2)))) 2 volume := by
    refine MemLp.of_bound ((((contDiff_psiSqR n).continuous.measurable.comp hmf).mul
      (hmℓ.mul (measurable_gradH hyp hac hN p)).neg).aestronglyMeasurable)
      (((n : ℝ) + 2) ^ 2 * (C1 * C)) (Eventually.of_forall fun y => ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_neg, uReg]
    have b1 : |psiSqR n (f (unflat y))| ≤ ((n : ℝ) + 2) ^ 2 := by
      rw [abs_of_nonneg (le_trans (by positivity) (psiSqR_bounds n _).1)]; exact (psiSqR_bounds n _).2
    have b2 : |gibbsDensR V W N (unflat y)| ≤ C1 := by
      rw [abs_of_pos (hc1.trans_le (h1 _).1)]; exact (h1 _).2
    have b3 := hC y p
    have hC1 : 0 ≤ C1 := (hc1.trans_le ((h1 (unflat y)).1.trans (h1 (unflat y)).2)).le
    gcongr
  refine ((t1.add t2).const_mul (1 / Zreg V W n f)).ae_eq (Eventually.of_forall fun y => ?_)
  simp only [GQreg, Pi.add_apply]
  ring

end regInt

end SharpLSI
