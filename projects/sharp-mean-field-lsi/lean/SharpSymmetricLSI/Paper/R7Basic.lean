import SharpSymmetricLSI.Paper.Tensorize
import SharpSymmetricLSI.Statements.R34_Lemma_B_1

/-!
# Toolkit for Section 2.3 (R7): scaling in `H¹(P_N)`, entropy identities

* `klFun_sq_ge`: `klFun(s²) ≥ (s - 1)²` for `s ≥ 0` (replaces Jensen in (2.21); approved).
* `Phi_eq_klFun`: `Φ(s) = klFun(s²)`.
* `memH1C_smul`, `energy_smul`, `memH1C_add_const`, `energy_add_const`, `energy_lt_top`.
* `ent_const_mul`, `ent_normalized`.
-/

open MeasureTheory Set Filter Topology InformationTheory
open scoped ENNReal

namespace SharpLSI

theorem klFun_sq_sub (s : ℝ) (hs : 0 ≤ s) : klFun (s ^ 2) - (s - 1) ^ 2 = 2 * s * klFun s := by
  unfold klFun
  rcases hs.eq_or_lt with h | h
  · subst h; simp
  · rw [Real.log_pow]; push_cast; ring

/-- `klFun(s²) ≥ (s - 1)²` for `s ≥ 0`. -/
theorem klFun_sq_ge {s : ℝ} (hs : 0 ≤ s) : (s - 1) ^ 2 ≤ klFun (s ^ 2) := by
  have := klFun_sq_sub s hs
  have h2 : 0 ≤ 2 * s * klFun s := mul_nonneg (by linarith) (klFun_nonneg hs)
  linarith

theorem Phi_eq_klFun (s : ℝ) : Phi s = klFun (s ^ 2) := by
  unfold Phi klFun; ring

/-! ### Entropy -/

section Ent

variable {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]

theorem ent_const_mul {u : α → ℝ} (hu : Integrable u P) {c : ℝ} (hc : 0 ≤ c) :
    ent P (fun x => c * u x) = ENNReal.ofReal c * ent P u := by
  unfold ent
  simp only [hu, hu.const_mul c, ↓reduceIte]
  rw [integral_const_mul, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  rcases hc.eq_or_lt with h0 | h0
  · subst h0; simp
  · rw [← ENNReal.ofReal_mul hc, mul_div_mul_left _ _ h0.ne', mul_assoc]

theorem ent_normalized {u : α → ℝ} (hu : Integrable u P) (h1 : ∫ x, u x ∂P = 1) :
    ent P u = ∫⁻ x, ENNReal.ofReal (klFun (u x)) ∂P := by
  unfold ent; simp [hu, h1]

/-- `∫ (f - 1)² ≤ Ent(f²)` when `∫ f² = 1`. -/
theorem lintegral_sub_one_sq_le_ent {f : α → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hi : Integrable (fun x => f x ^ 2) P) (h1 : ∫ x, f x ^ 2 ∂P = 1) :
    ∫⁻ x, ENNReal.ofReal ((f x - 1) ^ 2) ∂P ≤ ent P (fun x => f x ^ 2) := by
  rw [ent_normalized P hi h1]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (klFun_sq_ge (hf0 x))

/-- For `∫ f² = 1` and finite entropy: `Ent(f²) = ∫ Φ(f)`, with `Φ(f)` integrable. -/
theorem ent_toReal_eq_integral_Phi {f : α → ℝ} (hf : AEStronglyMeasurable f P)
    (hi : Integrable (fun x => f x ^ 2) P) (h1 : ∫ x, f x ^ 2 ∂P = 1)
    (hfin : ent P (fun x => f x ^ 2) ≠ ⊤) :
    Integrable (fun x => Phi (f x)) P ∧
      (ent P (fun x => f x ^ 2)).toReal = ∫ x, Phi (f x) ∂P := by
  rw [ent_normalized P hi h1] at hfin ⊢
  have hm : AEStronglyMeasurable (fun x => klFun (f x ^ 2)) P :=
    (continuous_klFun.comp_aestronglyMeasurable (hf.pow 2))
  have hint : Integrable (fun x => klFun (f x ^ 2)) P := by
    refine ⟨hm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => klFun_nonneg (sq_nonneg _))]
    exact hfin.lt_top
  simp_rw [Phi_eq_klFun]
  refine ⟨hint, ?_⟩
  rw [← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x =>
    klFun_nonneg (sq_nonneg _)) hm]

end Ent

/-! ### Scaling in `H¹(P_N)` -/

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem sqNorm_smul {ι : Type*} [Fintype ι] (c : ℝ) (v : ι → ℝ) :
    sqNorm (fun k => c * v k) = c ^ 2 * sqNorm v := by
  simp only [sqNorm, mul_pow, Finset.mul_sum]

theorem memH1C_smul (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) (c : ℝ) : MemH1C (gibbs V W N) (fun X => c * f X) := by
  have hac := (gibbs_map_flat_ac hyp N).1
  have hw := isWeakGrad_weakGrad hf.1
  have hc := hw.cmul c
  refine ⟨⟨_, hc⟩, hf.2.1.const_mul c, ?_⟩
  refine (hf.2.2.const_mul |c|).ae_eq ?_
  filter_upwards [hac.ae_le (weakGrad_ae_eq hc)] with y hy
  change |c| * Real.sqrt (sqNorm (weakGrad (f ∘ unflat) y)) =
    Real.sqrt (sqNorm (weakGrad (fun y => c * (f ∘ unflat) y) y))
  rw [hy, sqNorm_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem energy_smul (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) (c : ℝ) :
    energy V W N (fun X => c * f X) = ENNReal.ofReal (c ^ 2) * energy V W N f := by
  have hac := (gibbs_map_flat_ac hyp N).1
  have hw := isWeakGrad_weakGrad hf.1
  have hc := hw.cmul c
  rw [energy_eq hyp ⟨_, hc⟩, energy_eq hyp hf.1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [hac.ae_le (weakGrad_ae_eq hc)] with y hy
  change ENNReal.ofReal (sqNorm (weakGrad (fun y => c * (f ∘ unflat) y) y)) = _
  rw [hy, sqNorm_smul, ENNReal.ofReal_mul (sq_nonneg c)]

theorem memH1C_add_const (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) (b : ℝ) : MemH1C (gibbs V W N) (fun X => f X + b) := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  have hac := (gibbs_map_flat_ac hyp N).1
  have hw := isWeakGrad_weakGrad hf.1
  have hb := hw.add (isWeakGrad_const b)
  simp only [Pi.zero_apply, add_zero] at hb
  refine ⟨⟨_, hb⟩, hf.2.1.add (memLp_const b), ?_⟩
  refine hf.2.2.ae_eq ?_
  filter_upwards [hac.ae_le (weakGrad_ae_eq hb)] with y hy
  change Real.sqrt (sqNorm (weakGrad (f ∘ unflat) y)) =
    Real.sqrt (sqNorm (weakGrad (fun y => (f ∘ unflat) y + b) y))
  rw [hy]

theorem energy_add_const (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) (b : ℝ) :
    energy V W N (fun X => f X + b) = energy V W N f := by
  have hac := (gibbs_map_flat_ac hyp N).1
  have hw := isWeakGrad_weakGrad hf.1
  have hb := hw.add (isWeakGrad_const b)
  simp only [Pi.zero_apply, add_zero] at hb
  rw [energy_eq hyp ⟨_, hb⟩, energy_eq hyp hf.1]
  refine lintegral_congr_ae ?_
  filter_upwards [hac.ae_le (weakGrad_ae_eq hb)] with y hy
  change ENNReal.ofReal (sqNorm (weakGrad (fun y => (f ∘ unflat) y + b) y)) = _
  rw [hy]

theorem energy_lt_top (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) : energy V W N f < ⊤ := by
  rw [energy_eq hyp hf.1]
  have := hf.2.2.integrable_sq
  have h2 : (fun y => Real.sqrt (sqNorm (weakGrad (f ∘ unflat) y)) ^ 2) =
      fun y => sqNorm (weakGrad (f ∘ unflat) y) := by
    funext y; rw [Real.sq_sqrt (sqNorm_nonneg _)]
  rw [h2] at this
  rw [← hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => sqNorm_nonneg _)]
  exact this.2

/-- `f ∈ L²(P_N)` from `f ∈ H¹(P_N)`. -/
theorem memLp_of_memH1C (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) : MemLp f 2 (gibbs V W N) := by
  have h := hf.2.1
  rw [memLp_map_measure_iff h.aestronglyMeasurable measurable_flat.aemeasurable] at h
  exact h

end SharpLSI
