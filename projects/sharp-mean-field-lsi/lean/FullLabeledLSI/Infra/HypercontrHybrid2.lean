import FullLabeledLSI.Infra.HypercontrTorus7
import FullLabeledLSI.Infra.HypercontrHybrid1

/-!
# The torus step of the hybrid moment bound

For a finite family `F = ∑_{k∈S} w_k ∏_i e_{φ(k) i}(x_i)` of tensor eigenfunctions with `φ` injective and
`∑_i λ_{φ(k) i} ≤ L` whenever `w_k ≠ 0`, and every `p ≥ 1`:
`∫ F^{2p} dμ^{⊗N} ≤ ((2p-1)^{L/(2a)})^{2p} (∑_k w_k²)^p`.
-/

open MeasureTheory SharpLSI
open scoped NNReal ENNReal

noncomputable section

namespace SharpLSI.FL.Hyb

open SharpLSI.FL.Gross

variable {d N : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e eC : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

lemma reindex_sum {ι : Type*} [DecidableEq ι] (S : Finset ι) (φ : ι → (Fin N → ℕ)) (w : ι → ℝ)
    (f : (Fin N → ℕ) → ℝ) :
    ∑ k ∈ S, w k * f (φ k) =
      ∑ j ∈ S.image φ, (∑ k ∈ S, if φ k = j then w k else 0) * f j := by
  symm
  calc ∑ j ∈ S.image φ, (∑ k ∈ S, if φ k = j then w k else 0) * f j
      = ∑ j ∈ S.image φ, ∑ k ∈ S, (if φ k = j then w k * f j else 0) := by
        simp_rw [Finset.sum_mul, ite_mul, zero_mul]
    _ = ∑ k ∈ S, ∑ j ∈ S.image φ, (if φ k = j then w k * f j else 0) := Finset.sum_comm
    _ = ∑ k ∈ S, w k * f (φ k) :=
        Finset.sum_congr rfl fun k hk => by
          rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem φ hk)]

theorem torus_step (hac : mu ≪ volume) (hca : volume ≪ mu) (hb : IsRefEigenbasis mu e lam)
    (hC1 : ∀ j, C1T (eC j)) (hae : ∀ j, eC j =ᵐ[mu] e j) {a : ℝ} (ha : 0 < a)
    (hrls : ENNReal.ofReal a ≤ rLS mu) {L : ℝ} {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (φ : ι → (Fin N → ℕ)) (hφ : Function.Injective φ) (w : ι → ℝ)
    (hL : ∀ k ∈ S, w k ≠ 0 → ∑ i, lam (φ k i) ≤ L) (p : ℕ) (hp : 1 ≤ p) :
    ∫⁻ X, ENNReal.ofReal ((∑ k ∈ S, w k * ∏ i, e (φ k i) (X i)) ^ (2 * p))
        ∂(Measure.pi fun _ : Fin N => mu) ≤
      ENNReal.ofReal ((((2 * p : ℝ) - 1) ^ (L / (2 * a))) ^ (2 * p) * (∑ k ∈ S, w k ^ 2) ^ p) := by
  classical
  set Q := Measure.pi fun _ : Fin N => mu with hQ
  set S' := S.filter (fun k => w k ≠ 0) with hS'
  set T := S'.image φ with hT
  set cc : (Fin N → ℕ) → ℝ := fun j => ∑ k ∈ S', if φ k = j then w k else 0 with hcc
  set F : Config N d → ℝ := fun X => ∑ k ∈ S, w k * ∏ i, e (φ k i) (X i) with hF
  have hF1 : ∀ X, F X = ∑ j ∈ T, cc j * ∏ i, e (j i) (X i) := by
    intro X
    have h1 : ∑ k ∈ S', w k * ∏ i, e (φ k i) (X i) = ∑ k ∈ S, w k * ∏ i, e (φ k i) (X i) :=
      Finset.sum_filter_of_ne (fun k _ hk => left_ne_zero_of_mul hk)
    show ∑ k ∈ S, w k * ∏ i, e (φ k i) (X i) = _
    rw [← h1, reindex_sum S' φ w (fun j => ∏ i, e (j i) (X i))]
  have hspec : ∀ j ∈ T, ∑ i, lam (j i) ≤ L := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact hL k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2
  have hInS : InSpectralRange e lam L F := ⟨T, cc, hspec, hF1⟩
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hG := gross_torus hac hca hb hC1 hae ha hrls hInS (q := 2 * p) (by linarith)
  have hE := (torus_energy_formula hac hca hb hC1 hae T cc hF1).1
  -- the sum of squares of the coefficients
  have hcc_eq : ∀ k ∈ S', cc (φ k) = w k := by
    intro k hk
    simp only [hcc]
    rw [Finset.sum_eq_single k]
    · simp
    · intro k' _ hk'
      rw [if_neg]; exact fun h => hk' (hφ h)
    · intro h; exact absurd hk h
  have hsum : ∑ j ∈ T, cc j ^ 2 = ∑ k ∈ S, w k ^ 2 := by
    rw [hT, Finset.sum_image (fun x _ y _ h => hφ h)]
    rw [Finset.sum_congr rfl fun k hk => by rw [hcc_eq k hk]]
    exact Finset.sum_filter_of_ne (fun k _ hk => by
      intro h; apply hk; simp [h])
  have hFu : F =ᵐ[Q] uFun (MT eC T) (fun k : T => cc k.1) := by
    filter_upwards [ae_poly_eq hae T cc] with X hX
    rw [hF1 X, hX]
  have hmem : MemLp F 2 Q :=
    (memLp_uFun (fun k n => memLp_MT hC1 T k n) (fun k : T => cc k.1) (p := 2) (by simp)).ae_eq
      hFu.symm
  have hmeas : AEStronglyMeasurable F Q := hmem.aestronglyMeasurable
  have hF2int : Integrable (fun X => F X ^ 2) Q := hmem.integrable_sq
  -- the (2p)-th power of the (2p)-norm as a lintegral
  have hlp : eLpNorm F (ENNReal.ofReal (2 * p)) Q ^ (2 * p) =
      ∫⁻ X, ENNReal.ofReal (F X ^ (2 * p)) ∂Q := by
    have h2p : ((2 * p : ℕ) : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h := eLpNorm_nnreal_pow_eq_lintegral h2p hmeas
    simp only [NNReal.coe_natCast, ENNReal.rpow_natCast, ENNReal.coe_natCast] at h
    have e1 : (ENNReal.ofReal (2 * (p : ℝ))) = ((2 * p : ℕ) : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_natCast]; push_cast; rfl
    rw [e1, h]
    refine lintegral_congr fun X => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
      (even_two_mul p).pow_abs]
  -- the squared 2-norm as a lintegral
  have hl2 : eLpNorm F 2 Q ^ 2 = ENNReal.ofReal (∑ k ∈ S, w k ^ 2) := by
    have h := eLpNorm_nnreal_pow_eq_lintegral (μ := Q) (f := F) (p := 2) (by norm_num) hmeas
    simp only [NNReal.coe_ofNat, ENNReal.rpow_ofNat, ENNReal.coe_ofNat] at h
    rw [h, ← hsum, ← hE, ofReal_integral_eq_lintegral_ofReal hF2int
      (Filter.Eventually.of_forall fun X => sq_nonneg _)]
    refine lintegral_congr fun X => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have hM0 : 0 ≤ ((2 * p : ℝ) - 1) ^ (L / (2 * a)) :=
    Real.rpow_nonneg (by linarith) _
  rw [← hlp]
  calc eLpNorm F (ENNReal.ofReal (2 * p)) Q ^ (2 * p)
      ≤ (ENNReal.ofReal (((2 * p : ℝ) - 1) ^ (L / (2 * a))) * eLpNorm F 2 Q) ^ (2 * p) := by
        gcongr
    _ = ENNReal.ofReal ((((2 * p : ℝ) - 1) ^ (L / (2 * a))) ^ (2 * p)) *
          (eLpNorm F 2 Q ^ 2) ^ p := by
        rw [mul_pow, ENNReal.ofReal_pow hM0, pow_mul (eLpNorm F 2 Q) 2 p]
    _ = ENNReal.ofReal ((((2 * p : ℝ) - 1) ^ (L / (2 * a))) ^ (2 * p) * (∑ k ∈ S, w k ^ 2) ^ p) := by
        rw [hl2, ← ENNReal.ofReal_pow (Finset.sum_nonneg fun k _ => sq_nonneg _),
          ← ENNReal.ofReal_mul (pow_nonneg hM0 _)]

end SharpLSI.FL.Hyb

end
