import SharpSymmetricLSI.Paper.RefSpectrum10
import SharpSymmetricLSI.Paper.Moser5

/-!
# R23 (6.1), part 11: polynomial moment bounds for eigenfunctions

For eigenpairs `(e, λ)` of `P = ρm` (`IsEig`): `|e| ≤ K_B(1+λ)^d` (Moser, `moser_bound`), and for
every `m` there are `K, q` with `∫|∂ₖe|^{2^{m+1}} ≤ K(1+λ)^q` and `∫|g|^{2^{m+1}} ≤ K(1+λ)^q`,
`g = λe + b·∇e` (`moments`), uniformly over all eigenpairs.
-/

open MeasureTheory Filter Topology Complex
open scoped ENNReal Real ContDiff NNReal
open UnitAddTorus

namespace SharpLSI

variable {d : ℕ}

/-- `(e, λ)` is a normalized weak eigenpair of `P`. -/
def IsEig (P : Measure (Torus d)) (e : Torus d → ℝ) (lam : ℝ) : Prop :=
  MemH1 P e ∧ ∫ x, e x ^ 2 ∂P = 1 ∧
    ∀ φ, MemH1 P φ → dirB P e φ = lam * ∫ x, e x * φ x ∂P

theorem pow_le_pow_of_one_le {x : ℝ} (hx : 1 ≤ x) {a b : ℕ} (hab : a ≤ b) : x ^ a ≤ x ^ b :=
  pow_le_pow_right₀ hx hab

section poly

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C) (hρc : Continuous ρ) {Lσ : ℝ≥0}
  (hσ : LipschitzWith Lσ (recipD ρ ∘ liftT))
include hρ

theorem IsEig.lam_eq {e : Torus d → ℝ} {lam : ℝ} (h : IsEig (densMeasure ρ) e lam) :
    lam = dirE (densMeasure ρ) e := by
  have h1 := h.2.2 e h.1
  have h2 : ∫ x, e x * e x ∂densMeasure ρ = 1 := by
    have := h.2.1; simp_rw [sq] at this; exact this
  rw [h2, mul_one] at h1
  rw [← h1, dirE_eq_dirB hρ]

theorem IsEig.lam_nonneg {e : Torus d → ℝ} {lam : ℝ} (h : IsEig (densMeasure ρ) e lam) :
    0 ≤ lam := by
  rw [h.lam_eq hρ]; exact dirE_nonneg hρ e

/-- **Moser: polynomial `L^∞` bound.** -/
theorem moser_bound : ∃ KB : ℝ, 0 ≤ KB ∧ ∀ e lam, IsEig (densMeasure ρ) e lam →
    ∀ᵐ y ∂volume, |e y| ≤ KB * (1 + lam) ^ d := by
  haveI := hρ.isProb
  set a := 1 / c
  set b := C
  have ha0 : 0 < a := by have := hρ.pos; positivity
  have hb0 : 0 < b := hρ.C_pos
  set D := max (2 * a * b) 2
  refine ⟨Real.sqrt a * (2 * (3 * D) ^ d) * 4 ^ d, by positivity, fun e lam h => ?_⟩
  have hlam := h.lam_nonneg hρ
  have hm := ae_abs_le_moser ha0 hb0 hρ.haar_le_smul hρ.le_smul h.1 hlam (fun φ hφ => h.2.2 φ hφ)
  filter_upwards [hm] with y hy
  refine hy.trans ?_
  have hN : moserN e 0 ≤ Real.sqrt a := by
    have hm0 : mSeq 0 = 1 := by simp [mSeq]
    have hI : ∫ x, |e x| ^ 2 ≤ a := by
      have := integral_le_smul_of_le ha0.le hρ.haar_le_smul (fun x => sq_nonneg (e x))
        h.1.2.1.integrable_sq
      rw [h.2.1, mul_one] at this
      simpa [sq_abs] using this
    have : moserN e 0 = Real.sqrt (∫ x, |e x| ^ 2) := by
      simp only [moserN, hm0, mul_one]
      rw [Real.sqrt_eq_rpow]
      norm_num
    rw [this]
    exact Real.sqrt_le_sqrt hI
  have hA : moserA (Fin d) a b lam ≤ 2 * (3 * D) ^ d * (1 + lam) ^ d := by
    unfold moserA
    rw [Fintype.card_fin]
    have h1 : 2 * a * b ≤ D := le_max_left _ _
    have h2 : (2 : ℝ) ≤ D := le_max_right _ _
    have hb : 3 * (2 * a * b * lam + 2) ≤ 3 * D * (1 + lam) := by nlinarith
    calc 2 * (3 * (2 * a * b * lam + 2)) ^ d ≤ 2 * (3 * D * (1 + lam)) ^ d := by
          gcongr
      _ = 2 * (3 * D) ^ d * (1 + lam) ^ d := by rw [mul_pow]; ring
  have hA0 : 0 ≤ moserA (Fin d) a b lam := by unfold moserA; positivity
  calc moserN e 0 * moserA (Fin d) a b lam * 4 ^ Fintype.card (Fin d)
      ≤ Real.sqrt a * (2 * (3 * D) ^ d * (1 + lam) ^ d) * 4 ^ d := by
        rw [Fintype.card_fin]
        gcongr
    _ = Real.sqrt a * (2 * (3 * D) ^ d) * 4 ^ d * (1 + lam) ^ d := by ring

theorem lintegral_enorm_pow_le_ofReal {f : Torus d → ℝ} (hf : AEStronglyMeasurable f volume)
    (N : ℕ) : ∫⁻ y, ‖f y‖ₑ ^ (N : ℝ) = ∫⁻ y, ENNReal.ofReal (|f y| ^ N) := by
  refine lintegral_congr fun y => ?_
  rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _)
    (Nat.cast_nonneg _), Real.rpow_natCast]

include hρc hσ in
/-- From gradient moments to moments of `g = λe + b·∇e`. -/
theorem src_moment (hd : 1 ≤ d) (N : ℕ) (hN : 1 ≤ N) {KB K : ℝ} {q : ℕ} (hKB : 0 ≤ KB)
    (hK : 0 ≤ K) {e : Torus d → ℝ} {lam : ℝ} (h : IsEig (densMeasure ρ) e lam)
    (hB : ∀ᵐ y ∂volume, |e y| ≤ KB * (1 + lam) ^ d)
    (hG : ∀ k, ∫⁻ y, ‖weakGrad e y k‖ₑ ^ (N : ℝ) ≤ ENNReal.ofReal (K * (1 + lam) ^ q)) :
    ∫⁻ y, ‖srcG ρ lam e y‖ₑ ^ (N : ℝ) ≤
      ENNReal.ofReal (2 ^ (N - 1) * (KB ^ N + (C * Lσ) ^ N * d ^ N * K) *
        (1 + lam) ^ (N + d * N + q)) := by
  haveI := hρ.isProb
  have hlam := h.lam_nonneg hρ
  set ℓ := C * Lσ
  have hℓ : 0 ≤ ℓ := mul_nonneg hρ.C_pos.le Lσ.2
  have hev : MemLp e 2 volume := memLp_vol hρ.haar_le_smul h.1
  have hge : ∀ k, MemLp (fun y => weakGrad e y k) 2 volume := fun k =>
    memLp_grad_vol hρ.haar_le_smul hρ.le_smul h.1 k
  have hsg := memLp_srcG hρ hρc hσ h.1 lam
  set B := KB * (1 + lam) ^ d
  have hB0 : 0 ≤ B := by positivity
  -- pointwise
  have hpt : ∀ y, |srcG ρ lam e y| ^ N ≤
      2 ^ (N - 1) * (lam ^ N * |e y| ^ N + ℓ ^ N * ((d : ℝ) ^ (N - 1) * ∑ k, |weakGrad e y k| ^ N)) := by
    intro y
    have h1 : |srcG ρ lam e y| ≤ lam * |e y| + ℓ * ∑ k, |weakGrad e y k| := by
      unfold srcG
      refine (abs_add_le _ _).trans (add_le_add (by rw [abs_mul, abs_of_nonneg hlam]) ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (abs_driftB_le hρ hρc hσ y k) (abs_nonneg _)
    have h2 : (lam * |e y| + ℓ * ∑ k, |weakGrad e y k|) ^ N ≤
        2 ^ (N - 1) * ((lam * |e y|) ^ N + (ℓ * ∑ k, |weakGrad e y k|) ^ N) := by
      have := Real.rpow_sum_le_const_mul_sum_rpow (s := Finset.univ)
        (f := ![lam * |e y|, ℓ * ∑ k, |weakGrad e y k|]) (p := (N : ℝ)) (by exact_mod_cast hN)
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Finset.card_univ,
        Fintype.card_fin] at this
      rw [abs_of_nonneg (mul_nonneg hlam (abs_nonneg (e y))),
        abs_of_nonneg (mul_nonneg hℓ (Finset.sum_nonneg fun k _ => abs_nonneg (weakGrad e y k)))]
        at this
      simp only [Real.rpow_natCast] at this
      rw [show ((2 : ℕ) : ℝ) ^ ((N : ℝ) - 1) = 2 ^ (N - 1) by
        rw [← Real.rpow_natCast, Nat.cast_sub hN]; push_cast; rfl] at this
      exact this
    have h3 : (∑ k, |weakGrad e y k|) ^ N ≤ (d : ℝ) ^ (N - 1) * ∑ k, |weakGrad e y k| ^ N := by
      have := Real.rpow_sum_le_const_mul_sum_rpow (s := Finset.univ)
        (f := fun k => weakGrad e y k) (p := (N : ℝ)) (by exact_mod_cast hN)
      simp only [Finset.card_univ, Fintype.card_fin, Real.rpow_natCast] at this
      rw [show ((d : ℕ) : ℝ) ^ ((N : ℝ) - 1) = (d : ℝ) ^ (N - 1) by
        rw [← Real.rpow_natCast, Nat.cast_sub hN]; push_cast; rfl] at this
      exact this
    calc |srcG ρ lam e y| ^ N ≤ (lam * |e y| + ℓ * ∑ k, |weakGrad e y k|) ^ N :=
          pow_le_pow_left₀ (abs_nonneg _) h1 N
      _ ≤ 2 ^ (N - 1) * ((lam * |e y|) ^ N + (ℓ * ∑ k, |weakGrad e y k|) ^ N) := h2
      _ ≤ _ := by
          rw [mul_pow, mul_pow]
          gcongr
  set a1 : ℝ := 2 ^ (N - 1) * lam ^ N
  set a2 : ℝ := 2 ^ (N - 1) * (ℓ ^ N * (d : ℝ) ^ (N - 1))
  have ha1 : 0 ≤ a1 := by positivity
  have ha2 : 0 ≤ a2 := by positivity
  have hEm : AEMeasurable (fun y => ENNReal.ofReal (|e y| ^ N)) volume :=
    (hev.aestronglyMeasurable.aemeasurable.abs.pow_const N).ennreal_ofReal
  have hGm : ∀ k, AEMeasurable (fun y => ENNReal.ofReal (|weakGrad e y k| ^ N)) volume := fun k =>
    ((hge k).aestronglyMeasurable.aemeasurable.abs.pow_const N).ennreal_ofReal
  have hEB : ∫⁻ y, ENNReal.ofReal (|e y| ^ N) ≤ ENNReal.ofReal (B ^ N) := by
    calc ∫⁻ y, ENNReal.ofReal (|e y| ^ N) ≤ ∫⁻ _, ENNReal.ofReal (B ^ N) :=
          lintegral_mono_ae (hB.mono fun y hy =>
            ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) hy N))
      _ = ENNReal.ofReal (B ^ N) := by simp
  have hGK : ∀ k, ∫⁻ y, ENNReal.ofReal (|weakGrad e y k| ^ N) ≤
      ENNReal.ofReal (K * (1 + lam) ^ q) := fun k => by
    rw [← lintegral_enorm_pow_le_ofReal hρ (hge k).aestronglyMeasurable]; exact hG k
  rw [lintegral_enorm_pow_le_ofReal hρ hsg.aestronglyMeasurable]
  calc ∫⁻ y, ENNReal.ofReal (|srcG ρ lam e y| ^ N)
      ≤ ∫⁻ y, (ENNReal.ofReal a1 * ENNReal.ofReal (|e y| ^ N) +
          ∑ k, ENNReal.ofReal a2 * ENNReal.ofReal (|weakGrad e y k| ^ N)) := by
        refine lintegral_mono fun y => ?_
        rw [← ENNReal.ofReal_mul ha1]
        simp_rw [← ENNReal.ofReal_mul ha2]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity),
          ← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun k _ => by positivity)]
        refine ENNReal.ofReal_le_ofReal ((hpt y).trans (le_of_eq ?_))
        simp only [a1, a2, Finset.mul_sum, mul_add]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun k _ => by ring
    _ = ENNReal.ofReal a1 * (∫⁻ y, ENNReal.ofReal (|e y| ^ N)) +
          ∑ k, ENNReal.ofReal a2 * ∫⁻ y, ENNReal.ofReal (|weakGrad e y k| ^ N) := by
        rw [lintegral_add_left' (hEm.const_mul _), lintegral_const_mul'' _ hEm,
          lintegral_finset_sum' _ fun k _ => (hGm k).const_mul _]
        congr 1
        exact Finset.sum_congr rfl fun k _ => lintegral_const_mul'' (ENNReal.ofReal a2) (hGm k)
    _ ≤ ENNReal.ofReal a1 * ENNReal.ofReal (B ^ N) +
          ∑ _k : Fin d, ENNReal.ofReal a2 * ENNReal.ofReal (K * (1 + lam) ^ q) := by
        exact add_le_add (mul_le_mul' le_rfl hEB)
          (Finset.sum_le_sum fun k _ => mul_le_mul' le_rfl (hGK k))
    _ = ENNReal.ofReal (a1 * B ^ N + d * (a2 * (K * (1 + lam) ^ q))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_mul ha1, ← ENNReal.ofReal_mul ha2, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1l : 1 ≤ 1 + lam := by linarith
        have hl : lam ≤ 1 + lam := by linarith
        have hp1 : (1 + lam) ^ (N + d * N) ≤ (1 + lam) ^ (N + d * N + q) :=
          pow_le_pow_of_one_le h1l (by omega)
        have hp2 : (1 + lam) ^ q ≤ (1 + lam) ^ (N + d * N + q) :=
          pow_le_pow_of_one_le h1l (by omega)
        have hdN : (d : ℝ) * (d : ℝ) ^ (N - 1) = (d : ℝ) ^ N := by
          rw [← pow_succ']; congr 1; omega
        have hlN : lam ^ N ≤ (1 + lam) ^ N := pow_le_pow_left₀ hlam hl N
        have hBN : B ^ N = KB ^ N * (1 + lam) ^ (d * N) := by
          simp only [B]; rw [mul_pow, ← pow_mul]
        have e1 : a1 * B ^ N ≤ 2 ^ (N - 1) * KB ^ N * (1 + lam) ^ (N + d * N + q) := by
          rw [hBN]
          calc a1 * (KB ^ N * (1 + lam) ^ (d * N))
              = 2 ^ (N - 1) * KB ^ N * (lam ^ N * (1 + lam) ^ (d * N)) := by simp only [a1]; ring
            _ ≤ 2 ^ (N - 1) * KB ^ N * ((1 + lam) ^ N * (1 + lam) ^ (d * N)) := by gcongr
            _ = 2 ^ (N - 1) * KB ^ N * (1 + lam) ^ (N + d * N) := by rw [pow_add]
            _ ≤ _ := by gcongr
        have e2 : d * (a2 * (K * (1 + lam) ^ q)) ≤
            2 ^ (N - 1) * (ℓ ^ N * d ^ N * K) * (1 + lam) ^ (N + d * N + q) := by
          calc (d : ℝ) * (a2 * (K * (1 + lam) ^ q))
              = 2 ^ (N - 1) * (ℓ ^ N * ((d : ℝ) * d ^ (N - 1)) * K) * (1 + lam) ^ q := by
                simp only [a2]; ring
            _ = 2 ^ (N - 1) * (ℓ ^ N * d ^ N * K) * (1 + lam) ^ q := by rw [hdN]
            _ ≤ _ := by gcongr
        calc a1 * B ^ N + d * (a2 * (K * (1 + lam) ^ q))
            ≤ 2 ^ (N - 1) * KB ^ N * (1 + lam) ^ (N + d * N + q) +
              2 ^ (N - 1) * (ℓ ^ N * d ^ N * K) * (1 + lam) ^ (N + d * N + q) := add_le_add e1 e2
          _ = _ := by ring

include hρc hσ in
/-- **Polynomial moment bounds** for all eigenpairs. -/
theorem moments (hd : 1 ≤ d) (m : ℕ) : ∃ K : ℝ, ∃ q : ℕ, 0 ≤ K ∧
    ∀ e lam, IsEig (densMeasure ρ) e lam →
      (∀ k, ∫⁻ y, ‖weakGrad e y k‖ₑ ^ ((2 ^ (m + 1) : ℕ) : ℝ) ≤
        ENNReal.ofReal (K * (1 + lam) ^ q)) ∧
      ∫⁻ y, ‖srcG ρ lam e y‖ₑ ^ ((2 ^ (m + 1) : ℕ) : ℝ) ≤ ENNReal.ofReal (K * (1 + lam) ^ q) := by
  haveI := hρ.isProb
  obtain ⟨KB, hKB, hBnd⟩ := moser_bound hρ
  -- gradient moments imply source moments (same exponent)
  have upg : ∀ N : ℕ, 1 ≤ N → ∀ K : ℝ, ∀ q : ℕ, 0 ≤ K →
      (∀ e lam, IsEig (densMeasure ρ) e lam →
        ∀ k, ∫⁻ y, ‖weakGrad e y k‖ₑ ^ (N : ℝ) ≤ ENNReal.ofReal (K * (1 + lam) ^ q)) →
      ∃ K' : ℝ, ∃ q' : ℕ, 0 ≤ K' ∧ ∀ e lam, IsEig (densMeasure ρ) e lam →
        (∀ k, ∫⁻ y, ‖weakGrad e y k‖ₑ ^ (N : ℝ) ≤ ENNReal.ofReal (K' * (1 + lam) ^ q')) ∧
        ∫⁻ y, ‖srcG ρ lam e y‖ₑ ^ (N : ℝ) ≤ ENNReal.ofReal (K' * (1 + lam) ^ q') := by
    intro N hN K q hK hG
    set K2 := 2 ^ (N - 1) * (KB ^ N + (C * Lσ) ^ N * d ^ N * K)
    have hK2 : 0 ≤ K2 := by
      have := hρ.C_pos; positivity
    refine ⟨K + K2, N + d * N + q, by positivity, fun e lam h => ⟨fun k => ?_, ?_⟩⟩
    · refine (hG e lam h k).trans (ENNReal.ofReal_le_ofReal ?_)
      have hl := h.lam_nonneg hρ
      have h1 : (1 + lam) ^ q ≤ (1 + lam) ^ (N + d * N + q) :=
        pow_le_pow_of_one_le (by linarith) (by omega)
      have : 0 ≤ (1 + lam) ^ (N + d * N + q) := by positivity
      nlinarith
    · refine (src_moment hρ hρc hσ hd N hN hKB hK h (hBnd e lam h) (hG e lam h)).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have hl := h.lam_nonneg hρ
      have : 0 ≤ (1 + lam) ^ (N + d * N + q) := by positivity
      nlinarith
  induction m with
  | zero =>
    refine upg 2 (by norm_num) (1 / c) 1 (by have := hρ.pos; positivity) fun e lam h k => ?_
    have hgP := gradP hρ h.1 k
    rw [lintegral_enorm_pow_le_ofReal hρ ((memLp_grad_vol hρ.haar_le_smul hρ.le_smul h.1 k).aestronglyMeasurable),
      ← ofReal_integral_eq_lintegral_ofReal
        ((memLp_grad_vol hρ.haar_le_smul hρ.le_smul h.1 k).integrable_sq.congr
          (Eventually.of_forall fun y => by simp [sq_abs]))
        (Eventually.of_forall fun y => by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hc0 : 0 ≤ 1 / c := by have := hρ.pos; positivity
    have h1 := integral_le_smul_of_le hc0 hρ.haar_le_smul (fun y => sq_nonneg (weakGrad e y k))
      hgP.integrable_sq
    have h2 : ∫ y, weakGrad e y k ^ 2 ∂densMeasure ρ ≤ lam := by
      rw [h.lam_eq hρ, dirE]
      exact integral_mono (gradP hρ h.1 k).integrable_sq
        (integrable_finset_sum _ fun j _ => (gradP hρ h.1 j).integrable_sq)
        fun y => Finset.single_le_sum (f := fun j => weakGrad e y j ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
    simp_rw [sq_abs]
    calc ∫ y, weakGrad e y k ^ 2 ≤ 1 / c * ∫ y, weakGrad e y k ^ 2 ∂densMeasure ρ := h1
      _ ≤ 1 / c * (1 + lam) ^ 1 := by
          gcongr; rw [pow_one]; linarith
  | succ m ih =>
    obtain ⟨K, q, hK, hKq⟩ := ih
    obtain ⟨A, hA0, hA⟩ := grad_step (ι := Fin d) m
    set N : ℕ := 2 ^ (m + 1)
    have hN1 : 1 ≤ N := Nat.one_le_two_pow
    set K3 := ((2 * N - 1) * KB) ^ N * A ^ N * K
    have hK3 : 0 ≤ K3 := by
      have : (1 : ℝ) ≤ 2 * N - 1 := by
        have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
        linarith
      exact mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg (by linarith) hKB) _)
        (pow_nonneg hA0 _)) hK
    refine upg (2 ^ (m + 1 + 1)) Nat.one_le_two_pow K3 (d * N + q) hK3 fun e lam h k => ?_
    have hl := h.lam_nonneg hρ
    have hst := hA e (srcG ρ lam e) (weakGrad e) (memLp_vol hρ.haar_le_smul h.1)
      (memLp_srcG hρ hρc hσ h.1 lam) (isWeakGrad_weakGrad h.1.1)
      (fun k => memLp_grad_vol hρ.haar_le_smul hρ.le_smul h.1 k)
      (cf_srcG hρ hρc hσ h.1 h.2.2) _ (hBnd e lam h) k
    have hg := (hKq e lam h).2
    have e1 : ((2 : ℝ) ^ (m + 1 + 1)) = ((2 ^ (m + 1 + 1) : ℕ) : ℝ) := by push_cast; rfl
    have e2 : ((2 : ℝ) ^ (m + 1)) = ((2 ^ (m + 1) : ℕ) : ℝ) := by push_cast; rfl
    rw [e1, e2] at hst
    refine hst.trans ?_
    refine (mul_le_mul' le_rfl hg).trans ?_
    rw [← ENNReal.ofReal_mul (by
      have : (1 : ℝ) ≤ 2 * 2 ^ (m + 1) - 1 := by
        have : (1 : ℝ) ≤ 2 ^ (m + 1) := one_le_pow₀ (by norm_num)
        linarith
      exact mul_nonneg (pow_nonneg (mul_nonneg (by linarith) (mul_nonneg hKB
        (pow_nonneg (by linarith) _))) _) (pow_nonneg hA0 _))]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    simp only [K3, N]
    push_cast
    simp only [mul_pow, ← pow_mul, pow_add]
    ring

end poly

end SharpLSI
