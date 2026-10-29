import FullLabeledLSI.Infra.HypercontrHybrid4
import FullLabeledLSI.Infra.HypercontrBonami

/-!
# The Gaussian step and the even-moment hybrid bound

* `gauss_step`: `∫ (∑_{jB} P_{jB}(y)²)^p dγ ≤ (2p-1)^{pD} (∑_j c_j²)^p`, `D = ⌊L/λ₁⌋`
  (Minkowski in `L^p` plus Bonami for the Gaussian polynomials `P_{jB}`).
* `hybrid_even`: for every `p ≥ 1` there is `K` with
  `∫⁻ ofReal ((hybPoly e c B)^{2p}) d(hybMeasure) ≤ ofReal (K (∑_j c_j²)^p)` for all `N`, `B`, `c` with
  `SpectralCoeff lam L c`.
-/

open MeasureTheory SharpLSI
open scoped ENNReal

noncomputable section

namespace SharpLSI.FL.Hyb

open SharpLSI.FL.Gross

variable {N J : ℕ}

/-- The Gaussian reference measure on `(y_{i,m})`. -/
abbrev gaussMeas (N J : ℕ) : Measure (Fin N → Fin J → ℝ) :=
  Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin J => ProbabilityTheory.gaussianReal 0 1

variable (B : Finset (Fin N))

/-- The non-vanishing terms of `P_{jB}`. -/
def KS (c : (Fin N → Fin (J + 1)) → ℝ) (jB : Fin N → Fin (J + 1)) : Finset (Fin N → Fin (J + 1)) :=
  (SC B).filter fun jC => c (mergeJ B jB jC) ≠ 0

lemma Pfun_curried (c : (Fin N → Fin (J + 1)) → ℝ) (jB : Fin N → Fin (J + 1))
    (y : Fin N → Fin J → ℝ) :
    Pfun B c jB y = ∑ k : ↥(KS B c jB), c (mergeJ B jB k.1) * ∏ s ∈ suppC k.1, y s.1 s.2 := by
  unfold Pfun
  rw [Finset.sum_coe_sort (KS B c jB) (fun k => c (mergeJ B jB k) * ∏ s ∈ suppC k, y s.1 s.2)]
  have h : ∑ k ∈ KS B c jB, c (mergeJ B jB k) * ∏ s ∈ suppC k, y s.1 s.2 =
      ∑ k ∈ SC B, c (mergeJ B jB k) * ∏ s ∈ suppC k, y s.1 s.2 := by
    unfold KS
    exact Finset.sum_filter_of_ne (fun k _ hk => left_ne_zero_of_mul hk)
  rw [h]
  exact Finset.sum_congr rfl fun k _ => by rw [gaussFac, prod_gamF_eq]

lemma sum_sq_KS (c : (Fin N → Fin (J + 1)) → ℝ) (jB : Fin N → Fin (J + 1)) :
    ∑ k : ↥(KS B c jB), c (mergeJ B jB k.1) ^ 2 = ∑ jC ∈ SC B, c (mergeJ B jB jC) ^ 2 := by
  rw [Finset.sum_coe_sort (KS B c jB) (fun k => c (mergeJ B jB k) ^ 2)]
  unfold KS
  exact Finset.sum_filter_of_ne (fun k _ hk => by intro h; apply hk; simp [h])

lemma measurable_Pfun (c : (Fin N → Fin (J + 1)) → ℝ) (jB : Fin N → Fin (J + 1)) :
    Measurable (Pfun B c jB : (Fin N → Fin J → ℝ) → ℝ) := by
  have : (Pfun B c jB : (Fin N → Fin J → ℝ) → ℝ) = fun y =>
      ∑ k : ↥(KS B c jB), c (mergeJ B jB k.1) * ∏ s ∈ suppC k.1, y s.1 s.2 := by
    funext y; exact Pfun_curried B c jB y
  rw [this]
  exact Finset.measurable_sum _ fun k _ => measurable_const.mul
    (Finset.measurable_prod _ fun s _ => (measurable_pi_apply s.2).comp (measurable_pi_apply s.1))

variable {lam : ℕ → ℝ}

/-- A non-vanishing coefficient controls the `Bᶜ`-part of the spectral sum. -/
lemma sum_lam_jC_le (hlam0 : lam 0 = 0) (hnn : ∀ m, 0 ≤ lam m) {jB jC : Fin N → Fin (J + 1)}
    (hB : jB ∈ SB B) (hC : jC ∈ SC B) :
    ∑ i, lam (jC i) ≤ ∑ i, lam (mergeJ B jB jC i) ∧ ∑ i, lam (jB i) ≤ ∑ i, lam (mergeJ B jB jC i) := by
  simp only [SB, SC, Finset.mem_filter, Finset.mem_univ, true_and] at hB hC
  constructor <;> refine Finset.sum_le_sum fun i _ => ?_
  · by_cases hi : i ∈ B
    · simp [mergeJ, hi, hC i hi, hlam0, hnn]
    · simp [mergeJ, hi]
  · by_cases hi : i ∈ B
    · simp [mergeJ, hi]
    · simp [mergeJ, hi, hB i hi, hlam0, hnn]

theorem gauss_step (hlam0 : lam 0 = 0) (hnn : ∀ m, 0 ≤ lam m) (h1 : 0 < lam 1)
    (hmono : ∀ m, 1 ≤ m → lam 1 ≤ lam m) {L : ℝ} {c : (Fin N → Fin (J + 1)) → ℝ}
    (hc : SpectralCoeff lam L c) {p : ℕ} (hp : 1 ≤ p) :
    ∫⁻ y, ENNReal.ofReal ((∑ jB ∈ SB B, Pfun B c jB y ^ 2) ^ p) ∂(gaussMeas N J) ≤
      ENNReal.ofReal (((2 * p : ℝ) - 1) ^ (p * ⌊L / lam 1⌋₊) * (∑ j, c j ^ 2) ^ p) := by
  set D := ⌊L / lam 1⌋₊ with hD
  have hPint : ∀ jB, Integrable (fun y => Pfun B c jB y ^ (2 * p)) (gaussMeas N J) := by
    intro jB
    have := Bonami.integrable_curried_pow p (ι := Fin N) (κ := Fin J)
      (fun k : ↥(KS B c jB) => suppC k.1) (fun k => c (mergeJ B jB k.1))
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pfun_curried B c jB y]
  have hPm : ∀ jB, AEStronglyMeasurable (Pfun B c jB) (gaussMeas N J) := fun jB =>
    (measurable_Pfun B c jB).aestronglyMeasurable
  have hmink := Bonami.lintegral_minkowski_sq_sum (μ := gaussMeas N J) (SB B)
    (fun jB y => Pfun B c jB y) hp hPm hPint
  refine hmink.trans (ENNReal.ofReal_le_ofReal ?_)
  have hX : 0 ≤ ((2 * p : ℝ) - 1) ^ D := by
    have : (1 : ℝ) ≤ 2 * p - 1 := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    positivity
  have hbon : ∀ jB ∈ SB B, (∫ y, Pfun B c jB y ^ (2 * p) ∂(gaussMeas N J)) ^ ((1 : ℝ) / p) ≤
      ((2 * p : ℝ) - 1) ^ D * ∑ jC ∈ SC B, c (mergeJ B jB jC) ^ 2 := by
    intro jB hjB
    have hcard : ∀ k : ↥(KS B c jB), (suppC k.1).card ≤ D := by
      intro k
      have hk := k.2
      simp only [KS, Finset.mem_filter] at hk
      obtain ⟨hkC, hne⟩ := hk
      have hspec : ∑ i, lam (mergeJ B jB k.1 i) ≤ L := hc _ hne
      have := (sum_lam_jC_le B hlam0 hnn hjB hkC).1
      have h2 := card_suppC_le hnn h1 hmono (L := L) (jC := k.1) (this.trans hspec)
      exact Nat.le_floor h2
    have hinj : Function.Injective (fun k : ↥(KS B c jB) => suppC k.1) := fun k1 k2 h =>
      Subtype.ext (suppC_injective h)
    have hb := Bonami.gaussian_bonami_curried D p hp (ι := Fin N) (κ := Fin J)
      (fun k : ↥(KS B c jB) => suppC k.1) hinj hcard (fun k => c (mergeJ B jB k.1))
    have hb' : ∫ y, Pfun B c jB y ^ (2 * p) ∂(gaussMeas N J) ≤
        (((2 * p : ℝ) - 1) ^ D * ∑ jC ∈ SC B, c (mergeJ B jB jC) ^ 2) ^ p := by
      simp_rw [Pfun_curried B c jB]
      rw [mul_pow, ← pow_mul, mul_comm D p, ← sum_sq_KS B c jB]
      exact hb
    have hY : 0 ≤ ∑ jC ∈ SC B, c (mergeJ B jB jC) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc (∫ y, Pfun B c jB y ^ (2 * p) ∂(gaussMeas N J)) ^ ((1 : ℝ) / p)
        ≤ ((((2 * p : ℝ) - 1) ^ D * ∑ jC ∈ SC B, c (mergeJ B jB jC) ^ 2) ^ p) ^ ((1 : ℝ) / p) :=
          Real.rpow_le_rpow (integral_nonneg fun y => by
            rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _) hb' (by positivity)
      _ = _ := by
          rw [one_div, Real.pow_rpow_inv_natCast (mul_nonneg hX hY) (by omega)]
  have hsum : ∑ jB ∈ SB B, (∫ y, Pfun B c jB y ^ (2 * p) ∂(gaussMeas N J)) ^ ((1 : ℝ) / p) ≤
      ((2 * p : ℝ) - 1) ^ D * ∑ j, c j ^ 2 := by
    calc _ ≤ ∑ jB ∈ SB B, (((2 * p : ℝ) - 1) ^ D * ∑ jC ∈ SC B, c (mergeJ B jB jC) ^ 2) :=
          Finset.sum_le_sum hbon
      _ = ((2 * p : ℝ) - 1) ^ D * ∑ jB ∈ SB B, ∑ jC ∈ SC B, c (mergeJ B jB jC) ^ 2 := by
          rw [Finset.mul_sum]
      _ = _ := by rw [← sum_split B (fun j => c j ^ 2)]
  have hnn' : 0 ≤ ∑ jB ∈ SB B, (∫ y, Pfun B c jB y ^ (2 * p) ∂(gaussMeas N J)) ^ ((1 : ℝ) / p) :=
    Finset.sum_nonneg fun jB _ => Real.rpow_nonneg (integral_nonneg fun y => by
      rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _) _
  calc (∑ jB ∈ SB B, (∫ y, Pfun B c jB y ^ (2 * p) ∂(gaussMeas N J)) ^ ((1 : ℝ) / p)) ^ p
      ≤ (((2 * p : ℝ) - 1) ^ D * ∑ j, c j ^ 2) ^ p := pow_le_pow_left₀ hnn' hsum p
    _ = _ := by rw [mul_pow, ← pow_mul, mul_comm D p]

end SharpLSI.FL.Hyb

end
