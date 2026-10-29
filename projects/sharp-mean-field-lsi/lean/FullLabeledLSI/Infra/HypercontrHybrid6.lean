import FullLabeledLSI.Infra.HypercontrHybrid5
import FullLabeledLSI.Infra.HypercontrHybrid3

/-!
# `hybrid_poly_moment`: uniform moments of spectral polynomials on the hybrid space

For fixed `mu, e, lam, J, L, q` there is `K ≥ 0` such that for all `N`, all retained sets `B` and all
`SpectralCoeff lam L c`:
`∫⁻ ofReal (|hybPoly e c B|^q) d hybMeasure ≤ ofReal (K * (√(∑ c²))^q)`.
-/

open MeasureTheory SharpLSI
open scoped ENNReal

noncomputable section

namespace SharpLSI.FL.Hyb

open SharpLSI.FL.Gross

variable {d N J : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e eC : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

instance hybMeasure_prob : IsProbabilityMeasure (hybMeasure mu N J) := by
  unfold hybMeasure; infer_instance

theorem hybrid_even (hac : mu ≪ volume) (hca : volume ≪ mu) (hb : IsRefEigenbasis mu e lam)
    (hC1 : ∀ j, C1T (eC j)) (hae : ∀ j, eC j =ᵐ[mu] e j) {a : ℝ} (ha : 0 < a)
    (hrls : ENNReal.ofReal a ≤ rLS mu) (hlam0 : lam 0 = 0) (hnn : ∀ m, 0 ≤ lam m)
    (h1 : 0 < lam 1) (hmono : ∀ m, 1 ≤ m → lam 1 ≤ lam m) (J : ℕ) (L : ℝ) {p : ℕ} (hp : 1 ≤ p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (B : Finset (Fin N)) (c : (Fin N → Fin (J + 1)) → ℝ),
      SpectralCoeff lam L c →
      ∫⁻ ω, ENNReal.ofReal ((hybPoly e c B ω) ^ (2 * p)) ∂(hybMeasure mu N J) ≤
        ENNReal.ofReal (K * (∑ j, c j ^ 2) ^ p) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hM0 : 0 ≤ (((2 * p : ℝ) - 1) ^ (L / (2 * a))) ^ (2 * p) :=
    pow_nonneg (Real.rpow_nonneg (by linarith) _) _
  have hX0 : 0 ≤ ((2 * p : ℝ) - 1) ^ (p * ⌊L / lam 1⌋₊) := pow_nonneg (by linarith) _
  refine ⟨(((2 * p : ℝ) - 1) ^ (L / (2 * a))) ^ (2 * p) *
    ((2 * p : ℝ) - 1) ^ (p * ⌊L / lam 1⌋₊), mul_nonneg hM0 hX0, ?_⟩
  intro N B c hc
  rw [lintegral_hyb_split hC1 hae c B (2 * p)]
  have he0 := hb.zero
  have hinj : Function.Injective (fun (jB : Fin N → Fin (J + 1)) (i : Fin N) => (jB i : ℕ)) :=
    fun j1 j2 h => funext fun i => Fin.ext (congrFun h i)
  have hL : ∀ y, ∀ k ∈ SB B, Pfun B c k y ≠ 0 →
      ∑ i, lam ((fun (jB : Fin N → Fin (J + 1)) (i : Fin N) => (jB i : ℕ)) k i) ≤ L := by
    intro y k hk hne
    unfold Pfun at hne
    obtain ⟨jC, hjC, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hcne : c (mergeJ B k jC) ≠ 0 := left_ne_zero_of_mul hne'
    have h2 := (sum_lam_jC_le B hlam0 hnn hk hjC).2
    exact h2.trans (hc _ hcne)
  have hpt : ∀ y, ∫⁻ x, ENNReal.ofReal ((hybPoly e c B (x, y)) ^ (2 * p))
        ∂(Measure.pi fun _ : Fin N => mu) ≤
      ENNReal.ofReal ((((2 * p : ℝ) - 1) ^ (L / (2 * a))) ^ (2 * p) *
        (∑ jB ∈ SB B, Pfun B c jB y ^ 2) ^ p) := by
    intro y
    have h := torus_step hac hca hb hC1 hae ha hrls (L := L) (SB B)
      (fun (jB : Fin N → Fin (J + 1)) (i : Fin N) => (jB i : ℕ)) hinj
      (fun jB => Pfun B c jB y) (hL y) p hp
    refine le_trans (le_of_eq ?_) h
    refine lintegral_congr fun x => ?_
    rw [hybPoly_eq B e he0 c x y]
    congr 2
    refine Finset.sum_congr rfl fun jB _ => ?_
    unfold torusFac
    ring
  have hG := gauss_step B hlam0 hnn h1 hmono hc hp
  calc ∫⁻ y, ∫⁻ x, ENNReal.ofReal ((hybPoly e c B (x, y)) ^ (2 * p))
        ∂(Measure.pi fun _ : Fin N => mu) ∂(gaussMeas N J)
      ≤ ∫⁻ y, ENNReal.ofReal ((((2 * p : ℝ) - 1) ^ (L / (2 * a))) ^ (2 * p) *
          (∑ jB ∈ SB B, Pfun B c jB y ^ 2) ^ p) ∂(gaussMeas N J) := lintegral_mono hpt
    _ = ENNReal.ofReal ((((2 * p : ℝ) - 1) ^ (L / (2 * a))) ^ (2 * p)) *
          ∫⁻ y, ENNReal.ofReal ((∑ jB ∈ SB B, Pfun B c jB y ^ 2) ^ p) ∂(gaussMeas N J) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun y => ?_
        rw [ENNReal.ofReal_mul hM0]
    _ ≤ ENNReal.ofReal ((((2 * p : ℝ) - 1) ^ (L / (2 * a))) ^ (2 * p)) *
          ENNReal.ofReal (((2 * p : ℝ) - 1) ^ (p * ⌊L / lam 1⌋₊) * (∑ j, c j ^ 2) ^ p) :=
        mul_le_mul' le_rfl hG
    _ = _ := by
        rw [← ENNReal.ofReal_mul hM0]
        congr 1; ring

/-- Scaling `c ↦ c / s` and the pointwise bound `|t|^q ≤ 1 + t^{2q}` give all natural `q`. -/
theorem hybrid_poly_moment (hac : mu ≪ volume) (hca : volume ≪ mu) (hb : IsRefEigenbasis mu e lam)
    (hC1 : ∀ j, C1T (eC j)) (hae : ∀ j, eC j =ᵐ[mu] e j) {a : ℝ} (ha : 0 < a)
    (hrls : ENNReal.ofReal a ≤ rLS mu) (hlam0 : lam 0 = 0) (hnn : ∀ m, 0 ≤ lam m)
    (h1 : 0 < lam 1) (hmono : ∀ m, 1 ≤ m → lam 1 ≤ lam m) (J : ℕ) (L : ℝ) (q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (B : Finset (Fin N)) (c : (Fin N → Fin (J + 1)) → ℝ),
      SpectralCoeff lam L c →
      ∫⁻ ω, ENNReal.ofReal (|hybPoly e c B ω| ^ q) ∂(hybMeasure mu N J) ≤
        ENNReal.ofReal (K * (Real.sqrt (∑ j, c j ^ 2)) ^ q) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine ⟨1, zero_le_one, fun N B c _ => ?_⟩
    simp
  · obtain ⟨K0, hK0, hK⟩ := hybrid_even hac hca hb hC1 hae ha hrls hlam0 hnn h1 hmono J L hq
    refine ⟨K0 + 1, by linarith, fun N B c hc => ?_⟩
    set s := Real.sqrt (∑ j, c j ^ 2) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    rcases hs0.eq_or_lt with hs00 | hspos
    · -- all coefficients vanish
      have hz : ∀ j, c j = 0 := by
        intro j
        have : ∑ j, c j ^ 2 = 0 := by
          have := Real.sqrt_eq_zero'.mp hs00.symm
          exact le_antisymm this (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp this j
          (Finset.mem_univ j)
        exact pow_eq_zero_iff (by norm_num) |>.mp h2
      have hF : ∀ ω, hybPoly e c B ω = 0 := fun ω => by simp [hybPoly, hz]
      simp [hF, zero_pow hq.ne']
    · set c' : (Fin N → Fin (J + 1)) → ℝ := fun j => c j / s with hc'
      have hc'spec : SpectralCoeff lam L c' := by
        intro j hj
        apply hc
        intro h0; apply hj; simp [hc', h0]
      have hs2 : s ^ 2 = ∑ j, c j ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      have hsum' : ∑ j, c' j ^ 2 = 1 := by
        simp only [hc', div_pow]
        rw [← Finset.sum_div, ← hs2]
        exact div_self (by positivity)
      have hscale : ∀ ω, hybPoly e c B ω = s * hybPoly e c' B ω := by
        intro ω
        unfold hybPoly
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hc']
        field_simp
      have hbound := hK N B c' hc'spec
      rw [hsum'] at hbound
      simp only [one_pow, mul_one] at hbound
      have hpt : ∀ ω, ENNReal.ofReal (|hybPoly e c B ω| ^ q) ≤
          ENNReal.ofReal (s ^ q) * (1 + ENNReal.ofReal ((hybPoly e c' B ω) ^ (2 * q))) := by
        intro ω
        rw [hscale ω, abs_mul, abs_of_nonneg hs0, mul_pow]
        rw [ENNReal.ofReal_mul (pow_nonneg hs0 _)]
        refine mul_le_mul' le_rfl ?_
        have hev : (hybPoly e c' B ω) ^ (2 * q) = |hybPoly e c' B ω| ^ (2 * q) :=
          ((even_two_mul q).pow_abs _).symm
        rw [hev]
        set t := |hybPoly e c' B ω|
        have ht : 0 ≤ t := abs_nonneg _
        have hle : t ^ q ≤ 1 + t ^ (2 * q) := by
          rcases le_total t 1 with h | h
          · have : t ^ q ≤ 1 := pow_le_one₀ ht h
            have : 0 ≤ t ^ (2 * q) := pow_nonneg ht _
            linarith
          · have : t ^ q ≤ t ^ (2 * q) := pow_le_pow_right₀ h (by omega)
            have : 0 ≤ (1 : ℝ) := zero_le_one
            linarith
        calc ENNReal.ofReal (t ^ q) ≤ ENNReal.ofReal (1 + t ^ (2 * q)) :=
              ENNReal.ofReal_le_ofReal hle
          _ = 1 + ENNReal.ofReal (t ^ (2 * q)) := by
              rw [ENNReal.ofReal_add zero_le_one (pow_nonneg ht _), ENNReal.ofReal_one]
      calc ∫⁻ ω, ENNReal.ofReal (|hybPoly e c B ω| ^ q) ∂(hybMeasure mu N J)
          ≤ ∫⁻ ω, ENNReal.ofReal (s ^ q) * (1 + ENNReal.ofReal ((hybPoly e c' B ω) ^ (2 * q)))
              ∂(hybMeasure mu N J) := lintegral_mono hpt
        _ = ENNReal.ofReal (s ^ q) * (1 + ∫⁻ ω, ENNReal.ofReal ((hybPoly e c' B ω) ^ (2 * q))
              ∂(hybMeasure mu N J)) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
        _ ≤ ENNReal.ofReal (s ^ q) * (1 + ENNReal.ofReal K0) :=
            mul_le_mul' le_rfl (add_le_add le_rfl hbound)
        _ = ENNReal.ofReal ((K0 + 1) * s ^ q) := by
            rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hK0,
              ← ENNReal.ofReal_mul (pow_nonneg hs0 q)]
            congr 1; ring

end SharpLSI.FL.Hyb

end
