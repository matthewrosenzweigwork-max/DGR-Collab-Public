import FullLabeledLSI.Paper.Hybrid63AltD

/-!
# Proposition 6.3, step R4b (7.21): the moment bounds on the pair space

`pair_moments`: uniform bounds for `∫ |P|^8`, `∫ |Zfp + Zlow|^4` and
`∫ |Zfp - Zlow|^2 ≤ Kd · |B_N| / N`.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace SharpLSI.FL

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ} {J : ℕ}

theorem kappa0_bounds (N b : ℕ) (hb : b < N) :
    0 ≤ 1 - (Real.sqrt N)⁻¹ * Real.sqrt ((N - b : ℕ) : ℝ) ∧
      1 - (Real.sqrt N)⁻¹ * Real.sqrt ((N - b : ℕ) : ℝ) ≤ (b : ℝ) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hb)
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hn : ((N - b : ℕ) : ℝ) = (N : ℝ) - b := by
    rw [Nat.cast_sub hb.le]
  set x : ℝ := (Real.sqrt N)⁻¹ * Real.sqrt ((N - b : ℕ) : ℝ) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ^ 2 = ((N : ℝ) - b) / N := by
    rw [hx, mul_pow, inv_pow, Real.sq_sqrt hNpos.le, Real.sq_sqrt (Nat.cast_nonneg _), hn]
    field_simp
  have hx1 : x ≤ 1 := by
    have : x ^ 2 ≤ 1 := by
      rw [hx2, div_le_one hNpos]
      have : (0 : ℝ) ≤ b := Nat.cast_nonneg b
      linarith
    nlinarith [sq_nonneg (x - 1)]
  refine ⟨by linarith, ?_⟩
  have h1 : x ^ 2 ≤ x := by nlinarith
  have : (b : ℝ) / N = 1 - x ^ 2 := by rw [hx2]; field_simp; ring
  rw [this]; linarith

theorem measurable_pP (hG : GoodBasis μ e) {N : ℕ} (B : Finset (Fin N))
    (c : (Fin N → Fin (J + 1)) → ℝ) :
    Measurable fun w : Fin N → Torus d × (Fin J → ℝ) => pP e c B w :=
  measurable_polyF_lf hG B c

theorem pair_moments (hG : GoodBasis μ e) (hmom : HybridPolyMoment μ e lam J)
    (hlam0 : lam 0 = 0) (L B : ℝ) :
    ∃ M8 M4 Kd : ℝ, 0 ≤ M8 ∧ 0 ≤ M4 ∧ 0 ≤ Kd ∧
      ∀ (N : ℕ) (c : (Fin N → Fin (J + 1)) → ℝ), SpectralCoeff lam L c → ∑ j, c j ^ 2 ≤ B ^ 2 →
        ∀ δ : ℝ, 0 < lowCount c δ →
          (Integrable (fun w => |pP e c Finset.univ w| ^ 8) (pairMeasure μ N J) ∧
            ∫ w, |pP e c Finset.univ w| ^ 8 ∂pairMeasure μ N J ≤ M8) ∧
          ∀ i : Fin J,
            (Integrable (fun w => |Zfp e N i w + zP e c δ Finset.univ w i| ^ 4) (pairMeasure μ N J) ∧
              ∫ w, |Zfp e N i w + zP e c δ Finset.univ w i| ^ 4 ∂pairMeasure μ N J ≤ M4) ∧
            (Integrable (fun w => |Zfp e N i w - zP e c δ Finset.univ w i| ^ 2) (pairMeasure μ N J) ∧
              ∫ w, |Zfp e N i w - zP e c δ Finset.univ w i| ^ 2 ∂pairMeasure μ N J ≤
                Kd * ((retained c δ).card / N)) := by
  set L0 : ℝ := ∑ m : Fin J, |lam ((m : ℕ) + 1)| with hL0
  obtain ⟨K8, hK80, hK8⟩ := hmom L 8
  obtain ⟨K4, hK40, hK4⟩ := hmom L0 4
  obtain ⟨K2, hK20, hK2⟩ := hmom L0 2
  refine ⟨K8 * |B| ^ 8, 16 * K4, 4 * K2, by positivity, by positivity, by positivity, ?_⟩
  intro N c hc hB δ hn
  have hcard : (retained c δ).card ≤ N := by
    simpa using Finset.card_le_univ (retained c δ)
  have hbN : (retained c δ).card < N := by
    unfold lowCount at hn; omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hbN)
  have he0 := hG.zero
  refine ⟨?_, fun i => ?_⟩
  · obtain ⟨hi, hI⟩ := poly_moment hG hK80 hK8 hc Finset.univ
    refine ⟨hi, hI.trans ?_⟩
    have hsq : Real.sqrt (∑ j, c j ^ 2) ≤ |B| := by
      calc Real.sqrt (∑ j, c j ^ 2) ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hB
        _ = |B| := Real.sqrt_sq_eq_abs B
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 8) hK80
  · set a : ℝ := (N : ℝ) ^ (-(1 / 2 : ℝ)) with ha
    have hL0le : lam ((i : ℕ) + 1) ≤ L0 :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun m : Fin J => |lam ((m : ℕ) + 1)|)
        (fun m _ => abs_nonneg _) (Finset.mem_univ i))
    have hcz : ∀ T : Finset (Fin N), SpectralCoeff lam L0 (cZ T a i) := fun T =>
      spectralCoeff_mono hL0le (spectralCoeff_cZ hlam0 T a i)
    have ha2 : a ^ 2 = (N : ℝ)⁻¹ := rpow_neg_half_sq_alt N
    -- Zfp
    have hZf := poly_moment hG hK40 hK4 (hcz Finset.univ) Finset.univ
    have hsumUniv : ∑ j : Fin N → Fin (J + 1), (cZ (Finset.univ : Finset (Fin N)) a i j) ^ 2 = 1 := by
      rw [sum_sq_cZ, ha2]; simp; field_simp
    rw [hsumUniv] at hZf
    simp only [Real.sqrt_one, one_pow, mul_one] at hZf
    have hZfeq : ∀ w, pP e (cZ Finset.univ a i) Finset.univ w = Zfp e N i w := fun w =>
      (Zfp_eq_pP he0 i w).symm
    simp only [hZfeq] at hZf
    -- Zl
    have hZl4 := zP_moment hG hlam0 hK40 hK4 c δ hn Finset.univ i
    have hZl2 := zP_moment hG hlam0 hK20 hK2 c δ hn Finset.univ i
    -- measurability
    have mZf : Measurable fun w : Fin N → Torus d × (Fin J → ℝ) => Zfp e N i w := by
      have := measurable_pP hG (Finset.univ : Finset (Fin N)) (cZ Finset.univ a i)
      simpa only [← hZfeq] using this
    have mZl : Measurable fun w : Fin N → Torus d × (Fin J → ℝ) =>
        zP e c δ Finset.univ w i := measurable_zP hG c δ Finset.univ i
    refine ⟨?_, ?_⟩
    · -- fourth moment of the sum
      have hpt : ∀ w, |Zfp e N i w + zP e c δ Finset.univ w i| ^ 4 ≤
          8 * (|Zfp e N i w| ^ 4 + |zP e c δ Finset.univ w i| ^ 4) := by
        intro w
        set x := |Zfp e N i w|
        set y := |zP e c δ Finset.univ w i|
        have hx : 0 ≤ x := abs_nonneg _
        have hy : 0 ≤ y := abs_nonneg _
        have h1 : |Zfp e N i w + zP e c δ Finset.univ w i| ≤ x + y := abs_add_le _ _
        calc |Zfp e N i w + zP e c δ Finset.univ w i| ^ 4 ≤ (x + y) ^ 4 :=
              pow_le_pow_left₀ (abs_nonneg _) h1 4
          _ ≤ 8 * (x ^ 4 + y ^ 4) := by
              nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), mul_nonneg hx hy,
                sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 + y ^ 2 - 2 * x * y)]
      have hbi : Integrable (fun w => 8 * (|Zfp e N i w| ^ 4 + |zP e c δ Finset.univ w i| ^ 4))
          (pairMeasure μ N J) := (hZf.1.add hZl4.1).const_mul 8
      have hint : Integrable (fun w => |Zfp e N i w + zP e c δ Finset.univ w i| ^ 4)
          (pairMeasure μ N J) := by
        refine hbi.mono' ((mZf.add mZl).abs.pow_const 4).aestronglyMeasurable
          (Filter.Eventually.of_forall fun w => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hpt w
      refine ⟨hint, ?_⟩
      calc ∫ w, |Zfp e N i w + zP e c δ Finset.univ w i| ^ 4 ∂pairMeasure μ N J
          ≤ ∫ w, 8 * (|Zfp e N i w| ^ 4 + |zP e c δ Finset.univ w i| ^ 4) ∂pairMeasure μ N J :=
            integral_mono hint hbi hpt
        _ = 8 * (∫ w, |Zfp e N i w| ^ 4 ∂pairMeasure μ N J +
              ∫ w, |zP e c δ Finset.univ w i| ^ 4 ∂pairMeasure μ N J) := by
            rw [integral_const_mul, integral_add hZf.1 hZl4.1]
        _ ≤ 16 * K4 := by linarith [hZf.2, hZl4.2]
    · -- second moment of the difference
      set P1 : (Fin N → Torus d × (Fin J → ℝ)) → ℝ := fun w =>
        pP e (cZ (retained c δ) a i) Finset.univ w with hP1
      have hP1m : Measurable P1 := by
        exact measurable_pP hG (Finset.univ : Finset (Fin N)) (cZ (retained c δ) a i)
      have hbq := poly_moment hG hK20 hK2 (hcz (retained c δ)) Finset.univ
      have hsumB : ∑ j : Fin N → Fin (J + 1), (cZ (retained c δ) a i j) ^ 2 = (retained c δ).card / N := by
        rw [sum_sq_cZ, ha2]; field_simp
      have hP1I : ∫ w, |P1 w| ^ 2 ∂pairMeasure μ N J ≤ K2 * ((retained c δ).card / N) := by
        refine hbq.2.trans ?_
        rw [hsumB, Real.sq_sqrt (by positivity)]
      set κ0 : ℝ := 1 - a * Real.sqrt (lowCount c δ) with hκ0
      have hlow : (lowCount c δ : ℝ) = ((N - (retained c δ).card : ℕ) : ℝ) := rfl
      have hκb := kappa0_bounds N (retained c δ).card hbN
      have hκ0' : κ0 = 1 - (Real.sqrt N)⁻¹ * Real.sqrt ((N - (retained c δ).card : ℕ) : ℝ) := by
        rw [hκ0, ha, rpow_neg_half_eq, hlow]
      have hκlo : 0 ≤ κ0 := by rw [hκ0']; exact hκb.1
      have hκhi : κ0 ≤ (retained c δ).card / N := by rw [hκ0']; exact hκb.2
      have hbN1 : ((retained c δ).card : ℝ) / N ≤ 1 := by
        rw [div_le_one hNpos]; exact_mod_cast hcard
      have hnpos : (0 : ℝ) < Real.sqrt (lowCount c δ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
      have hid : ∀ w, Zfp e N i w - zP e c δ Finset.univ w i = P1 w - κ0 * zP e c δ Finset.univ w i := by
        intro w
        have hs := Finset.sum_add_sum_compl (retained c δ) (fun l => e ((i : ℕ) + 1) (w l).1)
        simp only [hP1, Zfp, zP_univ_eq he0, pP_cZ_sub he0, hκ0, ← ha]
        rw [← hs]
        field_simp
        ring
      have hpt : ∀ w, |Zfp e N i w - zP e c δ Finset.univ w i| ^ 2 ≤
          2 * |P1 w| ^ 2 + 2 * (((retained c δ).card : ℝ) / N) *
            |zP e c δ Finset.univ w i| ^ 2 := by
        intro w
        rw [hid w, sq_abs, sq_abs, sq_abs]
        have h1 : (P1 w - κ0 * zP e c δ Finset.univ w i) ^ 2 ≤
            2 * P1 w ^ 2 + 2 * (κ0 * zP e c δ Finset.univ w i) ^ 2 := by
          nlinarith [sq_nonneg (P1 w + κ0 * zP e c δ Finset.univ w i)]
        have h2 : (κ0 * zP e c δ Finset.univ w i) ^ 2 ≤
            (((retained c δ).card : ℝ) / N) * zP e c δ Finset.univ w i ^ 2 := by
          rw [mul_pow]
          have : κ0 ^ 2 ≤ ((retained c δ).card : ℝ) / N := by nlinarith
          exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
        nlinarith
      have hbi : Integrable (fun w => 2 * |P1 w| ^ 2 + 2 * (((retained c δ).card : ℝ) / N) *
          |zP e c δ Finset.univ w i| ^ 2) (pairMeasure μ N J) :=
        (hbq.1.const_mul 2).add (hZl2.1.const_mul _)
      have mD : Measurable fun w : Fin N → Torus d × (Fin J → ℝ) =>
          |Zfp e N i w - zP e c δ Finset.univ w i| ^ 2 := ((mZf.sub mZl).abs).pow_const 2
      have hint : Integrable (fun w => |Zfp e N i w - zP e c δ Finset.univ w i| ^ 2)
          (pairMeasure μ N J) := by
        refine hbi.mono' mD.aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hpt w
      refine ⟨hint, ?_⟩
      calc ∫ w, |Zfp e N i w - zP e c δ Finset.univ w i| ^ 2 ∂pairMeasure μ N J
          ≤ ∫ w, (2 * |P1 w| ^ 2 + 2 * (((retained c δ).card : ℝ) / N) *
              |zP e c δ Finset.univ w i| ^ 2) ∂pairMeasure μ N J := integral_mono hint hbi hpt
        _ = 2 * ∫ w, |P1 w| ^ 2 ∂pairMeasure μ N J + 2 * (((retained c δ).card : ℝ) / N) *
              ∫ w, |zP e c δ Finset.univ w i| ^ 2 ∂pairMeasure μ N J := by
            rw [integral_add (hbq.1.const_mul 2) (hZl2.1.const_mul _), integral_const_mul,
              integral_const_mul]
        _ ≤ 2 * (K2 * ((retained c δ).card / N)) + 2 * (((retained c δ).card : ℝ) / N) * K2 := by
            have hbn : (0 : ℝ) ≤ 2 * (((retained c δ).card : ℝ) / N) :=
              mul_nonneg (by norm_num) (div_nonneg (Nat.cast_nonneg _) hNpos.le)
            have h1 : 2 * ∫ w, |P1 w| ^ 2 ∂pairMeasure μ N J ≤ 2 * (K2 * ((retained c δ).card / N)) :=
              by linarith
            have h2 : 2 * (((retained c δ).card : ℝ) / N) *
                ∫ w, |zP e c δ Finset.univ w i| ^ 2 ∂pairMeasure μ N J ≤
                2 * (((retained c δ).card : ℝ) / N) * K2 := mul_le_mul_of_nonneg_left hZl2.2 hbn
            linarith
        _ = 4 * K2 * ((retained c δ).card / N) := by ring

end SharpLSI.FL

end
