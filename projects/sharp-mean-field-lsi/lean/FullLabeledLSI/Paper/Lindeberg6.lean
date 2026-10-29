import FullLabeledLSI.Paper.Lindeberg5

/-!
# Lemma 7.1, part 7: uniform moments of the joint vector `(P, Z^low)` (Piece H1)

For every intermediate label set `B'`, every `s`, and coefficient arrays of spectral level `L` with
`∑ c_j² ≤ B²`, the joint vector `Vec = (pP, zP ∘ castLE)` has `E ‖Vec‖^s` bounded by a constant
independent of `N, c, δ, B'`. Inputs: `HybridPolyMoment` for the array `c` and for the arrays
`cZ` representing the normalized sums `zP`.
-/

open MeasureTheory ProbabilityTheory
open scoped ContDiff

namespace SharpLSI.FL

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ} {J JR : ℕ}

/-! ### Elementary norm inequalities -/

theorem pi_norm_pow_le {n : ℕ} (z : Fin n → ℝ) (s : ℕ) : ‖z‖ ^ s ≤ 1 + ∑ m, |z m| ^ s := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · have : z = 0 := Subsingleton.elim _ _
    subst this
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp
    · simp [zero_pow hs.ne']
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun b => ‖z b‖₊)
    have hnorm : ‖z‖ = |z i| := by
      rw [← Real.norm_eq_abs, ← coe_nnnorm, Pi.nnnorm_def, hi]
      simp
    rw [hnorm]
    have := Finset.single_le_sum (f := fun m => |z m| ^ s) (fun m _ => by positivity)
      (Finset.mem_univ i)
    linarith

theorem prod_norm_pow_le {n : ℕ} (a : ℝ) (z : Fin n → ℝ) (s : ℕ) :
    ‖(a, z)‖ ^ s ≤ 1 + |a| ^ s + ∑ m, |z m| ^ s := by
  have hs : 0 ≤ ∑ m, |z m| ^ s := Finset.sum_nonneg fun _ _ => by positivity
  have ha : 0 ≤ |a| ^ s := by positivity
  rw [Prod.norm_def]
  rcases max_choice ‖a‖ ‖z‖ with h | h
  · rw [h, Real.norm_eq_abs]; linarith
  · rw [h]; have := pi_norm_pow_le z s; linarith

theorem one_add_pow_le (x : ℝ) (hx : 0 ≤ x) (m : ℕ) : (1 + x) ^ m ≤ 2 ^ m * (1 + x ^ m) := by
  by_cases h : x ≤ 1
  · calc (1 + x) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ ≤ 2 ^ m * (1 + x ^ m) := by
          have : 0 ≤ x ^ m := by positivity
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) m]
  · push Not at h
    calc (1 + x) ^ m ≤ (2 * x) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * x ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (1 + x ^ m) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-! ### The joint vector -/

/-- The joint vector `(pP, zP ∘ castLE)` on the label-wise space. -/
noncomputable def Vec (e : ℕ → Torus d → ℝ) {N J JR : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (hJ : JR ≤ J) (B : Finset (Fin N)) (w : Fin N → Torus d × (Fin J → ℝ)) :
    ℝ × (Fin JR → ℝ) :=
  (pP e c B w, fun m => zP e c δ B w (Fin.castLE hJ m))

theorem Fint_eq_Phi_Vec (e : ℕ → Torus d → ℝ) {N J JR : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ)
    (δ : ℝ) (hJ : JR ≤ J) (Φ : ℝ × (Fin JR → ℝ) → ℝ) (B : Finset (Fin N))
    (w : Fin N → Torus d × (Fin J → ℝ)) : Fint e c δ hJ Φ B w = Φ (Vec e c δ hJ B w) := rfl

theorem measurable_Vec (hG : GoodBasis μ e) {N J JR : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (hJ : JR ≤ J) (B : Finset (Fin N)) :
    Measurable (Vec e c δ hJ B : (Fin N → Torus d × (Fin J → ℝ)) → ℝ × (Fin JR → ℝ)) :=
  Measurable.prodMk (measurable_polyF_lf hG B c)
    (measurable_pi_iff.2 fun m => measurable_zP hG c δ B _)

/-! ### Moments of label polynomials from the interface -/

theorem poly_moment (hG : GoodBasis μ e) {K : ℝ} (hK0 : 0 ≤ K) {L : ℝ} {q : ℕ}
    (hK : ∀ (N : ℕ) (B : Finset (Fin N)) (c : (Fin N → Fin (J + 1)) → ℝ),
      SpectralCoeff lam L c → ∫⁻ w, ENNReal.ofReal (|polyB e c B w| ^ q) ∂hybMeasure μ N J ≤
        ENNReal.ofReal (K * Real.sqrt (∑ j, c j ^ 2) ^ q))
    {N : ℕ} {c : (Fin N → Fin (J + 1)) → ℝ} (hc : SpectralCoeff lam L c) (B : Finset (Fin N)) :
    Integrable (fun w => |pP e c B w| ^ q) (pairMeasure μ N J) ∧
      ∫ w, |pP e c B w| ^ q ∂pairMeasure μ N J ≤ K * Real.sqrt (∑ j, c j ^ 2) ^ q := by
  have h := hK N B c hc
  rw [lintegral_hyb_eq] at h
  have hmeas : Measurable fun w : Fin N → Torus d × (Fin J → ℝ) => |pP e c B w| ^ q :=
    ((measurable_polyF_lf hG B c).abs).pow_const q
  exact integrable_integral_le_of_lintegral_le hmeas.aestronglyMeasurable
    (fun w => by positivity) (by positivity) h

theorem spectralCoeff_mono {L L' : ℝ} (hL : L ≤ L') {N : ℕ} {c : (Fin N → Fin (J + 1)) → ℝ}
    (hc : SpectralCoeff lam L c) : SpectralCoeff lam L' c :=
  fun j hj => (hc j hj).trans hL

theorem zP_eq_polyF (he0 : e 0 = fun _ => 1) {N : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (B : Finset (Fin N)) (r : Fin J) (w : Fin N → Torus d × (Fin J → ℝ)) :
    zP e c δ B w r = pP e (cZ (retained c δ)ᶜ (Real.sqrt (lowCount c δ))⁻¹ r) B w := by
  have := polyF_cZ (lf e B) (fun l s => lf_zero e he0 B l s) (retained c δ)ᶜ
    (Real.sqrt (lowCount c δ))⁻¹ r w
  exact this.symm

theorem sum_sq_cZ_eq_one {N : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) (r : Fin J)
    (hn : 0 < lowCount c δ) :
    ∑ j, (cZ (retained c δ)ᶜ (Real.sqrt (lowCount c δ))⁻¹ r j) ^ 2 = 1 := by
  rw [sum_sq_cZ, ← lowCount_eq_card]
  have hn' : (0 : ℝ) < lowCount c δ := by exact_mod_cast hn
  rw [inv_pow, Real.sq_sqrt hn'.le]
  field_simp

/-- Moments of the fluctuation `zP`: independent of `N, c, δ, B'`. -/
theorem zP_moment (hG : GoodBasis μ e) (hlam0 : lam 0 = 0) {s : ℕ} {KZ : ℝ} (hKZ0 : 0 ≤ KZ)
    (hKZ : ∀ (N : ℕ) (B : Finset (Fin N)) (c : (Fin N → Fin (J + 1)) → ℝ),
      SpectralCoeff lam (∑ m : Fin J, |lam ((m : ℕ) + 1)|) c →
        ∫⁻ w, ENNReal.ofReal (|polyB e c B w| ^ s) ∂hybMeasure μ N J ≤
          ENNReal.ofReal (KZ * Real.sqrt (∑ j, c j ^ 2) ^ s))
    {N : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) (hn : 0 < lowCount c δ)
    (B : Finset (Fin N)) (r : Fin J) :
    Integrable (fun w => |zP e c δ B w r| ^ s) (pairMeasure μ N J) ∧
      ∫ w, |zP e c δ B w r| ^ s ∂pairMeasure μ N J ≤ KZ := by
  have hcZ : SpectralCoeff lam (∑ m : Fin J, |lam ((m : ℕ) + 1)|)
      (cZ (retained c δ)ᶜ (Real.sqrt (lowCount c δ))⁻¹ r) := by
    refine spectralCoeff_mono ?_ (spectralCoeff_cZ hlam0 (retained c δ)ᶜ
      (Real.sqrt (lowCount c δ))⁻¹ r)
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun m : Fin J => |lam ((m : ℕ) + 1)|)
      (fun m _ => abs_nonneg _) (Finset.mem_univ r))
  obtain ⟨hi, hI⟩ := poly_moment hG hKZ0 hKZ hcZ B
  simp only [sum_sq_cZ_eq_one c δ r hn, Real.sqrt_one, one_pow, mul_one] at hI
  simp only [zP_eq_polyF hG.zero c δ B r]
  exact ⟨hi, hI⟩

/-- **Piece H1.** Uniform moments of the joint vector. -/
theorem Vec_moment (hG : GoodBasis μ e) (hmom : HybridPolyMoment μ e lam J) (hlam0 : lam 0 = 0)
    (hJ : JR ≤ J) (L B : ℝ) (s : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (N : ℕ) (c : (Fin N → Fin (J + 1)) → ℝ), SpectralCoeff lam L c →
      ∑ j, c j ^ 2 ≤ B ^ 2 → ∀ δ : ℝ, 0 < lowCount c δ → ∀ B' : Finset (Fin N),
        Integrable (fun w => ‖Vec e c δ hJ B' w‖ ^ s) (pairMeasure μ N J) ∧
          ∫ w, ‖Vec e c δ hJ B' w‖ ^ s ∂pairMeasure μ N J ≤ M := by
  obtain ⟨Kh, hKh0, hKh⟩ := hmom L s
  obtain ⟨KZ, hKZ0, hKZ⟩ := hmom (∑ m : Fin J, |lam ((m : ℕ) + 1)|) s
  refine ⟨1 + Kh * |B| ^ s + (JR : ℝ) * KZ, by positivity, ?_⟩
  intro N c hc hB δ hn B'
  obtain ⟨hpi, hpI⟩ := poly_moment hG hKh0 hKh hc B'
  have hz := fun m : Fin JR => zP_moment hG hlam0 hKZ0 hKZ c δ hn B' (Fin.castLE hJ m)
  have hsq : Real.sqrt (∑ j, c j ^ 2) ≤ |B| := by
    calc Real.sqrt (∑ j, c j ^ 2) ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hB
      _ = |B| := Real.sqrt_sq_eq_abs B
  set bound : (Fin N → Torus d × (Fin J → ℝ)) → ℝ := fun w =>
    1 + |pP e c B' w| ^ s + ∑ m : Fin JR, |zP e c δ B' w (Fin.castLE hJ m)| ^ s with hbound
  have hbi : Integrable bound (pairMeasure μ N J) :=
    ((integrable_const (1 : ℝ)).add hpi).add (integrable_finsetSum _ fun m _ => (hz m).1)
  have hpt : ∀ w, ‖Vec e c δ hJ B' w‖ ^ s ≤ bound w := fun w =>
    prod_norm_pow_le _ _ s
  have hmeas : Measurable fun w : Fin N → Torus d × (Fin J → ℝ) => ‖Vec e c δ hJ B' w‖ ^ s :=
    ((measurable_Vec hG c δ hJ B').norm).pow_const s
  refine ⟨hbi.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun w => ?_), ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt w
  · have hI : ∫ w, ‖Vec e c δ hJ B' w‖ ^ s ∂pairMeasure μ N J ≤
        ∫ w, bound w ∂pairMeasure μ N J :=
      integral_mono_of_nonneg (ae_of_all _ fun w => by positivity) hbi (ae_of_all _ hpt)
    refine hI.trans ?_
    have hv : ∫ w, bound w ∂pairMeasure μ N J = 1 + ∫ w, |pP e c B' w| ^ s ∂pairMeasure μ N J +
        ∑ m : Fin JR, ∫ w, |zP e c δ B' w (Fin.castLE hJ m)| ^ s ∂pairMeasure μ N J := by
      simp only [hbound]
      have hint1 : Integrable (fun w => 1 + |pP e c B' w| ^ s) (pairMeasure μ N J) :=
        (integrable_const (1 : ℝ)).add hpi
      have hint2 : Integrable
          (fun w => ∑ m : Fin JR, |zP e c δ B' w (Fin.castLE hJ m)| ^ s) (pairMeasure μ N J) :=
        integrable_finsetSum _ fun m _ => (hz m).1
      rw [integral_add hint1 hint2, integral_add (integrable_const (1 : ℝ)) hpi,
        integral_finsetSum _ fun m _ => (hz m).1]
      simp
    rw [hv]
    have h1 : ∫ w, |pP e c B' w| ^ s ∂pairMeasure μ N J ≤ Kh * |B| ^ s :=
      hpI.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq s) hKh0)
    have h2 : ∑ m : Fin JR, ∫ w, |zP e c δ B' w (Fin.castLE hJ m)| ^ s ∂pairMeasure μ N J ≤
        (JR : ℝ) * KZ := by
      calc _ ≤ ∑ _m : Fin JR, KZ := Finset.sum_le_sum fun m _ => (hz m).2
        _ = (JR : ℝ) * KZ := by simp
    linarith

end SharpLSI.FL
