import FullLabeledLSI.Paper.Lindeberg4

/-!
# Lemma 7.1, part 6: telescoping (Piece E) and the rate (7.12) (Piece G)

* `telescope`: replacing a set `T` of low-influence labels one at a time.
* `joint_rate_good`: `|IP univ − IP (retained)| ≤ C (√δ + n^{-1/2})` for a `GoodBasis`.
* `joint_rate_of_moment`: the statement of S26 `joint_rate`, for a reference eigenbasis, with the
  interface `HybridPolyMoment` as an explicit hypothesis (the frozen S26 stays `sorry` until lane 3
  delivers the interface).
-/

open MeasureTheory ProbabilityTheory
open scoped ContDiff

namespace SharpLSI.FL

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ} {J JR : ℕ}

/-- **Piece E.** Telescoping over a set `T` of low-influence labels. -/
theorem telescope (hG : GoodBasis μ e) (hmom : HybridPolyMoment μ e lam J) (hlam0 : lam 0 = 0)
    (hnn : ∀ k, 0 ≤ lam k) (hJ : JR ≤ J) {Φ : ℝ × (Fin JR → ℝ) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hΦc : HasCompactSupport Φ) (L : ℝ) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (N : ℕ) (c : (Fin N → Fin (J + 1)) → ℝ), SpectralCoeff lam L c →
      ∀ (δ : ℝ) (T : Finset (Fin N)), T ⊆ (retained c δ)ᶜ →
        |IP μ e c δ hJ Φ Finset.univ - IP μ e c δ hJ Φ (Finset.univ \ T)| ≤
          ∑ i ∈ T, C₁ * (Real.sqrt (infl c i) ^ 3 + ((Real.sqrt (lowCount c δ))⁻¹) ^ 3) := by
  obtain ⟨C₁, h0, hC⟩ := step_bound hG hmom hlam0 hnn hJ hΦ hΦc L
  refine ⟨C₁, h0, fun N c hc δ T => ?_⟩
  induction T using Finset.induction_on with
  | empty => intro _; simp
  | insert i T' hiT ih =>
    intro hsub
    have hsub' : T' ⊆ (retained c δ)ᶜ := fun x hx => hsub (Finset.mem_insert_of_mem hx)
    have hi_low : i ∈ (retained c δ)ᶜ := hsub (Finset.mem_insert_self i T')
    have hiB : i ∈ Finset.univ \ T' := by simp [hiT]
    have hstep := hC N c hc δ (Finset.univ \ T') i hiB hi_low
    rw [← Finset.sdiff_insert] at hstep
    rw [Finset.sum_insert hiT]
    have hih := ih hsub'
    calc |IP μ e c δ hJ Φ Finset.univ - IP μ e c δ hJ Φ (Finset.univ \ insert i T')|
        = |(IP μ e c δ hJ Φ Finset.univ - IP μ e c δ hJ Φ (Finset.univ \ T')) +
            (IP μ e c δ hJ Φ (Finset.univ \ T') - IP μ e c δ hJ Φ (Finset.univ \ insert i T'))| := by
          congr 1; ring
      _ ≤ |IP μ e c δ hJ Φ Finset.univ - IP μ e c δ hJ Φ (Finset.univ \ T')| +
          |IP μ e c δ hJ Φ (Finset.univ \ T') - IP μ e c δ hJ Φ (Finset.univ \ insert i T')| :=
          abs_add_le _ _
      _ ≤ _ := by linarith

/-- **Piece G (good basis).** The rate (7.12). -/
theorem joint_rate_good (hG : GoodBasis μ e) (hmom : HybridPolyMoment μ e lam J)
    (hlam0 : lam 0 = 0) (hnn : ∀ k, 0 ≤ lam k) (hmono : Monotone lam) (hpos : 0 < lam 1)
    (hJ : JR ≤ J) {Φ : ℝ × (Fin JR → ℝ) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ)
    (L B : ℝ) :
    ∃ C : ℝ, ∀ (N : ℕ) (c : (Fin N → Fin (J + 1)) → ℝ), SpectralCoeff lam L c →
      ∑ j, c j ^ 2 ≤ B ^ 2 → ∀ δ : ℝ, 0 < δ → 0 < lowCount c δ →
        |IP μ e c δ hJ Φ Finset.univ - IP μ e c δ hJ Φ (retained c δ)| ≤
          C * (Real.sqrt δ + (Real.sqrt (lowCount c δ))⁻¹) := by
  obtain ⟨C₁, h0, hC⟩ := telescope hG hmom hlam0 hnn hJ hΦ hΦc L
  set D : ℝ := max (L / lam 1) 0 * B ^ 2 with hD
  refine ⟨C₁ * max D 1, fun N c hc hB δ hδ hn => ?_⟩
  have hT := hC N c hc δ (retained c δ)ᶜ subset_rfl
  have hcompl : (Finset.univ \ (retained c δ)ᶜ) = retained c δ := by
    ext x; simp
  rw [hcompl] at hT
  set a : ℝ := (Real.sqrt (lowCount c δ))⁻¹ with ha
  have ha0 : 0 ≤ a := by positivity
  have hcard : (((retained c δ)ᶜ).card : ℝ) = (lowCount c δ : ℝ) := by
    rw [lowCount_eq_card]
  have hsum1 : ∑ i ∈ (retained c δ)ᶜ, C₁ * (Real.sqrt (infl c i) ^ 3 + a ^ 3) =
      C₁ * (∑ i ∈ (retained c δ)ᶜ, Real.sqrt (infl c i) ^ 3 +
        (((retained c δ)ᶜ).card : ℝ) * a ^ 3) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    simp
  have hnat : (((retained c δ)ᶜ).card : ℝ) * a ^ 3 = a := by
    rw [hcard, ha]; exact nat_mul_inv_sqrt_cube hn
  have hS : 0 ≤ ∑ j, c j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hinfl : ∑ i, infl c i ≤ D := by
    refine (sum_infl_le hlam0 hnn hmono hpos hc).trans ?_
    calc L / lam 1 * ∑ j, c j ^ 2 ≤ max (L / lam 1) 0 * ∑ j, c j ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hS
      _ ≤ max (L / lam 1) 0 * B ^ 2 := mul_le_mul_of_nonneg_left hB (le_max_right _ _)
  have hlow : ∑ i ∈ (retained c δ)ᶜ, Real.sqrt (infl c i) ^ 3 ≤ Real.sqrt δ * D :=
    (sum_low_sqrt_cube_le c hδ.le).trans (mul_le_mul_of_nonneg_left hinfl (Real.sqrt_nonneg _))
  have hsd : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  refine hT.trans ?_
  rw [hsum1, hnat]
  have hDm : D ≤ max D 1 := le_max_left _ _
  have h1m : (1 : ℝ) ≤ max D 1 := le_max_right _ _
  calc C₁ * (∑ i ∈ (retained c δ)ᶜ, Real.sqrt (infl c i) ^ 3 + a)
      ≤ C₁ * (Real.sqrt δ * D + a) := mul_le_mul_of_nonneg_left (by linarith) h0
    _ ≤ C₁ * (max D 1 * (Real.sqrt δ + a)) := by
        apply mul_le_mul_of_nonneg_left _ h0
        nlinarith [mul_le_mul_of_nonneg_left hDm hsd, mul_le_mul_of_nonneg_right h1m ha0]
    _ = C₁ * max D 1 * (Real.sqrt δ + a) := by ring


/-- **S26 `joint_rate`, with the interface `HybridPolyMoment` as an explicit hypothesis.** -/
theorem joint_rate_of_moment {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (J JR : ℕ) (hJ : JR ≤ J) (hmom : HybridPolyMoment (μ : Measure (Torus d)) e lam J)
    (Φ : ℝ × (Fin JR → ℝ) → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ)
    (L B : ℝ) :
    ∃ C : ℝ, ∀ (N : ℕ) (c : (Fin N → Fin (J + 1)) → ℝ), SpectralCoeff lam L c →
      ∑ j, c j ^ 2 ≤ B ^ 2 → ∀ δ : ℝ, 0 < δ → 0 < lowCount c δ →
        |∫ X, Φ (polyEval e c X, fun m => Zlow e c δ X (Fin.castLE hJ m))
            ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) -
          ∫ w, Φ (hybEval e c δ w, fun m => Glow c δ w (Fin.castLE hJ m))
            ∂hybMeasure (μ : Measure (Torus d)) N J| ≤
        C * (Real.sqrt δ + (Real.sqrt (lowCount c δ))⁻¹) := by
  obtain ⟨e', hG, hae⟩ := exists_goodBasis hd hyp hr hμ he
  obtain ⟨hl0, hnn, hmono, hpos⟩ := lam_facts hd hyp hr hμ he
  have hae' : ∀ j, e j =ᵐ[(μ : Measure (Torus d))] e' j := fun j => (hae j).symm
  have hmom' := hmom.of_ae_eq hae'
  obtain ⟨C, hC⟩ := joint_rate_good hG hmom' hl0 hnn hmono hpos hJ hΦ hΦc L B
  refine ⟨C, fun N c hc hB δ hδ hn => ?_⟩
  rw [integral_orig_congr hae' c δ hJ Φ, integral_hyb_congr hae' c δ hJ Φ,
    integral_orig_eq_IP, integral_hyb_eq_IP]
  exact hC N c hc hB δ hδ hn

end SharpLSI.FL
