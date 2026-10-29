import FullLabeledLSI.Paper.Lindeberg6
import FullLabeledLSI.Paper.LindebergApprox

/-!
# Lemma 7.1, part 8: continuous tests of polynomial growth (7.11) (Piece H)

* `IP_close`: replacing a continuous `Φ` of polynomial growth by an approximant `Ψ` which is
  `ε'`-close up to the tail `{‖p‖ > ρ}` changes `IP` by at most `ε' + C (1+M)/(1+ρ)`, with `M` a
  bound for the moment `E ‖Vec‖^{k+1}`.
* `lowCount_lower`: the number of low-influence labels is at least `N − D/δ`.
* `joint_replace_good`, `joint_replace_of_moment`: (7.11), with the interface as a hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ContDiff

namespace SharpLSI.FL

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ} {J JR : ℕ}

theorem abs_le_growth {Φ : ℝ × (Fin JR → ℝ) → ℝ} {K : ℝ} {k : ℕ} (hK0 : 0 ≤ K)
    (hK : ∀ p, |Φ p| ≤ K * (1 + ‖p‖) ^ k) (p : ℝ × (Fin JR → ℝ)) :
    |Φ p| ≤ K * 2 ^ (k + 1) * (1 + ‖p‖ ^ (k + 1)) := by
  have h1 : (1 + ‖p‖) ^ k ≤ (1 + ‖p‖) ^ (k + 1) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg p]) (Nat.le_succ k)
  have h2 := one_add_pow_le ‖p‖ (norm_nonneg p) (k + 1)
  calc |Φ p| ≤ K * (1 + ‖p‖) ^ k := hK p
    _ ≤ K * (1 + ‖p‖) ^ (k + 1) := mul_le_mul_of_nonneg_left h1 hK0
    _ ≤ K * (2 ^ (k + 1) * (1 + ‖p‖ ^ (k + 1))) := mul_le_mul_of_nonneg_left h2 hK0
    _ = K * 2 ^ (k + 1) * (1 + ‖p‖ ^ (k + 1)) := by ring

theorem tail_le {Φ : ℝ × (Fin JR → ℝ) → ℝ} {K : ℝ} {k : ℕ} (hK0 : 0 ≤ K)
    (hK : ∀ p, |Φ p| ≤ K * (1 + ‖p‖) ^ k) {ρ : ℝ} (hρ : 0 < ρ) (p : ℝ × (Fin JR → ℝ)) :
    (if ρ < ‖p‖ then |Φ p| else 0) ≤ K * 2 ^ (k + 1) / (1 + ρ) * (1 + ‖p‖ ^ (k + 1)) := by
  have hc : 0 ≤ K * 2 ^ (k + 1) / (1 + ρ) :=
    div_nonneg (mul_nonneg hK0 (by positivity)) (by linarith)
  split_ifs with h
  · rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    have hp : 0 ≤ ‖p‖ := norm_nonneg p
    have h2 := one_add_pow_le ‖p‖ hp (k + 1)
    calc |Φ p| * (1 + ρ) ≤ |Φ p| * (1 + ‖p‖) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ ≤ K * (1 + ‖p‖) ^ k * (1 + ‖p‖) :=
          mul_le_mul_of_nonneg_right (hK p) (by linarith)
      _ = K * (1 + ‖p‖) ^ (k + 1) := by ring
      _ ≤ K * (2 ^ (k + 1) * (1 + ‖p‖ ^ (k + 1))) := mul_le_mul_of_nonneg_left h2 hK0
      _ = K * 2 ^ (k + 1) * (1 + ‖p‖ ^ (k + 1)) := by ring
  · exact mul_nonneg hc (by positivity)

/-- Closeness of `IP Φ` and `IP Ψ` up to the tail. -/
theorem IP_close (hG : GoodBasis μ e) {N : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (hJ : JR ≤ J) {Φ Ψ : ℝ × (Fin JR → ℝ) → ℝ} (hΦ : Continuous Φ) (hΨ : Continuous Ψ)
    {BΨ : ℝ} (hΨb : ∀ p, ‖Ψ p‖ ≤ BΨ) {K : ℝ} {k : ℕ} (hK0 : 0 ≤ K)
    (hK : ∀ p, |Φ p| ≤ K * (1 + ‖p‖) ^ k) {ρ ε' M : ℝ} (hρ : 0 < ρ)
    (happ : ∀ p, |Φ p - Ψ p| ≤ ε' + (if ρ < ‖p‖ then |Φ p| else 0))
    (B' : Finset (Fin N))
    (hVi : Integrable (fun w => ‖Vec e c δ hJ B' w‖ ^ (k + 1)) (pairMeasure μ N J))
    (hVM : ∫ w, ‖Vec e c δ hJ B' w‖ ^ (k + 1) ∂pairMeasure μ N J ≤ M) :
    |IP μ e c δ hJ Φ B' - IP μ e c δ hJ Ψ B'| ≤
      ε' + K * 2 ^ (k + 1) / (1 + ρ) * (1 + M) := by
  set Q := pairMeasure μ N J with hQ
  set Kg : ℝ := K * 2 ^ (k + 1) with hKg
  have hKg0 : 0 ≤ Kg := mul_nonneg hK0 (by positivity)
  have hc0 : 0 ≤ Kg / (1 + ρ) := div_nonneg hKg0 (by linarith)
  have hVm := measurable_Vec hG c δ hJ B'
  have hΦm : Measurable fun w => Φ (Vec e c δ hJ B' w) := hΦ.measurable.comp hVm
  have hΨm : Measurable fun w => Ψ (Vec e c δ hJ B' w) := hΨ.measurable.comp hVm
  have hΨi : Integrable (fun w => Ψ (Vec e c δ hJ B' w)) Q :=
    Integrable.of_bound hΨm.aestronglyMeasurable BΨ (ae_of_all _ fun w => hΨb _)
  have hbi : Integrable (fun w => Kg * (1 + ‖Vec e c δ hJ B' w‖ ^ (k + 1))) Q :=
    ((integrable_const (1 : ℝ)).add hVi).const_mul _
  have hΦi : Integrable (fun w => Φ (Vec e c δ hJ B' w)) Q :=
    hbi.mono' hΦm.aestronglyMeasurable (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs]; exact abs_le_growth hK0 hK _)
  have hIP : ∀ F : ℝ × (Fin JR → ℝ) → ℝ, IP μ e c δ hJ F B' =
      ∫ w, F (Vec e c δ hJ B' w) ∂Q := fun F => rfl
  rw [hIP, hIP, ← integral_sub hΦi hΨi]
  set W : (Fin N → Torus d × (Fin J → ℝ)) → ℝ := fun w =>
    ε' + Kg / (1 + ρ) * (1 + ‖Vec e c δ hJ B' w‖ ^ (k + 1)) with hW
  have hWi : Integrable W Q :=
    (integrable_const ε').add (((integrable_const (1 : ℝ)).add hVi).const_mul _)
  have hpt : ∀ w, ‖Φ (Vec e c δ hJ B' w) - Ψ (Vec e c δ hJ B' w)‖ ≤ W w := by
    intro w
    rw [Real.norm_eq_abs]
    exact (happ _).trans (add_le_add_right (tail_le hK0 hK hρ _) _)
  refine (norm_integral_le_of_norm_le hWi (ae_of_all _ hpt)).trans ?_
  have hWv : ∫ w, W w ∂Q = ε' + Kg / (1 + ρ) * (1 + ∫ w, ‖Vec e c δ hJ B' w‖ ^ (k + 1) ∂Q) := by
    simp only [hW]
    have hint0 : Integrable (fun w => 1 + ‖Vec e c δ hJ B' w‖ ^ (k + 1)) Q :=
      (integrable_const (1 : ℝ)).add hVi
    have hint1 : Integrable
        (fun w => Kg / (1 + ρ) * (1 + ‖Vec e c δ hJ B' w‖ ^ (k + 1))) Q := hint0.const_mul _
    rw [integral_add (integrable_const ε') hint1, integral_const_mul,
      integral_add (integrable_const (1 : ℝ)) hVi]
    simp
  rw [hWv]
  have : Kg / (1 + ρ) * (1 + ∫ w, ‖Vec e c δ hJ B' w‖ ^ (k + 1) ∂Q) ≤ Kg / (1 + ρ) * (1 + M) :=
    mul_le_mul_of_nonneg_left (by linarith) hc0
  linarith

/-- A lower bound on the number of low-influence labels. -/
theorem lowCount_lower {lam : ℕ → ℝ} (hlam0 : lam 0 = 0) (hnn : ∀ k, 0 ≤ lam k)
    (hmono : Monotone lam) (hpos : 0 < lam 1) {N : ℕ} {L B : ℝ}
    {c : (Fin N → Fin (J + 1)) → ℝ} (hc : SpectralCoeff lam L c) (hB : ∑ j, c j ^ 2 ≤ B ^ 2)
    {δ : ℝ} (hδ : 0 < δ) :
    (N : ℝ) - max (L / lam 1) 0 * B ^ 2 / δ ≤ (lowCount c δ : ℝ) := by
  refine le_trans ?_ (lowCount_ge hlam0 hnn hmono hpos hc hδ)
  have hS : 0 ≤ ∑ j, c j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : L / lam 1 * ∑ j, c j ^ 2 ≤ max (L / lam 1) 0 * B ^ 2 :=
    calc L / lam 1 * ∑ j, c j ^ 2 ≤ max (L / lam 1) 0 * ∑ j, c j ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hS
      _ ≤ max (L / lam 1) 0 * B ^ 2 := mul_le_mul_of_nonneg_left hB (le_max_right _ _)
  have := div_le_div_of_nonneg_right h1 hδ.le
  linarith

/-- **Piece H.** (7.11) for a `GoodBasis`. -/
theorem joint_replace_good (hG : GoodBasis μ e) (hmom : HybridPolyMoment μ e lam J)
    (hlam0 : lam 0 = 0) (hnn : ∀ k, 0 ≤ lam k) (hmono : Monotone lam) (hpos : 0 < lam 1)
    (hJ : JR ≤ J) {Φ : ℝ × (Fin JR → ℝ) → ℝ} (hΦ : Continuous Φ)
    (hgrowth : ∃ (K : ℝ) (k : ℕ), ∀ p, |Φ p| ≤ K * (1 + ‖p‖) ^ k) (L B : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ᶠ N in atTop, ∀ c : (Fin N → Fin (J + 1)) → ℝ, SpectralCoeff lam L c →
        ∑ j, c j ^ 2 ≤ B ^ 2 →
          |IP μ e c δ hJ Φ Finset.univ - IP μ e c δ hJ Φ (retained c δ)| ≤ ε := by
  intro ε hε
  obtain ⟨K, k, hK⟩ := hgrowth
  have hK0 : 0 ≤ K := by
    have := hK 0
    simp only [norm_zero, add_zero, one_pow, mul_one] at this
    exact (abs_nonneg _).trans this
  obtain ⟨M, hM0, hM⟩ := Vec_moment hG hmom hlam0 hJ L B (k + 1)
  set Kg : ℝ := K * 2 ^ (k + 1) with hKg
  have hKg0 : 0 ≤ Kg := mul_nonneg hK0 (by positivity)
  set ρ : ℝ := 8 * Kg * (1 + M) / ε + 1 with hρdef
  have hρ : 0 < ρ := by positivity
  have hε8 : 0 < ε / 8 := by positivity
  obtain ⟨Ψ, hΨs, hΨc, hΨa⟩ := exists_smooth_approx_cutoff hΦ hρ hε8
  obtain ⟨BΨ, hBΨ⟩ := hΨc.exists_bound_of_continuous hΨs.continuous
  obtain ⟨C0, hC0⟩ := joint_rate_good hG hmom hlam0 hnn hmono hpos hJ hΨs hΨc L B
  set C : ℝ := max C0 0 with hC
  have hC0' : 0 ≤ C := le_max_right _ _
  have hCC : ∀ x, 0 ≤ x → C0 * x ≤ C * x := fun x hx =>
    mul_le_mul_of_nonneg_right (le_max_left _ _) hx
  -- closeness for every admissible `c` and every `B'`
  have hclose : ∀ (N : ℕ) (c : (Fin N → Fin (J + 1)) → ℝ), SpectralCoeff lam L c →
      ∑ j, c j ^ 2 ≤ B ^ 2 → ∀ (δ : ℝ), 0 < lowCount c δ → ∀ B' : Finset (Fin N),
        |IP μ e c δ hJ Φ B' - IP μ e c δ hJ Ψ B'| ≤ ε / 4 := by
    intro N c hc hB δ hn B'
    obtain ⟨hVi, hVM⟩ := hM N c hc hB δ hn B'
    have h := IP_close hG c δ hJ hΦ hΨs.continuous hBΨ hK0 hK hρ
      (fun p => hΨa p) B' hVi hVM
    refine h.trans ?_
    have hfrac : Kg / (1 + ρ) * (1 + M) ≤ ε / 8 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      have : ε / 8 * (1 + ρ) = Kg * (1 + M) + ε / 4 := by
        simp only [hρdef]; field_simp; ring
      rw [this]
      linarith
    linarith
  refine ⟨(ε / (4 * (C + 1))) ^ 2, by positivity, fun δ hδ hδ₀ => ?_⟩
  set D' : ℝ := max (L / lam 1) 0 * B ^ 2 with hD'
  set n₀ : ℝ := (4 * (C + 1) / ε) ^ 2 with hn₀
  filter_upwards [eventually_ge_atTop (⌈n₀ + D' / δ⌉₊ + 1)] with N hN c hc hB
  have hNr : n₀ + D' / δ + 1 ≤ (N : ℝ) := by
    have h1 : n₀ + D' / δ ≤ (⌈n₀ + D' / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈n₀ + D' / δ⌉₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    push_cast at h2
    linarith
  have hlow := lowCount_lower hlam0 hnn hmono hpos hc hB hδ
  have hnr : n₀ + 1 ≤ (lowCount c δ : ℝ) := by
    have : D' / δ = max (L / lam 1) 0 * B ^ 2 / δ := rfl
    linarith
  have hn0 : 0 < lowCount c δ := by
    have : (0 : ℝ) < (lowCount c δ : ℝ) := by
      have : 0 ≤ n₀ := by positivity
      linarith
    exact_mod_cast this
  have hrate := hC0 N c hc hB δ hδ hn0
  -- numerical estimates
  have hC1 : 0 < 4 * (C + 1) := by positivity
  have hsqδ : Real.sqrt δ < ε / (4 * (C + 1)) := by
    calc Real.sqrt δ < Real.sqrt ((ε / (4 * (C + 1))) ^ 2) := Real.sqrt_lt_sqrt hδ.le hδ₀
      _ = ε / (4 * (C + 1)) := Real.sqrt_sq (by positivity)
  have hsqn : 4 * (C + 1) / ε ≤ Real.sqrt (lowCount c δ) := by
    calc 4 * (C + 1) / ε = Real.sqrt n₀ := by
          rw [hn₀, Real.sqrt_sq (by positivity)]
      _ ≤ Real.sqrt (lowCount c δ) := Real.sqrt_le_sqrt (by linarith)
  have hainv : (Real.sqrt (lowCount c δ))⁻¹ ≤ ε / (4 * (C + 1)) := by
    have hpos' : 0 < 4 * (C + 1) / ε := by positivity
    calc (Real.sqrt (lowCount c δ))⁻¹ ≤ (4 * (C + 1) / ε)⁻¹ := inv_anti₀ hpos' hsqn
      _ = ε / (4 * (C + 1)) := by rw [inv_div]
  have hCe : C * (ε / (4 * (C + 1))) ≤ ε / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ hC1 (by norm_num : (0 : ℝ) < 4)]
    nlinarith [hε]
  have hsum : C0 * (Real.sqrt δ + (Real.sqrt (lowCount c δ))⁻¹) ≤ ε / 2 := by
    have hnn' : 0 ≤ Real.sqrt δ + (Real.sqrt (lowCount c δ))⁻¹ := by positivity
    calc C0 * (Real.sqrt δ + (Real.sqrt (lowCount c δ))⁻¹)
        ≤ C * (Real.sqrt δ + (Real.sqrt (lowCount c δ))⁻¹) := hCC _ hnn'
      _ ≤ C * (ε / (4 * (C + 1)) + ε / (4 * (C + 1))) := by
          apply mul_le_mul_of_nonneg_left _ hC0'
          linarith
      _ = 2 * (C * (ε / (4 * (C + 1)))) := by ring
      _ ≤ ε / 2 := by linarith
  have e1 := hclose N c hc hB δ hn0 Finset.univ
  have e2 := hclose N c hc hB δ hn0 (retained c δ)
  calc |IP μ e c δ hJ Φ Finset.univ - IP μ e c δ hJ Φ (retained c δ)|
      = |(IP μ e c δ hJ Φ Finset.univ - IP μ e c δ hJ Ψ Finset.univ) +
          (IP μ e c δ hJ Ψ Finset.univ - IP μ e c δ hJ Ψ (retained c δ)) +
          (IP μ e c δ hJ Ψ (retained c δ) - IP μ e c δ hJ Φ (retained c δ))| := by
        congr 1; ring
    _ ≤ |IP μ e c δ hJ Φ Finset.univ - IP μ e c δ hJ Ψ Finset.univ| +
          |IP μ e c δ hJ Ψ Finset.univ - IP μ e c δ hJ Ψ (retained c δ)| +
          |IP μ e c δ hJ Ψ (retained c δ) - IP μ e c δ hJ Φ (retained c δ)| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ ε / 4 + ε / 2 + ε / 4 := by
        have e2' : |IP μ e c δ hJ Ψ (retained c δ) - IP μ e c δ hJ Φ (retained c δ)| ≤ ε / 4 := by
          rw [abs_sub_comm]; exact e2
        have := hrate
        linarith
    _ = ε := by ring

/-- **S26 `joint_replace` with the interface `HybridPolyMoment` as an explicit hypothesis.** -/
theorem joint_replace_of_moment {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (J JR : ℕ) (hJ : JR ≤ J) (hmom : HybridPolyMoment (μ : Measure (Torus d)) e lam J)
    (Φ : ℝ × (Fin JR → ℝ) → ℝ) (hΦ : Continuous Φ)
    (hgrowth : ∃ (K : ℝ) (k : ℕ), ∀ p, |Φ p| ≤ K * (1 + ‖p‖) ^ k) (L B : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ᶠ N in atTop, ∀ c : (Fin N → Fin (J + 1)) → ℝ, SpectralCoeff lam L c →
        ∑ j, c j ^ 2 ≤ B ^ 2 →
          |∫ X, Φ (polyEval e c X, fun m => Zlow e c δ X (Fin.castLE hJ m))
              ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) -
            ∫ w, Φ (hybEval e c δ w, fun m => Glow c δ w (Fin.castLE hJ m))
              ∂hybMeasure (μ : Measure (Torus d)) N J| ≤ ε := by
  obtain ⟨e', hG, hae⟩ := exists_goodBasis hd hyp hr hμ he
  obtain ⟨hl0, hnn, hmono, hpos⟩ := lam_facts hd hyp hr hμ he
  have hae' : ∀ j, e j =ᵐ[(μ : Measure (Torus d))] e' j := fun j => (hae j).symm
  have hmom' := hmom.of_ae_eq hae'
  intro ε hε
  obtain ⟨δ₀, hδ₀, hδ⟩ := joint_replace_good hG hmom' hl0 hnn hmono hpos hJ hΦ hgrowth L B ε hε
  refine ⟨δ₀, hδ₀, fun δ hδpos hδlt => ?_⟩
  filter_upwards [hδ δ hδpos hδlt] with N hN c hc hB
  rw [integral_orig_congr hae' c δ hJ Φ, integral_hyb_congr hae' c δ hJ Φ,
    integral_orig_eq_IP, integral_hyb_eq_IP]
  exact hN c hc hB

end SharpLSI.FL
