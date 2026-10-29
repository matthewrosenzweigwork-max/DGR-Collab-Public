import FullLabeledLSI.Paper.Lindeberg3

/-!
# Lemma 7.1, part 5: the one-label Lindeberg step bound (Piece D)

`step_bound`: for `Φ ∈ C_c^∞`, a label `i ∈ B` of low influence,
`|IP B − IP (B.erase i)| ≤ C₁ (√Inf_i ^ 3 + (n^{-1/2}) ^ 3)`, `C₁` independent of `N, c, δ, B, i`.
-/

open MeasureTheory ProbabilityTheory
open scoped ContDiff

namespace SharpLSI.FL

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ} {J JR : ℕ}

/-- The inner (label-`i`) difference is controlled by the swap lemma. -/
theorem step_inner_bound (hG : GoodBasis μ e) {N : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (hJ : JR ≤ J) {Φ : ℝ × (Fin JR → ℝ) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {K₃ : ℝ}
    (hK₃ : ∀ z, ‖iteratedFDeriv ℝ 3 Φ z‖ ≤ K₃) {Bφ : ℝ} (hBφ : ∀ y, ‖Φ y‖ ≤ Bφ)
    (B : Finset (Fin N)) (i : Fin N) (hiB : i ∈ B) (hi : i ∈ (retained c δ)ᶜ)
    (w : Fin N → Torus d × (Fin J → ℝ)) :
    |∫ s, (Fint e c δ hJ Φ B (Function.update w i s) -
        Fint e c δ hJ Φ (B.erase i) (Function.update w i s)) ∂labelMeasure μ J| ≤
      K₃ * (∑ r : Fin J, |bco e c B i r.succ w| + (Real.sqrt (lowCount c δ))⁻¹) ^ 3 / 6 *
        (∫ y, ‖y‖ ^ 3 ∂epsLaw μ e J + ∫ y, ‖y‖ ^ 3 ∂gaussPi J) := by
  set a : ℝ := (Real.sqrt (lowCount c δ))⁻¹ with ha
  have ha0 : 0 ≤ a := by positivity
  set Ψ : (Fin J → ℝ) → ℝ := Psi e c δ hJ Φ B i w with hΨ
  have hΨc : Continuous Ψ := Psi_continuous c δ hJ hΦ.continuous B i w
  have hΨb : ∀ u, ‖Ψ u‖ ≤ Bφ := fun u => hBφ _
  have e1 : ∀ s : Torus d × (Fin J → ℝ),
      Fint e c δ hJ Φ B (Function.update w i s) -
        Fint e c δ hJ Φ (B.erase i) (Function.update w i s) = Ψ (eps e J s.1) - Ψ s.2 := by
    intro s
    rw [Fint_mem hG.zero c δ hJ Φ (B := B) (B₀ := B) i hi hiB (fun l _ => Iff.rfl),
      Fint_not_mem hG.zero c δ hJ Φ (B := B) (B₀ := B.erase i) i hi (Finset.notMem_erase i B)
        (fun l hl => by simp [Finset.mem_erase, hl]),
      Function.update_self]
    simp only [hΨ, Psi_update hG.zero]
  simp_rw [e1]
  have hI1 : Integrable (fun s : Torus d × (Fin J → ℝ) => Ψ (eps e J s.1)) (labelMeasure μ J) :=
    Integrable.of_bound (hΨc.measurable.comp ((measurable_eps hG J).comp measurable_fst)).aestronglyMeasurable
      Bφ (ae_of_all _ fun s => hΨb _)
  have hI2 : Integrable (fun s : Torus d × (Fin J → ℝ) => Ψ s.2) (labelMeasure μ J) :=
    Integrable.of_bound (hΨc.measurable.comp measurable_snd).aestronglyMeasurable
      Bφ (ae_of_all _ fun s => hΨb _)
  rw [integral_sub hI1 hI2]
  have h1 : ∫ s : Torus d × (Fin J → ℝ), Ψ (eps e J s.1) ∂labelMeasure μ J =
      ∫ u, Ψ u ∂epsLaw μ e J := by
    unfold labelMeasure
    rw [integral_fun_fst (fun x => Ψ (eps e J x))]
    simp only [probReal_univ, one_smul]
    rw [epsLaw, integral_map (measurable_eps hG J).aemeasurable hΨc.measurable.aestronglyMeasurable]
  have h2 : ∫ s : Torus d × (Fin J → ℝ), Ψ s.2 ∂labelMeasure μ J = ∫ u, Ψ u ∂gaussPi J := by
    unfold labelMeasure
    rw [integral_fun_snd (fun y => Ψ y)]
    simp only [probReal_univ, one_smul]
  rw [h1, h2]
  have hΨaff : Ψ = fun u => Φ ((bco e c B i 0 w, fun r' : Fin JR =>
      Cz e c δ B i (Fin.castLE hJ r') w) + Mlin hJ (fun r => bco e c B i r.succ w) a u) :=
    funext fun u => Psi_eq_affine c δ hJ Φ B i w u
  have hΦ3 : ContDiff ℝ 3 Φ := hΦ.of_le (by simp)
  have hsw := swap_affine hΦ3 hK₃ (bco e c B i 0 w, fun r' : Fin JR =>
      Cz e c δ B i (Fin.castLE hJ r') w) (Mlin hJ (fun r => bco e c B i r.succ w) a)
    (epsLaw μ e J) (gaussPi J) (epsLaw_integrable_cube hG J) (gaussPi_integrable_norm_cube J)
    (epsLaw_mean hG J) (epsLaw_cov hG J)
  rw [hΨaff]
  refine hsw.trans ?_
  have hMn : ‖Mlin hJ (fun r => bco e c B i r.succ w) a‖ ≤ ∑ r : Fin J, |bco e c B i r.succ w| + a := by
    have := Mlin_norm_le hJ (fun r => bco e c B i r.succ w) a
    rwa [abs_of_nonneg ha0] at this
  have hK0 : 0 ≤ K₃ := (norm_nonneg _).trans (hK₃ 0)
  have hM3 : 0 ≤ ∫ y, ‖y‖ ^ 3 ∂epsLaw μ e J + ∫ y, ‖y‖ ^ 3 ∂gaussPi J :=
    add_nonneg (integral_nonneg fun _ => by positivity) (integral_nonneg fun _ => by positivity)
  gcongr


/-- **Piece D.** One Lindeberg step. -/
theorem step_bound (hG : GoodBasis μ e) (hmom : HybridPolyMoment μ e lam J) (hlam0 : lam 0 = 0)
    (hnn : ∀ k, 0 ≤ lam k) (hJ : JR ≤ J) {Φ : ℝ × (Fin JR → ℝ) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hΦc : HasCompactSupport Φ) (L : ℝ) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (N : ℕ) (c : (Fin N → Fin (J + 1)) → ℝ), SpectralCoeff lam L c →
      ∀ (δ : ℝ) (B : Finset (Fin N)) (i : Fin N), i ∈ B → i ∈ (retained c δ)ᶜ →
        |IP μ e c δ hJ Φ B - IP μ e c δ hJ Φ (B.erase i)| ≤
          C₁ * (Real.sqrt (infl c i) ^ 3 + ((Real.sqrt (lowCount c δ))⁻¹) ^ 3) := by
  obtain ⟨K₃, hK₃0, hK₃⟩ := hΦc.exists_bound_iteratedFDeriv hΦ 3
  obtain ⟨Bφ, hBφ⟩ := hΦc.exists_bound_of_continuous hΦ.continuous
  obtain ⟨Kh, hKh0, hKh⟩ := hmom L 3
  have hK₃' : ∀ z, ‖iteratedFDeriv ℝ 3 Φ z‖ ≤ K₃ := fun z => hK₃ 3 le_rfl z
  set M3 : ℝ := ∫ y, ‖y‖ ^ 3 ∂epsLaw μ e J + ∫ y, ‖y‖ ^ 3 ∂gaussPi J with hM3
  have hM3nn : 0 ≤ M3 :=
    add_nonneg (integral_nonneg fun _ => by positivity) (integral_nonneg fun _ => by positivity)
  refine ⟨K₃ / 6 * M3 * 4 * ((J : ℝ) ^ 3 * Kh + 1), by positivity, ?_⟩
  intro N c hc δ B i hiB hilow
  set a : ℝ := (Real.sqrt (lowCount c δ))⁻¹ with ha
  have ha0 : 0 ≤ a := by positivity
  set Q := pairMeasure μ N J with hQ
  have hFm : ∀ B₀, Measurable (Fint e c δ hJ Φ B₀ : (Fin N → Torus d × (Fin J → ℝ)) → ℝ) :=
    fun B₀ => measurable_Fint hG c δ hJ hΦ.continuous B₀
  have hFi : ∀ B₀, Integrable (Fint e c δ hJ Φ B₀) Q := fun B₀ =>
    Integrable.of_bound (hFm B₀).aestronglyMeasurable Bφ (ae_of_all _ fun w => hBφ _)
  have hIP : ∀ B₀, IP μ e c δ hJ Φ B₀ = ∫ w, Fint e c δ hJ Φ B₀ w ∂Q := fun B₀ => rfl
  rw [hIP, hIP, ← integral_sub (hFi B) (hFi (B.erase i))]
  have hH : Integrable (fun w => Fint e c δ hJ Φ B w - Fint e c δ hJ Φ (B.erase i) w) Q :=
    (hFi B).sub (hFi (B.erase i))
  have key : ∫ w, (Fint e c δ hJ Φ B w - Fint e c δ hJ Φ (B.erase i) w) ∂Q =
      ∫ w, ∫ s, (Fint e c δ hJ Φ B (Function.update w i s) -
        Fint e c δ hJ Φ (B.erase i) (Function.update w i s)) ∂labelMeasure μ J ∂Q :=
    integral_pi_update (labelMeasure μ J) i hH
  rw [key]
  set G : (Fin N → Torus d × (Fin J → ℝ)) → ℝ := fun w =>
    K₃ / 6 * M3 * 4 * ((J : ℝ) ^ 2 * ∑ r : Fin J, |bco e c B i r.succ w| ^ 3 + a ^ 3) with hGdef
  have hbd : ∀ w, ‖∫ s, (Fint e c δ hJ Φ B (Function.update w i s) -
        Fint e c δ hJ Φ (B.erase i) (Function.update w i s)) ∂labelMeasure μ J‖ ≤ G w := by
    intro w
    rw [Real.norm_eq_abs]
    refine (step_inner_bound hG c δ hJ hΦ hK₃' hBφ B i hiB hilow w).trans ?_
    have hx : 0 ≤ ∑ r : Fin J, |bco e c B i r.succ w| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h2 := cube_add_le _ a hx ha0
    have h3 := sum_cube_le (fun r : Fin J => |bco e c B i r.succ w|) (fun r => abs_nonneg _)
    calc K₃ * (∑ r : Fin J, |bco e c B i r.succ w| + a) ^ 3 / 6 * M3
        ≤ K₃ * (4 * ((∑ r : Fin J, |bco e c B i r.succ w|) ^ 3 + a ^ 3)) / 6 * M3 := by gcongr
      _ ≤ K₃ * (4 * ((J : ℝ) ^ 2 * ∑ r : Fin J, |bco e c B i r.succ w| ^ 3 + a ^ 3)) / 6 * M3 := by
          gcongr
      _ = G w := by simp only [hGdef]; ring
  have hmr := fun r : Fin J => bco_moment hG hKh0 hKh hlam0 hnn hc B i r
  have hsumi : Integrable (fun w => ∑ r : Fin J, |bco e c B i r.succ w| ^ 3) Q :=
    integrable_finsetSum _ fun r _ => (hmr r).1
  have hGi : Integrable G Q :=
    (((hsumi.const_mul ((J : ℝ) ^ 2)).add (integrable_const (a ^ 3))).const_mul _)
  refine (norm_integral_le_of_norm_le hGi (ae_of_all _ hbd)).trans ?_
  have hGv : ∫ w, G w ∂Q = K₃ / 6 * M3 * 4 * ((J : ℝ) ^ 2 *
      ∑ r : Fin J, ∫ w, |bco e c B i r.succ w| ^ 3 ∂Q + a ^ 3) := by
    simp only [hGdef]
    rw [integral_const_mul, integral_add (hsumi.const_mul _) (integrable_const _),
      integral_const_mul, integral_finsetSum _ fun r _ => (hmr r).1]
    simp only [integral_const, probReal_univ, one_smul]
    rfl
  rw [hGv]
  set T : ℝ := Real.sqrt (infl c i) ^ 3 with hT
  have hT0 : 0 ≤ T := by positivity
  have hsum : ∑ r : Fin J, ∫ w, |bco e c B i r.succ w| ^ 3 ∂Q ≤ (J : ℝ) * (Kh * T) := by
    calc ∑ r : Fin J, ∫ w, |bco e c B i r.succ w| ^ 3 ∂Q ≤ ∑ _r : Fin J, Kh * T :=
          Finset.sum_le_sum fun r _ => (hmr r).2
      _ = (J : ℝ) * (Kh * T) := by simp
  have hJ0 : (0 : ℝ) ≤ J := by positivity
  have ha3 : 0 ≤ a ^ 3 := by positivity
  have hfin : (J : ℝ) ^ 2 * ∑ r : Fin J, ∫ w, |bco e c B i r.succ w| ^ 3 ∂Q + a ^ 3 ≤
      ((J : ℝ) ^ 3 * Kh + 1) * (T + a ^ 3) := by
    have h1 : (J : ℝ) ^ 2 * ∑ r : Fin J, ∫ w, |bco e c B i r.succ w| ^ 3 ∂Q ≤
        (J : ℝ) ^ 2 * ((J : ℝ) * (Kh * T)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    have h2 : (J : ℝ) ^ 2 * ((J : ℝ) * (Kh * T)) = (J : ℝ) ^ 3 * Kh * T := by ring
    nlinarith [mul_nonneg (mul_nonneg (pow_nonneg hJ0 3) hKh0) ha3]
  have hc0 : 0 ≤ K₃ / 6 * M3 * 4 := by positivity
  calc K₃ / 6 * M3 * 4 * ((J : ℝ) ^ 2 * ∑ r : Fin J, ∫ w, |bco e c B i r.succ w| ^ 3 ∂Q + a ^ 3)
      ≤ K₃ / 6 * M3 * 4 * (((J : ℝ) ^ 3 * Kh + 1) * (T + a ^ 3)) :=
        mul_le_mul_of_nonneg_left hfin hc0
    _ = K₃ / 6 * M3 * 4 * ((J : ℝ) ^ 3 * Kh + 1) * (Real.sqrt (infl c i) ^ 3 + a ^ 3) := by
        rw [hT]; ring

end SharpLSI.FL
