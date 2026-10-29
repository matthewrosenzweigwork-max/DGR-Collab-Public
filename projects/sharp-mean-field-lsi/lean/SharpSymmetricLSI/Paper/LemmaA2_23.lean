import SharpSymmetricLSI.Paper.LemmaA2_22

/-!
# R25 Lemma A.2, part 23: `K_t → K` in `L²` and in energy

With `F_t = K_t - K`, Parseval and the weighted Hilbert–Schmidt identity give
`∬ F_t² = ∑ (e^{-t(λ_i+λ_j)} - 1)² T_ij²` and `∬ |∇_x F_t|² = ∑ λ_i (…)² T_ij²` (similarly in `y`);
dominated convergence for series gives the limits (`tendsto_L2_Kt`, `tendsto_energy_Kt`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

theorem lipschitzWith_of_lift_bound (hd : 1 ≤ d) {f : Torus d → ℝ} {L : ℝ} (hL0 : 0 ≤ L)
    (hf : ∀ a b, f (liftT a) - f (liftT b) ≤ L * dE a b) :
    LipschitzWith (Real.toNNReal (L * d)) (f ∘ liftT) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [Real.dist_eq, Real.coe_toNNReal _ (mul_nonneg hL0 (Nat.cast_nonneg _)), abs_le]
  have h1 := hf a b
  have h2 := hf b a
  rw [dE_symm'] at h2
  have h3 := mul_le_mul_of_nonneg_left (dE_le_card_mul_dist hd a b) hL0
  simp only [Function.comp]
  constructor <;> nlinarith

section coeffsub

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C) (hρc : Continuous ρ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (hb : IsRefEigenbasis (densMeasure ρ) e lam)
include hρ hρc hb

theorem Tc_sub {A B : Torus d → Torus d → ℝ} (hA : Continuous (Function.uncurry A))
    (hB : Continuous (Function.uncurry B)) (i j : ℕ) :
    ∫ y, (∫ x, (A x y - B x y) * e i x ∂densMeasure ρ) * e j y ∂densMeasure ρ =
      (∫ y, (∫ x, A x y * e i x ∂densMeasure ρ) * e j y ∂densMeasure ρ) -
        ∫ y, (∫ x, B x y * e i x ∂densMeasure ρ) * e j y ∂densMeasure ρ := by
  haveI := hρ.isProb
  set P := densMeasure ρ
  have hei : ∀ i, Integrable (e i) P := fun i => ((hb.memH1 i).2.1).integrable one_le_two
  have hbd : ∀ {F : Torus d → Torus d → ℝ}, Continuous (Function.uncurry F) → ∃ B, ∀ x y, |F x y| ≤ B :=
    fun {F} hF => by
      obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
      exact ⟨B, fun x y => by simpa [Real.norm_eq_abs] using hB (x, y) (mem_univ _)⟩
  obtain ⟨BA, hBA⟩ := hbd hA
  obtain ⟨BB, hBB⟩ := hbd hB
  have hin : ∀ {F : Torus d → Torus d → ℝ}, Continuous (Function.uncurry F) → ∀ y i,
      Integrable (fun x => F x y * e i x) P := fun {F} hF y i => by
    obtain ⟨B, hB⟩ := hbd hF
    exact (hei i).bdd_mul (c := B) ((hF.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x y)
  have hout : ∀ {F : Torus d → Torus d → ℝ}, Continuous (Function.uncurry F) →
      Integrable (fun y => (∫ x, F x y * e i x ∂P) * e j y) P := fun {F} hF => by
    obtain ⟨B, hB⟩ := hbd hF
    refine (hei j).bdd_mul (c := B) (continuous_slice_coeff hρ hρc hb hF i).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_coeff_le_sup hρ hb (hF.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (fun x => hB x y) i)
  rw [← integral_sub (hout hA) (hout hB)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [← sub_mul, ← integral_sub (hin hA y i) (hin hB y i)]
  congr 1; congr 1; funext x; ring

theorem transpose_coeff {A : Torus d → Torus d → ℝ} (hA : Continuous (Function.uncurry A)) (i j : ℕ) :
    ∫ y, (∫ x, A y x * e i x ∂densMeasure ρ) * e j y ∂densMeasure ρ =
      ∫ y, (∫ x, A x y * e j x ∂densMeasure ρ) * e i y ∂densMeasure ρ :=
  fubini_coeff hρ hb (A := fun a b => A b a) (hA.comp (continuous_snd.prodMk continuous_fst)) i j

end coeffsub

theorem exp_mul_exp_sub_one_sq_le {t a b : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.exp (-t * a) * Real.exp (-t * b) - 1) ^ 2 ≤ 1 := by
  have h1 : Real.exp (-t * a) * Real.exp (-t * b) ≤ 1 := by
    rw [← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by nlinarith)
  have h2 : 0 ≤ Real.exp (-t * a) * Real.exp (-t * b) := by positivity
  nlinarith

theorem tendsto_exp_mul_exp_sub_one {s : ℕ → ℝ} (hs0 : Tendsto s atTop (𝓝 0)) (a b : ℝ) :
    Tendsto (fun n => (Real.exp (-s n * a) * Real.exp (-s n * b) - 1) ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun n => Real.exp (-s n * a) * Real.exp (-s n * b)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n => Real.exp (-s n * a)) atTop (𝓝 1) := by
      have h' : Tendsto (fun n => -s n * a) atTop (𝓝 0) := by simpa using (hs0.neg).mul_const a
      have := (Real.continuous_exp.tendsto 0).comp h'
      rw [Real.exp_zero] at this; exact this
    have h2 : Tendsto (fun n => Real.exp (-s n * b)) atTop (𝓝 1) := by
      have h' : Tendsto (fun n => -s n * b) atTop (𝓝 0) := by simpa using (hs0.neg).mul_const b
      have := (Real.continuous_exp.tendsto 0).comp h'
      rw [Real.exp_zero] at this; exact this
    simpa using h1.mul h2
  have := ((h.sub_const 1).pow 2)
  simpa using this

section conv

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C) (hρc : Continuous ρ) {K : ℝ}
  (hQ : ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
      ∀ ξ : Fin d → ℝ, -K * (∑ k, ξ k ^ 2) * ∫ x, φ x ≤
        ∫ x, -Real.log (ρ (liftT x)) * secondDirDeriv φ ξ x)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (hb : IsRefEigenbasis (densMeasure ρ) e lam)
  {eC : ℕ → Torus d → ℝ} (heC1 : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT))
  (heCae : ∀ j, eC j =ᵐ[densMeasure ρ] e j)
  {M M' : ℕ → ℝ} (hM : ∀ j x, |eC j x| ≤ M j) (hM' : ∀ j x, ‖fderiv ℝ (eC j ∘ liftT) x‖ ≤ M' j)
  (hS : ∀ t, 0 < t → Summable (fun j => Real.exp (-t * lam j) * M j) ∧
    Summable (fun j => Real.exp (-t * lam j) * M' j))
  (hd : 1 ≤ d) (hK0 : 0 ≤ K) {Kf : Torus d → Torus d → ℝ}
  (hKc : Continuous (Function.uncurry Kf)) {BK : ℝ} (hBK : ∀ x y, |Kf x y| ≤ BK) {LK : ℝ}
  (hLK0 : 0 ≤ LK) (hL1 : ∀ y a b, Kf (liftT a) y - Kf (liftT b) y ≤ LK * dE a b)
  (hL2 : ∀ x a b, Kf x (liftT a) - Kf x (liftT b) ≤ LK * dE a b)
include hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2

/-- The coefficients of `K_t - K`. -/
theorem Ft_coeff {t : ℝ} (ht : 0 < t) (i j : ℕ) :
    ∫ y, (∫ x, (Kt (densMeasure ρ) e eC lam t Kf x y - Kf x y) * e i x ∂densMeasure ρ) * e j y
        ∂densMeasure ρ =
      (Real.exp (-t * lam i) * Real.exp (-t * lam j) - 1) *
        ∫ y, (∫ x, Kf x y * e i x ∂densMeasure ρ) * e j y ∂densMeasure ρ := by
  rw [Tc_sub hρ hρc hb (continuous_Kt hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2 ht)
    hKc, Kt_coeff2 hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2 ht]
  ring

/-- **`K_t → K` in `L²(μ⊗μ)`.** -/
theorem tendsto_L2_Kt {s : ℕ → ℝ} (hs : ∀ n, 0 < s n) (hs0 : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, (∫ x, (Kt (densMeasure ρ) e eC lam (s n) Kf x y - Kf x y) ^ 2
      ∂densMeasure ρ) ∂densMeasure ρ) atTop (𝓝 0) := by
  set P := densMeasure ρ
  set T : ℕ × ℕ → ℝ := fun ij => ∫ y, (∫ x, Kf x y * e ij.1 x ∂P) * e ij.2 y ∂P
  have hT := parseval_gen hρ hρc hb hKc
  have hlam0 : ∀ i, 0 ≤ lam i := fun i => refLam_nonneg hρ hb i
  have hval : ∀ n, ∫ y, (∫ x, (Kt P e eC lam (s n) Kf x y - Kf x y) ^ 2 ∂P) ∂P =
      ∑' ij : ℕ × ℕ, (Real.exp (-s n * lam ij.1) * Real.exp (-s n * lam ij.2) - 1) ^ 2 * T ij ^ 2 := by
    intro n
    have hF : Continuous (Function.uncurry fun x y => Kt P e eC lam (s n) Kf x y - Kf x y) :=
      (continuous_Kt hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2 (hs n)).sub hKc
    have h := parseval_gen hρ hρc hb hF
    refine h.tsum_eq.symm.trans (tsum_congr fun ij => ?_)
    rw [Ft_coeff hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2 (hs n)]
    ring
  simp_rw [hval]
  have := tendsto_tsum_of_dominated_convergence (bound := fun ij => T ij ^ 2) hT.summable
    (f := fun n (ij : ℕ × ℕ) =>
      (Real.exp (-s n * lam ij.1) * Real.exp (-s n * lam ij.2) - 1) ^ 2 * T ij ^ 2)
    (g := fun _ => (0 : ℝ))
    (fun ij => by simpa using (tendsto_exp_mul_exp_sub_one hs0 (lam ij.1) (lam ij.2)).mul_const (T ij ^ 2))
    (Eventually.of_forall fun n ij => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_of_le_one_left (sq_nonneg _)
        (exp_mul_exp_sub_one_sq_le (hs n).le (hlam0 _) (hlam0 _)))
  simpa using this

/-- **`K_t → K` in energy, first variable.** -/
theorem tendsto_energy_Kt_x {s : ℕ → ℝ} (hs : ∀ n, 0 < s n) (hs0 : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, (∫ x, sqNorm (lipGrad (fun x =>
      Kt (densMeasure ρ) e eC lam (s n) Kf x y - Kf x y) x) ∂densMeasure ρ) ∂densMeasure ρ)
      atTop (𝓝 0) := by
  set P := densMeasure ρ
  set T : ℕ × ℕ → ℝ := fun ij => ∫ y, (∫ x, Kf x y * e ij.1 x ∂P) * e ij.2 y ∂P
  have hlam0 : ∀ i, 0 ≤ lam i := fun i => refLam_nonneg hρ hb i
  have hT := weighted_hs_gen hρ hρc hb hKc (fun y => lipschitzWith_of_lift_bound hd hLK0 (hL1 y))
  have hval : ∀ n, ∫ y, (∫ x, sqNorm (lipGrad (fun x =>
      Kt P e eC lam (s n) Kf x y - Kf x y) x) ∂P) ∂P =
      ∑' ij : ℕ × ℕ, (Real.exp (-s n * lam ij.1) * Real.exp (-s n * lam ij.2) - 1) ^ 2 *
        (lam ij.1 * T ij ^ 2) := by
    intro n
    obtain ⟨-, hK1, -, -, -⟩ := Kt_props hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 (hs n) hKc hBK
      hLK0 hL1 hL2
    have hF : Continuous (Function.uncurry fun x y => Kt P e eC lam (s n) Kf x y - Kf x y) :=
      (continuous_Kt hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2 (hs n)).sub hKc
    have hE : 0 ≤ Real.exp (K * s n) * LK + LK := by positivity
    have h := weighted_hs_gen hρ hρc hb hF (fun y => lipschitzWith_of_lift_bound hd hE
      fun a b => by have := hK1 y a b; have := hL1 y b a; rw [dE_symm'] at this; nlinarith)
    refine h.tsum_eq.symm.trans (tsum_congr fun ij => ?_)
    rw [Ft_coeff hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2 (hs n)]
    ring
  simp_rw [hval]
  have := tendsto_tsum_of_dominated_convergence (bound := fun ij => lam ij.1 * T ij ^ 2)
    hT.summable (g := fun _ => (0 : ℝ))
    (f := fun n (ij : ℕ × ℕ) =>
      (Real.exp (-s n * lam ij.1) * Real.exp (-s n * lam ij.2) - 1) ^ 2 * (lam ij.1 * T ij ^ 2))
    (fun ij => by simpa using (tendsto_exp_mul_exp_sub_one hs0 (lam ij.1) (lam ij.2)).mul_const (lam ij.1 * T ij ^ 2))
    (Eventually.of_forall fun n ij => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (mul_nonneg (hlam0 _) (sq_nonneg _)))]
      exact mul_le_of_le_one_left (mul_nonneg (hlam0 _) (sq_nonneg _))
        (exp_mul_exp_sub_one_sq_le (hs n).le (hlam0 _) (hlam0 _)))
  simpa using this

/-- **`K_t → K` in energy, second variable.** -/
theorem tendsto_energy_Kt_y {s : ℕ → ℝ} (hs : ∀ n, 0 < s n) (hs0 : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, (∫ x, sqNorm (lipGrad (fun x =>
      Kt (densMeasure ρ) e eC lam (s n) Kf y x - Kf y x) x) ∂densMeasure ρ) ∂densMeasure ρ)
      atTop (𝓝 0) := by
  set P := densMeasure ρ
  set T : ℕ × ℕ → ℝ := fun ij => ∫ y, (∫ x, Kf x y * e ij.2 x ∂P) * e ij.1 y ∂P
  have hlam0 : ∀ i, 0 ≤ lam i := fun i => refLam_nonneg hρ hb i
  have hKcT : Continuous (Function.uncurry fun x y => Kf y x) :=
    hKc.comp (continuous_snd.prodMk continuous_fst)
  have hT0 := weighted_hs_gen hρ hρc hb hKcT (fun y => lipschitzWith_of_lift_bound hd hLK0 (hL2 y))
  have hT : HasSum (fun ij : ℕ × ℕ => lam ij.1 * T ij ^ 2)
      (∫ y, (∫ x, sqNorm (lipGrad (fun x => Kf y x) x) ∂P) ∂P) := by
    convert hT0 using 2 with ij
    simp only [T]
    rw [transpose_coeff hρ hρc hb hKc]
  have hval : ∀ n, ∫ y, (∫ x, sqNorm (lipGrad (fun x =>
      Kt P e eC lam (s n) Kf y x - Kf y x) x) ∂P) ∂P =
      ∑' ij : ℕ × ℕ, (Real.exp (-s n * lam ij.2) * Real.exp (-s n * lam ij.1) - 1) ^ 2 *
        (lam ij.1 * T ij ^ 2) := by
    intro n
    obtain ⟨-, -, hK2, -, -⟩ := Kt_props hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 (hs n) hKc hBK
      hLK0 hL1 hL2
    have hF : Continuous (Function.uncurry fun x y => Kt P e eC lam (s n) Kf x y - Kf x y) :=
      (continuous_Kt hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2 (hs n)).sub hKc
    have hFT : Continuous (Function.uncurry fun x y => Kt P e eC lam (s n) Kf y x - Kf y x) :=
      hF.comp (continuous_snd.prodMk continuous_fst)
    have hE : 0 ≤ Real.exp (K * s n) * LK + LK := by positivity
    have h := weighted_hs_gen hρ hρc hb hFT (fun y => lipschitzWith_of_lift_bound hd hE
      fun a b => by have := hK2 y a b; have := hL2 y b a; rw [dE_symm'] at this; nlinarith)
    refine h.tsum_eq.symm.trans (tsum_congr fun ij => ?_)
    rw [transpose_coeff hρ hρc hb hF,
      Ft_coeff hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2 (hs n)]
    ring
  simp_rw [hval]
  have := tendsto_tsum_of_dominated_convergence (bound := fun ij => lam ij.1 * T ij ^ 2)
    hT.summable (g := fun _ => (0 : ℝ))
    (f := fun n (ij : ℕ × ℕ) =>
      (Real.exp (-s n * lam ij.2) * Real.exp (-s n * lam ij.1) - 1) ^ 2 * (lam ij.1 * T ij ^ 2))
    (fun ij => by simpa using (tendsto_exp_mul_exp_sub_one hs0 (lam ij.2) (lam ij.1)).mul_const (lam ij.1 * T ij ^ 2))
    (Eventually.of_forall fun n ij => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (mul_nonneg (hlam0 _) (sq_nonneg _)))]
      exact mul_le_of_le_one_left (mul_nonneg (hlam0 _) (sq_nonneg _))
        (exp_mul_exp_sub_one_sq_le (hs n).le (hlam0 _) (hlam0 _)))
  simpa using this

end conv

end SharpLSI
