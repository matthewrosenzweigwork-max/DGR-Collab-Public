import SharpSymmetricLSI.Paper.CosineMinimizer

/-!
# (3.25): `λ^all_{N,κ} ≥ a max{e^{-κN/2}, e^{-2κ} - κ/N}` (Phase 3, lane C; R39)

The second-order inequality of Lemma 3.7 (smooth functions) is applied to the Fourier partial
sums `S_R f` of the minimizer `f` of Step 2. As `R → ∞`, `∇S_R f → ∇f` and
`L S_R f → L f = Δf - ∇U·∇f` in `L²`, and `L f = -λ f` (Fourier form of (3.42)), so
`a(e^{-2κ} - κ/N) λ ≤ ∫ (Lf)² dP = λ²`.
-/

open MeasureTheory InformationTheory Set Filter Topology Complex
open scoped ENNReal Real ContDiff ComplexConjugate
open UnitAddTorus

namespace SharpLSI

theorem psum_sum {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type*} (s : Finset α)
    (c : α → (ι → ℤ) → ℂ) (R : ℕ) (y : UnitAddTorus ι) :
    ∑ a ∈ s, psum (c a) R y = psum (fun k => ∑ a ∈ s, c a k) R y := by
  unfold psum psumC
  rw [← Complex.re_sum]
  congr 1
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

theorem Dk_psum {ι : Type} [Fintype ι] [DecidableEq ι] (c : (ι → ℤ) → ℂ) (R : ℕ) (p : ι) :
    Dk (psum c R ∘ liftT) p = psum (fun k => 2 * π * I * k p * c k) R ∘ liftT :=
  funext fun x => fderiv_psum c R x p

section Cosine

variable {N : ℕ}

theorem tendsto_weighted_sq {κ : ℝ} (hκ : 0 ≤ κ) {a : ℕ → UnitAddTorus (Fin N × Fin 1) → ℝ}
    {b : UnitAddTorus (Fin N × Fin 1) → ℝ} (ha : ∀ R, MemLp (a R) 2 volume) (hb : MemLp b 2 volume)
    (hlim : Tendsto (fun R => ∫ y, (a R y - b y) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun R => ∫ y, gsW κ N y * a R y ^ 2) atTop (𝓝 (∫ y, gsW κ N y * b y ^ 2)) := by
  obtain ⟨m, hm, hbd⟩ := gsW_bounds (N := N) hκ
  have hwm : AEStronglyMeasurable (gsW κ N) volume := (measurable_gsW κ).aestronglyMeasurable
  have hgb : ∀ y, ‖gsW κ N y‖ ≤ gsC κ N := fun y => by
    rw [Real.norm_eq_abs, abs_of_pos (gsW_pos κ y)]; exact (hbd y).2
  have hd : ∀ R, MemLp (fun y => a R y - b y) 2 volume := fun R => (ha R).sub hb
  have hwb : MemLp (fun y => gsW κ N y * b y) 2 volume := by
    refine (hb.const_mul (gsC κ N)).of_le (hwm.mul hb.aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (gsC_pos κ N).le]
    exact mul_le_mul_of_nonneg_right (hgb y) (norm_nonneg _)
  have h1 := tendsto_integral_mul_of_sq hd hwb hlim
  have h0 : Tendsto (fun R => ∫ y, gsW κ N y * (a R y - b y) ^ 2) atTop (𝓝 0) := by
    have hup : Tendsto (fun R => gsC κ N * ∫ y, (a R y - b y) ^ 2) atTop (𝓝 0) := by
      simpa using hlim.const_mul (gsC κ N)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun R => integral_nonneg fun y => mul_nonneg (gsW_pos κ y).le (sq_nonneg _)) fun R => ?_
    rw [← integral_const_mul]
    exact integral_mono (((hd R).integrable_sq).bdd_mul hwm (Eventually.of_forall hgb))
      ((hd R).integrable_sq.const_mul _) fun y => mul_le_mul_of_nonneg_right (hbd y).2 (sq_nonneg _)
  have hexp : ∀ R, ∫ y, gsW κ N y * a R y ^ 2 =
      (∫ y, gsW κ N y * (a R y - b y) ^ 2) + 2 * (∫ y, gsW κ N y * b y * (a R y - b y)) +
        ∫ y, gsW κ N y * b y ^ 2 := fun R => by
    have i1 : Integrable (fun y => gsW κ N y * (a R y - b y) ^ 2) volume :=
      ((hd R).integrable_sq).bdd_mul hwm (Eventually.of_forall hgb)
    have i2 : Integrable (fun y => gsW κ N y * b y * (a R y - b y)) volume := hwb.integrable_mul (hd R)
    have i3 : Integrable (fun y => gsW κ N y * b y ^ 2) volume :=
      hb.integrable_sq.bdd_mul hwm (Eventually.of_forall hgb)
    have e : (fun y => gsW κ N y * a R y ^ 2) = fun y =>
        gsW κ N y * (a R y - b y) ^ 2 + 2 * (gsW κ N y * b y * (a R y - b y)) +
          gsW κ N y * b y ^ 2 := by funext y; ring
    rw [e, integral_add (f := fun y => gsW κ N y * (a R y - b y) ^ 2 +
        2 * (gsW κ N y * b y * (a R y - b y))) (g := fun y => gsW κ N y * b y ^ 2)
        (i1.add (i2.const_mul 2)) i3,
      integral_add (f := fun y => gsW κ N y * (a R y - b y) ^ 2)
        (g := fun y => 2 * (gsW κ N y * b y * (a R y - b y))) i1 (i2.const_mul 2),
      integral_const_mul]
  have := (h0.add (h1.const_mul 2)).add (tendsto_const_nhds (x := ∫ y, gsW κ N y * b y ^ 2))
  simp only [mul_zero, zero_add] at this
  exact this.congr fun R => (hexp R).symm

theorem cf_add' {ι : Type} [Fintype ι] [DecidableEq ι] {a b : UnitAddTorus ι → ℝ}
    (ha : Integrable a volume) (hb : Integrable b volume) (k : ι → ℤ) :
    cf (fun y => a y + b y) k = cf a k + cf b k := by
  simp only [cf, SharpLSI.mFourierCoeff_eq_integral, Complex.ofReal_add, smul_add]
  exact integral_add (integrable_mFourier_smul' ha (-k)) (integrable_mFourier_smul' hb (-k))

theorem cf_const_mul' {ι : Type} [Fintype ι] [DecidableEq ι] (a : UnitAddTorus ι → ℝ) (c : ℝ)
    (k : ι → ℤ) : cf (fun y => c * a y) k = c * cf a k := by
  simp only [cf, SharpLSI.mFourierCoeff_eq_integral]
  rw [← integral_const_mul]; congr 1; funext t; push_cast; simp only [smul_eq_mul]; ring

/-- The data of the minimizer of Step 2. -/
def IsGapMin (κ : ℝ) (N : ℕ) (f : UnitAddTorus (Fin N × Fin 1) → ℝ)
    (G : UnitAddTorus (Fin N × Fin 1) → Fin N × Fin 1 → ℝ) : Prop :=
  MemLp f 2 volume ∧ (∀ j, MemLp (fun y => G y j) 2 volume) ∧ IsWeakGrad f G ∧
    ∫ y, gsW κ N y * f y = 0 ∧ ∫ y, gsW κ N y * f y ^ 2 = 1 ∧
    ∫ y, gsW κ N y * sqNorm (G y) = (lamAll cosV (cosW κ) N).toReal

/-- `Δf` via Fourier: coefficients `-4π²|k|² f̂(k)`. -/
noncomputable def lapC (f : UnitAddTorus (Fin N × Fin 1) → ℝ) (k : Fin N × Fin 1 → ℤ) : ℂ :=
  ((-(4 * π ^ 2 * ∑ j, ((k j : ℝ)) ^ 2) : ℝ) : ℂ) * cf f k

theorem exists_lap {κ : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N) {f G} (h : IsGapMin κ N f G) :
    ∃ Lap : UnitAddTorus (Fin N × Fin 1) → ℝ, MemLp Lap 2 volume ∧ ∀ k, cf Lap k = lapC f k := by
  obtain ⟨hf2, hG2, hfG, hmean, hnorm, hE⟩ := h
  have hH2 := summable_H2 hκ hN hf2 hG2 hfG hmean hnorm hE
  refine exists_of_cf ?_ fun k => ?_
  · refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) (hH2.mul_left (16 * π ^ 4))
    have hs0 : 0 ≤ ∑ j, ((k j : ℝ)) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    rw [lapC, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity),
      mul_pow]
    have h1 : (4 * π ^ 2 * ∑ j, ((k j : ℝ)) ^ 2) ^ 2 ≤ 16 * π ^ 4 * (1 + ∑ j, ((k j : ℝ)) ^ 2) ^ 2 := by
      have h2 := pow_le_pow_left₀ hs0 (by linarith : ∑ j, ((k j : ℝ)) ^ 2 ≤ 1 + ∑ j, ((k j : ℝ)) ^ 2) 2
      have h3 : 0 ≤ 16 * π ^ 4 := by positivity
      calc (4 * π ^ 2 * ∑ j, ((k j : ℝ)) ^ 2) ^ 2 = 16 * π ^ 4 * (∑ j, ((k j : ℝ)) ^ 2) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 h3
    calc (4 * π ^ 2 * ∑ j, ((k j : ℝ)) ^ 2) ^ 2 * ‖cf f k‖ ^ 2
        ≤ 16 * π ^ 4 * (1 + ∑ j, ((k j : ℝ)) ^ 2) ^ 2 * ‖cf f k‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = _ := by ring
  · simp only [lapC, Pi.neg_apply, Int.cast_neg, neg_sq, cf_neg, map_mul, Complex.conj_ofReal]

/-- Partial sums: gradient and Laplacian. -/
theorem Dk_psum_cf {f : UnitAddTorus (Fin N × Fin 1) → ℝ}
    {G : UnitAddTorus (Fin N × Fin 1) → Fin N × Fin 1 → ℝ}
    (hcfG : ∀ p k, cf (fun y => G y p) k = 2 * π * I * k p * cf f k) (R : ℕ) (p) (y) :
    Dk (psum (cf f) R ∘ liftT) p (secT y) = psum (cf (fun y => G y p)) R y := by
  rw [Dk_psum]
  simp only [Function.comp_apply, liftT_secT]
  congr 1; funext k; rw [hcfG]

theorem lap_psum (f : UnitAddTorus (Fin N × Fin 1) → ℝ) (R : ℕ) (y) :
    ∑ p, Dk (Dk (psum (cf f) R ∘ liftT) p) p (secT y) = psum (lapC f) R y := by
  simp_rw [Dk_psum]
  simp only [Function.comp_apply, liftT_secT]
  rw [psum_sum]
  congr 1; funext k
  simp only [lapC]
  push_cast
  rw [Finset.mul_sum, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring_nf; rw [Complex.I_sq]; ring

theorem memLp_drift {κ : ℝ} {G : UnitAddTorus (Fin N × Fin 1) → Fin N × Fin 1 → ℝ}
    (hG2 : ∀ j, MemLp (fun y => G y j) 2 volume) :
    MemLp (fun y => ∑ p, Dk (UL κ N) p (secT y) * G y p) 2 volume := by
  have := (memLp_eigen_rhs (κ := κ) (f := fun _ => (0 : ℝ)) (memLp_const 0) hG2 0).neg
  refine this.ae_eq (Eventually.of_forall fun y => ?_)
  simp

/-- `L f = -λ f`, hence `∫ w (Lf)² = λ²`. -/
theorem integral_Lf_sq {κ : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N) {f G} (h : IsGapMin κ N f G)
    {Lap : UnitAddTorus (Fin N × Fin 1) → ℝ} (hLap2 : MemLp Lap 2 volume)
    (hLapc : ∀ k, cf Lap k = lapC f k) :
    ∫ y, gsW κ N y * (Lap y - ∑ p, Dk (UL κ N) p (secT y) * G y p) ^ 2 =
      (lamAll cosV (cosW κ) N).toReal ^ 2 := by
  obtain ⟨hf2, hG2, hfG, hmean, hnorm, hE⟩ := h
  set L := (lamAll cosV (cosW κ) N).toReal with hL
  set S := fun y => ∑ p, Dk (UL κ N) p (secT y) * G y p with hS
  have hS2 : MemLp S 2 volume := memLp_drift hG2
  have he := cf_eigen hκ hN hf2 hG2 hfG hmean hnorm hE
  have hLf2 : MemLp (fun y => Lap y - S y) 2 volume := hLap2.sub hS2
  have hT2 : MemLp (fun y => (Lap y - S y) + L * f y) 2 volume := hLf2.add (hf2.const_mul L)
  have hzero : ∀ k, cf (fun y => (Lap y - S y) + L * f y) k = 0 := fun k => by
    rw [cf_add' (hLf2.integrable one_le_two) ((hf2.integrable one_le_two).const_mul L),
      cf_sub (hLap2.integrable one_le_two) (hS2.integrable one_le_two), hLapc, cf_const_mul']
    have h3 := he k
    rw [cf_sub ((hf2.integrable one_le_two).const_mul L) (hS2.integrable one_le_two),
      cf_const_mul'] at h3
    simp only [lapC]
    push_cast at h3 ⊢
    linear_combination -h3
  have hP := hasSum_sq_mFourierCoeff_real hT2
  have h0 : ∫ y, ((Lap y - S y) + L * f y) ^ 2 = 0 := by
    rw [← hP.tsum_eq]
    have : ∀ k, ‖mFourierCoeff (fun y => (((Lap y - S y) + L * f y : ℝ) : ℂ)) k‖ ^ 2 = 0 :=
      fun k => by rw [show mFourierCoeff (fun y => (((Lap y - S y) + L * f y : ℝ) : ℂ)) k =
        cf (fun y => (Lap y - S y) + L * f y) k from rfl, hzero]; simp
    simp only [this, tsum_zero]
  have hae : (fun y => ((Lap y - S y) + L * f y) ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _) hT2.integrable_sq).mp h0
  calc ∫ y, gsW κ N y * (Lap y - S y) ^ 2 = ∫ y, L ^ 2 * (gsW κ N y * f y ^ 2) :=
        integral_congr_ae (hae.mono fun y hy => by
          simp only [Pi.zero_apply] at hy
          have h1 : Lap y - S y = -(L * f y) := by
            have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy
            linarith
          show gsW κ N y * (Lap y - S y) ^ 2 = L ^ 2 * (gsW κ N y * f y ^ 2)
          rw [h1]; ring)
    _ = L ^ 2 := by rw [integral_const_mul, hnorm, mul_one]

theorem tendsto_generator_psum {κ : ℝ} (hN : 1 ≤ N) {G : UnitAddTorus (Fin N × Fin 1) → Fin N × Fin 1 → ℝ}
    (hG2 : ∀ j, MemLp (fun y => G y j) 2 volume) {Lap : UnitAddTorus (Fin N × Fin 1) → ℝ}
    (hLap2 : MemLp Lap 2 volume) :
    Tendsto (fun R => ∫ y, ((psum (cf Lap) R y -
        ∑ p, Dk (UL κ N) p (secT y) * psum (cf (fun y => G y p)) R y) -
        (Lap y - ∑ p, Dk (UL κ N) p (secT y) * G y p)) ^ 2) atTop (𝓝 0) := by
  have hU := smPer_UL (N := N) κ
  obtain ⟨B, hB⟩ : ∃ B, ∀ p x, |Dk (UL κ N) p x| ≤ B := by
    choose C hC using fun p => periodic_bounded (hU.Dk p).1.continuous (hU.Dk p).2
    exact ⟨∑ p, |C p|, fun p x => ((Real.norm_eq_abs _).symm ▸ hC p x).trans
      ((le_abs_self _).trans (Finset.single_le_sum (f := fun p => |C p|)
        (fun p _ => abs_nonneg _) (Finset.mem_univ p)))⟩
  set n : ℝ := (Fintype.card (Fin N × Fin 1) : ℝ)
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set dL := fun R y => psum (cf Lap) R y - Lap y
  set dG := fun R p y => psum (cf (fun y => G y p)) R y - G y p
  have hcL := tendsto_psum_sq hLap2
  have hcG := fun p => tendsto_psum_sq (hG2 p)
  have hup : Tendsto (fun R => 2 * (∫ y, dL R y ^ 2) +
      2 * n * (B ^ 2 * ∑ p, ∫ y, dG R p y ^ 2)) atTop (𝓝 0) := by
    have h1 := hcL.const_mul 2
    have h2 := ((tendsto_finset_sum Finset.univ fun p _ => hcG p).const_mul (B ^ 2)).const_mul (2 * n)
    have := h1.add h2
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun R => integral_nonneg fun y => sq_nonneg _) fun R => ?_
  have hiL : Integrable (fun y => dL R y ^ 2) volume := ((memLp_psum _ R 2).sub hLap2).integrable_sq
  have hiG : ∀ p, Integrable (fun y => dG R p y ^ 2) volume := fun p =>
    ((memLp_psum _ R 2).sub (hG2 p)).integrable_sq
  have hiS : Integrable (fun y => ∑ p, dG R p y ^ 2) volume := integrable_finset_sum _ fun p _ => hiG p
  have hlhs : MemLp (fun y => (psum (cf Lap) R y -
      ∑ p, Dk (UL κ N) p (secT y) * psum (cf (fun y => G y p)) R y) -
      (Lap y - ∑ p, Dk (UL κ N) p (secT y) * G y p)) 2 volume :=
    ((memLp_psum _ R 2).sub (memLp_drift (κ := κ) (G := fun y p => psum (cf (fun y => G y p)) R y)
      fun j => memLp_psum _ R 2)).sub (hLap2.sub (memLp_drift hG2))
  have hpt : ∀ y, ((psum (cf Lap) R y - ∑ p, Dk (UL κ N) p (secT y) * psum (cf (fun y => G y p)) R y) -
      (Lap y - ∑ p, Dk (UL κ N) p (secT y) * G y p)) ^ 2 ≤
      2 * dL R y ^ 2 + 2 * n * (B ^ 2 * ∑ p, dG R p y ^ 2) := fun y => by
    have e : (psum (cf Lap) R y - ∑ p, Dk (UL κ N) p (secT y) * psum (cf (fun y => G y p)) R y) -
        (Lap y - ∑ p, Dk (UL κ N) p (secT y) * G y p) =
        dL R y - ∑ p, Dk (UL κ N) p (secT y) * dG R p y := by
      simp only [dL, dG, mul_sub, Finset.sum_sub_distrib]; ring
    rw [e]
    have h1 : (∑ p, Dk (UL κ N) p (secT y) * dG R p y) ^ 2 ≤
        n * ∑ p, (Dk (UL κ N) p (secT y) * dG R p y) ^ 2 := sq_sum_le_card_mul_sum_sq
    have h2 : ∑ p, (Dk (UL κ N) p (secT y) * dG R p y) ^ 2 ≤ B ^ 2 * ∑ p, dG R p y ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun p _ => ?_
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB p _) 2) (sq_nonneg _)
    have h3 := mul_le_mul_of_nonneg_left h2 hn0
    nlinarith [sq_nonneg (dL R y + ∑ p, Dk (UL κ N) p (secT y) * dG R p y)]
  calc _ ≤ ∫ y, (2 * dL R y ^ 2 + 2 * n * (B ^ 2 * ∑ p, dG R p y ^ 2)) :=
        integral_mono hlhs.integrable_sq ((hiL.const_mul 2).add ((hiS.const_mul _).const_mul _)) hpt
    _ = _ := by
        rw [integral_add (f := fun y => 2 * dL R y ^ 2)
          (g := fun y => 2 * n * (B ^ 2 * ∑ p, dG R p y ^ 2)) (hiL.const_mul 2)
          ((hiS.const_mul _).const_mul _), integral_const_mul, integral_const_mul, integral_const_mul,
          integral_finset_sum _ fun p _ => hiG p]

theorem gsW_norm_le {κ : ℝ} (hκ : 0 ≤ κ) (y : UnitAddTorus (Fin N × Fin 1)) :
    ‖gsW κ N y‖ ≤ gsC κ N := by
  obtain ⟨m, hm, hb⟩ := gsW_bounds (N := N) hκ
  rw [Real.norm_eq_abs, abs_of_pos (gsW_pos κ y)]; exact (hb y).2

/-- The second-order inequality for the partial sums, on the flat torus. -/
theorem second_order_psum {κ : ℝ} (hκ : 0 < κ) {f : UnitAddTorus (Fin N × Fin 1) → ℝ}
    {G : UnitAddTorus (Fin N × Fin 1) → Fin N × Fin 1 → ℝ}
    (hcfG : ∀ p k, cf (fun y => G y p) k = 2 * π * I * k p * cf f k) (R : ℕ) :
    aCos * (Real.exp (-2 * κ) - κ / N) *
        ∑ p, ∫ y, gsW κ N y * psum (cf (fun y => G y p)) R y ^ 2 ≤
      ∫ y, gsW κ N y * (psum (lapC f) R y -
        ∑ p, Dk (UL κ N) p (secT y) * psum (cf (fun y => G y p)) R y) ^ 2 := by
  set g := psum (cf f) R with hg
  have hη : IsSmoothC (fun X => g (flat X)) := contDiff_psum (cf f) R
  have h2 := cosine_second_order_aux hκ hη
  have hcomp : (fun X => g (flat X)) ∘ unflat = g := rfl
  have e1 : ∀ X : Config N 1, gradDotC (fun X => g (flat X)) (fun X => g (flat X)) X =
      ∑ p, psum (cf (fun y => G y p)) R (flat X) ^ 2 := fun X => by
    have := gradDotC_unflat (fun X => g (flat X)) (flat X)
    rw [hcomp] at this
    refine this.trans (Finset.sum_congr rfl fun p _ => ?_)
    rw [Dk_psum_cf hcfG]
  have e2 : ∀ X : Config N 1, cosGen κ N (fun X => g (flat X)) X =
      psum (lapC f) R (flat X) -
        ∑ p, Dk (UL κ N) p (secT (flat X)) * psum (cf (fun y => G y p)) R (flat X) := fun X => by
    have := cosGen_unflat κ (fun X => g (flat X)) (flat X)
    rw [hcomp] at this
    refine this.trans ?_
    simp only [Lop]
    rw [Finset.sum_sub_distrib, lap_psum]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Dk_psum_cf hcfG]
  simp_rw [e1, e2] at h2
  have hm1 : AEStronglyMeasurable (fun y => ∑ p, psum (cf (fun y => G y p)) R y ^ 2) volume :=
    (continuous_finset_sum _ fun p _ => (continuous_psum _ R).pow 2).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun y => (psum (lapC f) R y -
      ∑ p, Dk (UL κ N) p (secT y) * psum (cf (fun y => G y p)) R y) ^ 2) volume :=
    ((memLp_psum _ R 2).sub (memLp_drift (κ := κ) (G := fun y p => psum (cf (fun y => G y p)) R y)
      fun j => memLp_psum _ R 2)).aestronglyMeasurable.pow 2
  rw [integral_flat (κ := κ) _ hm1, integral_flat (κ := κ) _ hm2] at h2
  have hsum : ∫ y, gsW κ N y * ∑ p, psum (cf (fun y => G y p)) R y ^ 2 =
      ∑ p, ∫ y, gsW κ N y * psum (cf (fun y => G y p)) R y ^ 2 := by
    rw [← integral_finset_sum _ fun p _ =>
      ((memLp_psum _ R 2).integrable_sq).bdd_mul (measurable_gsW κ).aestronglyMeasurable
        (Eventually.of_forall (gsW_norm_le hκ.le))]
    congr 1; funext y; rw [Finset.mul_sum]
  rw [← hsum]; exact h2

/-- Step 2 bound: `a(e^{-2κ} - κ/N) ≤ λ`. -/
theorem lam_ge_second_order {κ : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N) :
    aCos * (Real.exp (-2 * κ) - κ / N) ≤ (lamAll cosV (cosW κ) N).toReal := by
  set ρ := aCos * (Real.exp (-2 * κ) - κ / N) with hρ
  set L := (lamAll cosV (cosW κ) N).toReal with hL
  have hLt := lamAll_lt_top (κ := κ) hN
  have hLpos : 0 < L := by
    have h1 := lamAll_ge_exp hκ hN
    have h2 : 0 < ENNReal.ofReal (aCos * Real.exp (-κ * N / 2)) :=
      ENNReal.ofReal_pos.mpr (by unfold aCos; positivity)
    exact ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le h2 h1)) hLt.ne
  obtain ⟨f, G, hmin⟩ : ∃ f G, IsGapMin κ N f G := by
    obtain ⟨f, G, h⟩ := exists_minimizer_flat hκ hN; exact ⟨f, G, h⟩
  obtain ⟨hf2, hG2, hfG, hmean, hnorm, hE⟩ := hmin
  have hcfG : ∀ p k, cf (fun y => G y p) k = 2 * π * I * k p * cf f k := fun p k =>
    mFourierCoeff_grad hfG (hf2.integrable one_le_two) (fun j => (hG2 j).integrable one_le_two) k p
  obtain ⟨Lap, hLap2, hLapc⟩ := exists_lap hκ hN ⟨hf2, hG2, hfG, hmean, hnorm, hE⟩
  have hLfeq := integral_Lf_sq hκ hN ⟨hf2, hG2, hfG, hmean, hnorm, hE⟩ hLap2 hLapc
  have hpsL : ∀ R, psum (lapC f) R = psum (cf Lap) R := fun R => by
    congr 1; funext k; rw [hLapc]
  -- limits
  have hconv := tendsto_generator_psum (κ := κ) hN hG2 hLap2
  have hLR2 : ∀ R, MemLp (fun y => psum (cf Lap) R y -
      ∑ p, Dk (UL κ N) p (secT y) * psum (cf (fun y => G y p)) R y) 2 volume := fun R =>
    (memLp_psum _ R 2).sub (memLp_drift (κ := κ) (G := fun y p => psum (cf (fun y => G y p)) R y)
      fun j => memLp_psum _ R 2)
  have hlimL := tendsto_weighted_sq hκ.le hLR2
    (b := fun y => Lap y - ∑ p, Dk (UL κ N) p (secT y) * G y p) (hLap2.sub (memLp_drift hG2)) hconv
  rw [hLfeq] at hlimL
  have hlimG : Tendsto (fun R => ρ * ∑ p, ∫ y, gsW κ N y * psum (cf (fun y => G y p)) R y ^ 2)
      atTop (𝓝 (ρ * ∑ p, ∫ y, gsW κ N y * G y p ^ 2)) :=
    (tendsto_finset_sum Finset.univ fun p _ => tendsto_weighted_sq hκ.le
      (fun R => memLp_psum (cf (fun y => G y p)) R 2) (hG2 p) (tendsto_psum_sq (hG2 p))).const_mul ρ
  have hsumG : ∑ p, ∫ y, gsW κ N y * G y p ^ 2 = L := by
    rw [hL, ← hE, ← integral_finset_sum _ fun p _ => (hG2 p).integrable_sq.bdd_mul
      (measurable_gsW κ).aestronglyMeasurable (Eventually.of_forall (gsW_norm_le hκ.le))]
    congr 1; funext y; unfold sqNorm; rw [Finset.mul_sum]
  rw [hsumG] at hlimG
  have hineq : ∀ R, ρ * ∑ p, ∫ y, gsW κ N y * psum (cf (fun y => G y p)) R y ^ 2 ≤
      ∫ y, gsW κ N y * (psum (cf Lap) R y -
        ∑ p, Dk (UL κ N) p (secT y) * psum (cf (fun y => G y p)) R y) ^ 2 := fun R => by
    have := second_order_psum hκ hcfG R
    rwa [hpsL] at this
  have hfin := le_of_tendsto_of_tendsto' hlimG hlimL hineq
  have : ρ * L ≤ L * L := by nlinarith
  exact le_of_mul_le_mul_right this hLpos

/-- (3.25). -/
theorem cosine_labeled_poincare_aux {κ : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N) :
    ENNReal.ofReal (aCos * max (Real.exp (-κ * N / 2)) (Real.exp (-2 * κ) - κ / N)) ≤
      lamAll cosV (cosW κ) N := by
  have hLt := lamAll_lt_top (κ := κ) hN
  have h1 := lamAll_ge_exp hκ hN
  have h2 := lam_ge_second_order hκ hN
  have ha0 : 0 < aCos := by unfold aCos; positivity
  have h1' : aCos * Real.exp (-κ * N / 2) ≤ (lamAll cosV (cosW κ) N).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hLt.ne).mp h1
  rw [ENNReal.ofReal_le_iff_le_toReal hLt.ne]
  rcases le_total (Real.exp (-κ * N / 2)) (Real.exp (-2 * κ) - κ / N) with h | h
  · rw [max_eq_right h]; exact h2
  · rw [max_eq_left h]; exact h1'

end Cosine

theorem min_le_max_cos {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) :
    min (Real.exp (-2 * κ) / 2) (Real.exp (-κ ^ 2 * Real.exp (2 * κ))) ≤
      max (Real.exp (-κ * N / 2)) (Real.exp (-2 * κ) - κ / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rcases le_or_gt (2 * κ * Real.exp (2 * κ)) N with h | h
  · refine (min_le_left _ _).trans (le_trans ?_ (le_max_right _ _))
    have he : Real.exp (-2 * κ) * Real.exp (2 * κ) = 1 := by
      rw [← Real.exp_add]; simp
    have : κ / N ≤ Real.exp (-2 * κ) / 2 := by
      rw [div_le_div_iff₀ hN' (by norm_num)]
      have hpos : 0 < Real.exp (-2 * κ) := Real.exp_pos _
      nlinarith
    linarith
  · refine (min_le_right _ _).trans (le_trans ?_ (le_max_left _ _))
    refine Real.exp_le_exp.mpr ?_
    have : κ * N < κ * (2 * κ * Real.exp (2 * κ)) := mul_lt_mul_of_pos_left h hκ
    nlinarith

/-- (3.27) and `inf_N r^all_{N,κ} > 0`. -/
theorem cosine_uniform_all_aux {κ : ℝ} (hκ : 0 < κ) :
    ENNReal.ofReal (aCos * min (Real.exp (-2 * κ) / 2) (Real.exp (-κ ^ 2 * Real.exp (2 * κ))))
        ≤ ⨅ N ∈ {N : ℕ | 1 ≤ N}, lamAll cosV (cosW κ) N ∧
      0 < aCos * min (Real.exp (-2 * κ) / 2) (Real.exp (-κ ^ 2 * Real.exp (2 * κ))) ∧
      0 < ⨅ N ∈ {N : ℕ | 1 ≤ N}, rAll cosV (cosW κ) N := by
  have ha0 : 0 < aCos := by unfold aCos; positivity
  set c := aCos * min (Real.exp (-2 * κ) / 2) (Real.exp (-κ ^ 2 * Real.exp (2 * κ))) with hc
  have hc0 : 0 < c := mul_pos ha0 (lt_min (by positivity) (Real.exp_pos _))
  have hlam : ∀ N, 1 ≤ N → ENNReal.ofReal c ≤ lamAll cosV (cosW κ) N := fun N hN =>
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (min_le_max_cos hκ hN) ha0.le)).trans
      (cosine_labeled_poincare_aux hκ hN)
  refine ⟨le_iInf₂ fun N hN => hlam N hN, hc0, ?_⟩
  set b := (2 * κ + 8) * aCos with hb
  have hb0 : 0 < b := by positivity
  set X := 2 * aCos * c / (4 * c + b) with hX
  have hX0 : 0 < X := by positivity
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hX0) (le_iInf₂ fun N (hN : 1 ≤ N) => ?_)
  refine le_trans ?_ (rAll_ge_of_lamAll hκ hN)
  have hLt := lamAll_lt_top (κ := κ) hN
  set l := (lamAll cosV (cosW κ) N).toReal
  have hLl : lamAll cosV (cosW κ) N = ENNReal.ofReal l := (ENNReal.ofReal_toReal hLt.ne).symm
  have hcl : c ≤ l := (ENNReal.ofReal_le_iff_le_toReal hLt.ne).mp (hlam N hN)
  have hl0 : 0 ≤ l := hc0.le.trans hcl
  rw [hLl]
  have hXe : 2 * ENNReal.ofReal aCos * ENNReal.ofReal l /
      (4 * ENNReal.ofReal l + ENNReal.ofReal ((2 * κ + 8) * aCos)) =
      ENNReal.ofReal (2 * aCos * l / (4 * l + (2 * κ + 8) * aCos)) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]; simp
    · rw [ENNReal.ofReal_add (by positivity) hb0.le, ENNReal.ofReal_mul (p := 4) (by norm_num)]
      simp [hb]
  rw [hXe]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hX, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hcl (by positivity : (0 : ℝ) ≤ 2 * aCos * b)]

end SharpLSI
