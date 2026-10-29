import SharpSymmetricLSI.Paper.LemmaA2_23

/-!
# R25 Lemma A.2, part 24: double eigen-series and their truncations

For coefficients `|A_ij| ≤ B gᵢ gⱼ` with `∑ gᵢ (Mᵢ + M'ᵢ) < ∞`, the double series
`∑ᵢ (∑ⱼ A_ij eCⱼ(y)) eCᵢ(x)` and its square truncations differ by at most
`B ∑_{(i,j) ∉ N²} gᵢ Mᵢ gⱼ Mⱼ`, and similarly for the partial derivatives
(`dsum_sub_trunc_le`, `dpart_dsum_sub_trunc_le`); these tails tend to `0`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

theorem abs_tsum_le_of_le {f b : ℕ → ℝ} (hb : Summable b) (h : ∀ j, |f j| ≤ b j) :
    |∑' j, f j| ≤ ∑' j, b j := by
  have hf : Summable f := Summable.of_norm_bounded hb fun j => by rw [Real.norm_eq_abs]; exact h j
  have h1 : ‖∑' j, f j‖ ≤ ∑' j, ‖f j‖ := norm_tsum_le_tsum_norm hf.norm
  simp only [Real.norm_eq_abs] at h1
  exact h1.trans (hf.abs.tsum_le_tsum h hb)

/-- A series has Lipschitz constant `∑ |bᵢ| M'ᵢ` on lifts. -/
theorem series_lift_bound {eC : ℕ → Torus d → ℝ} (heC1 : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT))
    {M M' : ℕ → ℝ} (hM : ∀ j x, |eC j x| ≤ M j) (hM' : ∀ j x, ‖fderiv ℝ (eC j ∘ liftT) x‖ ≤ M' j)
    {b : ℕ → ℝ} (hbM : Summable fun j => |b j| * M j) (hbM' : Summable fun j => |b j| * M' j)
    (x y : Fin d → ℝ) :
    series b eC (liftT x) - series b eC (liftT y) ≤ (∑' j, |b j| * M' j) * dE x y := by
  simp only [series]
  rw [← (summable_series_at hM hbM _).tsum_sub (summable_series_at hM hbM _)]
  have hterm : ∀ j, |b j * eC j (liftT x) - b j * eC j (liftT y)| ≤ |b j| * M' j * dE x y := by
    intro j
    rw [← mul_sub, abs_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := univ)
      (f := eC j ∘ liftT) (fun z _ => ((heC1 j).differentiable one_ne_zero z))
      (fun z _ => hM' j z) convex_univ (mem_univ y) (mem_univ x)
    rw [Real.norm_eq_abs] at hmv
    refine hmv.trans (mul_le_mul_of_nonneg_left ?_ ((norm_nonneg _).trans (hM' j 0)))
    rw [← dist_eq_norm]; exact dist_le_dE x y
  have hs : Summable fun j => |b j| * M' j * dE x y := hbM'.mul_right _
  exact (le_abs_self _).trans ((abs_tsum_le_of_le hs hterm).trans (le_of_eq tsum_mul_right))

/-- The tail weight outside the square `N × N`. -/
noncomputable def tailW (u v : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑' i, u i * ∑' j, (if i < N ∧ j < N then 0 else v j)

theorem tendsto_tailW {u v : ℕ → ℝ} (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ j, 0 ≤ v j)
    (hu : Summable u) (hv : Summable v) : Tendsto (tailW u v) atTop (𝓝 0) := by
  have hin : ∀ i, Tendsto (fun N => ∑' j, (if i < N ∧ j < N then 0 else v j)) atTop (𝓝 0) := by
    intro i
    have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (bound := v) hv
      (f := fun N j => if i < N ∧ j < N then 0 else v j) (g := fun _ => (0 : ℝ))
      (fun j => tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨max i j + 1, fun N hN => by
        show (0 : ℝ) = if i < N ∧ j < N then 0 else v j
        rw [if_pos ⟨by omega, by omega⟩]⟩))
      (Eventually.of_forall fun N j => by
        split_ifs <;> simp [abs_of_nonneg (hv0 j), hv0 j])
    simpa using this
  have hle : ∀ i N, ∑' j, (if i < N ∧ j < N then 0 else v j) ≤ ∑' j, v j := fun i N =>
    Summable.tsum_le_tsum (fun j => by split_ifs <;> simp [hv0 j])
      (hv.of_nonneg_of_le (fun j => by split_ifs <;> simp [hv0 j])
        (fun j => by split_ifs <;> simp [hv0 j])) hv
  have hnn : ∀ i N, 0 ≤ ∑' j, (if i < N ∧ j < N then 0 else v j) := fun i N =>
    tsum_nonneg fun j => by split_ifs <;> simp [hv0 j]
  have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (bound := fun i => u i * ∑' j, v j)
    (hu.mul_right _) (f := fun N i => u i * ∑' j, (if i < N ∧ j < N then 0 else v j))
    (g := fun _ => (0 : ℝ)) (fun i => by simpa using (hin i).const_mul (u i))
    (Eventually.of_forall fun N i => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hu0 i) (hnn i N))]
      exact mul_le_mul_of_nonneg_left (hle i N) (hu0 i))
  unfold tailW; simpa using this

theorem tsum_split_lt {f : ℕ → ℝ} (hf : Summable f) (N : ℕ) :
    ∑' j, f j = ∑ j ∈ Finset.range N, f j + ∑' j, (if j < N then 0 else f j) := by
  have h1 : Summable fun j => if j < N then f j else 0 :=
    Summable.of_norm_bounded hf.abs fun j => by split_ifs <;> simp
  have h2 : Summable fun j => if j < N then 0 else f j :=
    Summable.of_norm_bounded hf.abs fun j => by split_ifs <;> simp
  have e1 : ∑' j, (if j < N then f j else 0) = ∑ j ∈ Finset.range N, f j := by
    rw [tsum_eq_sum (s := Finset.range N) fun j hj => by
      simp only [Finset.mem_range] at hj; simp [hj]]
    exact Finset.sum_congr rfl fun j hj => by simp [Finset.mem_range.mp hj]
  rw [← e1, ← h1.tsum_add h2]
  exact tsum_congr fun j => by split_ifs <;> simp

/-- The square truncation of `K_t`. -/
noncomputable def KtN (P : Measure (Torus d)) (e eC : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (t : ℝ)
    (Kf : Torus d → Torus d → ℝ) (N : ℕ) (x y : Torus d) : ℝ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    Real.exp (-t * lam i) * Real.exp (-t * lam j) *
      (∫ y', (∫ x', Kf x' y' * e i x' ∂P) * e j y' ∂P) * eC i x * eC j y

section trunc

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

theorem abs_T_le (i j : ℕ) :
    |∫ y', (∫ x', Kf x' y' * e i x' ∂densMeasure ρ) * e j y' ∂densMeasure ρ| ≤ BK := by
  have hc := continuous_slice_coeff hρ hρc hb hKc i
  exact abs_coeff_le_sup hρ hb hc.aestronglyMeasurable (fun y => abs_coeff_le_sup hρ hb
    (hKc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable (fun x => hBK x y) i) j

/-- **`K_t` as a double series.** -/
theorem Kt_series {t : ℝ} (ht : 0 < t) (x y : Torus d) :
    Kt (densMeasure ρ) e eC lam t Kf x y =
      ∑' i, (Real.exp (-t * lam i) * ∑' j, Real.exp (-t * lam j) *
        (∫ y', (∫ x', Kf x' y' * e i x' ∂densMeasure ρ) * e j y' ∂densMeasure ρ) * eC j y) *
          eC i x := by
  haveI := hρ.isProb
  set P := densMeasure ρ
  have hM0 : ∀ j, 0 ≤ M j := fun j => (abs_nonneg _).trans (hM j (Classical.arbitrary _))
  have hBK0 : 0 ≤ BK := (abs_nonneg _).trans (hBK (Classical.arbitrary _) (Classical.arbitrary _))
  simp only [Kt, semi, series]
  refine tsum_congr fun i => ?_
  congr 2
  -- `∫ M_t(x',y) e_i(x') = ∑ⱼ e^{-tλⱼ} T_ij eCⱼ(y)`
  have hei : Integrable (e i) P := ((hb.memH1 i).2.1).integrable one_le_two
  set k : ℕ → Torus d → ℝ := fun j x' => ∫ y', Kf x' y' * e j y' ∂P
  have hkc : ∀ j, Continuous (k j) := fun j => by
    have := continuous_slice_coeff hρ hρc hb (F := fun a b => Kf b a)
      (hKc.comp (continuous_snd.prodMk continuous_fst)) j
    exact this
  have hkb : ∀ j x', |k j x'| ≤ BK := fun j x' => abs_coeff_le_sup hρ hb
    (hKc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable (fun y' => hBK x' y') j
  have hMt : ∀ x', Mt P e eC lam t Kf x' y = ∑' j, Real.exp (-t * lam j) * k j x' * eC j y := by
    intro x'; simp only [Mt, semi, series, k]
  simp_rw [hMt]
  have hint : ∀ j, Integrable (fun x' => Real.exp (-t * lam j) * k j x' * eC j y * e i x') P :=
    fun j => hei.bdd_mul (c := Real.exp (-t * lam j) * BK * M j)
      (((continuous_const.mul (hkc j)).mul continuous_const).aestronglyMeasurable)
      (Eventually.of_forall fun x' => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hkb j x') (Real.exp_pos _).le) (hM j y)
          (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le hBK0))
  have hsum : Summable fun j => ∫ x', ‖Real.exp (-t * lam j) * k j x' * eC j y * e i x'‖ ∂P := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun _ => norm_nonneg _)
      (fun j => ?_) (((hS t ht).1).mul_left BK)
    calc ∫ x', ‖Real.exp (-t * lam j) * k j x' * eC j y * e i x'‖ ∂P
        ≤ ∫ x', Real.exp (-t * lam j) * BK * M j * |e i x'| ∂P := by
          refine integral_mono (hint j).norm (hei.abs.const_mul _) fun x' => ?_
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hkb j x') (Real.exp_pos _).le) (hM j y)
            (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le hBK0)
      _ = Real.exp (-t * lam j) * BK * M j * ∫ x', |e i x'| ∂P := integral_const_mul _ _
      _ ≤ BK * (Real.exp (-t * lam j) * M j) := by
          have := integral_abs_e_le' hρ hb i
          have h0 : 0 ≤ Real.exp (-t * lam j) * BK * M j :=
            mul_nonneg (mul_nonneg (Real.exp_pos _).le hBK0) (hM0 j)
          nlinarith
  rw [show (fun x' => (∑' j, Real.exp (-t * lam j) * k j x' * eC j y) * e i x') =
      fun x' => ∑' j, Real.exp (-t * lam j) * k j x' * eC j y * e i x' from
    funext fun x' => (tsum_mul_right).symm, ← integral_tsum_of_summable_integral_norm hint hsum]
  refine tsum_congr fun j => ?_
  rw [show (fun x' => Real.exp (-t * lam j) * k j x' * eC j y * e i x') =
      fun x' => (Real.exp (-t * lam j) * eC j y) * (k j x' * e i x') from
    funext fun x' => by ring, integral_const_mul]
  have hf := fubini_coeff hρ hb hKc i j
  simp only [k] at hf ⊢
  rw [← hf]; ring

/-- **Truncation estimates for `K_t`.** -/
theorem Kt_sub_KtN {t : ℝ} (ht : 0 < t) (N : ℕ) (y : Torus d) :
    ∃ β : ℕ → ℝ, (∀ x, Kt (densMeasure ρ) e eC lam t Kf x y - KtN (densMeasure ρ) e eC lam t Kf N x y =
      series β eC x) ∧
    ∀ i, |β i| ≤ BK * (Real.exp (-t * lam i) *
      ∑' j, (if i < N ∧ j < N then 0 else Real.exp (-t * lam j) * M j)) := by
  set P := densMeasure ρ
  set g : ℕ → ℝ := fun j => Real.exp (-t * lam j)
  set T : ℕ → ℕ → ℝ := fun i j => ∫ y', (∫ x', Kf x' y' * e i x' ∂P) * e j y' ∂P
  have hM0 : ∀ j, 0 ≤ M j := fun j => (abs_nonneg _).trans (hM j (Classical.arbitrary _))
  have hBK0 : 0 ≤ BK := (abs_nonneg _).trans (hBK (Classical.arbitrary _) (Classical.arbitrary _))
  have hT : ∀ i j, |T i j| ≤ BK := fun i j => abs_T_le hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc
    hBK hLK0 hL1 hL2 i j
  have hgM := (hS t ht).1
  set f : ℕ → ℕ → ℝ := fun i j => g j * T i j * eC j y
  have hfb : ∀ i j, |f i j| ≤ BK * (g j * M j) := fun i j => by
    simp only [f]; rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc g j * |T i j| * |eC j y| ≤ g j * BK * M j :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hT i j) (Real.exp_pos _).le) (hM j y)
            (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le hBK0)
      _ = BK * (g j * M j) := by ring
  have hfs : ∀ i, Summable (f i) := fun i =>
    Summable.of_norm_bounded (hgM.mul_left BK) fun j => by rw [Real.norm_eq_abs]; exact hfb i j
  set β : ℕ → ℝ := fun i => g i * ∑' j, f i j -
    (if i < N then ∑ j ∈ Finset.range N, g i * g j * T i j * eC j y else 0)
  refine ⟨β, fun x => ?_, fun i => ?_⟩
  · rw [Kt_series hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2 ht]
    have hKN : KtN P e eC lam t Kf N x y = ∑' i,
        (if i < N then ∑ j ∈ Finset.range N, g i * g j * T i j * eC j y else 0) * eC i x := by
      rw [tsum_eq_sum (s := Finset.range N) fun i hi => by
        simp only [Finset.mem_range] at hi; simp [hi]]
      simp only [KtN]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [if_pos (Finset.mem_range.mp hi), Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hKN, series]
    have hA : Summable fun i => (g i * ∑' j, f i j) * eC i x := by
      refine Summable.of_norm_bounded ((hgM.mul_left (BK * ∑' j, g j * M j))) fun i => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 : |∑' j, f i j| ≤ BK * ∑' j, g j * M j := by
        rw [← tsum_mul_left]; exact abs_tsum_le_of_le (hgM.mul_left BK) (hfb i)
      calc g i * |∑' j, f i j| * |eC i x| ≤ g i * (BK * ∑' j, g j * M j) * M i :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le) (hM i x) (abs_nonneg _)
              (mul_nonneg (Real.exp_pos _).le (mul_nonneg hBK0 (tsum_nonneg fun j =>
                mul_nonneg (Real.exp_pos _).le (hM0 j))))
        _ = (BK * ∑' j, g j * M j) * (g i * M i) := by ring
    have hB : Summable fun i =>
        (if i < N then ∑ j ∈ Finset.range N, g i * g j * T i j * eC j y else 0) * eC i x :=
      summable_of_ne_finset_zero (s := Finset.range N) fun i hi => by
        simp only [Finset.mem_range] at hi; simp [hi]
    rw [← hA.tsum_sub hB]
    exact tsum_congr fun i => by simp only [β, f]; ring
  · have hsplit := tsum_split_lt (hfs i) N
    by_cases hi : i < N
    · have hβ : β i = g i * ∑' j, (if j < N then 0 else f i j) := by
        simp only [β, if_pos hi]
        rw [hsplit, mul_add, Finset.mul_sum]
        have : ∑ j ∈ Finset.range N, g i * f i j =
            ∑ j ∈ Finset.range N, g i * g j * T i j * eC j y :=
          Finset.sum_congr rfl fun j _ => by simp only [f]; ring
        rw [this]; ring
      rw [hβ, abs_mul, abs_of_pos (Real.exp_pos _), mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      rw [← tsum_mul_left]
      refine abs_tsum_le_of_le ((hgM.mul_left BK).of_nonneg_of_le (fun j => by
        split_ifs <;> simp [mul_nonneg hBK0 (mul_nonneg (Real.exp_pos _).le (hM0 j))])
        (fun j => by split_ifs <;> simp [mul_nonneg hBK0 (mul_nonneg (Real.exp_pos _).le (hM0 j))]))
        fun j => ?_
      by_cases hj : j < N
      · simp [hi, hj]
      · simp only [hj, if_false, hi, true_and]; exact hfb i j
    · have hβ : β i = g i * ∑' j, f i j := by simp only [β, if_neg hi, sub_zero]
      rw [hβ, abs_mul, abs_of_pos (Real.exp_pos _), mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      rw [← tsum_mul_left]
      refine abs_tsum_le_of_le ((hgM.mul_left BK).congr fun j => by simp [hi]) fun j => ?_
      simp only [hi, false_and, if_false]; exact hfb i j

theorem Kt_KtN_close {t : ℝ} (ht : 0 < t) (N : ℕ) :
    (∀ x y, |Kt (densMeasure ρ) e eC lam t Kf x y - KtN (densMeasure ρ) e eC lam t Kf N x y| ≤
      BK * tailW (fun i => Real.exp (-t * lam i) * M i) (fun j => Real.exp (-t * lam j) * M j) N) ∧
    (∀ y a b, (Kt (densMeasure ρ) e eC lam t Kf (liftT a) y -
        KtN (densMeasure ρ) e eC lam t Kf N (liftT a) y) -
      (Kt (densMeasure ρ) e eC lam t Kf (liftT b) y -
        KtN (densMeasure ρ) e eC lam t Kf N (liftT b) y) ≤
      BK * tailW (fun i => Real.exp (-t * lam i) * M' i) (fun j => Real.exp (-t * lam j) * M j) N *
        dE a b) := by
  set g : ℕ → ℝ := fun j => Real.exp (-t * lam j)
  have hM0 : ∀ j, 0 ≤ M j := fun j => (abs_nonneg _).trans (hM j (Classical.arbitrary _))
  have hM0' : ∀ j, 0 ≤ M' j := fun j => (norm_nonneg _).trans (hM' j 0)
  have hBK0 : 0 ≤ BK := (abs_nonneg _).trans (hBK (Classical.arbitrary _) (Classical.arbitrary _))
  set r : ℕ → ℝ := fun i => ∑' j, (if i < N ∧ j < N then 0 else g j * M j)
  have hr0 : ∀ i, 0 ≤ r i := fun i => tsum_nonneg fun j => by
    split_ifs <;> nlinarith [mul_nonneg (Real.exp_pos (-t * lam j)).le (hM0 j)]
  have hrle : ∀ i, r i ≤ ∑' j, g j * M j := fun i =>
    Summable.tsum_le_tsum (fun j => by split_ifs <;> nlinarith [mul_nonneg (Real.exp_pos (-t * lam j)).le (hM0 j)])
      (((hS t ht).1).of_nonneg_of_le (fun j => by
        split_ifs <;> nlinarith [mul_nonneg (Real.exp_pos (-t * lam j)).le (hM0 j)])
        (fun j => by split_ifs <;> nlinarith [mul_nonneg (Real.exp_pos (-t * lam j)).le (hM0 j)])) (hS t ht).1
  have hsumW : ∀ {w : ℕ → ℝ}, (∀ i, 0 ≤ w i) → Summable (fun i => g i * w i) →
      Summable fun i => g i * w i * r i := fun {w} hw hs =>
    (hs.mul_right (∑' j, g j * M j)).of_nonneg_of_le
      (fun i => mul_nonneg (mul_nonneg (Real.exp_pos _).le (hw i)) (hr0 i))
      (fun i => mul_le_mul_of_nonneg_left (hrle i) (mul_nonneg (Real.exp_pos _).le (hw i)))
  constructor
  · intro x y
    obtain ⟨β, hβ, hβb⟩ := Kt_sub_KtN hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2
      ht N y
    rw [hβ x, series]
    have hb' : ∀ i, |β i * eC i x| ≤ BK * (g i * M i * r i) := fun i => by
      rw [abs_mul]
      calc |β i| * |eC i x| ≤ BK * (g i * r i) * M i :=
            mul_le_mul (hβb i) (hM i x) (abs_nonneg _)
              (mul_nonneg hBK0 (mul_nonneg (Real.exp_pos _).le (hr0 i)))
        _ = BK * (g i * M i * r i) := by ring
    refine (abs_tsum_le_of_le ((hsumW hM0 (hS t ht).1).mul_left BK) hb').trans (le_of_eq ?_)
    rw [tsum_mul_left]; simp only [tailW]; congr 1
    try exact tsum_congr fun i => by ring
  · intro y a b
    obtain ⟨β, hβ, hβb⟩ := Kt_sub_KtN hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2
      ht N y
    rw [hβ, hβ]
    have hb1 : ∀ i, |β i| * M i ≤ BK * (g i * M i * r i) := fun i => by
      calc |β i| * M i ≤ BK * (g i * r i) * M i := mul_le_mul_of_nonneg_right (hβb i) (hM0 i)
        _ = BK * (g i * M i * r i) := by ring
    have hb2 : ∀ i, |β i| * M' i ≤ BK * (g i * M' i * r i) := fun i => by
      calc |β i| * M' i ≤ BK * (g i * r i) * M' i := mul_le_mul_of_nonneg_right (hβb i) (hM0' i)
        _ = BK * (g i * M' i * r i) := by ring
    have hs1 : Summable fun i => |β i| * M i := ((hsumW hM0 (hS t ht).1).mul_left BK).of_nonneg_of_le
      (fun i => mul_nonneg (abs_nonneg _) (hM0 i)) hb1
    have hs2 : Summable fun i => |β i| * M' i :=
      ((hsumW hM0' (hS t ht).2).mul_left BK).of_nonneg_of_le
        (fun i => mul_nonneg (abs_nonneg _) (hM0' i)) hb2
    refine (series_lift_bound heC1 hM hM' hs1 hs2 a b).trans
      (mul_le_mul_of_nonneg_right ?_ (dE_nonneg a b))
    refine (Summable.tsum_le_tsum hb2 hs2 ((hsumW hM0' (hS t ht).2).mul_left BK)).trans
      (le_of_eq ?_)
    rw [tsum_mul_left]; simp only [tailW]; congr 1
    try exact tsum_congr fun i => by ring

theorem T_symm_A2 (hsymm : ∀ x y, Kf x y = Kf y x) (i j : ℕ) :
    ∫ y', (∫ x', Kf x' y' * e i x' ∂densMeasure ρ) * e j y' ∂densMeasure ρ =
      ∫ y', (∫ x', Kf x' y' * e j x' ∂densMeasure ρ) * e i y' ∂densMeasure ρ := by
  have h := transpose_coeff hρ hρc hb hKc i j
  have e : (fun y => (∫ x, Kf y x * e i x ∂densMeasure ρ) * e j y) =
      fun y => (∫ x, Kf x y * e i x ∂densMeasure ρ) * e j y :=
    funext fun y => by congr 2; funext x; rw [hsymm]
  rw [e] at h; exact h

theorem KtN_symm (hsymm : ∀ x y, Kf x y = Kf y x) {t : ℝ} (N : ℕ) (x y : Torus d) :
    KtN (densMeasure ρ) e eC lam t Kf N x y = KtN (densMeasure ρ) e eC lam t Kf N y x := by
  simp only [KtN]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [T_symm_A2 hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2 hsymm j i]
  ring

theorem Kt_symm (hsymm : ∀ x y, Kf x y = Kf y x) {t : ℝ} (ht : 0 < t) (x y : Torus d) :
    Kt (densMeasure ρ) e eC lam t Kf x y = Kt (densMeasure ρ) e eC lam t Kf y x := by
  set P := densMeasure ρ
  set g : ℕ → ℝ := fun j => Real.exp (-t * lam j)
  set T : ℕ → ℕ → ℝ := fun i j => ∫ y', (∫ x', Kf x' y' * e i x' ∂P) * e j y' ∂P
  have hM0 : ∀ j, 0 ≤ M j := fun j => (abs_nonneg _).trans (hM j (Classical.arbitrary _))
  have hBK0 : 0 ≤ BK := (abs_nonneg _).trans (hBK (Classical.arbitrary _) (Classical.arbitrary _))
  have hT : ∀ i j, |T i j| ≤ BK := fun i j => abs_T_le hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc
    hBK hLK0 hL1 hL2 i j
  have hTs : ∀ i j, T i j = T j i := fun i j =>
    T_symm_A2 hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2 hsymm i j
  have hgM := (hS t ht).1
  set u : ℕ → ℝ := fun j => g j * M j
  have hu0 : ∀ j, 0 ≤ u j := fun j => mul_nonneg (Real.exp_pos _).le (hM0 j)
  set F : ℕ → ℕ → Torus d → Torus d → ℝ := fun i j a b => g i * g j * T i j * eC j b * eC i a
  have hFb : ∀ i j a b, |F i j a b| ≤ BK * (u i * u j) := fun i j a b => by
    simp only [F, u]
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos (-t * lam i)),
      abs_of_pos (Real.exp_pos (-t * lam j))]
    calc g i * g j * |T i j| * |eC j b| * |eC i a| ≤ g i * g j * BK * M j * M i := by
          have hgg : 0 ≤ g i * g j := mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
          have h1 : g i * g j * |T i j| ≤ g i * g j * BK := mul_le_mul_of_nonneg_left (hT i j) hgg
          have h2 : g i * g j * |T i j| * |eC j b| ≤ g i * g j * BK * M j :=
            mul_le_mul h1 (hM j b) (abs_nonneg _) (mul_nonneg hgg hBK0)
          exact mul_le_mul h2 (hM i a) (abs_nonneg _) (mul_nonneg (mul_nonneg hgg hBK0) (hM0 j))
      _ = BK * (g i * M i * (g j * M j)) := by ring
  have hprod : Summable fun p : ℕ × ℕ => u p.1 * u p.2 :=
    hgM.mul_of_nonneg hgM hu0 hu0
  have hsF : ∀ a b, Summable (Function.uncurry fun i j => F i j a b) := fun a b =>
    Summable.of_norm_bounded (hprod.mul_left BK) fun p => by
      rw [Real.norm_eq_abs]; exact hFb p.1 p.2 a b
  have hrep : ∀ a b, Kt P e eC lam t Kf a b = ∑' i, ∑' j, F i j a b := fun a b => by
    rw [Kt_series hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2 ht]
    refine tsum_congr fun i => ?_
    rw [← tsum_mul_left, ← tsum_mul_right]
    exact tsum_congr fun j => by simp only [F]; ring
  rw [hrep, hrep]
  rw [← (hsF x y).tsum_comm]
  refine tsum_congr fun j => tsum_congr fun i => ?_
  simp only [F]; rw [hTs i j]; ring

end trunc

end SharpLSI
