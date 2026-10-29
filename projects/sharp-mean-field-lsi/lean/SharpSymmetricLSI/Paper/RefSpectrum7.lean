import SharpSymmetricLSI.Paper.RefSpectrum6

/-!
# R23 (6.1), part 7: positivity and the Weyl lower bound, for every reference eigenbasis

* `refLam_zero`, `refLam_nonneg`, `refLam_pos`: `λ₀ = 0`, `λⱼ ≥ 0`, and `λⱼ > 0` for `j ≥ 1` (if `λ₁ = 0`
  then `∇e₁ = 0`, so `e₁` is constant by the Poincaré inequality, and `e₁ ⊥ e₀ = 1` forces `e₁ = 0`).
* `weyl_step`: if `2(2M+1)^d < j+1`, some nonzero `f = ∑_{i≤j} aᵢeᵢ` has `f̂ = 0` on `[-M,M]^d`, so
  `((M+1)² - 1)∫f² dm ≤ ∫|∇f|² dm ≤ c⁻¹ λⱼ ∫f² dP ≤ (C/c) λⱼ ∫f² dm`.
* `weyl`: `λⱼ ≥ c₀ j^{2/d}` for `j ≥ 1`.
-/

open MeasureTheory Filter Topology Complex
open scoped ENNReal Real
open UnitAddTorus

namespace SharpLSI

variable {d : ℕ} {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (hb : IsRefEigenbasis (densMeasure ρ) e lam)
include hρ hb

theorem refBasis_eig (j : ℕ) {φ : Torus d → ℝ} (hφ : MemH1 (densMeasure ρ) φ) :
    dirB (densMeasure ρ) (e j) φ = lam j * ∫ x, e j x * φ x ∂densMeasure ρ :=
  hb.eigen j φ hφ

theorem refLam_eq_dirE (j : ℕ) : lam j = dirE (densMeasure ρ) (e j) := by
  have h := refBasis_eig hρ hb j (hb.memH1 j)
  rw [hb.orthonormal j j, if_pos rfl, mul_one] at h
  rw [← h, dirE_eq_dirB hρ]

theorem refLam_nonneg (j : ℕ) : 0 ≤ lam j := by
  rw [refLam_eq_dirE hρ hb]; exact dirE_nonneg hρ _

theorem refLam_zero : lam 0 = 0 := by
  rw [refLam_eq_dirE hρ hb, hb.zero, dirE_one hρ]

theorem refLam_pos (hd : 1 ≤ d) {j : ℕ} (hj : 1 ≤ j) : 0 < lam j := by
  set P := densMeasure ρ
  haveI := hρ.isProb
  refine lt_of_lt_of_le ?_ (hb.mono hj)
  rcases (refLam_nonneg hρ hb 1).eq_or_lt with h0 | h
  swap; · exact h
  exfalso
  have hH := hb.memH1 1
  have hE : dirE P (e 1) = 0 := by rw [← refLam_eq_dirE hρ hb, ← h0]
  -- all partial derivatives vanish in `L²(m)`
  have hgP := fun k => gradP hρ hH k
  have hgv : ∀ k, MemLp (fun y => weakGrad (e 1) y k) 2 volume := fun k =>
    (hgP k).of_measure_le_smul ENNReal.ofReal_ne_top hρ.haar_le_smul
  have hk : ∀ k, ∫ y, weakGrad (e 1) y k ^ 2 ∂P = 0 := by
    have hsum : ∑ k, ∫ y, weakGrad (e 1) y k ^ 2 ∂P = 0 := by
      rw [← integral_finsetSum _ fun k _ => (hgP k).integrable_sq]; exact hE
    exact fun k => (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
      integral_nonneg fun _ => sq_nonneg _).mp hsum k (Finset.mem_univ k)
  have hkv : ∀ k, ∫ y, weakGrad (e 1) y k ^ 2 = 0 := by
    intro k
    have hc0 : 0 ≤ 1 / c := by have := hρ.pos; positivity
    have := integral_le_smul_of_le hc0 hρ.haar_le_smul (fun y => sq_nonneg (weakGrad (e 1) y k))
      (hgP k).integrable_sq
    rw [hk k, mul_zero] at this
    exact le_antisymm this (integral_nonneg fun _ => sq_nonneg _)
  have huv : MemLp (e 1) 2 volume := hH.2.1.of_measure_le_smul ENNReal.ofReal_ne_top
    hρ.haar_le_smul
  have hpoinc := poincare_torus (isWeakGrad_weakGrad hH.1) huv hgv
  simp only [hkv, Finset.sum_const_zero] at hpoinc
  have h4 : (0 : ℝ) < 4 * π ^ 2 := by positivity
  have hvar : ProbabilityTheory.variance (e 1) volume = 0 := by
    refine le_antisymm ?_ (ProbabilityTheory.variance_nonneg _ _)
    have : 4 * π ^ 2 * ProbabilityTheory.variance (e 1) volume ≤ 4 * π ^ 2 * 0 := by
      rw [mul_zero]; exact hpoinc
    exact le_of_mul_le_mul_left this h4
  rw [ProbabilityTheory.variance_eq_integral huv.aestronglyMeasurable.aemeasurable] at hvar
  set m₀ := ∫ y, e 1 y
  have hconst : e 1 =ᵐ[volume] fun _ => m₀ := by
    have := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg (e 1 y - m₀))
      (huv.sub (memLp_const m₀)).integrable_sq).mp hvar
    filter_upwards [this] with y hy
    simpa [sub_eq_zero] using hy
  have hconstP : e 1 =ᵐ[P] fun _ => m₀ := hρ.ac.ae_le hconst
  have h10 : ∫ x, e 1 x ∂P = 0 := by
    have := hb.orthonormal 1 0
    rw [if_neg one_ne_zero, hb.zero] at this
    simpa using this
  have hm0 : m₀ = 0 := by
    rw [integral_congr_ae hconstP] at h10
    simpa using h10
  have h11 := hb.orthonormal 1 1
  rw [if_pos rfl] at h11
  have : ∫ x, e 1 x * e 1 x ∂P = 0 := by
    rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (hconstP.mono fun y hy => by simp [hy, hm0])]
    simp
  linarith

omit hb in
theorem dirB_finsum_left {κ : Type*} (s : Finset κ) (u : κ → Torus d → ℝ)
    (hu : ∀ i ∈ s, MemH1 (densMeasure ρ) (u i)) (a : κ → ℝ) {w : Torus d → ℝ}
    (hw : MemH1 (densMeasure ρ) w) :
    dirB (densMeasure ρ) (fun x => ∑ i ∈ s, a i * u i x) w =
      ∑ i ∈ s, a i * dirB (densMeasure ρ) (u i) w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := dirB_one hρ w
    unfold dirB at this ⊢
    have hw0 : weakGrad (fun _ : Torus d => (0 : ℝ)) =ᵐ[volume] 0 :=
      weakGrad_ae_unique (isWeakGrad_weakGrad ⟨0, by simpa using isWeakGrad_const (ι := Fin d) 0⟩)
        (by simpa using isWeakGrad_const (ι := Fin d) 0)
    have hw0P : weakGrad (fun _ : Torus d => (0 : ℝ)) =ᵐ[densMeasure ρ] 0 := hρ.ac.ae_le hw0
    rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (hw0P.mono fun x hx => by simp [hx])]
    simp
  | insert b s hbs ih =>
    have h1 := memH1_finsum hρ s u (fun i hi => hu i (Finset.mem_insert_of_mem hi)) a
    have hub := hu b (Finset.mem_insert_self b s)
    have e : (fun x => ∑ i ∈ insert b s, a i * u i x) =
        fun x => 1 * (∑ i ∈ s, a i * u i x) + a b * u b x := by
      funext x; rw [Finset.sum_insert hbs]; ring
    rw [e, dirB_lin_left hρ h1 hub hw, ih fun i hi => hu i (Finset.mem_insert_of_mem hi),
      Finset.sum_insert hbs]
    ring

omit hρ hb in
theorem card_box (M : ℕ) : (box (ι := Fin d) M).card = (2 * M + 1) ^ d := by
  simp only [box, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  omega

/-- **One Weyl step.** -/
theorem weyl_step (hd : 1 ≤ d) {j M : ℕ} (hjM : 2 * (2 * M + 1) ^ d < j + 1) :
    (((M : ℝ) + 1) ^ 2 - 1) * c ≤ C * lam j := by
  set P := densMeasure ρ
  haveI := hρ.isProb
  set S := box (ι := Fin d) M
  set κ := {k // k ∈ S}
  -- the coefficient map
  let L : (Fin (j + 1) → ℝ) →ₗ[ℝ] (κ → ℂ) :=
    { toFun := fun a k => ∑ i, (a i : ℂ) * mFourierCoeff (fun y => (e i y : ℂ)) k.1
      map_add' := fun a b => by funext k; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r a => by
        funext k; simp [Finset.mul_sum, mul_assoc] }
  have hfin : Module.finrank ℝ (κ → ℂ) < Module.finrank ℝ (Fin (j + 1) → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Module.finrank_pi_fintype,
      Finset.sum_const, Finset.card_univ, Complex.finrank_real_complex, smul_eq_mul,
      Fintype.card_coe, card_box]
    linarith
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (L.ker_ne_bot_of_finrank_lt hfin)
  rw [LinearMap.mem_ker] at ha
  set f : Torus d → ℝ := fun x => ∑ i, a i * e i x
  have hH : ∀ i, MemH1 P (e i) := hb.memH1
  have hfH : MemH1 P f := memH1_finsum hρ Finset.univ (fun i : Fin (j + 1) => e i)
    (fun i _ => hH i) a
  have hfv : MemLp f 2 volume := memLp_vol hρ.haar_le_smul hfH
  have hev : ∀ i, MemLp (e i) 2 volume := fun i => memLp_vol hρ.haar_le_smul (hH i)
  -- Fourier coefficients of `f`
  have hcf : ∀ k ∈ S, mFourierCoeff (fun y => (f y : ℂ)) k = 0 := by
    intro k hk
    have := congrFun ha ⟨k, hk⟩
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
    rw [← this, mFourierCoeff_eq_integral]
    have e1 : (fun t => mFourier (-k) t • ((f t : ℝ) : ℂ)) =
        fun t => ∑ i, (a i : ℂ) * (mFourier (-k) t • (e i t : ℂ)) := by
      funext t; simp only [f]; push_cast; rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp only [smul_eq_mul]; ring
    rw [e1, integral_finsetSum _ fun (i : Fin (j + 1)) _ =>
      (integrable_mFourier_smul' ((hev i).integrable one_le_two) (-k)).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, mFourierCoeff_eq_integral]
  -- `∫ f² dP = ∑ aᵢ²`
  have hon : ∀ i l : Fin (j + 1), ∫ x, e i x * e l x ∂P = if i = l then 1 else 0 := by
    intro i l
    rw [hb.orthonormal i l]
    simp [Fin.val_inj]
  have hfe : ∀ l : Fin (j + 1), ∫ x, e l x * f x ∂P = a l := by
    intro l
    simp only [f, Finset.mul_sum]
    rw [integral_finsetSum _ fun (i : Fin (j + 1)) _ =>
      ((hH l).2.1.integrable_mul (hH i).2.1).const_mul (a i) |>.congr
        (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)]
    simp_rw [show ∀ i x, e l x * (a i * e i x) = a i * (e i x * e l x) from fun i x => by ring,
      integral_const_mul, hon]
    simp
  have hnorm : ∫ x, f x ^ 2 ∂P = ∑ i, a i ^ 2 := by
    have : ∫ x, f x ^ 2 ∂P = ∑ l, a l * ∫ x, e l x * f x ∂P := by
      simp only [sq, f, Finset.sum_mul]
      rw [integral_finsetSum _ fun (l : Fin (j + 1)) _ =>
        ((hH l).2.1.integrable_mul hfH.2.1).const_mul (a l) |>.congr
        (Eventually.of_forall fun x => by simp only [Pi.mul_apply, f]; ring)]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← integral_const_mul]; congr 1; funext x; ring
    rw [this]; simp_rw [hfe]
    exact Finset.sum_congr rfl fun l _ => (sq _).symm
  have hpos : 0 < ∑ i, a i ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by by_contra h; push Not at h; exact ha0 (funext h)
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => a i ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
  -- the energy
  have hE : dirE P f ≤ lam j * ∑ i, a i ^ 2 := by
    rw [dirE_eq_dirB hρ, dirB_finsum_left hρ Finset.univ (fun i : Fin (j + 1) => e i)
      (fun i _ => hH i) a hfH, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [refBasis_eig hρ hb i hfH, hfe]
    have hli : lam i ≤ lam j := hb.mono (Nat.lt_succ_iff.mp i.2)
    nlinarith [refLam_nonneg hρ hb i, sq_nonneg (a i)]
  -- Haar side
  have hgv : ∀ k, MemLp (fun y => weakGrad f y k) 2 volume := fun k =>
    memLp_grad_vol hρ.haar_le_smul hρ.le_smul hfH k
  have hwt := hasSum_wt_cf (isWeakGrad_weakGrad hfH.1) hfv hgv
  have hpar := hasSum_sq_mFourierCoeff_real hfv
  have hM : ((M : ℝ) + 1) ^ 2 * ∫ y, f y ^ 2 ≤ (∫ y, f y ^ 2) + ∑ k, ∫ y, weakGrad f y k ^ 2 := by
    have hle : ∑' k, ((M : ℝ) + 1) ^ 2 * ‖mFourierCoeff (fun y => (f y : ℂ)) k‖ ^ 2 ≤
        ∑' k, wt k * ‖cf f k‖ ^ 2 := by
      refine (hpar.summable.mul_left _).tsum_le_tsum (fun k => ?_) hwt.summable
      by_cases hk : k ∈ S
      · simp [cf, hcf k hk]
      · exact mul_le_mul_of_nonneg_right (wt_ge_of_not_mem_box hk) (sq_nonneg _)
    rwa [tsum_mul_left, hpar.tsum_eq, hwt.tsum_eq] at hle
  have hc0 : 0 ≤ 1 / c := by have := hρ.pos; positivity
  have hgrad : ∑ k, ∫ y, weakGrad f y k ^ 2 ≤ 1 / c * dirE P f := by
    rw [dirE, integral_finsetSum _ fun k _ => (gradP hρ hfH k).integrable_sq, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ =>
      integral_le_smul_of_le hc0 hρ.haar_le_smul (fun _ => sq_nonneg _) (gradP hρ hfH k).integrable_sq
  have hPm : ∫ x, f x ^ 2 ∂P ≤ C * ∫ y, f y ^ 2 :=
    integral_le_smul_of_le hρ.C_pos.le hρ.le_smul (fun _ => sq_nonneg _) hfv.integrable_sq
  have hm0 : 0 < ∫ y, f y ^ 2 := by
    rcases (integral_nonneg fun y => sq_nonneg (f y) : 0 ≤ ∫ y, f y ^ 2).eq_or_lt with h0 | h
    · exfalso
      have hz := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg (f y))
        hfv.integrable_sq).mp h0.symm
      have hzP : (fun y => f y ^ 2) =ᵐ[P] 0 := hρ.ac.ae_le hz
      have : ∫ x, f x ^ 2 ∂P = 0 := by rw [integral_congr_ae hzP]; simp
      rw [hnorm] at this; linarith
    · exact h
  have hlj := refLam_nonneg hρ hb j
  have key : (((M : ℝ) + 1) ^ 2 - 1) * ∫ y, f y ^ 2 ≤ (C / c * lam j) * ∫ y, f y ^ 2 := by
    calc (((M : ℝ) + 1) ^ 2 - 1) * ∫ y, f y ^ 2 ≤ ∑ k, ∫ y, weakGrad f y k ^ 2 := by linarith
      _ ≤ 1 / c * dirE P f := hgrad
      _ ≤ 1 / c * (lam j * ∑ i, a i ^ 2) := mul_le_mul_of_nonneg_left hE hc0
      _ = 1 / c * lam j * ∫ x, f x ^ 2 ∂P := by rw [hnorm]; ring
      _ ≤ 1 / c * lam j * (C * ∫ y, f y ^ 2) :=
          mul_le_mul_of_nonneg_left hPm (mul_nonneg hc0 hlj)
      _ = (C / c * lam j) * ∫ y, f y ^ 2 := by ring
  have := le_of_mul_le_mul_right key hm0
  have hc := hρ.pos
  rw [div_mul_eq_mul_div, le_div_iff₀ hc] at this
  linarith

/-- **The Weyl lower bound** `λⱼ ≥ c₀ j^{2/d}`. -/
theorem weyl (hd : 1 ≤ d) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ j : ℕ, 1 ≤ j → c₀ * (j : ℝ) ^ (2 / (d : ℝ)) ≤ lam j := by
  have hc := hρ.pos
  have hC := hρ.C_pos
  have hl1 := refLam_pos hρ hb hd (le_refl 1)
  have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have h2d : 2 / (d : ℝ) ≤ 2 := by rw [div_le_iff₀ hd0]; nlinarith
  have h2d0 : 0 ≤ 2 / (d : ℝ) := by positivity
  have hpow2 : (2 : ℝ) ^ (2 / (d : ℝ)) ≤ 4 := by
    calc (2 : ℝ) ^ (2 / (d : ℝ)) ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h2d
      _ = 4 := by norm_num
  refine ⟨min (c / (128 * C)) (lam 1 / 64), lt_min (by positivity) (by positivity), fun j hj => ?_⟩
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  set r : ℝ := ((j : ℝ) + 1) / 2
  have hr1 : 1 ≤ r := by simp only [r]; linarith
  set sR : ℝ := r ^ (1 / (d : ℝ))
  have hs0 : 0 < sR := Real.rpow_pos_of_pos (by linarith) _
  have hsd : sR ^ d = r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), one_div_mul_cancel hd0.ne',
      Real.rpow_one]
  have hs2 : sR ^ 2 = r ^ (2 / (d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; push_cast; ring
  have hjr : (j : ℝ) ^ (2 / (d : ℝ)) ≤ 4 * sR ^ 2 := by
    have : (j : ℝ) ≤ 2 * r := by simp only [r]; linarith
    calc (j : ℝ) ^ (2 / (d : ℝ)) ≤ (2 * r) ^ (2 / (d : ℝ)) :=
          Real.rpow_le_rpow (by positivity) this h2d0
      _ = 2 ^ (2 / (d : ℝ)) * r ^ (2 / (d : ℝ)) := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 4 * sR ^ 2 := by rw [hs2]; gcongr
  by_cases hs4 : 4 ≤ sR
  · set M := ⌊sR / 4⌋₊
    have hM1 : (1 : ℝ) ≤ M := by
      have : 1 ≤ M := Nat.le_floor (by push_cast; linarith)
      exact_mod_cast this
    have hMs : (M : ℝ) ≤ sR / 4 := Nat.floor_le (by positivity)
    have hMs' : sR / 4 < M + 1 := Nat.lt_floor_add_one _
    have hcond : 2 * (2 * M + 1) ^ d < j + 1 := by
      have h1 : (2 * (M : ℝ) + 1) < sR := by linarith
      have h2 : (2 * (M : ℝ) + 1) ^ d < sR ^ d :=
        pow_lt_pow_left₀ h1 (by positivity) (by omega)
      rw [hsd] at h2
      have : (2 * ((2 * M + 1 : ℕ) : ℝ) ^ d) < (j : ℝ) + 1 := by
        push_cast; simp only [r] at h2; linarith
      exact_mod_cast this
    have hstep := weyl_step hρ hb hd hcond
    have hM2 : (sR ^ 2) / 32 ≤ ((M : ℝ) + 1) ^ 2 - 1 := by
      have h3 : sR ^ 2 / 16 < ((M : ℝ) + 1) ^ 2 := by
        have : sR / 4 < (M : ℝ) + 1 := hMs'
        nlinarith
      nlinarith
    have hlam : c * (sR ^ 2 / 32) ≤ C * lam j := by
      calc c * (sR ^ 2 / 32) ≤ c * (((M : ℝ) + 1) ^ 2 - 1) := mul_le_mul_of_nonneg_left hM2 hc.le
        _ = (((M : ℝ) + 1) ^ 2 - 1) * c := mul_comm _ _
        _ ≤ C * lam j := hstep
    calc min (c / (128 * C)) (lam 1 / 64) * (j : ℝ) ^ (2 / (d : ℝ))
        ≤ c / (128 * C) * (4 * sR ^ 2) :=
          mul_le_mul (min_le_left _ _) hjr (by positivity) (by positivity)
      _ = (c * (sR ^ 2 / 32)) / C := by field_simp; ring
      _ ≤ (C * lam j) / C := div_le_div_of_nonneg_right hlam hC.le
      _ = lam j := by field_simp
  · push Not at hs4
    have hr4 : r < 4 ^ d := by
      rw [← hsd]; exact pow_lt_pow_left₀ hs4 hs0.le (by omega)
    have hj64 : (j : ℝ) ^ (2 / (d : ℝ)) ≤ 64 := by
      have hjr' : (j : ℝ) ≤ 2 * 4 ^ d := by simp only [r] at hr4; linarith
      calc (j : ℝ) ^ (2 / (d : ℝ)) ≤ (2 * 4 ^ d) ^ (2 / (d : ℝ)) :=
            Real.rpow_le_rpow (by positivity) hjr' h2d0
        _ = 2 ^ (2 / (d : ℝ)) * ((4 : ℝ) ^ d) ^ (2 / (d : ℝ)) :=
            Real.mul_rpow (by norm_num) (by positivity)
        _ = 2 ^ (2 / (d : ℝ)) * 16 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            rw [show (d : ℝ) * (2 / d) = 2 by field_simp]; norm_num
        _ ≤ 4 * 16 := by gcongr
        _ = 64 := by norm_num
    calc min (c / (128 * C)) (lam 1 / 64) * (j : ℝ) ^ (2 / (d : ℝ))
        ≤ lam 1 / 64 * 64 :=
          mul_le_mul (min_le_right _ _) hj64 (by positivity) (by positivity)
      _ = lam 1 := by ring
      _ ≤ lam j := hb.mono hj

end SharpLSI
