import SharpSymmetricLSI.Paper.RefSpectrum13

/-!
# R23 (6.1), part 14: `W^{2,p}` for eigenfunctions
-/

open MeasureTheory Filter Topology Complex
open scoped ENNReal Real ContDiff NNReal
open UnitAddTorus

namespace SharpLSI

variable {d : ℕ} {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C) (hρc : Continuous ρ)
  {Lσ : ℝ≥0} (hσ : LipschitzWith Lσ (recipD ρ ∘ liftT))
include hρ hρc hσ

omit hρ hρc hσ in
theorem exists_pow_two_ge {p : ℝ≥0∞} (hp : p ≠ ⊤) : ∃ m : ℕ, p ≤ ENNReal.ofReal ((2 : ℝ) ^ (m + 1)) := by
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hp
  refine ⟨n, hn.le.trans ?_⟩
  rw [← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  have : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
  have h2 : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
  linarith

/-- **`W^{2,p}`**, every finite `p`. -/
theorem w2p (hd : 1 ≤ d) {e : Torus d → ℝ} {lam : ℝ} (h : IsEig (densMeasure ρ) e lam)
    (k : Fin d) :
    HasWeakGrad (fun x => weakGrad e x k) ∧
      ∀ l (p : ℝ≥0∞), p ≠ ⊤ →
        MemLp (fun x => weakGrad (fun y => weakGrad e y k) x l) p (haar d) := by
  haveI := hρ.isProb
  have hev : MemLp e 2 volume := memLp_vol hρ.haar_le_smul h.1
  have hge : ∀ k, MemLp (fun y => weakGrad e y k) 2 volume := fun k =>
    memLp_grad_vol hρ.haar_le_smul hρ.le_smul h.1 k
  have hg := memLp_srcG hρ hρc hσ h.1 lam
  have hcf := cf_srcG hρ hρc hσ h.1 h.2.2
  choose H hH2 hHc using fun l => exists_d2 hev hg hcf k l
  have hcfk : ∀ κ, mFourierCoeff (fun y => (weakGrad e y k : ℂ)) κ =
      2 * π * I * κ k * mFourierCoeff (fun y => (e y : ℂ)) κ := fun κ =>
    mFourierCoeff_grad (isWeakGrad_weakGrad h.1.1) (hev.integrable one_le_two)
      (fun j => (hge j).integrable one_le_two) κ k
  have hw : IsWeakGrad (fun x => weakGrad e x k) (fun y l => H l y) :=
    isWeakGrad_of_cf (hge k) hH2 fun l κ => by simp only [cf]; rw [hHc l κ, hcfk κ, d2c]; ring
  refine ⟨⟨_, hw⟩, fun l p hp => ?_⟩
  have hae : weakGrad (fun x => weakGrad e x k) =ᵐ[volume] fun y l => H l y :=
    weakGrad_ae_unique (isWeakGrad_weakGrad ⟨_, hw⟩) hw
  obtain ⟨m, hm⟩ := exists_pow_two_ge hp
  obtain ⟨K, q, hK, hmom⟩ := moments hρ hρc hσ hd m
  obtain ⟨A, hA0, hA⟩ := heat_d2_bound (ι := Fin d) m
  set P : ℝ := (2 : ℝ) ^ (m + 1)
  have hP0 : 0 < P := by positivity
  have hPc : ((2 ^ (m + 1) : ℕ) : ℝ) = P := by push_cast; rfl
  have hgm := (hmom e lam h).2
  rw [hPc] at hgm
  have hbound : ∀ t, 0 < t → ∫⁻ y, ‖heatT t (H l) y‖ₑ ^ P ≤
      ENNReal.ofReal A ^ P * ENNReal.ofReal (K * (1 + lam) ^ q) := by
    intro t ht
    calc ∫⁻ y, ‖heatT t (H l) y‖ₑ ^ P
        = ∫⁻ y, ‖dpart (dpart (heatT t e) k) l y‖ₑ ^ P :=
          lintegral_congr_ae ((heatT_d2 hev (hH2 l) (hHc l) ht).mono fun y hy => by simp only [hy])
      _ ≤ ENNReal.ofReal A ^ P * ∫⁻ y, ‖srcG ρ lam e y‖ₑ ^ P := hA e _ hev hg hcf t ht k l
      _ ≤ _ := mul_le_mul' le_rfl hgm
  have hfin := lintegral_le_of_heatT ((hH2 l).integrable one_le_two) hP0.le hbound
  have hlt : ∫⁻ y, ‖H l y‖ₑ ^ P < ⊤ :=
    lt_of_le_of_lt hfin (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hP0.le
      ENNReal.ofReal_ne_top) ENNReal.ofReal_lt_top)
  have hmem := (memLp_of_lintegral_rpow_lt_top (hH2 l).aestronglyMeasurable hP0 hlt).mono_exponent hm
  exact hmem.ae_eq (hae.mono fun y hy => by simp only [hy])

end SharpLSI
