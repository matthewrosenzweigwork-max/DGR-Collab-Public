import SharpSymmetricLSI.Paper.LemmaA2_5

/-!
# R25 (A.9), part 6: the resolvent for a smooth density

For a good density `ρ` with smooth lift, `τ > 0` and a smooth periodic `Φ`, the series
`u = ∑ ⟨Φ, e_j⟩_μ/(1+τλ_j) eC_j` converges in `C¹` (coefficients of `Φ` decay faster than any
power of `λ_j`, the eigenfunctions grow polynomially in `C¹`, and `λ_j ≥ c j^{2/d}`), and solves
the resolvent equation `u - τ L u = Φ` in the integrated form
`∫ ρ (Φ - u) Θ dm = -τ ∫ u div(ρ∇Θ) dm` for all smooth periodic `Θ` (`exists_resolvent_smooth`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

theorem lipschitz_of_smooth_periodic {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (hp : IsPer F) :
    ∃ L : ℝ≥0, LipschitzWith L F := by
  obtain ⟨B, hB⟩ := periodic_bounded (hF.continuous_fderiv (by simp)) hp.fderiv
  refine ⟨Real.toNNReal B, lipschitzWith_of_nnnorm_fderiv_le (hF.differentiable (by simp))
    fun x => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
  exact (hB x).trans (le_max_left _ _)

section resolvent

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C) (hρs : ContDiff ℝ ∞ (ρ ∘ liftT))
include hρ hρs

/-- **The resolvent for a smooth density.** -/
theorem exists_resolvent_smooth (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) {Φ : (Fin d → ℝ) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦp : IsPer Φ) :
    ∃ u : Torus d → ℝ, ContDiff ℝ 1 (u ∘ liftT) ∧
      ∀ Θ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ Θ → IsPer Θ →
        ∫ y, ρ y * (Φ (secT y) - u y) * Θ (secT y) = -τ * ∫ y, u y * divRho ρ Θ (secT y) := by
  haveI := hρ.isProb
  have hpos : ∀ y, 0 < ρ y := fun y => hρ.pos.trans_le (hρ.lower y)
  have hρc : Continuous ρ := continuous_of_liftT' hρs.continuous
  have hσs : ContDiff ℝ ∞ (recipD ρ ∘ liftT) :=
    contDiff_const.div hρs fun x => (hpos _).ne'
  obtain ⟨Lσ, hσ⟩ := lipschitz_of_smooth_periodic hσs (isPer_comp_liftT _)
  set P := densMeasure ρ
  set e := eSeq P
  set lam : ℕ → ℝ := fun n => dirE P (eSeq P n)
  have hb : IsRefEigenbasis P e lam := isRefEigenbasis_eSeq hρ hd
  obtain ⟨Cc, q, hc1⟩ := c1rep hρ hρc hσ hd
  choose eC heC1 heCae heCb _ using fun j => hc1 (e j) (lam j) (isEig_of_basis hb j)
  set M : ℕ → ℝ := fun j => Cc * (1 + lam j) ^ q
  have hlam0 : ∀ j, 0 ≤ lam j := fun j => refLam_nonneg hρ hb j
  have hM : ∀ j x, |eC j x| ≤ M j := fun j x =>
    le_trans (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (heCb j x)
  have hCc : 0 ≤ Cc := by
    have h0 := (abs_nonneg _).trans (hM 0 0)
    have : 0 < (1 + lam 0) ^ q := pow_pos (by linarith [hlam0 0]) q
    exact nonneg_of_mul_nonneg_left h0 this
  have hM0 : ∀ j, 0 ≤ M j := fun j => mul_nonneg hCc (pow_nonneg (by linarith [hlam0 j]) q)
  set M' : ℕ → ℝ := fun j => d * M j
  have hM' : ∀ j x, ‖fderiv ℝ (eC j ∘ liftT) x‖ ≤ M' j := by
    intro j x
    refine (norm_fderiv_le_sum _ x).trans ?_
    have hi : ∀ i, |fderiv ℝ (eC j ∘ liftT) x (Pi.single i 1)| ≤ M j := by
      intro i
      rw [← fderiv_lift_repTorus]
      refine (abs_le_sqrt_sqNorm (fun k => cpartial (eC j) k (liftT x)) i).trans ?_
      exact le_trans (le_add_of_nonneg_left (abs_nonneg _)) (heCb j _)
    calc ∑ i, |fderiv ℝ (eC j ∘ liftT) x (Pi.single i 1)| ≤ ∑ _i : Fin d, M j :=
          Finset.sum_le_sum fun i _ => hi i
      _ = M' j := by simp [M']
  -- coefficients and their decay
  set cf : ℕ → ℝ := fun j => ∫ y, e j y * Φ (secT y) ∂P
  set a : ℕ → ℝ := fun j => cf j / (1 + τ * lam j)
  have hden : ∀ j, 1 ≤ 1 + τ * lam j := fun j => by nlinarith [hlam0 j]
  have ha : ∀ j, a j * (1 + τ * lam j) = cf j := fun j => by
    simp only [a]; field_simp [(lt_of_lt_of_le one_pos (hden j)).ne']
  have habs : ∀ j, |a j| ≤ |cf j| := fun j => by
    simp only [a, abs_div]
    rw [abs_of_pos (lt_of_lt_of_le one_pos (hden j))]
    exact div_le_self (abs_nonneg _) (hden j)
  set m := q + d
  obtain ⟨B, hB⟩ := periodic_bounded (contDiff_iterate_genA hρs hΦ hpos m).continuous
    (isPer_iterate_genA hΦp m)
  set D := (1 + B ^ 2) / 2
  have hdec : ∀ j, |lam j| ^ m * |cf j| ≤ D := fun j =>
    abs_coeff_le hρ hρs (isEig_of_basis hb j) hΦ hΦp m fun x => by
      rw [← Real.norm_eq_abs]; exact hB x
  obtain ⟨c₀, hc₀, hw⟩ := weyl hρ hb hd
  have hl1 : 0 < lam 1 := refLam_pos hρ hb hd le_rfl
  set κ := 1 + 1 / lam 1
  have hκ : 0 ≤ κ := by positivity
  have hdd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsum : Summable fun j => |cf j| * M j := by
    refine summable_of_le_div_sq (fun j => mul_nonneg (abs_nonneg _) (hM0 j))
      (K := D * Cc * κ ^ q / c₀ ^ d) fun j hj => ?_
    have hlj : lam 1 ≤ lam j := hb.mono hj
    have hlpos : 0 < lam j := hl1.trans_le hlj
    have h1 : 1 + lam j ≤ κ * lam j := by
      simp only [κ]; rw [add_mul, one_mul, div_mul_eq_mul_div, one_mul, add_comm]
      have : 1 ≤ lam j / lam 1 := (one_le_div hl1).mpr hlj
      linarith
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    have hwj : c₀ ^ d * (j : ℝ) ^ 2 ≤ lam j ^ d := by
      have h2 := pow_le_pow_left₀ (by positivity) (hw j hj) d
      have e : (c₀ * (j : ℝ) ^ (2 / (d : ℝ))) ^ d = c₀ ^ d * (j : ℝ) ^ 2 := by
        rw [mul_pow, ← Real.rpow_natCast ((j : ℝ) ^ (2 / (d : ℝ))), ← Real.rpow_mul hj0.le,
          div_mul_cancel₀ _ hdd]
        norm_num
      rwa [e] at h2
    have hc : |cf j| ≤ D / lam j ^ m := by
      rw [le_div_iff₀ (pow_pos hlpos m), mul_comm]
      have := hdec j
      rwa [abs_of_pos hlpos] at this
    have hMj : M j ≤ Cc * (κ ^ q * lam j ^ q) := by
      simp only [M]
      refine mul_le_mul_of_nonneg_left ?_ hCc
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith [hlam0 j]) h1 q
    calc |cf j| * M j ≤ D / lam j ^ m * (Cc * (κ ^ q * lam j ^ q)) :=
          mul_le_mul hc hMj (hM0 j) (by positivity)
      _ = D * Cc * κ ^ q / lam j ^ d := by
          simp only [m]; rw [pow_add]; field_simp
      _ ≤ D * Cc * κ ^ q / (c₀ ^ d * (j : ℝ) ^ 2) := by
          have hD : 0 ≤ D := by positivity
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hwj
      _ = D * Cc * κ ^ q / c₀ ^ d / (j : ℝ) ^ 2 := by rw [div_div]
  have hsum' : Summable fun j => |cf j| * M' j := by
    refine (hsum.mul_left (d : ℝ)).congr fun j => ?_
    simp only [M']; ring
  have hsa : Summable fun j => |a j| * M j :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (abs_nonneg _) (hM0 j))
      (fun j => mul_le_mul_of_nonneg_right (habs j) (hM0 j)) hsum
  have hsa' : Summable fun j => |a j| * M' j :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hM0 j)))
      (fun j => mul_le_mul_of_nonneg_right (habs j) (mul_nonneg (Nat.cast_nonneg _) (hM0 j))) hsum'
  set u := series a eC
  set f' := series cf eC
  have hu1 : ContDiff ℝ 1 (u ∘ liftT) := contDiff_series heC1 hM hM' hsa hsa'
  have hf1 : ContDiff ℝ 1 (f' ∘ liftT) := contDiff_series heC1 hM hM' hsum hsum'
  have huc : Continuous u := continuous_of_liftT' hu1.continuous
  have hfc : Continuous f' := continuous_of_liftT' hf1.continuous
  -- `f' = Φ` `μ`-a.e.
  have hΦc : Continuous fun y => Φ (secT y) := by
    refine continuous_of_liftT' ?_
    rw [show (fun y => Φ (secT y)) ∘ liftT = Φ from comp_secT_comp_liftT hΦp]
    exact hΦ.continuous
  obtain ⟨BΦ, hBΦ⟩ := periodic_bounded hΦ.continuous hΦp
  obtain ⟨Bf, hBf⟩ := (isCompact_univ.image hfc).isBounded.exists_norm_le
  have hdiff : MemLp (fun y => f' y - Φ (secT y)) 2 P :=
    MemLp.of_bound (hfc.sub hΦc).aestronglyMeasurable (Bf + BΦ) (Eventually.of_forall fun y =>
      (norm_sub_le _ _).trans (add_le_add (hBf _ ⟨y, trivial, rfl⟩) (hBΦ _)))
  have hfΦ : (fun y => f' y - Φ (secT y)) =ᵐ[P] 0 := by
    refine hb.complete _ hdiff fun i => ?_
    have hei : Integrable (e i) P := ((hb.memH1 i).2.1).integrable one_le_two
    have h1 : Integrable (fun y => f' y * e i y) P :=
      hei.bdd_mul (c := Bf) hfc.aestronglyMeasurable
        (Eventually.of_forall fun y => hBf _ ⟨y, trivial, rfl⟩)
    have h2 : Integrable (fun y => Φ (secT y) * e i y) P :=
      hei.bdd_mul (c := BΦ) hΦc.aestronglyMeasurable (Eventually.of_forall fun y => hBΦ _)
    simp_rw [sub_mul]
    rw [integral_sub h1 h2, coeff_series hρ hb heC1 heCae hM hsum i]
    simp only [cf]
    rw [sub_eq_zero]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  refine ⟨u, hu1, fun Θ hΘ hp => ?_⟩
  -- termwise identities
  obtain ⟨BΘ, hBΘ⟩ := periodic_bounded hΘ.continuous hp
  have hΘc : Continuous fun y => Θ (secT y) := by
    refine continuous_of_liftT' ?_
    rw [show (fun y => Θ (secT y)) ∘ liftT = Θ from comp_secT_comp_liftT hp]
    exact hΘ.continuous
  have hdivc : Continuous fun y => divRho ρ Θ (secT y) := by
    refine continuous_of_liftT' ?_
    rw [show (fun y => divRho ρ Θ (secT y)) ∘ liftT = divRho ρ Θ from
      comp_secT_comp_liftT (isPer_divRho hp)]
    exact (contDiff_divRho hρs hΘ).continuous
  obtain ⟨Bdiv, hBdiv⟩ := periodic_bounded (contDiff_divRho hρs hΘ).continuous (isPer_divRho hp)
  set x : ℕ → ℝ := fun j => ∫ y, eC j y * Θ (secT y) ∂P
  set z : ℕ → ℝ := fun j => ∫ y, eC j y * divRho ρ Θ (secT y)
  have hxz : ∀ j, lam j * x j = -z j := by
    intro j
    have h := hb.eigen j _ (memH1_smooth hρ hρs hΘ hp)
    have h' : dirB P (e j) (Θ ∘ secT) = lam j * ∫ y, e j y * (Θ ∘ secT) y ∂P := h
    rw [dirB_smooth_eq hρ hρs (hb.memH1 j) hΘ hp] at h'
    have hx' : x j = ∫ y, e j y * Θ (secT y) ∂P :=
      integral_congr_ae ((heCae j).mono fun y hy => by simp only [hy])
    have hae' : eC j =ᵐ[volume] e j := hρ.ac'.ae_le (heCae j)
    have hz' : z j = ∫ y, e j y * divRho ρ Θ (secT y) :=
      integral_congr_ae (hae'.mono fun y hy => by simp only [hy])
    rw [hx', hz']
    simp only [Function.comp] at h'
    linarith
  have hΘi : Integrable (fun y => Θ (secT y)) P :=
    (integrable_const BΘ).mono' hΘc.aestronglyMeasurable (Eventually.of_forall fun y => hBΘ _)
  have hdivi : Integrable (fun y => divRho ρ Θ (secT y)) volume :=
    (integrable_const Bdiv).mono' hdivc.aestronglyMeasurable (Eventually.of_forall fun y => hBdiv _)
  have hux : ∫ y, u y * Θ (secT y) ∂P = ∑' j, a j * x j :=
    integral_series_mul heC1 hM hsa hΘi
  have hfx : ∫ y, f' y * Θ (secT y) ∂P = ∑' j, cf j * x j :=
    integral_series_mul heC1 hM hsum hΘi
  have huz : ∫ y, u y * divRho ρ Θ (secT y) = ∑' j, a j * z j :=
    integral_series_mul heC1 hM hsa hdivi
  have hxb : ∀ j, |x j| ≤ M j * BΘ := fun j => by
    calc |x j| ≤ ∫ y, |eC j y * Θ (secT y)| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ _y, M j * BΘ ∂P := integral_mono_of_nonneg
          (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
          (Eventually.of_forall fun y => by
            show |eC j y * Θ (secT y)| ≤ M j * BΘ
            rw [abs_mul]
            exact mul_le_mul (hM j y) (by rw [← Real.norm_eq_abs]; exact hBΘ _) (abs_nonneg _)
              (hM0 j))
      _ = M j * BΘ := by simp
  have hBΘ0 : 0 ≤ BΘ := (norm_nonneg _).trans (hBΘ 0)
  have hsx : ∀ b : ℕ → ℝ, Summable (fun j => |b j| * M j) → Summable fun j => b j * x j :=
    fun b hb' => Summable.of_norm_bounded (hb'.mul_right BΘ) fun j => by
      rw [Real.norm_eq_abs, abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hxb j) (abs_nonneg _)
  have hkey : ∑' j, a j * z j = -(1 / τ) * (∑' j, cf j * x j - ∑' j, a j * x j) := by
    rw [← (hsx cf hsum).tsum_sub (hsx a hsa), ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [show z j = -(lam j * x j) by linarith [hxz j], ← ha j]
    field_simp
    ring
  -- assemble
  have hlhs : ∫ y, ρ y * (Φ (secT y) - u y) * Θ (secT y) =
      ∫ y, f' y * Θ (secT y) ∂P - ∫ y, u y * Θ (secT y) ∂P := by
    have hfi : Integrable (fun y => f' y * Θ (secT y)) P :=
      hΘi.bdd_mul (c := Bf) hfc.aestronglyMeasurable
        (Eventually.of_forall fun y => hBf _ ⟨y, trivial, rfl⟩)
    obtain ⟨Bu, hBu⟩ := (isCompact_univ.image huc).isBounded.exists_norm_le
    have hui : Integrable (fun y => u y * Θ (secT y)) P :=
      hΘi.bdd_mul (c := Bu) huc.aestronglyMeasurable
        (Eventually.of_forall fun y => hBu _ ⟨y, trivial, rfl⟩)
    rw [← integral_sub hfi hui, hρ.integral_eq]
    refine integral_congr_ae ?_
    filter_upwards [hρ.ac' hfΦ] with y hy
    simp only [Pi.zero_apply, sub_eq_zero] at hy
    rw [hy]; ring
  rw [hlhs, hux, hfx, huz, hkey]
  field_simp

end resolvent

end SharpLSI
