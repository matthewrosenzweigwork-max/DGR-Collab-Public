import FullLabeledLSI.Paper.Sec8Fourier10
import SharpSymmetricLSI.Paper.CosineD6
import SharpSymmetricLSI.Paper.CosineMinimizer

/-!
# Section 8.5 (Corollary 8.4), part 11: `r_ms = 4 pi^2` and the limit

* the one-particle test `1 + ε cos(2π x_i)` gives `r_LS(m) ≤ 4π²` on `𝕋^d`;
* `r_ms ≤ r_LS(m)` through the equilibrium `m` and `r_ms ≥ 4π²` from `ms_lower`;
* the assembly `fourier_core`, taking the open Theorem 1.1 (`r^all_N → r_ms`) as a hypothesis.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {d : ℕ}

theorem contDiff_mode1_lift (i : Fin d) (ε : ℝ) :
    ContDiff ℝ ∞ (cosDmode1 i ε ∘ liftT) := by
  have : cosDmode1 i ε ∘ liftT = fun z : Fin d → ℝ => 1 + ε * Real.cos (2 * π * z i) := by
    funext z; simp only [Function.comp, cosDmode1, cosDc_liftT]
  rw [this]
  exact contDiff_const.add (contDiff_const.mul (Real.contDiff_cos.comp
    (contDiff_const.mul (contDiff_apply ℝ ℝ i))))

theorem memH1_mode1 (i : Fin d) (ε : ℝ) : MemH1 (haar d) (cosDmode1 i ε) :=
  memH1_of_contDiff (contDiff_mode1_lift i ε)

theorem fderiv_mode1 (i : Fin d) (ε : ℝ) (z : Fin d → ℝ) (k : Fin d) :
    fderiv ℝ (cosDmode1 i ε ∘ liftT) z (Pi.single k 1) =
      if k = i then -(ε * (2 * π) * Real.sin (2 * π * z i)) else 0 := by
  have hlift : cosDmode1 i ε ∘ liftT =
      (fun t : ℝ => 1 + ε * Real.cos (2 * π * t)) ∘ (fun z : Fin d → ℝ => z i) := by
    funext z; simp only [Function.comp, cosDmode1, cosDc_liftT]
  have hG : HasDerivAt (fun t : ℝ => 1 + ε * Real.cos (2 * π * t))
      (-(ε * (2 * π) * Real.sin (2 * π * z i))) (z i) := by
    have := (((hasDerivAt_id' (z i)).const_mul (2 * π)).cos.const_mul ε).const_add 1
    convert this using 1; ring
  have hP : HasFDerivAt (fun z : Fin d → ℝ => z i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) z := hasFDerivAt_apply i z
  rw [hlift, (hG.comp_hasFDerivAt z hP).fderiv]
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk]

theorem ent_mode1 (i : Fin d) (ε : ℝ) :
    ent (haar d) (fun x => cosDmode1 i ε x ^ 2) =
      ent (haar 1) (fun x => (1 + ε * gCos x) ^ 2) := by
  have hc : Continuous fun y : Torus 1 => (1 + ε * gCos y) ^ 2 :=
    (continuous_const.add (continuous_const.mul continuous_gCos)).pow 2
  have h := ent_comp (haar d) (measurable_cosDproj i)
    (u := fun y : Torus 1 => (1 + ε * gCos y) ^ 2)
    (by rw [map_cosDproj_haar]; exact hc.aestronglyMeasurable)
  rw [map_cosDproj_haar] at h
  exact h

theorem dirichlet_mode1 (i : Fin d) (ε : ℝ) :
    dirichlet (haar d) (cosDmode1 i ε) = dirichlet (haar 1) (fun x => 1 + ε * gCos x) := by
  set Φ : Torus 1 → ℝ := fun y => (ε * (2 * π) * Real.sin (2 * π * secT y 0)) ^ 2 with hΦ
  have hs0 : Measurable fun y : Torus 1 => secT y 0 :=
    (measurable_pi_apply 0).comp measurable_secT
  have hΦm : Measurable Φ :=
    (measurable_const.mul (Real.measurable_sin.comp (measurable_const.mul hs0))).pow_const 2
  have hL : dirichlet (haar d) (cosDmode1 i ε) =
      ∫⁻ x, ENNReal.ofReal (Φ (cosDproj i x)) ∂haar d := by
    unfold dirichlet
    refine lintegral_congr_ae ?_
    filter_upwards [weakGrad_ae_eq_of_contDiff ((contDiff_mode1_lift i ε).of_le (by simp))]
      with x hx
    rw [hx]
    simp only [fderiv_mode1]
    congr 1
    unfold sqNorm
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp only [ite_true, hΦ]
    have e : secT (cosDproj i x) 0 = secT x i := rfl
    rw [e]; ring
  have hR : dirichlet (haar 1) (fun x => 1 + ε * gCos x) =
      ∫⁻ y, ENNReal.ofReal (Φ y) ∂haar 1 := by
    unfold dirichlet
    refine lintegral_congr_ae ?_
    filter_upwards [weakGrad_ae_eq_of_contDiff (contDiff_hEps_lift ε)] with x hx
    rw [hx]
    unfold sqNorm
    rw [Fin.sum_univ_one]
    beta_reduce
    rw [fderiv_hEps_lift]
    simp only [hΦ]
    congr 1
    ring
  have hmap := lintegral_map (μ := haar d) (f := fun y => ENNReal.ofReal (Φ y))
    (g := cosDproj i) (ENNReal.measurable_ofReal.comp hΦm) (measurable_cosDproj i)
  rw [map_cosDproj_haar] at hmap
  rw [hL, hR, hmap]

/-- The one-particle test `1 + ε cos(2π x_i)` gives `r_LS(m) ≤ 4π²` on `𝕋^d`. -/
theorem rLS_haar_le_d (hd : 1 ≤ d) : rLS (haar d) ≤ ENNReal.ofReal aCos := by
  set i : Fin d := ⟨0, hd⟩ with hi
  have hsmall : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), |ε| < 1 / 40 :=
    eventually_nhdsWithin_of_eventually_nhds
      ((continuous_abs.tendsto (0 : ℝ)).eventually (gt_mem_nhds (by norm_num)))
  have hne : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ε ≠ 0 := self_mem_nhdsWithin
  refine ge_of_tendsto cosine_test_quotient ?_
  filter_upwards [hsmall, hne] with ε h1 h2
  have hE : 0 < entHEps ε := by
    have hb := (abs_le.mp (entHEps_approx (ε := ε) (by linarith))).1
    have he2 : 0 < ε ^ 2 := by positivity
    have h3 : |ε| ^ 3 = |ε| * ε ^ 2 := by rw [pow_succ, sq_abs]; ring
    have h4 : 0 < ε ^ 2 * (1 - 20 * |ε|) := mul_pos he2 (by linarith)
    rw [h3] at hb
    linarith
  have hpos1 : 0 < ent (haar 1) (fun x => (1 + ε * gCos x) ^ 2) := by
    rw [ent_hEps]; exact ENNReal.ofReal_pos.mpr hE
  have hpos : 0 < ent (haar d) (fun x => cosDmode1 i ε x ^ 2) := by
    rw [ent_mode1]; exact hpos1
  unfold rLS
  have hmem : cosDmode1 i ε ∈ {f : Torus d → ℝ | MemH1 (haar d) f ∧
      0 < ent (haar d) (fun x => f x ^ 2)} := ⟨memH1_mode1 i ε, hpos⟩
  have h := iInf₂_le (f := fun (f : Torus d → ℝ) _ =>
    2 * dirichlet (haar d) f / ent (haar d) (fun x => f x ^ 2)) (cosDmode1 i ε) hmem
  rw [dirichlet_mode1, ent_mode1] at h
  exact h

/-- `r_ms ≤ 4π²`. -/
theorem rMs_WG_le {G : Torus d → ℝ} (hd : 1 ≤ d) (hG : IsSmoothT G) (hGe : ∀ x, G (-x) = G x)
    (hGk : ∀ k : Fin d → ℤ, k ≠ 0 → 0 ≤ (cf G k).re) :
    rMs (fun _ => (0 : ℝ)) (WG G) ≤ ENNReal.ofReal aCos := by
  obtain ⟨KW, hyp⟩ := hyp_WG hG hGe
  refine le_trans ?_ (rLS_haar_le_d hd)
  have h := equilibrium_inf_le_rLS hyp (isMinimizer_haar_WG hG hGk)
  refine le_trans (le_iInf₂ fun F hF => ?_) h
  exact iInf₂_le F hF.1

/-- `r_ms ≥ 4π²`. -/
theorem le_rMs_WG {G : Torus d → ℝ} (hd : 1 ≤ d) (hG : IsSmoothT G) (hGe : ∀ x, G (-x) = G x)
    (hGk : ∀ k : Fin d → ℤ, k ≠ 0 → 0 ≤ (cf G k).re) :
    ENNReal.ofReal aCos ≤ rMs (fun _ => (0 : ℝ)) (WG G) := by
  obtain ⟨KW, hyp⟩ := hyp_WG hG hGe
  unfold rMs
  refine le_iInf₂ fun F hF => ?_
  have hpos : 0 < (msGap (fun _ => (0 : ℝ)) (WG G) F).toENNReal :=
    EReal.toENNReal_pos_iff.2 hF.2
  have hfin : (msGap (fun _ => (0 : ℝ)) (WG G) F).toENNReal ≠ ⊤ :=
    EReal.toENNReal_ne_top_iff.2 (msGap_msDiss_lt_top hd hyp hF.1).1.ne
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hpos.ne'))
    (Or.inl (ENNReal.mul_ne_top (by norm_num) hfin))]
  have h := ms_lower hG hGe hGk F hF.1
  calc ENNReal.ofReal aCos * (2 * (msGap (fun _ => (0 : ℝ)) (WG G) F).toENNReal)
      = ENNReal.ofReal (2 * aCos) * (msGap (fun _ => (0 : ℝ)) (WG G) F).toENNReal := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]; ring
    _ ≤ _ := h

/-- Corollary 8.4, (8.17), from the limit theorem `r^all_N → r_ms` for this `W`. -/
theorem fourier_core (hd : 1 ≤ d) (G : Torus d → ℝ) (hGs : IsSmoothT G)
    (hGe : ∀ x, G (-x) = G x) (hGk : ∀ k : Fin d → ℤ, k ≠ 0 → 0 ≤ (fourierCoeffT G k).re)
    (hlim : ∀ KW : ℝ, Hyp (fun _ : Torus d => (0 : ℝ)) (WG G) 0 KW →
      Tendsto (fun N => rAll (fun _ : Torus d => (0 : ℝ)) (WG G) N) atTop
        (𝓝 (rMs (fun _ : Torus d => (0 : ℝ)) (WG G)))) :
    rMs (fun _ => (0 : ℝ)) (fun x y => G (x - y) - G 0) = ENNReal.ofReal aCos ∧
      Tendsto (fun N => rAll (fun _ => (0 : ℝ)) (fun x y => G (x - y) - G 0) N) atTop
        (𝓝 (ENNReal.ofReal aCos)) := by
  have hGk' : ∀ k : Fin d → ℤ, k ≠ 0 → 0 ≤ (cf G k).re := fun k hk => by
    have := hGk k hk
    rwa [fourierCoeffT_eq_cf] at this
  have heq : rMs (fun _ : Torus d => (0 : ℝ)) (WG G) = ENNReal.ofReal aCos :=
    le_antisymm (rMs_WG_le hd hGs hGe hGk') (le_rMs_WG hd hGs hGe hGk')
  obtain ⟨KW, hyp⟩ := hyp_WG hGs hGe
  refine ⟨heq, ?_⟩
  have := hlim KW hyp
  rw [heq] at this
  exact this

end Sec8
end SharpLSI.FL
