import DGPS.FiniteN.ScalarCosine

/-!
# FIN056: the fold auxiliary cubic geometry

At the fold field `h_c = κ g(s_*) - s_*` the scalar auxiliary potential
`ψ(t) = (t - h_c)²/(2κ) - log I₀(t)` (`DGPS.Models.scalarPsi κ h_c`) has exactly two stationary
points: the double negative point `t_* = -s_*` and a unique positive nondegenerate global
minimizer `t₊`.  Moreover `ψ'(t_*) = ψ''(t_*) = 0`, `ψ'''(t_*) = g''(s_*) < 0` and
`Δ = ψ(t_*) - ψ(t₊) > 0`.

The proof is one-variable calculus on `ψ' = (t - h)/κ - g`: the Bessel ratio `g` is odd and `g'` is
even and strictly decreasing on `[0, ∞)`, so `ψ'' = 1/κ - g'` is positive for `|t| > s_*` and
negative for `|t| < s_*`.  Hence `ψ'` increases up to `-s_*` (value `0` there), decreases to `s_*`,
and increases again to `+∞`; this classifies all roots and gives monotonicity of `ψ` on both
sides of `t₊`.

The main theorem is `DGPS.FiniteN.fold_auxiliary_cubic_geometry`.
-/

open Filter Topology

namespace DGPS.Models

open DGPS.Circle.BesselMoments

/-- The scalar auxiliary potential `ψ_h(t) = (t - h)²/(2κ) - log I₀(t)`. -/
noncomputable def scalarPsi (κ h t : ℝ) : ℝ :=
  (t - h) ^ 2 / (2 * κ) - Real.log (besselI 0 t)

end DGPS.Models

namespace DGPS.FiniteN.ScalarFoldFIN056

open DGPS.Models DGPS.Circle.BesselMoments DGPS.Circle.BesselConcavity
open DGPS.Circle.BesselMonotonicity

/-- The candidate derivative `ψ'(t) = (t - h)/κ - g(t)`. -/
noncomputable def psiDerivFIN056 (κ h t : ℝ) : ℝ := (t - h) / κ - besselRatio t

theorem hasDerivAt_scalarPsi_FIN056 {κ : ℝ} (hκ : 0 < κ) (h t : ℝ) :
    HasDerivAt (scalarPsi κ h) (psiDerivFIN056 κ h t) t := by
  have h1 : HasDerivAt (fun x : ℝ => (x - h) ^ 2 / (2 * κ)) ((t - h) / κ) t := by
    have := (((hasDerivAt_id t).sub_const h).pow 2).div_const (2 * κ)
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have h2 : HasDerivAt (fun x => Real.log (besselI 0 x)) (besselRatio t) t :=
    (hasDerivAt_besselI_zero t).log (besselI_zero_pos t).ne'
  exact h1.sub h2

theorem deriv_scalarPsi_FIN056 {κ : ℝ} (hκ : 0 < κ) (h : ℝ) :
    deriv (scalarPsi κ h) = psiDerivFIN056 κ h :=
  funext fun t => (hasDerivAt_scalarPsi_FIN056 hκ h t).deriv

theorem hasDerivAt_psiDeriv_FIN056 (κ h t : ℝ) :
    HasDerivAt (psiDerivFIN056 κ h) (1 / κ - ratioDeriv t) t := by
  have := (((hasDerivAt_id t).sub_const h).div_const κ).sub (hasDerivAt_ratio t)
  refine this.congr_deriv ?_
  simp [one_div]

theorem continuous_psiDeriv_FIN056 (κ h : ℝ) : Continuous (psiDerivFIN056 κ h) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_psiDeriv_FIN056 κ h t).continuousAt

theorem deriv_psiDeriv_FIN056 (κ h : ℝ) :
    deriv (psiDerivFIN056 κ h) = fun t => 1 / κ - ratioDeriv t :=
  funext fun t => (hasDerivAt_psiDeriv_FIN056 κ h t).deriv

theorem hasDerivAt_secondDeriv_FIN056 (κ : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun x => 1 / κ - ratioDeriv x) (-ratioDeriv2 t) t := by
  have : HasDerivAt (fun x => 1 / κ - ratioDeriv x) (0 - ratioDeriv2 t) t :=
    (hasDerivAt_const t (1 / κ)).sub (hasDerivAt_ratioDeriv t ht)
  rwa [zero_sub] at this

/-- `g` is odd, hence `g'` is even. -/
theorem ratioDeriv_neg_FIN056 (t : ℝ) : ratioDeriv (-t) = ratioDeriv t := by
  have h1 : HasDerivAt (fun x => -besselRatio (-x)) (ratioDeriv (-t)) t := by
    have := ((hasDerivAt_ratio (-t)).comp t (hasDerivAt_neg t)).neg
    refine this.congr_deriv ?_
    ring
  have h2 : (fun x => -besselRatio (-x)) = besselRatio := by
    funext x; rw [besselRatio_neg]; ring
  rw [h2] at h1
  exact h1.unique (hasDerivAt_ratio t)

/-- `g''` is odd. -/
theorem ratioDeriv2_neg_FIN056 {t : ℝ} (ht : t ≠ 0) : ratioDeriv2 (-t) = -ratioDeriv2 t := by
  unfold ratioDeriv2
  rw [ratioDeriv_neg_FIN056, besselRatio_neg]
  field_simp
  ring

theorem ratioDeriv_abs_FIN056 (t : ℝ) : ratioDeriv |t| = ratioDeriv t := by
  rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, ratioDeriv_neg_FIN056]

section Fold

variable {κ h s : ℝ}

theorem psiDeriv_neg_s_FIN056 (hκ : 0 < κ) (hh : h = κ * besselRatio s - s) :
    psiDerivFIN056 κ h (-s) = 0 := by
  unfold psiDerivFIN056
  rw [besselRatio_neg, hh]
  field_simp
  ring

theorem second_pos_FIN056 (hs : 0 < s) (hsd : ratioDeriv s = 1 / κ) {t : ℝ} (ht : s < |t|) :
    0 < 1 / κ - ratioDeriv t := by
  have := strictAntiOn_ratioDeriv (Set.mem_Ici.mpr hs.le)
    (Set.mem_Ici.mpr (hs.le.trans ht.le)) ht
  rw [ratioDeriv_abs_FIN056, hsd] at this
  linarith

theorem second_neg_FIN056 (hs : 0 < s) (hsd : ratioDeriv s = 1 / κ) {t : ℝ} (ht : |t| < s) :
    1 / κ - ratioDeriv t < 0 := by
  have := strictAntiOn_ratioDeriv (Set.mem_Ici.mpr (abs_nonneg t))
    (Set.mem_Ici.mpr hs.le) ht
  rw [ratioDeriv_abs_FIN056, hsd] at this
  linarith

/-- `ψ' < 0` to the left of `-s`. -/
theorem psiDeriv_neg_left_FIN056 (hκ : 0 < κ) (hs : 0 < s) (hsd : ratioDeriv s = 1 / κ)
    (hh : h = κ * besselRatio s - s) {t : ℝ} (ht : t < -s) : psiDerivFIN056 κ h t < 0 := by
  have hmono : StrictMonoOn (psiDerivFIN056 κ h) (Set.Iic (-s)) := by
    refine strictMonoOn_of_deriv_pos (convex_Iic (-s))
      (continuous_psiDeriv_FIN056 κ h).continuousOn ?_
    intro x hx
    rw [interior_Iic] at hx
    rw [deriv_psiDeriv_FIN056]
    refine second_pos_FIN056 hs hsd ?_
    have : x < -s := hx
    rw [abs_of_neg (by linarith)]
    linarith
  have := hmono (Set.mem_Iic.mpr ht.le) (Set.mem_Iic.mpr le_rfl) ht
  rwa [psiDeriv_neg_s_FIN056 hκ hh] at this

/-- `ψ' < 0` on `(-s, s]`. -/
theorem psiDeriv_neg_mid_FIN056 (hκ : 0 < κ) (hs : 0 < s) (hsd : ratioDeriv s = 1 / κ)
    (hh : h = κ * besselRatio s - s) {t : ℝ} (ht1 : -s < t) (ht2 : t ≤ s) :
    psiDerivFIN056 κ h t < 0 := by
  have hanti : StrictAntiOn (psiDerivFIN056 κ h) (Set.Icc (-s) s) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc (-s) s)
      (continuous_psiDeriv_FIN056 κ h).continuousOn ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [deriv_psiDeriv_FIN056]
    refine second_neg_FIN056 hs hsd ?_
    rw [abs_lt]
    exact hx
  have := hanti (Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩) (Set.mem_Icc.mpr ⟨ht1.le, ht2⟩) ht1
  rwa [psiDeriv_neg_s_FIN056 hκ hh] at this

theorem psiDeriv_strictMonoOn_FIN056 (hs : 0 < s) (hsd : ratioDeriv s = 1 / κ) :
    StrictMonoOn (psiDerivFIN056 κ h) (Set.Ici s) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici s)
    (continuous_psiDeriv_FIN056 κ h).continuousOn ?_
  intro x hx
  rw [interior_Ici] at hx
  rw [deriv_psiDeriv_FIN056]
  refine second_pos_FIN056 hs hsd ?_
  have : s < x := hx
  rw [abs_of_pos (by linarith)]
  exact this

theorem exists_positive_root_FIN056 (hκ : 0 < κ) (hs : 0 < s) (hsd : ratioDeriv s = 1 / κ)
    (hh : h = κ * besselRatio s - s) :
    ∃ tp : ℝ, s < tp ∧ psiDerivFIN056 κ h tp = 0 := by
  set b : ℝ := max s (h + 2 * κ) with hb
  have hbs : s ≤ b := le_max_left _ _
  have hbh : h + 2 * κ ≤ b := le_max_right _ _
  have hdb : 0 < psiDerivFIN056 κ h b := by
    unfold psiDerivFIN056
    have h1 := besselRatio_lt_one b
    have h2 : 2 ≤ (b - h) / κ := by
      rw [le_div_iff₀ hκ]; linarith
    linarith
  have hds : psiDerivFIN056 κ h s < 0 := by
    refine psiDeriv_neg_mid_FIN056 hκ hs hsd hh (by linarith) le_rfl
  obtain ⟨tp, htp, hz⟩ := intermediate_value_Icc hbs
    (continuous_psiDeriv_FIN056 κ h).continuousOn
    (Set.mem_Icc.mpr ⟨hds.le, hdb.le⟩)
  refine ⟨tp, ?_, hz⟩
  rcases htp.1.eq_or_lt with h' | h'
  · rw [← h'] at hz; linarith
  · exact h'

end Fold

end DGPS.FiniteN.ScalarFoldFIN056

namespace DGPS.FiniteN

open DGPS.Models DGPS.Circle.BesselMoments DGPS.Circle.BesselConcavity
open DGPS.FiniteN.ScalarFoldFIN056

/-- **FIN056.** Fold auxiliary cubic geometry.  Fix `κ > 2` and put `h_c = scalarFoldField κ`,
`s_* = scalarFoldPoint κ`, `ψ = scalarPsi κ h_c`, so `ψ(t) = (t - h_c)²/(2κ) - log I₀(t)`.

Then `ψ' = (t - h_c)/κ - g` and there is `t₊ > 0` with `t₊ = h_c + κ g(t₊)` such that

1. the stationary points of `ψ` are exactly `t_* = -s_*` and `t₊` (`t₊` is the only positive one);
2. `ψ'(t_*) = ψ''(t_*) = 0`, `ψ'''(t_*) = g''(s_*) < 0`;
3. `t₊` is a nondegenerate (`ψ''(t₊) > 0`) strict global minimizer, and `ψ` is strictly decreasing
   on `(-∞, t₊]` (so `t_*` is a stationary inflection, not a local minimum);
4. `Δ = ψ(t_*) - ψ(t₊) > 0`. -/
theorem fold_auxiliary_cubic_geometry (κ : ℝ) (hκ : 2 < κ) :
    let hc := scalarFoldField κ
    let ψ := scalarPsi κ hc
    let sStar := scalarFoldPoint κ
    (∀ t : ℝ, HasDerivAt ψ ((t - hc) / κ - besselRatio t) t) ∧
    -sStar < 0 ∧
    ∃ tPlus : ℝ, 0 < tPlus ∧ tPlus = hc + κ * besselRatio tPlus ∧
      (∀ t : ℝ, deriv ψ t = 0 ↔ t = -sStar ∨ t = tPlus) ∧
      (∀ t : ℝ, 0 < t → deriv ψ t = 0 → t = tPlus) ∧
      deriv ψ (-sStar) = 0 ∧ deriv (deriv ψ) (-sStar) = 0 ∧
      deriv (deriv (deriv ψ)) (-sStar) = deriv (deriv besselRatio) sStar ∧
      deriv (deriv besselRatio) sStar < 0 ∧
      0 < deriv (deriv ψ) tPlus ∧
      (∀ t : ℝ, t ≠ tPlus → ψ tPlus < ψ t) ∧
      StrictAntiOn ψ (Set.Iic tPlus) ∧
      0 < ψ (-sStar) - ψ tPlus := by
  intro hc ψ sStar
  have hκ0 : 0 < κ := by linarith
  obtain ⟨hs, hsd'⟩ := scalarFoldPoint_spec κ hκ
  have hsd : ratioDeriv sStar = 1 / κ := by rw [deriv_ratio] at hsd'; exact hsd'
  have hh : hc = κ * besselRatio sStar - sStar := rfl
  obtain ⟨tp, hstp, hz⟩ := exists_positive_root_FIN056 hκ0 hs hsd hh
  have hder : deriv ψ = psiDerivFIN056 κ hc := deriv_scalarPsi_FIN056 hκ0 hc
  have hmono := psiDeriv_strictMonoOn_FIN056 (κ := κ) (h := hc) hs hsd
  have hdneg : ∀ x, x < tp → x ≠ -sStar → psiDerivFIN056 κ hc x < 0 := by
    intro x hx hx2
    rcases lt_or_gt_of_ne hx2 with h1 | h1
    · exact psiDeriv_neg_left_FIN056 hκ0 hs hsd hh h1
    · by_cases h3 : x ≤ sStar
      · exact psiDeriv_neg_mid_FIN056 hκ0 hs hsd hh h1 h3
      · have h4 : sStar < x := lt_of_not_ge h3
        have := hmono (Set.mem_Ici.mpr h4.le) (Set.mem_Ici.mpr hstp.le) hx
        rwa [hz] at this
  have hdpos : ∀ x, tp < x → 0 < psiDerivFIN056 κ hc x := by
    intro x hx
    have := hmono (Set.mem_Ici.mpr hstp.le) (Set.mem_Ici.mpr (hstp.le.trans hx.le)) hx
    rwa [hz] at this
  have hroots : ∀ t, psiDerivFIN056 κ hc t = 0 ↔ t = -sStar ∨ t = tp := by
    intro t
    constructor
    · intro h0
      by_contra hne
      push Not at hne
      rcases lt_or_gt_of_ne hne.2 with h1 | h1
      · exact (hdneg t h1 hne.1).ne h0
      · exact (hdpos t h1).ne' h0
    · rintro (rfl | rfl)
      · exact psiDeriv_neg_s_FIN056 hκ0 hh
      · exact hz
  have hcont : Continuous ψ :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_scalarPsi_FIN056 hκ0 hc t).continuousAt
  have hA1 : StrictAntiOn ψ (Set.Iic (-sStar)) := by
    refine strictAntiOn_of_deriv_neg (convex_Iic _) hcont.continuousOn ?_
    intro x hx
    rw [interior_Iic] at hx
    rw [hder]
    exact psiDeriv_neg_left_FIN056 hκ0 hs hsd hh hx
  have hA2 : StrictAntiOn ψ (Set.Icc (-sStar) tp) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont.continuousOn ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [hder]
    exact hdneg x hx.2 hx.1.ne'
  have hanti : StrictAntiOn ψ (Set.Iic tp) := by
    intro a ha b hb hab
    have ha' : a ≤ tp := ha
    have hb' : b ≤ tp := hb
    by_cases hb1 : b ≤ -sStar
    · exact hA1 (Set.mem_Iic.mpr (hab.le.trans hb1)) (Set.mem_Iic.mpr hb1) hab
    · have hb2 : -sStar < b := lt_of_not_ge hb1
      by_cases ha1 : -sStar ≤ a
      · exact hA2 (Set.mem_Icc.mpr ⟨ha1, ha'⟩) (Set.mem_Icc.mpr ⟨hb2.le, hb'⟩) hab
      · have ha2 : a < -sStar := lt_of_not_ge ha1
        have e1 : ψ (-sStar) < ψ a :=
          hA1 (Set.mem_Iic.mpr ha2.le) (Set.mem_Iic.mpr le_rfl) ha2
        have e2 : ψ b < ψ (-sStar) :=
          hA2 (Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩) (Set.mem_Icc.mpr ⟨hb2.le, hb'⟩) hb2
        exact e2.trans e1
  have hB : StrictMonoOn ψ (Set.Ici tp) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici _) hcont.continuousOn ?_
    intro x hx
    rw [interior_Ici] at hx
    rw [hder]
    exact hdpos x hx
  have hg2 : deriv (deriv besselRatio) sStar = ratioDeriv2 sStar := by
    have : deriv besselRatio = ratioDeriv := funext deriv_ratio
    rw [this]
    exact (hasDerivAt_ratioDeriv sStar hs.ne').deriv
  have hsne : -sStar ≠ 0 := by linarith
  refine ⟨fun t => hasDerivAt_scalarPsi_FIN056 hκ0 hc t, by linarith, tp, hs.trans hstp, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, hanti, ?_⟩
  · have := hz
    unfold psiDerivFIN056 at this
    have h2 : (tp - hc) / κ = besselRatio tp := by linarith
    rw [div_eq_iff hκ0.ne'] at h2
    linarith
  · intro t; rw [hder]; exact hroots t
  · intro t ht h0
    rw [hder] at h0
    rcases (hroots t).1 h0 with h1 | h1
    · linarith
    · exact h1
  · rw [hder]; exact psiDeriv_neg_s_FIN056 hκ0 hh
  · rw [hder, deriv_psiDeriv_FIN056]
    show 1 / κ - ratioDeriv (-sStar) = 0
    rw [ratioDeriv_neg_FIN056, hsd]; ring
  · rw [hder, deriv_psiDeriv_FIN056]
    rw [(hasDerivAt_secondDeriv_FIN056 κ hsne).deriv, ratioDeriv2_neg_FIN056 hs.ne', hg2]
    ring
  · rw [hg2]; exact ratioDeriv2_neg sStar hs
  · rw [hder, deriv_psiDeriv_FIN056]
    refine second_pos_FIN056 hs hsd ?_
    rw [abs_of_pos (hs.trans hstp)]; exact hstp
  · intro t ht
    rcases lt_or_gt_of_ne ht with h1 | h1
    · exact hanti (Set.mem_Iic.mpr h1.le) (Set.mem_Iic.mpr le_rfl) h1
    · exact hB (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h1.le) h1
  · have := hanti (Set.mem_Iic.mpr (by linarith : -sStar ≤ tp)) (Set.mem_Iic.mpr le_rfl)
      (by linarith : -sStar < tp)
    linarith

end DGPS.FiniteN
