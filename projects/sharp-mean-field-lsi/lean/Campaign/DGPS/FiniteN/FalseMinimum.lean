import DGPS.FiniteN.ScalarFoldFIN056
import DGPS.FiniteN.QuarticSaddle
import DGPS.Examples.AttractiveXYTilt

/-!
# FIN076: false minimum roots and the exact barrier

Fix `κ > 2` and `0 < h < h_c(κ)` in the scalar cosine model `scalarCosine κ h` (FIN055), with the
auxiliary potential `ψ_h(t) = (t - h)²/(2κ) - log I₀(t)` (`DGPS.Models.scalarPsi`, FIN056) and
the von Mises laws `q_t = xyLaw_EX023 t` (EX023), whose free energy in the scalar cosine model is
`F_h(q_t) = t g(t) - log I₀(t) - h g(t) - κ g(t)²/2` with `g = I₁/I₀`.

* `ψ' = (t - h)/κ - g` has `ψ'' = 1/κ - g'`, which is positive for `|t| > s_*` and negative for
  `|t| < s_*` (`g'` is even and strictly decreasing on `[0, ∞)`).  Together with `ψ'(-s_*) =
  (h_c - h)/κ > 0`, `ψ'(0) = -h/κ < 0`, `ψ'(s_*) = -(h_c + h)/κ < 0` and `ψ'(±∞) = ±∞` the
  intermediate value theorem gives exactly three critical points `a < -s_* < m < 0 < s_* < p`
  (`a = -s₂`, `m = -s₁`, `p = t₊`).
* `a` is a strict local minimum, `m` a strict local maximum, and `p` a nondegenerate strict global
  minimum of `ψ`; the global comparison uses the reflection identity `ψ(-t) = ψ(t) + 2 t h/κ`.
* At a critical `t` one has `F_h(q_t) = ψ_h(t) = κ g(t)²/2 - log I₀(t)`, so the barrier
  `B = ψ(m) - ψ(a) = F_h(q_m) - F_h(q_a)` is explicit.  The gap `Δ_- = ψ(a) - ψ(p)` is a different
  positive number.
* For `h = 1` and `κ = 5/g(4)` (the quartic member of FIN065) one has `s₂ = 4`.

The main theorem is `DGPS.FiniteN.false_minimum_roots_and_exact_barrier`.
-/

open Filter Topology

namespace DGPS.FiniteN.FalseMinimumFIN076

open DGPS.Models DGPS.Circle.BesselMoments DGPS.Circle.BesselConcavity
open DGPS.Circle.BesselMonotonicity DGPS.FiniteN.ScalarFoldFIN056
open DGPS.Examples.AttractiveXYTilt

section Calculus

variable {κ h s : ℝ}

theorem besselRatio_zero_FIN076 : besselRatio 0 = 0 := by
  have := besselRatio_neg 0
  rw [neg_zero] at this
  linarith

theorem psiDeriv_at_neg_FIN076 (hκ : 0 < κ) :
    psiDerivFIN056 κ h (-s) = (κ * besselRatio s - s - h) / κ := by
  unfold psiDerivFIN056
  rw [besselRatio_neg]
  field_simp
  ring

theorem psiDeriv_at_pos_FIN076 (hκ : 0 < κ) :
    psiDerivFIN056 κ h s = (s - h - κ * besselRatio s) / κ := by
  unfold psiDerivFIN056
  field_simp

theorem psiDeriv_at_zero_FIN076 : psiDerivFIN056 κ h 0 = -h / κ := by
  unfold psiDerivFIN056
  rw [besselRatio_zero_FIN076]
  ring

theorem psiDeriv_strictMonoOn_left_FIN076 (hs : 0 < s) (hsd : ratioDeriv s = 1 / κ) :
    StrictMonoOn (psiDerivFIN056 κ h) (Set.Iic (-s)) := by
  refine strictMonoOn_of_deriv_pos (convex_Iic (-s))
    (continuous_psiDeriv_FIN056 κ h).continuousOn ?_
  intro x hx
  rw [interior_Iic] at hx
  rw [deriv_psiDeriv_FIN056]
  refine second_pos_FIN056 hs hsd ?_
  have : x < -s := hx
  rw [abs_of_neg (by linarith)]
  linarith

theorem psiDeriv_strictAntiOn_mid_FIN076 (hs : 0 < s) (hsd : ratioDeriv s = 1 / κ) :
    StrictAntiOn (psiDerivFIN056 κ h) (Set.Icc (-s) s) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc (-s) s)
    (continuous_psiDeriv_FIN056 κ h).continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [deriv_psiDeriv_FIN056]
  refine second_neg_FIN056 hs hsd ?_
  rw [abs_lt]
  exact hx

/-- The three roots of `ψ'` and the sign pattern `- + - +` between them. -/
theorem three_roots_FIN076 (hκ : 0 < κ) (hs : 0 < s) (hsd : ratioDeriv s = 1 / κ)
    (hh0 : 0 < h) (hhc : h < κ * besselRatio s - s) :
    ∃ a m p : ℝ, a < -s ∧ -s < m ∧ m < 0 ∧ s < p ∧
      psiDerivFIN056 κ h a = 0 ∧ psiDerivFIN056 κ h m = 0 ∧ psiDerivFIN056 κ h p = 0 ∧
      (∀ t, t < a → psiDerivFIN056 κ h t < 0) ∧
      (∀ t, a < t → t < m → 0 < psiDerivFIN056 κ h t) ∧
      (∀ t, m < t → t < p → psiDerivFIN056 κ h t < 0) ∧
      (∀ t, p < t → 0 < psiDerivFIN056 κ h t) := by
  have hcont := continuous_psiDeriv_FIN056 κ h
  have hL := psiDeriv_strictMonoOn_left_FIN076 (κ := κ) (h := h) hs hsd
  have hM := psiDeriv_strictAntiOn_mid_FIN076 (κ := κ) (h := h) hs hsd
  have hR := psiDeriv_strictMonoOn_FIN056 (κ := κ) (h := h) hs hsd
  have fneg : 0 < psiDerivFIN056 κ h (-s) := by
    rw [psiDeriv_at_neg_FIN076 hκ]
    exact div_pos (by linarith) hκ
  have fzero : psiDerivFIN056 κ h 0 < 0 := by
    rw [psiDeriv_at_zero_FIN076]
    exact div_neg_of_neg_of_pos (by linarith) hκ
  have fs : psiDerivFIN056 κ h s < 0 := by
    rw [psiDeriv_at_pos_FIN076 hκ]
    exact div_neg_of_neg_of_pos (by linarith) hκ
  -- the left root
  have hfB : psiDerivFIN056 κ h (-(s + κ)) < 0 := by
    unfold psiDerivFIN056
    rw [besselRatio_neg]
    have h1 := besselRatio_lt_one (s + κ)
    have h2 : 1 < (s + κ + h) / κ := by
      rw [lt_div_iff₀ hκ]; linarith
    have h3 : (-(s + κ) - h) / κ = -((s + κ + h) / κ) := by ring
    linarith
  obtain ⟨a, ha, hfa⟩ := intermediate_value_Icc (show -(s + κ) ≤ -s by linarith)
    hcont.continuousOn (Set.mem_Icc.mpr ⟨hfB.le, fneg.le⟩)
  have has : a < -s := by
    rcases ha.2.eq_or_lt with h' | h'
    · rw [h'] at hfa; linarith
    · exact h'
  -- the middle root
  obtain ⟨m, hm, hfm⟩ := intermediate_value_Icc' (show -s ≤ 0 by linarith)
    hcont.continuousOn (Set.mem_Icc.mpr ⟨fzero.le, fneg.le⟩)
  have hm1 : -s < m := by
    rcases hm.1.eq_or_lt with h' | h'
    · rw [← h'] at hfm; linarith
    · exact h'
  have hm2 : m < 0 := by
    rcases hm.2.eq_or_lt with h' | h'
    · rw [h'] at hfm; linarith
    · exact h'
  -- the right root
  set b : ℝ := max s (h + 2 * κ) with hb
  have hbs : s ≤ b := le_max_left _ _
  have hbh : h + 2 * κ ≤ b := le_max_right _ _
  have hfb : 0 < psiDerivFIN056 κ h b := by
    unfold psiDerivFIN056
    have h1 := besselRatio_lt_one b
    have h2 : 2 ≤ (b - h) / κ := by
      rw [le_div_iff₀ hκ]; linarith
    linarith
  obtain ⟨p, hp, hfp⟩ := intermediate_value_Icc hbs hcont.continuousOn
    (Set.mem_Icc.mpr ⟨fs.le, hfb.le⟩)
  have hps : s < p := by
    rcases hp.1.eq_or_lt with h' | h'
    · rw [← h'] at hfp; linarith
    · exact h'
  refine ⟨a, m, p, has, hm1, hm2, hps, hfa, hfm, hfp, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have := hL (Set.mem_Iic.mpr (by linarith)) (Set.mem_Iic.mpr has.le) ht
    rwa [hfa] at this
  · intro t hat htm
    by_cases hts : t ≤ -s
    · have := hL (Set.mem_Iic.mpr has.le) (Set.mem_Iic.mpr hts) hat
      rwa [hfa] at this
    · have hts' : -s < t := lt_of_not_ge hts
      have := hM (Set.mem_Icc.mpr ⟨hts'.le, by linarith⟩)
        (Set.mem_Icc.mpr ⟨hm1.le, by linarith⟩) htm
      rwa [hfm] at this
  · intro t hmt htp
    by_cases hts : t ≤ s
    · have := hM (Set.mem_Icc.mpr ⟨hm1.le, by linarith⟩)
        (Set.mem_Icc.mpr ⟨by linarith, hts⟩) hmt
      rwa [hfm] at this
    · have hts' : s < t := lt_of_not_ge hts
      have := hR (Set.mem_Ici.mpr hts'.le) (Set.mem_Ici.mpr hps.le) htp
      rwa [hfp] at this
  · intro t hpt
    have := hR (Set.mem_Ici.mpr hps.le) (Set.mem_Ici.mpr (hps.le.trans hpt.le)) hpt
    rwa [hfp] at this

end Calculus

section Energy

/-- Reflection identity `ψ(-t) = ψ(t) + 2 t h / κ`. -/
theorem scalarPsi_neg_FIN076 {κ : ℝ} (hκ : 0 < κ) (h t : ℝ) :
    scalarPsi κ h (-t) = scalarPsi κ h t + 2 * t * h / κ := by
  unfold scalarPsi
  rw [besselI_neg]
  simp only [pow_zero, one_mul]
  field_simp
  ring

/-- At a critical point, `ψ(t) = κ g(t)²/2 - log I₀(t)`. -/
theorem scalarPsi_critical_FIN076 {κ h t : ℝ} (hκ : 0 < κ) (ht : psiDerivFIN056 κ h t = 0) :
    scalarPsi κ h t = κ * besselRatio t ^ 2 / 2 - Real.log (besselI 0 t) := by
  have e : t - h = κ * besselRatio t := by
    unfold psiDerivFIN056 at ht
    have : (t - h) / κ = besselRatio t := by linarith
    rw [div_eq_iff hκ.ne', mul_comm] at this
    exact this
  unfold scalarPsi
  rw [e]
  field_simp

/-- At a negative critical point `-s`, the same value in terms of `g(s)` and `I₀(s)`. -/
theorem scalarPsi_critical_neg_FIN076 {κ h s : ℝ} (hκ : 0 < κ)
    (ht : psiDerivFIN056 κ h (-s) = 0) :
    scalarPsi κ h (-s) = κ * besselRatio s ^ 2 / 2 - Real.log (besselI 0 s) := by
  rw [scalarPsi_critical_FIN076 hκ ht, besselRatio_neg, besselI_neg]
  simp

theorem freeEnergy_xyLaw_FIN076 (κ h t : ℝ) :
    DGPS.freeEnergy (scalarCosine κ h) (xyLaw_EX023 t) =
      ((t * besselRatio t - Real.log (besselI 0 t) - h * besselRatio t -
        κ * besselRatio t ^ 2 / 2 : ℝ) : EReal) := by
  have hm : ∫ x, scalarCos x ∂(xyLaw_EX023 t : MeasureTheory.Measure (DGPS.Torus 1)) =
      besselRatio t := by
    have := law_cos_EX023 t
    rw [DGPS.Examples.AttractiveXY.xyZ1] at this
    simpa [scalarCos, DGPS.Examples.AttractiveXY.xyMode_apply] using this
  rw [scalarCosine_freeEnergy, hm]
  obtain ⟨hf, he⟩ := law_entropy_EX023 t
  rw [← EReal.coe_ennreal_toReal hf, he, ← EReal.coe_add]
  congr 1
  ring

/-- **Gauge identity.**  At a critical point `t` of `ψ_h`, `F_h(q_t) = ψ_h(t)`. -/
theorem freeEnergy_xyLaw_critical_FIN076 {κ h t : ℝ} (hκ : 0 < κ)
    (ht : psiDerivFIN056 κ h t = 0) :
    DGPS.freeEnergy (scalarCosine κ h) (xyLaw_EX023 t) = ((scalarPsi κ h t : ℝ) : EReal) := by
  have e : t - h = κ * besselRatio t := by
    unfold psiDerivFIN056 at ht
    have : (t - h) / κ = besselRatio t := by linarith
    rw [div_eq_iff hκ.ne', mul_comm] at this
    exact this
  rw [freeEnergy_xyLaw_FIN076, scalarPsi_critical_FIN076 hκ ht]
  congr 1
  linear_combination (besselRatio t) * e

end Energy

section Main

/-- The conclusion of FIN076 for the data `(κ, h)` and the numbers `s₁, s₂, t₊`, with
`ψ = scalarPsi κ h`:

* the fixed-point equations `κ g(s₁) - s₁ = h`, `κ g(s₂) - s₂ = h`, `t₊ = h + κ g(t₊)`;
* the critical points of `ψ` are exactly `-s₂`, `-s₁`, `t₊`;
* `-s₂` is a strict local minimum with `ψ''(-s₂) > 0`, `-s₁` a strict local maximum with
  `ψ''(-s₁) < 0`, and `t₊` a nondegenerate (`ψ''(t₊) > 0`) strict global minimum;
* the barrier `B = ψ(-s₁) - ψ(-s₂)` is positive, equals
  `κ [g(s₁)² - g(s₂)²]/2 - log I₀(s₁) + log I₀(s₂)` and equals `F_h(q_{-s₁}) - F_h(q_{-s₂})` for
  the von Mises laws `q_t`;
* the remote-to-global gap `Δ_- = ψ(-s₂) - ψ(t₊) = F_h(q_{-s₂}) - F_h(q_{t₊})` is positive. -/
def FalseMinimumGeometryFIN076 (κ h s1 s2 tp : ℝ) : Prop :=
  κ * besselRatio s1 - s1 = h ∧ κ * besselRatio s2 - s2 = h ∧ tp = h + κ * besselRatio tp ∧
  (∀ t : ℝ, deriv (scalarPsi κ h) t = 0 ↔ t = -s2 ∨ t = -s1 ∨ t = tp) ∧
  (0 < deriv (deriv (scalarPsi κ h)) (-s2) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, t ≠ -s2 → |t - -s2| < ε →
      scalarPsi κ h (-s2) < scalarPsi κ h t) ∧
  (deriv (deriv (scalarPsi κ h)) (-s1) < 0 ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, t ≠ -s1 → |t - -s1| < ε →
      scalarPsi κ h t < scalarPsi κ h (-s1)) ∧
  (0 < deriv (deriv (scalarPsi κ h)) tp ∧
    ∀ t : ℝ, t ≠ tp → scalarPsi κ h tp < scalarPsi κ h t) ∧
  (0 < scalarPsi κ h (-s1) - scalarPsi κ h (-s2) ∧
    scalarPsi κ h (-s1) - scalarPsi κ h (-s2) =
      κ * (besselRatio s1 ^ 2 - besselRatio s2 ^ 2) / 2 - Real.log (besselI 0 s1) +
        Real.log (besselI 0 s2) ∧
    DGPS.freeEnergy (scalarCosine κ h) (xyLaw_EX023 (-s1)) -
        DGPS.freeEnergy (scalarCosine κ h) (xyLaw_EX023 (-s2)) =
      ((scalarPsi κ h (-s1) - scalarPsi κ h (-s2) : ℝ) : EReal)) ∧
  (0 < scalarPsi κ h (-s2) - scalarPsi κ h tp ∧
    DGPS.freeEnergy (scalarCosine κ h) (xyLaw_EX023 (-s2)) -
        DGPS.freeEnergy (scalarCosine κ h) (xyLaw_EX023 tp) =
      ((scalarPsi κ h (-s2) - scalarPsi κ h tp : ℝ) : EReal))

theorem general_FIN076 (κ h : ℝ) (hκ : 2 < κ) (hh0 : 0 < h) (hhc : h < scalarFoldField κ) :
    ∃ s1 s2 tp : ℝ, 0 < s1 ∧ s1 < scalarFoldPoint κ ∧ scalarFoldPoint κ < s2 ∧ 0 < tp ∧
      FalseMinimumGeometryFIN076 κ h s1 s2 tp := by
  have hκ0 : 0 < κ := by linarith
  obtain ⟨hs, hsd'⟩ := scalarFoldPoint_spec κ hκ
  have hsd : ratioDeriv (scalarFoldPoint κ) = 1 / κ := by rw [deriv_ratio] at hsd'; exact hsd'
  have hhc' : h < κ * besselRatio (scalarFoldPoint κ) - scalarFoldPoint κ := hhc
  obtain ⟨a, m, p, has, hm1, hm2, hps, hfa, hfm, hfp, S1, S2, S3, S4⟩ :=
    three_roots_FIN076 hκ0 hs hsd hh0 hhc'
  obtain ⟨s2, rfl⟩ : ∃ s2, a = -s2 := ⟨-a, (neg_neg a).symm⟩
  obtain ⟨s1, rfl⟩ : ∃ s1, m = -s1 := ⟨-m, (neg_neg m).symm⟩
  set sS := scalarFoldPoint κ with hsS
  have hs1 : 0 < s1 := by linarith
  have hs1' : s1 < sS := by linarith
  have hs2' : sS < s2 := by linarith
  have htp : 0 < p := by linarith
  have hder : deriv (scalarPsi κ h) = psiDerivFIN056 κ h := deriv_scalarPsi_FIN056 hκ0 h
  have hcont : Continuous (scalarPsi κ h) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_scalarPsi_FIN056 hκ0 h t).continuousAt
  have hdd : ∀ x, deriv (deriv (scalarPsi κ h)) x = 1 / κ - ratioDeriv x := by
    intro x; rw [hder, deriv_psiDeriv_FIN056]
  have P1 : StrictAntiOn (scalarPsi κ h) (Set.Iic (-s2)) := by
    refine strictAntiOn_of_deriv_neg (convex_Iic _) hcont.continuousOn ?_
    intro x hx
    rw [interior_Iic] at hx
    rw [hder]; exact S1 x hx
  have P2 : StrictMonoOn (scalarPsi κ h) (Set.Icc (-s2) (-s1)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont.continuousOn ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [hder]; exact S2 x hx.1 hx.2
  have P3 : StrictAntiOn (scalarPsi κ h) (Set.Icc (-s1) p) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont.continuousOn ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [hder]; exact S3 x hx.1 hx.2
  have P4 : StrictMonoOn (scalarPsi κ h) (Set.Ici p) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici _) hcont.continuousOn ?_
    intro x hx
    rw [interior_Ici] at hx
    rw [hder]; exact S4 x hx
  -- the global comparison
  have gl : ∀ u, -s1 ≤ u → u ≠ p → scalarPsi κ h p < scalarPsi κ h u := by
    intro u hu hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · exact P3 (Set.mem_Icc.mpr ⟨hu, h1.le⟩) (Set.mem_Icc.mpr ⟨by linarith, le_rfl⟩) h1
    · exact P4 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h1.le) h1
  have gl2 : ∀ t, t ≠ p → scalarPsi κ h p < scalarPsi κ h t := by
    intro t hne
    by_cases hmt : -s1 ≤ t
    · exact gl t hmt hne
    · have hlt : t < -s1 := lt_of_not_ge hmt
      have hrefl := scalarPsi_neg_FIN076 hκ0 h (-t)
      rw [neg_neg] at hrefl
      have hpos : 0 < 2 * -t * h / κ := by
        have : 0 < -t := by linarith
        positivity
      have hle : scalarPsi κ h p ≤ scalarPsi κ h (-t) := by
        rcases eq_or_ne (-t) p with h1 | h1
        · rw [h1]
        · exact (gl (-t) (by linarith) h1).le
      linarith
  have hcrit : ∀ t, psiDerivFIN056 κ h t = 0 ↔ t = -s2 ∨ t = -s1 ∨ t = p := by
    intro t
    constructor
    · intro h0
      by_contra hne
      push Not at hne
      obtain ⟨n1, n2, n3⟩ := hne
      rcases lt_or_gt_of_ne n1 with h1 | h1
      · exact (S1 t h1).ne h0
      · rcases lt_or_gt_of_ne n2 with h2 | h2
        · exact (S2 t h1 h2).ne' h0
        · rcases lt_or_gt_of_ne n3 with h3 | h3
          · exact (S3 t h2 h3).ne h0
          · exact (S4 t h3).ne' h0
    · rintro (rfl | rfl | rfl)
      · exact hfa
      · exact hfm
      · exact hfp
  have hr1 : κ * besselRatio s1 - s1 = h := by
    have := hfm
    rw [psiDeriv_at_neg_FIN076 hκ0, div_eq_zero_iff] at this
    have := this.resolve_right hκ0.ne'
    linarith
  have hr2 : κ * besselRatio s2 - s2 = h := by
    have := hfa
    rw [psiDeriv_at_neg_FIN076 hκ0, div_eq_zero_iff] at this
    have := this.resolve_right hκ0.ne'
    linarith
  have hr3 : p = h + κ * besselRatio p := by
    have := hfp
    unfold psiDerivFIN056 at this
    have h2 : (p - h) / κ = besselRatio p := by linarith
    rw [div_eq_iff hκ0.ne', mul_comm] at h2
    linarith
  have hB : 0 < scalarPsi κ h (-s1) - scalarPsi κ h (-s2) := by
    have := P2 (Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩) (Set.mem_Icc.mpr ⟨by linarith, le_rfl⟩)
      (by linarith : -s2 < -s1)
    linarith
  have hD : 0 < scalarPsi κ h (-s2) - scalarPsi κ h p := by
    have := gl2 (-s2) (by linarith)
    linarith
  refine ⟨s1, s2, p, hs1, hs1', hs2', htp, hr1, hr2, hr3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t; rw [hder]; exact hcrit t
  · refine ⟨?_, -s1 - -s2, by linarith, ?_⟩
    · rw [hdd]
      refine second_pos_FIN056 hs hsd ?_
      rw [abs_neg, abs_of_pos (by linarith)]; exact hs2'
    · intro t hne hlt
      have hlt' := (abs_lt.mp hlt).2
      rcases lt_or_gt_of_ne hne with h1 | h1
      · exact P1 (Set.mem_Iic.mpr h1.le) (Set.mem_Iic.mpr le_rfl) h1
      · exact P2 (Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩) (Set.mem_Icc.mpr ⟨h1.le, by linarith⟩) h1
  · refine ⟨?_, min (-s1 - -s2) (p - -s1), lt_min (by linarith) (by linarith), ?_⟩
    · rw [hdd]
      refine second_neg_FIN056 hs hsd ?_
      rw [abs_neg, abs_of_pos hs1]; exact hs1'
    · intro t hne hlt
      have hlt1 := (abs_lt.mp (lt_of_lt_of_le hlt (min_le_left _ _))).1
      have hlt2 := (abs_lt.mp (lt_of_lt_of_le hlt (min_le_right _ _))).2
      rcases lt_or_gt_of_ne hne with h1 | h1
      · exact P2 (Set.mem_Icc.mpr ⟨by linarith, h1.le⟩) (Set.mem_Icc.mpr ⟨by linarith, le_rfl⟩) h1
      · exact P3 (Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩) (Set.mem_Icc.mpr ⟨h1.le, by linarith⟩) h1
  · refine ⟨?_, gl2⟩
    rw [hdd]
    refine second_pos_FIN056 hs hsd ?_
    rw [abs_of_pos htp]; exact hps
  · refine ⟨hB, ?_, ?_⟩
    · rw [scalarPsi_critical_neg_FIN076 hκ0 hfm, scalarPsi_critical_neg_FIN076 hκ0 hfa]
      ring
    · rw [freeEnergy_xyLaw_critical_FIN076 hκ0 hfm, freeEnergy_xyLaw_critical_FIN076 hκ0 hfa,
        ← EReal.coe_sub]
  · refine ⟨hD, ?_⟩
    rw [freeEnergy_xyLaw_critical_FIN076 hκ0 hfa, freeEnergy_xyLaw_critical_FIN076 hκ0 hfp,
      ← EReal.coe_sub]

end Main

section Explicit

/-- The explicit member `h = 1`, `κ = 5 / g(4)`: `κ > 2`, `h_c(κ) > 1`, `s_* < 4`, and the
remote minimum sits at `t_- = -4` (`s₂ = 4`). -/
theorem explicit_FIN076 :
    2 < quarticKappa ∧ 1 < scalarFoldField quarticKappa ∧ scalarFoldPoint quarticKappa < 4 ∧
      ∃ s1 tp : ℝ, 0 < s1 ∧ s1 < scalarFoldPoint quarticKappa ∧ 0 < tp ∧
        FalseMinimumGeometryFIN076 quarticKappa 1 s1 4 tp := by
  have hb := DGPS.FiniteN.QuarticSaddle.quarticB_gt
  have hb67 : (6 / 7 : ℝ) < quarticB := lt_trans (by norm_num) hb
  have hb1 : quarticB < 1 := besselRatio_lt_one 4
  have hbpos : 0 < quarticB := by linarith
  have hκ2 : 2 < quarticKappa := by
    show (2 : ℝ) < 5 / quarticB
    rw [lt_div_iff₀ hbpos]; linarith
  have hκ0 : 0 < quarticKappa := by linarith
  have hκb : quarticKappa * quarticB = 5 := by
    show 5 / quarticB * quarticB = 5
    field_simp
  have hinv : 1 / quarticKappa = quarticB / 5 := by
    field_simp
    linarith
  obtain ⟨hs, hsd'⟩ := scalarFoldPoint_spec quarticKappa hκ2
  have hlt4 : scalarFoldPoint quarticKappa < 4 := by
    by_contra hge
    push Not at hge
    have h1 := strictAntiOn_ratioDeriv.antitoneOn (Set.mem_Ici.mpr (by norm_num : (0 : ℝ) ≤ 4))
      (Set.mem_Ici.mpr hs.le) hge
    rw [deriv_ratio] at hsd'
    rw [hsd', hinv] at h1
    have h2 := DGPS.FiniteN.QuarticSaddle.deriv_besselRatio_four
    rw [deriv_ratio] at h2
    rw [h2] at h1
    nlinarith
  have hc1 : 1 < scalarFoldField quarticKappa := by
    have := scalarFoldPoint_max quarticKappa hκ2 4 (by norm_num) (ne_of_gt hlt4)
    have e : quarticKappa * besselRatio 4 = 5 := hκb
    unfold scalarFoldField
    linarith
  obtain ⟨s1, s2, tp, h1, h2, h3, h4, hG⟩ := general_FIN076 quarticKappa 1 hκ2 one_pos hc1
  have hcrit : deriv (scalarPsi quarticKappa 1) (-4) = 0 := by
    rw [deriv_scalarPsi_FIN056 hκ0]
    unfold psiDerivFIN056
    rw [besselRatio_neg]
    have e : quarticKappa * besselRatio 4 = 5 := hκb
    have e2 : (-4 - 1) / quarticKappa = -(5 / quarticKappa) := by ring
    have e3 : 5 / quarticKappa = besselRatio 4 := by
      rw [div_eq_iff hκ0.ne']; linarith
    rw [e2, e3]; ring
  have hs2 : s2 = 4 := by
    rcases (hG.2.2.2.1 (-4)).1 hcrit with h5 | h5 | h5
    · linarith
    · linarith
    · linarith
  subst hs2
  exact ⟨hκ2, hc1, hlt4, s1, tp, h1, h2, h4, hG⟩

end Explicit

end DGPS.FiniteN.FalseMinimumFIN076

namespace DGPS.FiniteN

open DGPS.Models DGPS.FiniteN.FalseMinimumFIN076

/-- **FIN076.** False minimum roots and the exact barrier.

Fix `κ > 2` and `0 < h < h_c(κ)` (`h_c = scalarFoldField κ`, `s_* = scalarFoldPoint κ`) in the
scalar cosine model `scalarCosine κ h`, with `ψ = scalarPsi κ h` and `q_t = xyLaw_EX023 t` the von
Mises law.  Then there are `0 < s₁ < s_* < s₂` and `t₊ > 0` such that (see
`FalseMinimumGeometryFIN076`): the critical points of `ψ` are exactly `t_- = -s₂ < t_b = -s₁ < 0
< t₊`; `t_-` is a strict local minimum, `t_b` a strict local maximum and `t₊` the unique
nondegenerate global minimum of `ψ`; and the barrier `B = ψ(t_b) - ψ(t_-) > 0` equals
`F_h(q_{t_b}) - F_h(q_{t_-})` and `κ [g(s₁)² - g(s₂)²]/2 - log I₀(s₁) + log I₀(s₂)`, while the
remote-to-global gap `Δ_- = ψ(t_-) - ψ(t₊) = F_h(q_{t_-}) - F_h(q_{t₊}) > 0`.

For the explicit member `h = 1`, `κ = 5 / g(4)` (`quarticKappa`) the hypotheses hold
(`κ > 2`, `1 < h_c(κ)`, `s_* < 4`) and `s₂ = 4`, i.e. `t_- = -4` and
`B = κ [g(s₁)² - g(4)²]/2 - log I₀(s₁) + log I₀(4)`. -/
theorem false_minimum_roots_and_exact_barrier :
    (∀ κ h : ℝ, 2 < κ → 0 < h → h < scalarFoldField κ →
      ∃ s1 s2 tp : ℝ, 0 < s1 ∧ s1 < scalarFoldPoint κ ∧ scalarFoldPoint κ < s2 ∧ 0 < tp ∧
        FalseMinimumGeometryFIN076 κ h s1 s2 tp) ∧
    (2 < quarticKappa ∧ 1 < scalarFoldField quarticKappa ∧ scalarFoldPoint quarticKappa < 4 ∧
      ∃ s1 tp : ℝ, 0 < s1 ∧ s1 < scalarFoldPoint quarticKappa ∧ 0 < tp ∧
        FalseMinimumGeometryFIN076 quarticKappa 1 s1 4 tp) :=
  ⟨fun κ h hκ hh0 hhc => general_FIN076 κ h hκ hh0 hhc, explicit_FIN076⟩

end DGPS.FiniteN
