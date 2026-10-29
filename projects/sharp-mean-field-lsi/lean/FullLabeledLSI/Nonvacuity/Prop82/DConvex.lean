import Mathlib

/-!
# Lane D: half-turn averaging on the unit interval (pure real analysis)

`σ(t) = (f(t) + f(t + 1/2)) / 2` for a smooth positive 1-periodic `f`.
-/

open MeasureTheory intervalIntegral InformationTheory
open scoped ContDiff

namespace SharpLSI.FL.Prop82

lemma shift_half_integral {g : ℝ → ℝ} (_hc : Continuous g) (hp : Function.Periodic g 1) :
    ∫ t in (0 : ℝ)..1, g (t + 1 / 2) = ∫ t in (0 : ℝ)..1, g t := by
  rw [intervalIntegral.integral_comp_add_right g (1 / 2 : ℝ)]
  have := hp.intervalIntegral_add_eq (1 / 2 : ℝ) 0
  simp only [zero_add] at this
  rw [show (0 : ℝ) + 1 / 2 = 1 / 2 by norm_num, show (1 : ℝ) + 1 / 2 = 1 / 2 + 1 by norm_num, this]

lemma deriv_periodic_aux {f : ℝ → ℝ} (hper : ∀ t, f (t + 1) = f t) (t : ℝ) :
    deriv f (t + 1) = deriv f t := by
  have h := deriv_comp_add_const (f := f) (a := (1 : ℝ)) (x := t)
  have e : (fun x => f (x + 1)) = f := funext hper
  rw [e] at h
  exact h.symm

lemma sigma_hasDeriv {f : ℝ → ℝ} (hs : ContDiff ℝ ∞ f) (t : ℝ) :
    HasDerivAt (fun u => (f u + f (u + 1 / 2)) / 2)
      ((deriv f t + deriv f (t + 1 / 2)) / 2) t := by
  have hd : Differentiable ℝ f := hs.differentiable (by simp)
  have h1 : HasDerivAt f (deriv f t) t := (hd t).hasDerivAt
  have h2 : HasDerivAt (fun u => f (u + 1 / 2)) (deriv f (t + 1 / 2)) t :=
    ((hd (t + 1 / 2)).hasDerivAt).comp_add_const t (1 / 2)
  exact (h1.add h2).div_const 2

lemma titu {a b c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ((a + b) / 2) ^ 2 / ((c + d) / 2) ≤ (a ^ 2 / c + b ^ 2 / d) / 2 := by
  have hcd : 0 < c + d := by linarith
  rw [div_le_iff₀ (by linarith)]
  have : (a ^ 2 / c + b ^ 2 / d) / 2 * ((c + d) / 2) - ((a + b) / 2) ^ 2
      = (a * d - b * c) ^ 2 / (4 * c * d) := by
    field_simp
    ring
  have h2 : 0 ≤ (a * d - b * c) ^ 2 / (4 * c * d) := by positivity
  linarith

/-- Fisher information is convex under half-turn averaging (and translation invariant). -/
theorem fisher_half_average_le {f : ℝ → ℝ} (hs : ContDiff ℝ ∞ f) (hpos : ∀ t, 0 < f t)
    (hper : ∀ t, f (t + 1) = f t) :
    ∫ t in (0 : ℝ)..1, deriv (fun u => (f u + f (u + 1 / 2)) / 2) t ^ 2 /
        ((f t + f (t + 1 / 2)) / 2) ≤
      ∫ t in (0 : ℝ)..1, deriv f t ^ 2 / f t := by
  have hfc : Continuous f := hs.continuous
  have hdc : Continuous (deriv f) := hs.continuous_deriv (by simp)
  have hGc : Continuous (fun t => deriv f t ^ 2 / f t) :=
    (hdc.pow 2).div hfc (fun t => (hpos t).ne')
  have hGp : Function.Periodic (fun t => deriv f t ^ 2 / f t) 1 := by
    intro t
    simp only [deriv_periodic_aux hper, hper]
  have hG2c : Continuous (fun t => deriv f (t + 1 / 2) ^ 2 / f (t + 1 / 2)) :=
    hGc.comp (continuous_id.add continuous_const)
  have hL : Continuous (fun t => deriv (fun u => (f u + f (u + 1 / 2)) / 2) t ^ 2 /
        ((f t + f (t + 1 / 2)) / 2)) := by
    have hder : ∀ t, deriv (fun u => (f u + f (u + 1 / 2)) / 2) t =
        (deriv f t + deriv f (t + 1 / 2)) / 2 := fun t => (sigma_hasDeriv hs t).deriv
    simp_rw [hder]
    refine (((hdc.add (hdc.comp (continuous_id.add continuous_const))).div_const 2).pow 2).div
      ((hfc.add (hfc.comp (continuous_id.add continuous_const))).div_const 2) ?_
    intro t; have := hpos t; have := hpos (t + 1 / 2); positivity
  have key : ∫ t in (0 : ℝ)..1, deriv (fun u => (f u + f (u + 1 / 2)) / 2) t ^ 2 /
        ((f t + f (t + 1 / 2)) / 2) ≤
      ∫ t in (0 : ℝ)..1, ((deriv f t ^ 2 / f t + deriv f (t + 1 / 2) ^ 2 / f (t + 1 / 2)) / 2) := by
    apply intervalIntegral.integral_mono_on zero_le_one
      (hL.intervalIntegrable _ _)
      (((hGc.add hG2c).div_const 2).intervalIntegrable _ _)
    intro t _
    rw [(sigma_hasDeriv hs t).deriv]
    exact titu (hpos t) (hpos _)
  refine key.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hGc.intervalIntegrable _ _)
    (hG2c.intervalIntegrable _ _)]
  have := shift_half_integral hGc hGp
  rw [this]
  ring

/-- Half-turn averaging loses at most `log 2` of relative entropy. -/
theorem klFun_le_half_average_add_log_two_aux {f : ℝ → ℝ} (hs : ContDiff ℝ ∞ f)
    (hpos : ∀ t, 0 < f t) (hper : ∀ t, f (t + 1) = f t)
    (hmass : ∫ t in (0 : ℝ)..1, f t = 1) :
    ∫ t in (0 : ℝ)..1, klFun (f t) ≤
      ∫ t in (0 : ℝ)..1, klFun ((f t + f (t + 1 / 2)) / 2) + Real.log 2 := by
  have hfc : Continuous f := hs.continuous
  have hfp : Function.Periodic f 1 := hper
  have hsh : Continuous (fun t => f (t + 1 / 2)) := hfc.comp (continuous_id.add continuous_const)
  set σ : ℝ → ℝ := fun t => (f t + f (t + 1 / 2)) / 2 with hσ
  have hσc : Continuous σ := (hfc.add hsh).div_const 2
  have hσpos : ∀ t, 0 < σ t := fun t => by
    have := hpos t; have := hpos (t + 1 / 2); simp only [hσ]; positivity
  have hLc : Continuous (fun t => Real.log (σ t)) :=
    hσc.log (fun t => (hσpos t).ne')
  have hmass2 : ∫ t in (0 : ℝ)..1, f (t + 1 / 2) = 1 := by
    rw [shift_half_integral hfc hfp, hmass]
  have hmassσ : ∫ t in (0 : ℝ)..1, σ t = 1 := by
    simp only [hσ]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hfc.intervalIntegrable _ _)
      (hsh.intervalIntegrable _ _), hmass, hmass2]
    norm_num
  have hkl : ∀ g : ℝ → ℝ, Continuous g → (∀ t, 0 < g t) → ∫ t in (0 : ℝ)..1, g t = 1 →
      ∫ t in (0 : ℝ)..1, klFun (g t) = ∫ t in (0 : ℝ)..1, g t * Real.log (g t) := by
    intro g hg hgp hgm
    have hc1 : Continuous (fun t => g t * Real.log (g t)) :=
      hg.mul (hg.log (fun t => (hgp t).ne'))
    have : (fun t => klFun (g t)) = fun t => g t * Real.log (g t) - g t + 1 := by
      funext t; rw [InformationTheory.klFun_apply]; ring
    rw [this, intervalIntegral.integral_add (by exact (hc1.sub hg).intervalIntegrable _ _)
      (by exact intervalIntegrable_const), intervalIntegral.integral_sub
      (hc1.intervalIntegrable _ _) (hg.intervalIntegrable _ _), hgm]
    simp
  rw [hkl f hfc hpos hmass]
  have hklc : Continuous (fun t => klFun (σ t)) := continuous_klFun.comp hσc
  have e : ∫ t in (0 : ℝ)..1, (klFun ((f t + f (t + 1 / 2)) / 2) + Real.log 2) =
      (∫ t in (0 : ℝ)..1, σ t * Real.log (σ t)) + Real.log 2 := by
    have e0 : ∫ t in (0 : ℝ)..1, (klFun ((f t + f (t + 1 / 2)) / 2) + Real.log 2) =
        ∫ t in (0 : ℝ)..1, (klFun (σ t) + Real.log 2) := rfl
    rw [e0, intervalIntegral.integral_add (hklc.intervalIntegrable _ _) intervalIntegrable_const,
      hkl σ hσc hσpos hmassσ]
    simp
  rw [e]
  -- step 1
  have hfl : Continuous (fun t => f t * Real.log (f t)) :=
    hfc.mul (hfc.log (fun t => (hpos t).ne'))
  have hfL : Continuous (fun t => f t * Real.log (σ t)) := hfc.mul hLc
  have hf2 : Continuous (fun t => f t * Real.log 2) := hfc.mul continuous_const
  have step1 : ∫ t in (0 : ℝ)..1, f t * Real.log (f t) ≤
      ∫ t in (0 : ℝ)..1, (f t * Real.log 2 + f t * Real.log (σ t)) := by
    apply intervalIntegral.integral_mono_on zero_le_one (hfl.intervalIntegrable _ _)
      ((hf2.add hfL).intervalIntegrable _ _)
    intro t _
    have h1 : f t ≤ 2 * σ t := by
      have := hpos (t + 1 / 2); simp only [hσ]; linarith
    have h2 : Real.log (f t) ≤ Real.log 2 + Real.log (σ t) := by
      rw [← Real.log_mul (by norm_num) (hσpos t).ne']
      exact Real.log_le_log (hpos t) h1
    show f t * Real.log (f t) ≤ f t * Real.log 2 + f t * Real.log (σ t)
    nlinarith [mul_le_mul_of_nonneg_left h2 (hpos t).le]
  rw [intervalIntegral.integral_add (hf2.intervalIntegrable _ _)
    (hfL.intervalIntegrable _ _), intervalIntegral.integral_mul_const, hmass, one_mul] at step1
  -- step 2: ∫ f log σ = ∫ σ log σ
  have hσhalf : ∀ t, σ (t + 1 / 2) = σ t := fun t => by
    show (f (t + 1 / 2) + f (t + 1 / 2 + 1 / 2)) / 2 = (f t + f (t + 1 / 2)) / 2
    rw [show t + 1 / 2 + 1 / 2 = t + 1 by ring, hper]
    ring
  have hσone : ∀ t, σ (t + 1) = σ t := fun t => by
    rw [show t + 1 = (t + 1 / 2) + 1 / 2 by ring, hσhalf, hσhalf]
  have hper2 : Function.Periodic (fun t => f t * Real.log (σ t)) 1 := by
    intro t
    simp only [hper, hσone]
  have h1 : ∀ t, σ t * Real.log (σ t) = (f t * Real.log (σ t) +
      (fun s => f s * Real.log (σ s)) (t + 1 / 2)) / 2 := by
    intro t
    show σ t * Real.log (σ t) = (f t * Real.log (σ t) + f (t + 1 / 2) * Real.log (σ (t + 1 / 2))) / 2
    rw [hσhalf t]
    have e : σ t = (f t + f (t + 1 / 2)) / 2 := rfl
    rw [e]
    ring
  have hS : ∫ t in (0 : ℝ)..1, σ t * Real.log (σ t) = ∫ t in (0 : ℝ)..1, f t * Real.log (σ t) := by
    rw [intervalIntegral.integral_congr (g := fun t => (f t * Real.log (σ t) +
      (fun s => f s * Real.log (σ s)) (t + 1 / 2)) / 2) (fun t _ => h1 t)]
    have hshc : Continuous (fun t => (fun s => f s * Real.log (σ s)) (t + 1 / 2)) :=
      hfL.comp (continuous_id.add continuous_const)
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hfL.intervalIntegrable _ _)
      (hshc.intervalIntegrable _ _), shift_half_integral hfL hper2]
    ring
  rw [hS]
  linarith

/-- Parenthesised form: the integral of `klFun σ`, plus `log 2`. -/
theorem klFun_le_half_average_add_log_two {f : ℝ → ℝ} (hs : ContDiff ℝ ∞ f)
    (hpos : ∀ t, 0 < f t) (hper : ∀ t, f (t + 1) = f t)
    (hmass : ∫ t in (0 : ℝ)..1, f t = 1) :
    ∫ t in (0 : ℝ)..1, klFun (f t) ≤
      (∫ t in (0 : ℝ)..1, klFun ((f t + f (t + 1 / 2)) / 2)) + Real.log 2 := by
  have h := klFun_le_half_average_add_log_two_aux hs hpos hper hmass
  have hc : Continuous fun t => klFun ((f t + f (t + 1 / 2)) / 2) :=
    continuous_klFun.comp (((hs.continuous).add
      (hs.continuous.comp (continuous_id.add continuous_const))).div_const 2)
  rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _)
    (intervalIntegrable_const)] at h
  simpa using h

end SharpLSI.FL.Prop82

