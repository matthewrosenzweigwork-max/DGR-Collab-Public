import DGPS.Circle.BesselMonotonicity

/-!
# Critical radial Hessian coercivity (FIN027)

For `ψ(r) = r²/4 - log I₀(r)`, writing `I₀(t) = Q(t²/4)` with the entire series
`Q(s) = ∑ s^j/(j!)²`, the radial potential is `H(‖z‖²/4)` with `H(s) = s - log Q(s)`.
Its Hessian is `((1-R)/2)‖v‖² - (R'/4)⟨z,v⟩²` with `R = Q'/Q` antitone, and the EX003 ratio
inequalities give `1 - R(s) ≥ 2 c₀ min(4s, 1)`.
-/
open scoped ContDiff
open MeasureTheory Real Filter Topology
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments

namespace DGPS.FiniteN

/-- the entire function `Q(s) = ∑ s^j/(j!)²`, so that `I₀(t) = Q(t²/4)` -/
noncomputable def critQ (s : ℝ) : ℝ := ∑' j : ℕ, s ^ j / ((j.factorial : ℝ) ^ 2)

theorem critQ_eq_ofScalars :
    critQ = FormalMultilinearSeries.ofScalarsSum (E := ℝ) (fun j : ℕ => 1 / ((j.factorial : ℝ) ^ 2)) := by
  funext s
  simp [critQ, FormalMultilinearSeries.ofScalars_sum_eq, div_eq_mul_inv, mul_comm]

theorem critQ_contDiff : ContDiff ℝ ∞ critQ := by
  have hr : (FormalMultilinearSeries.ofScalars ℝ (fun j : ℕ => 1 / ((j.factorial : ℝ) ^ 2))).radius = ⊤ := by
    apply FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto
    · exact Filter.Eventually.of_forall fun n => by positivity
    · have : Tendsto (fun n : ℕ => (1 : ℝ) / ((n:ℝ) + 1) ^ 2) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := (1:ℝ))).div_atTop
          (tendsto_atTop_mono (fun n : ℕ => by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
            tendsto_natCast_atTop_atTop (f := fun n : ℕ => (n:ℝ)) (g := fun n : ℕ => ((n:ℝ)+1)^2))
      refine this.congr fun n => ?_
      simp [Nat.factorial_succ]
      field_simp
      rw [abs_of_nonneg (by positivity)]
  have h := (FormalMultilinearSeries.ofScalars ℝ (fun j : ℕ => 1 / ((j.factorial : ℝ) ^ 2))).analyticOnNhd
  rw [hr] at h
  rw [critQ_eq_ofScalars]
  refine AnalyticOnNhd.contDiff (fun x _ => h x (by simp))

/-- `A = Q'` -/
noncomputable def critA (s : ℝ) : ℝ := deriv critQ s

theorem critQ_hasDerivAt (s : ℝ) : HasDerivAt critQ (critA s) s :=
  (critQ_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt

theorem critA_contDiff : ContDiff ℝ ∞ critA := by
  have := (contDiff_infty_iff_deriv.mp critQ_contDiff).2
  exact this

theorem besselI_zero_eq_critQ (t : ℝ) : besselI 0 t = critQ (t ^ 2 / 4) :=
  ((DGPS.Examples.bessel_integral_series_and_moment_derivatives.2.2.1) t).tsum_eq.symm

theorem critQ_eq_besselI (s : ℝ) (hs : 0 ≤ s) : critQ s = besselI 0 (2 * Real.sqrt s) := by
  rw [besselI_zero_eq_critQ]
  congr 1
  rw [mul_pow, Real.sq_sqrt hs]; ring

theorem critQ_pos (s : ℝ) (hs : 0 ≤ s) : 0 < critQ s := by
  rw [critQ_eq_besselI s hs]
  exact DGPS.Examples.bessel_integral_series_and_moment_derivatives.2.1 _

theorem critA_eq_pos (s : ℝ) (hs : 0 < s) : critA s = 2 * besselI1Over (2 * Real.sqrt s) := by
  set t := 2 * Real.sqrt s with ht
  have htpos : 0 < t := by positivity
  have hts : t ^ 2 / 4 = s := by rw [ht, mul_pow, Real.sq_sqrt hs.le]; ring
  have h1 : HasDerivAt (fun x : ℝ => critQ (x ^ 2 / 4)) (critA s * (t / 2)) t := by
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 4) (t / 2) t := by
      have := (hasDerivAt_pow 2 t).div_const 4
      convert this using 1; ring
    have h3 := (critQ_hasDerivAt (t ^ 2 / 4)).comp t h2
    rw [hts] at h3
    exact h3
  have h4 : HasDerivAt (besselI 0) (besselI 1 t) t :=
    DGPS.Examples.bessel_integral_series_and_moment_derivatives.2.2.2.2.2.2.2.2.2.1 t
  have h5 : besselI 0 = fun x : ℝ => critQ (x ^ 2 / 4) := funext besselI_zero_eq_critQ
  rw [h5] at h4
  have h6 := h1.unique h4
  have h7 : besselI1Over t = besselI 1 t / t :=
    (DGPS.Examples.bessel_integral_series_and_moment_derivatives.2.2.2.2.2.2.1).2.2 t htpos.ne'
  rw [h7, ← h6]
  field_simp

theorem critA_eq (s : ℝ) (hs : 0 ≤ s) : critA s = 2 * besselI1Over (2 * Real.sqrt s) := by
  have hc1 : Continuous critA := critA_contDiff.continuous
  have hc2 : Continuous fun s : ℝ => 2 * besselI1Over (2 * Real.sqrt s) :=
    continuous_const.mul (continuous_besselI1Over.comp (continuous_const.mul Real.continuous_sqrt))
  have : Set.EqOn critA (fun s : ℝ => 2 * besselI1Over (2 * Real.sqrt s)) (Set.Ioi 0) :=
    fun x hx => critA_eq_pos x hx
  have h := this.closure hc1 hc2
  rw [closure_Ioi] at h
  exact h hs

theorem hasSum_critQ (s : ℝ) (hs : 0 ≤ s) :
    HasSum (fun j : ℕ => s ^ j / ((j.factorial : ℝ) ^ 2)) (critQ s) := by
  have h := DGPS.Examples.bessel_integral_series_and_moment_derivatives.2.2.1 (2 * Real.sqrt s)
  have e : (2 * Real.sqrt s) ^ 2 / 4 = s := by rw [mul_pow, Real.sq_sqrt hs]; ring
  rw [e] at h
  rwa [← critQ_eq_besselI s hs] at h

theorem hasSum_critA (s : ℝ) (hs : 0 ≤ s) :
    HasSum (fun j : ℕ => s ^ j / ((j.factorial : ℝ) * ((j + 1).factorial : ℝ))) (critA s) := by
  have h := DGPS.Examples.bessel_integral_series_and_moment_derivatives.2.2.2.2.2.1 (2 * Real.sqrt s)
  have e : (2 * Real.sqrt s) ^ 2 / 4 = s := by rw [mul_pow, Real.sq_sqrt hs]; ring
  rw [e] at h
  rw [critA_eq s hs]
  have := h.mul_left 2
  convert this using 1
  funext j
  ring

theorem critQ_le_exp (s : ℝ) (hs : 0 ≤ s) : critQ s ≤ Real.exp s := by
  rcases hs.eq_or_lt with h | h
  · subst h
    have := (hasSum_critQ 0 le_rfl).tsum_eq
    have h0 : critQ 0 = 1 := by
      have h1 : critQ 0 = ∑' j : ℕ, (0:ℝ) ^ j / ((j.factorial : ℝ) ^ 2) := rfl
      rw [h1, tsum_eq_single 0 (fun j hj => by simp [hj])]
      simp
    simp [h0]
  · rw [critQ_eq_besselI s hs]
    have := DGPS.Examples.strict_bessel_ratio_inequalities.2.1 (2 * Real.sqrt s) (by positivity)
    have e : (2 * Real.sqrt s) ^ 2 / 4 = s := by rw [mul_pow, Real.sq_sqrt hs]; ring
    rw [e] at this
    exact this.le

theorem critQ_sub_critA_ge (s : ℝ) (hs : 0 ≤ s) : s / 2 ≤ critQ s - critA s := by
  have h := (hasSum_critQ s hs).sub (hasSum_critA s hs)
  have hnn : ∀ j : ℕ, 0 ≤ s ^ j / ((j.factorial : ℝ) ^ 2) - s ^ j / ((j.factorial : ℝ) * ((j + 1).factorial : ℝ)) := by
    intro j
    rw [Nat.factorial_succ]
    push_cast
    have hf : (0:ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
    have : s ^ j / ((j.factorial : ℝ) * (((j:ℝ) + 1) * j.factorial)) ≤ s ^ j / ((j.factorial : ℝ) ^ 2) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j), sq_nonneg (j.factorial : ℝ)]
    linarith
  have := sum_le_hasSum {1} (fun j _ => hnn j) h
  rw [Finset.sum_singleton] at this
  have e : s ^ 1 / (((Nat.factorial 1 : ℕ) : ℝ) ^ 2) - s ^ 1 / (((Nat.factorial 1 : ℕ) : ℝ) * ((Nat.factorial (1 + 1) : ℕ) : ℝ)) = s / 2 := by
    norm_num [Nat.factorial]; ring
  rw [e] at this
  exact this


/-- `R = A / Q` -/
noncomputable def critR (s : ℝ) : ℝ := critA s / critQ s

/-- the constant `c₀ = (16 e^{1/4})⁻¹` -/
noncomputable def criticalC0 : ℝ := (16 * Real.exp (1 / 4))⁻¹

theorem criticalC0_pos : 0 < criticalC0 := by unfold criticalC0; positivity

theorem critR_ratio (s : ℝ) (hs : 0 < s) :
    besselRatio (2 * Real.sqrt s) / (2 * Real.sqrt s) = critR s / 2 := by
  set t := 2 * Real.sqrt s with ht
  have htpos : 0 < t := by positivity
  have h7 : besselI1Over t = besselI 1 t / t :=
    (DGPS.Examples.bessel_integral_series_and_moment_derivatives.2.2.2.2.2.2.1).2.2 t htpos.ne'
  have hQ : critQ s = besselI 0 t := critQ_eq_besselI s hs.le
  have hA : critA s = 2 * besselI1Over t := critA_eq_pos s hs
  have h0 : 0 < besselI 0 t := DGPS.Examples.bessel_integral_series_and_moment_derivatives.2.1 t
  unfold critR besselRatio
  rw [hQ, hA, h7]
  field_simp

theorem critR_anti {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') : critR s' ≤ critR s := by
  rcases hss.eq_or_lt with h | h
  · rw [h]
  · have ht : 2 * Real.sqrt s < 2 * Real.sqrt s' := by
      have := Real.sqrt_lt_sqrt hs.le h
      linarith
    have := DGPS.Examples.strict_bessel_ratio_inequalities.2.2.1 (show 2 * Real.sqrt s ∈ Set.Ioi (0:ℝ) from by
      simp only [Set.mem_Ioi]; positivity) (show 2 * Real.sqrt s' ∈ Set.Ioi (0:ℝ) from by
      simp only [Set.mem_Ioi]; have := Real.sqrt_pos.2 (hs.trans h); linarith) ht
    simp only at this
    rw [critR_ratio s' (hs.trans h), critR_ratio s hs] at this
    linarith

theorem one_sub_critR_small (s : ℝ) (hs : 0 ≤ s) (h4 : s ≤ 1 / 4) :
    s / (2 * Real.exp (1 / 4)) ≤ 1 - critR s := by
  have hQ := critQ_pos s hs
  have hle : critQ s ≤ Real.exp (1 / 4) :=
    (critQ_le_exp s hs).trans (Real.exp_le_exp.2 h4)
  have hge := critQ_sub_critA_ge s hs
  have : 1 - critR s = (critQ s - critA s) / critQ s := by
    unfold critR; field_simp
  rw [this, div_le_div_iff₀ (by positivity) hQ]
  have he := Real.exp_pos (1 / 4)
  nlinarith

theorem one_sub_critR_big (s : ℝ) (h4 : 1 / 4 ≤ s) :
    1 / (8 * Real.exp (1 / 4)) ≤ 1 - critR s := by
  have h1 := one_sub_critR_small (1 / 4) (by norm_num) le_rfl
  have h2 := critR_anti (show (0:ℝ) < 1 / 4 by norm_num) h4
  have : (1 / 4 : ℝ) / (2 * Real.exp (1 / 4)) = 1 / (8 * Real.exp (1 / 4)) := by
    field_simp; ring
  linarith

theorem two_c0_min_le (s : ℝ) (hs : 0 ≤ s) :
    2 * criticalC0 * min (4 * s) 1 ≤ 1 - critR s := by
  have he := Real.exp_pos (1 / 4)
  rcases le_total s (1 / 4) with h | h
  · have := one_sub_critR_small s hs h
    have e : 2 * criticalC0 * min (4 * s) 1 = s / (2 * Real.exp (1 / 4)) := by
      rw [min_eq_left (by linarith)]
      unfold criticalC0; field_simp; ring
    linarith
  · have := one_sub_critR_big s h
    have e : 2 * criticalC0 * min (4 * s) 1 = 1 / (8 * Real.exp (1 / 4)) := by
      rw [min_eq_right (by linarith)]
      unfold criticalC0; field_simp; ring
    linarith


/-- `H(s) = s - log Q(s)`: the radial potential is `ψ(r) = H(r²/4)`. -/
noncomputable def critH (s : ℝ) : ℝ := s - Real.log (critQ s)

theorem critH_hasDerivAt (s : ℝ) (hs : 0 ≤ s) : HasDerivAt critH (1 - critR s) s := by
  have h := (hasDerivAt_id' s).sub ((critQ_hasDerivAt s).log (critQ_pos s hs).ne')
  have e : critH = fun x => x - Real.log (critQ x) := rfl
  rw [e]
  convert h using 1
  rfl

theorem critR_differentiableAt (s : ℝ) (hs : 0 ≤ s) : DifferentiableAt ℝ critR s :=
  (critA_contDiff.differentiable (by simp) s).div
    (critQ_contDiff.differentiable (by simp) s) (critQ_pos s hs).ne'

section Hess
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasFDerivAt_comp_normSq {F : ℝ → ℝ} {F' : ℝ} (z : E) (h : HasDerivAt F F' (‖z‖ ^ 2 / 4)) :
    HasFDerivAt (fun x : E => F (‖x‖ ^ 2 / 4)) ((F' / 2) • innerSL ℝ z) z := by
  have h1 : HasFDerivAt (fun x : E => ‖x‖ ^ 2 / 4) ((1 / 2 : ℝ) • innerSL ℝ z) z := by
    have := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt).const_mul (1 / 4 : ℝ)
    have e : (fun x : E => ‖x‖ ^ 2 / 4) = fun x : E => (1 / 4 : ℝ) * ‖x‖ ^ 2 := by
      funext x; ring
    rw [e]
    convert this using 1
    ext y
    simp
    ring
  have := h.comp_hasFDerivAt z h1
  exact this.congr_fderiv (by rw [smul_smul]; congr 1; ring)

/-- the radial potential on an inner product space -/
noncomputable def critPot (z : E) : ℝ := critH (‖z‖ ^ 2 / 4)

theorem critPot_contDiff : ContDiff ℝ ∞ (critPot (E := E)) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  have h1 : ContDiffAt ℝ ∞ critH (‖z‖ ^ 2 / 4) := by
    unfold critH
    exact contDiffAt_id.sub (ContDiffAt.log critQ_contDiff.contDiffAt
      (critQ_pos _ (by positivity)).ne')
  have h2 : ContDiff ℝ ∞ (fun x : E => ‖x‖ ^ 2 / 4) :=
    (contDiff_norm_sq ℝ).div_const 4
  exact h1.comp z h2.contDiffAt

theorem critPot_hasFDerivAt (z : E) :
    HasFDerivAt critPot (((1 - critR (‖z‖ ^ 2 / 4)) / 2) • innerSL ℝ z) z :=
  hasFDerivAt_comp_normSq z (critH_hasDerivAt _ (by positivity))

theorem fderiv_critPot : fderiv ℝ (critPot (E := E)) =
    fun z => ((1 - critR (‖z‖ ^ 2 / 4)) / 2) • innerSL ℝ z :=
  funext fun z => (critPot_hasFDerivAt z).fderiv

/-- the Hessian quadratic form of the radial potential -/
theorem critPot_hessian (z v : E) :
    fderiv ℝ (fderiv ℝ (critPot (E := E))) z v v =
      ((1 - critR (‖z‖ ^ 2 / 4)) / 2) * ‖v‖ ^ 2
        - (deriv critR (‖z‖ ^ 2 / 4) / 4) * (inner ℝ z v) ^ 2 := by
  rw [fderiv_critPot]
  have hd : HasDerivAt critR (deriv critR (‖z‖ ^ 2 / 4)) (‖z‖ ^ 2 / 4) :=
    (critR_differentiableAt _ (by positivity)).hasDerivAt
  have hc : HasFDerivAt (fun x : E => (1 - critR (‖x‖ ^ 2 / 4)) / 2)
      (((-(deriv critR (‖z‖ ^ 2 / 4)) / 2) / 2) • innerSL ℝ z) z := by
    refine hasFDerivAt_comp_normSq (F := fun s => (1 - critR s) / 2) z ?_
    exact ((hasDerivAt_const _ (1:ℝ)).sub hd).div_const 2 |>.congr_deriv (by ring)
  have hg := (innerSL ℝ (E := E)).hasFDerivAt (x := z)
  have h2 := hc.smul hg
  have h3 : HasFDerivAt (fun x : E => ((1 - critR (‖x‖ ^ 2 / 4)) / 2) • innerSL ℝ x) _ z := h2
  rw [h3.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  have e1 : (innerSL ℝ v) v = ‖v‖ ^ 2 := by simp
  have e2 : (innerSL ℝ z) v = inner ℝ z v := by simp
  rw [e1, e2]
  ring


theorem critR_deriv_nonpos (s : ℝ) (hs : 0 < s) : deriv critR s ≤ 0 := by
  have hacc : AccPt s (𝓟 (Set.Ioi (0:ℝ))) := by
    have := (PerfectSpace.univ_preperfect (α := ℝ)).open_inter (isOpen_Ioi (a := (0:ℝ)))
    rw [Set.inter_univ] at this
    exact this s hs
  have hd := ((critR_differentiableAt s hs.le).hasDerivAt).hasDerivWithinAt (s := Set.Ioi 0)
  exact hd.nonpos_of_antitoneOn hacc (fun x hx y _ hxy => critR_anti hx hxy)

theorem critPot_hessian_ge (z v : E) :
    criticalC0 * min (‖z‖ ^ 2) 1 * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (critPot (E := E))) z v v := by
  rw [critPot_hessian]
  have h1 := two_c0_min_le (‖z‖ ^ 2 / 4) (by positivity)
  have e : min (4 * (‖z‖ ^ 2 / 4)) 1 = min (‖z‖ ^ 2) 1 := by congr 1; ring
  rw [e] at h1
  have h2 : 0 ≤ -(deriv critR (‖z‖ ^ 2 / 4) / 4) * (inner ℝ z v) ^ 2 := by
    rcases eq_or_ne z 0 with h | h
    · simp [h]
    · have := critR_deriv_nonpos (‖z‖ ^ 2 / 4) (by have := norm_pos_iff.2 h; positivity)
      have : 0 ≤ -(deriv critR (‖z‖ ^ 2 / 4) / 4) := by linarith
      positivity
  have h3 : criticalC0 * min (‖z‖ ^ 2) 1 * ‖v‖ ^ 2 ≤ ((1 - critR (‖z‖ ^ 2 / 4)) / 2) * ‖v‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖v‖)
    nlinarith
  linarith

end Hess

theorem critH_zero : critH 0 = 0 := by
  have h0 : critQ 0 = 1 := by
    have h1 : critQ 0 = ∑' j : ℕ, (0:ℝ) ^ j / ((j.factorial : ℝ) ^ 2) := rfl
    rw [h1, tsum_eq_single 0 (fun j hj => by simp [hj])]
    simp
  simp [critH, h0]

theorem monoOn_of_hasDerivAt {f f' : ℝ → ℝ} {a b : ℝ}
    (h : ∀ x, a ≤ x → x ≤ b → HasDerivAt f (f' x) x)
    (hn : ∀ x, a ≤ x → x ≤ b → 0 ≤ f' x) : MonotoneOn f (Set.Icc a b) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (fun x hx => (h x hx.1 hx.2).continuousAt.continuousWithinAt)
    (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Icc] at hx
    exact (h x hx.1.le hx.2.le).differentiableAt.differentiableWithinAt
  · rw [interior_Icc] at hx
    rw [(h x hx.1.le hx.2.le).deriv]
    exact hn x hx.1.le hx.2.le

theorem critH_ge_small (s : ℝ) (hs : 0 ≤ s) (h : s ≤ 1 / 4) :
    4 * criticalC0 * s ^ 2 ≤ critH s := by
  have hder : ∀ x, 0 ≤ x → HasDerivAt critH (1 - critR x) x := fun x hx => critH_hasDerivAt x hx
  have hm := monoOn_of_hasDerivAt (f := fun x => critH x - 4 * criticalC0 * x ^ 2)
    (f' := fun x => (1 - critR x) - 8 * criticalC0 * x) (a := 0) (b := 1 / 4)
    (fun x hx _ => by
      have := (hder x hx).sub (((hasDerivAt_pow 2 x).const_mul (4 * criticalC0)))
      convert this using 1; simp; ring)
    (fun x hx hx4 => by
      have := two_c0_min_le x hx
      rw [min_eq_left (by linarith)] at this
      nlinarith [criticalC0_pos])
  have := hm (a := 0) (by simp) (by constructor <;> linarith) hs
  simp only [critH_zero] at this
  nlinarith

/-- `H` is bounded below by a piecewise quadratic/linear function. -/
theorem critH_ge (s : ℝ) (hs : 0 ≤ s) :
    criticalC0 * min (4 * s ^ 2) s ≤ critH s := by
  have hc := criticalC0_pos
  have hder : ∀ x, 0 ≤ x → HasDerivAt critH (1 - critR x) x := fun x hx => critH_hasDerivAt x hx
  rcases le_total s (1 / 4) with h | h
  · have e : min (4 * s ^ 2) s = 4 * s ^ 2 := by
      apply min_eq_left; nlinarith
    rw [e]
    have := critH_ge_small s hs h
    linarith
  · have hm := monoOn_of_hasDerivAt (f := fun x => critH x - 2 * criticalC0 * x)
      (f' := fun x => (1 - critR x) - 2 * criticalC0) (a := 1 / 4) (b := s)
      (fun x hx _ => by
        have := (hder x (by linarith)).sub ((hasDerivAt_id' x).const_mul (2 * criticalC0))
        convert this using 1; simp)
      (fun x hx _ => by
        have := two_c0_min_le x (by linarith)
        rw [min_eq_right (by linarith)] at this
        linarith)
    have := hm (a := 1 / 4) (Set.mem_Icc.2 ⟨le_rfl, h⟩) (Set.mem_Icc.2 ⟨h, le_rfl⟩) h
    have hb := critH_ge_small (1 / 4) (by norm_num) le_rfl
    have e : min (4 * s ^ 2) s = s := by
      apply min_eq_right; nlinarith
    rw [e]
    simp only at this
    nlinarith

theorem tail_le (c : ℕ → ℝ) (S s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hS : HasSum (fun j : ℕ => s ^ j * c j) S) (hc : ∀ j, 0 ≤ c j)
    (hc2 : ∀ j, 2 ≤ j → c j ≤ (1 / 2 : ℝ) ^ j) :
    0 ≤ S - c 0 - s * c 1 ∧ S - c 0 - s * c 1 ≤ s ^ 2 / 2 := by
  have h := (hasSum_nat_add_iff' 2).2 hS
  have e : ∑ i ∈ Finset.range 2, s ^ i * c i = c 0 + s * c 1 := by
    simp [Finset.sum_range_succ]
  rw [e] at h
  have e2 : S - (c 0 + s * c 1) = S - c 0 - s * c 1 := by ring
  rw [e2] at h
  refine ⟨h.nonneg (fun n => by have := hc (n + 2); positivity), ?_⟩
  have hr : s / 2 < 1 := by linarith
  have hg := (hasSum_geometric_of_lt_one (by positivity : 0 ≤ s / 2) hr).mul_left ((s / 2) ^ 2)
  have hle := hasSum_le (fun n : ℕ => ?_) h hg
  · have h2 : (1 - s / 2)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc S - c 0 - s * c 1 ≤ (s / 2) ^ 2 * (1 - s / 2)⁻¹ := hle
      _ ≤ (s / 2) ^ 2 * 2 := by gcongr
      _ = s ^ 2 / 2 := by ring
  · calc s ^ (n + 2) * c (n + 2) ≤ s ^ (n + 2) * (1 / 2 : ℝ) ^ (n + 2) :=
          mul_le_mul_of_nonneg_left (hc2 _ (by omega)) (by positivity)
      _ = (s / 2) ^ 2 * (s / 2) ^ n := by rw [← mul_pow, pow_add]; ring

theorem two_pow_le_fact_sq (j : ℕ) (hj : 2 ≤ j) : (2 : ℕ) ^ j ≤ (j.factorial) ^ 2 := by
  induction j, hj using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [Nat.factorial_succ, mul_pow, pow_succ]
    have : 2 ≤ (n + 1) ^ 2 := by nlinarith
    calc 2 ^ n * 2 ≤ n.factorial ^ 2 * 2 := by gcongr
      _ ≤ n.factorial ^ 2 * (n + 1) ^ 2 := by gcongr
      _ = _ := by ring

theorem inv_fact_sq_le (j : ℕ) (hj : 2 ≤ j) : ((j.factorial : ℝ) ^ 2)⁻¹ ≤ (1 / 2 : ℝ) ^ j := by
  have h := two_pow_le_fact_sq j hj
  have h' : (2 : ℝ) ^ j ≤ (j.factorial : ℝ) ^ 2 := by exact_mod_cast h
  rw [one_div, inv_pow]
  exact inv_anti₀ (by positivity) h'

theorem inv_fact_fact_le (j : ℕ) (hj : 2 ≤ j) :
    ((j.factorial : ℝ) * ((j + 1).factorial : ℝ))⁻¹ ≤ (1 / 2 : ℝ) ^ j := by
  refine le_trans ?_ (inv_fact_sq_le j hj)
  apply inv_anti₀ (by positivity)
  rw [Nat.factorial_succ]; push_cast
  have : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  nlinarith [mul_pos hf hf]

theorem one_sub_critR_taylor (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |1 - critR s - s / 2| ≤ 2 * s ^ 2 := by
  have hQ : HasSum (fun j : ℕ => s ^ j * ((j.factorial : ℝ) ^ 2)⁻¹) (critQ s) := by
    simpa [div_eq_mul_inv] using hasSum_critQ s hs0
  have hA : HasSum (fun j : ℕ => s ^ j * ((j.factorial : ℝ) * ((j + 1).factorial : ℝ))⁻¹) (critA s) := by
    simpa [div_eq_mul_inv] using hasSum_critA s hs0
  obtain ⟨q0, q1⟩ := tail_le (fun j => ((j.factorial : ℝ) ^ 2)⁻¹) _ s hs0 hs1 hQ
    (fun j => by positivity) (fun j hj => inv_fact_sq_le j hj)
  obtain ⟨a0, a1⟩ := tail_le (fun j => ((j.factorial : ℝ) * ((j + 1).factorial : ℝ))⁻¹) _ s hs0 hs1 hA
    (fun j => by positivity) (fun j hj => inv_fact_fact_le j hj)
  norm_num [Nat.factorial] at q0 q1 a0 a1
  have hQpos := critQ_pos s hs0
  have e : 1 - critR s - s / 2 = (critQ s - critA s - s * critQ s / 2) / critQ s := by
    unfold critR; field_simp
  rw [e, abs_le]
  have hQ1 : 1 ≤ critQ s := by nlinarith
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  constructor
  · rw [le_div_iff₀ hQpos]
    nlinarith [mul_nonneg hs0 (sub_nonneg.2 q0), mul_nonneg hs2 (sub_nonneg.2 hQ1), mul_nonneg hs0 hs2]
  · rw [div_le_iff₀ hQpos]
    nlinarith [mul_nonneg hs0 (sub_nonneg.2 q0), mul_nonneg hs2 (sub_nonneg.2 hQ1), mul_nonneg hs0 hs2]

theorem critH_taylor (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |critH s - s ^ 2 / 4| ≤ 2 / 3 * s ^ 3 := by
  have hder : ∀ x, 0 ≤ x → HasDerivAt critH (1 - critR x) x := fun x hx => critH_hasDerivAt x hx
  have hK : ∀ x, 0 ≤ x → HasDerivAt (fun y => critH y - y ^ 2 / 4) ((1 - critR x) - x / 2) x := by
    intro x hx
    have := (hder x hx).sub ((hasDerivAt_pow 2 x).div_const 4)
    convert this using 1; simp; ring
  have hb : ∀ x, 0 ≤ x → x ≤ 1 → |(1 - critR x) - x / 2| ≤ 2 * x ^ 2 := fun x h0 h1 => by
    have := one_sub_critR_taylor x h0 h1
    simpa [sub_sub] using this
  have m1 := monoOn_of_hasDerivAt (f := fun y => (critH y - y ^ 2 / 4) + 2 / 3 * y ^ 3)
    (f' := fun x => ((1 - critR x) - x / 2) + 2 * x ^ 2) (a := 0) (b := 1)
    (fun x hx _ => by
      have := (hK x hx).add ((hasDerivAt_pow 3 x).const_mul (2 / 3))
      convert this using 1; simp; ring)
    (fun x hx hx1 => by have := (abs_le.1 (hb x hx hx1)).1; linarith)
  have m2 := monoOn_of_hasDerivAt (f := fun y => 2 / 3 * y ^ 3 - (critH y - y ^ 2 / 4))
    (f' := fun x => 2 * x ^ 2 - ((1 - critR x) - x / 2)) (a := 0) (b := 1)
    (fun x hx _ => by
      have := ((hasDerivAt_pow 3 x).const_mul (2 / 3)).sub (hK x hx)
      convert this using 1; simp; ring)
    (fun x hx hx1 => by have := (abs_le.1 (hb x hx hx1)).2; linarith)
  have h1 := m1 (a := 0) (by simp) (Set.mem_Icc.2 ⟨hs0, hs1⟩) hs0
  have h2 := m2 (a := 0) (by simp) (Set.mem_Icc.2 ⟨hs0, hs1⟩) hs0
  simp only [critH_zero] at h1 h2
  norm_num at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- the radial profile `ψ(r) = r²/4 - log I₀(r)` -/
noncomputable def criticalPsi (r : ℝ) : ℝ := r ^ 2 / 4 - Real.log (besselI 0 r)

/-- the radial potential `z ↦ ψ(‖z‖)` on a real inner product space -/
noncomputable def criticalPotential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : E) : ℝ := criticalPsi ‖z‖

theorem criticalPsi_eq (r : ℝ) : criticalPsi r = critH (r ^ 2 / 4) := by
  unfold criticalPsi critH
  rw [besselI_zero_eq_critQ]

theorem criticalPotential_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    criticalPotential (E := E) = critPot := by
  funext z
  exact criticalPsi_eq _

/-- **Critical radial Hessian coercivity.** For `ψ(r) = r²/4 - log I₀(r)` and the radial
potential `z ↦ ψ(‖z‖)` on a real inner product space (in particular `ℝ²`): the potential is smooth,
its Hessian satisfies `D²ψ(‖z‖) ≥ c₀ min(‖z‖², 1) I` with `c₀ = (16 e^{1/4})⁻¹`,
`ψ(r) ≥ (c₀/12) min(r⁴, r²)`, the sole minimum is `ψ(0) = 0`, and `|ψ(r) - r⁴/64| ≤ r⁶/96`
on `[0,1]` (so `ψ(r) = r⁴/64 + O(r⁶)`). -/
theorem critical_radial_hessian_coercivity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] :
    ContDiff ℝ ∞ (criticalPotential (E := E)) ∧
    (∀ z v : E, (16 * Real.exp (1 / 4))⁻¹ * min (‖z‖ ^ 2) 1 * ‖v‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (criticalPotential (E := E))) z v v) ∧
    (∀ r : ℝ, 0 ≤ r → (16 * Real.exp (1 / 4))⁻¹ / 12 * min (r ^ 4) (r ^ 2) ≤ criticalPsi r) ∧
    criticalPsi 0 = 0 ∧
    (∀ r : ℝ, 0 < r → 0 < criticalPsi r) ∧
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 → |criticalPsi r - r ^ 4 / 64| ≤ r ^ 6 / 96) := by
  have hc := criticalC0_pos
  have growth : ∀ r : ℝ, 0 ≤ r → criticalC0 / 12 * min (r ^ 4) (r ^ 2) ≤ criticalPsi r := by
    intro r hr
    rw [criticalPsi_eq]
    have h := critH_ge (r ^ 2 / 4) (by positivity)
    rcases le_total (r ^ 4) (r ^ 2) with h4 | h4
    · have e1 : min (r ^ 4) (r ^ 2) = r ^ 4 := min_eq_left h4
      have e2 : min (4 * (r ^ 2 / 4) ^ 2) (r ^ 2 / 4) = r ^ 4 / 4 := by
        rw [min_eq_left (by nlinarith)]; ring
      rw [e2] at h; rw [e1]
      have : 0 ≤ criticalC0 * r ^ 4 := by positivity
      nlinarith
    · have e1 : min (r ^ 4) (r ^ 2) = r ^ 2 := min_eq_right h4
      have e2 : min (4 * (r ^ 2 / 4) ^ 2) (r ^ 2 / 4) = r ^ 2 / 4 := by
        rw [min_eq_right (by nlinarith)]
      rw [e2] at h; rw [e1]
      have : 0 ≤ criticalC0 * r ^ 2 := by positivity
      nlinarith
  refine ⟨?_, ?_, growth, ?_, ?_, ?_⟩
  · rw [criticalPotential_eq]; exact critPot_contDiff
  · intro z v
    rw [criticalPotential_eq]
    exact critPot_hessian_ge z v
  · rw [criticalPsi_eq]; simp [critH_zero]
  · intro r hr
    have := growth r hr.le
    have : 0 < min (r ^ 4) (r ^ 2) := lt_min (by positivity) (by positivity)
    have : 0 < criticalC0 / 12 * min (r ^ 4) (r ^ 2) := by positivity
    linarith
  · intro r h0 h1
    rw [criticalPsi_eq]
    have := critH_taylor (r ^ 2 / 4) (by positivity) (by nlinarith)
    have e1 : (r ^ 2 / 4) ^ 2 / 4 = r ^ 4 / 64 := by ring
    have e2 : 2 / 3 * (r ^ 2 / 4) ^ 3 = r ^ 6 / 96 := by ring
    rwa [e1, e2] at this

end DGPS.FiniteN
