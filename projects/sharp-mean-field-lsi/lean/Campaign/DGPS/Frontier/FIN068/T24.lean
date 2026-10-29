import DGPS.Frontier.FIN068.T07
import DGPS.Frontier.FIN068.T23

/-!
Task id and title: FIN068.24, Curve Taylor bound and composition (module
`DGPS.Frontier.FIN068.T24`).

Provides:
* `DGPS.Frontier.FIN068.fin068_24_curve_taylor_bound_composition`: there are `δu, δz > 0` and a
  function `a`, `C^∞` on `Set.Ioo (-δz) δz`, which is the critical curve of FIN068.07 with
  `a'(0) = d / (32 A)` (FIN068.23), and there are `r` with `0 < r < δz` and `M ≥ 0` such that
  `|a''| ≤ M` on `Set.Icc (-r) r`, `|a z - d z / (32 A)| ≤ M z^2 / 2` for `|z| ≤ r`, and, for
  `x₀ y = -4 + a (y^2)`: `x₀` is `C^∞` on `|y| < √r`, even, satisfies the critical equation
  `ψ_x (x₀ y, y) = 0` for `|y| < √r`, and `|x₀ y - (-4 + d y^2 / (32 A))| ≤ M y^4 / 2` there.
  Here `A = b/5 - g'(4)` and `d = b - 4 g'(4)` are written out, `ψ_x (x, y)` is
  `deriv (fun x => quarticPsi_FIN066 !₂[x, y]) x`.
* Helper declarations, all with suffix `_FIN06824` and not part of the interface:
  `taylor_pos_FIN06824` (second-order bound on `[0, r]` from a bound on the first derivative),
  `taylor_symm_FIN06824` (the same on `[-r, r]`), `taylor_curve_FIN06824` (the bound for a
  function `C^∞` on an open interval with `|a''| ≤ M` on a closed symmetric subinterval),
  `exists_radius_FIN06824` (choice of `r`), `critical_equation_FIN06824` (the critical equation of
  the composed curve).

Proof: with `c = a'(0)` and `h z = a z - c z`, the function `h` has `h 0 = 0` and
`|h'(t)| = |a'(t) - a'(0)| ≤ M |t|` (mean value inequality for `a'`, whose derivative `a''` is
bounded by `M`). Then `z ↦ M z^2 / 2 ± h z` is monotone on `[0, r]` and antitone on `[-r, 0]`, which
gives `|h z| ≤ M z^2 / 2`. The bound `M` exists by compactness of `[-r, r]` and continuity of
`a''` there. The radius `r` is chosen below `δz`, below `1`, and so that `|a z| < 1` for `|z| ≤ r`.
For `|y| < √r` the squared radius `y^2` lies in `[0, r) ⊆ [-r, r]`. The critical equation uses
FIN068.04 (`ψ(-4 + u, y) = J(u, y^2)` for `|u| < 1`, `y^2 < 1`): the function `x ↦ ψ(x, y)` agrees
with `x ↦ J(x + 4, y^2)` on the open set `|x + 4| < 1`, which contains `x₀ y`, so the derivative is
`J_u(a (y^2), y^2) = 0` by FIN068.07 with no extra factor.

R5 notes:
* No hypothesis is added. The statement is closed (existential in `δu, δz, a, r, M`). The curve data
  (smoothness, `a 0 = 0`, root equation, uniqueness, `a'(0)`) is carried through unchanged from
  `fin068_23_first_derivative_critical_curve`, so that the `a` of the Taylor bound is the curve.
* "A closed symmetric interval inside the domain of `a`" is `Set.Icc (-r) r` with `r < δz`, inside
  the open interval `Set.Ioo (-δz) δz` on which `a` is `C^∞`. The specification's `δ_z` of the
  Taylor estimate is called `r` here, to keep it apart from the `δz` of the curve. `M_a` is `M`, and
  `a''` is `deriv (deriv a)`; `0 ≤ M` is stated and `|a''| ≤ M` on `Set.Icc (-r) r` is stated.
* Non-literal proof route: the specification asks for the scalar Taylor formula with integral
  remainder. The proof here obtains the same bound `|a z - a'(0) z| ≤ M z^2 / 2` from monotonicity
  of `z ↦ M z^2 / 2 ± (a z - a'(0) z)` and the mean value inequality for `a'`, which avoids the
  integral remainder and `iteratedDerivWithin`. The conclusion is the one specified.
* `r` also satisfies `|a z| < 1` for `|z| ≤ r` and `r < 1` internally, which is what FIN068.04 needs
  (`|u| < 1`, `y^2 < 1`) to turn `ψ(-4 + u, y)` into `J(u, y^2)`. These bounds are not part of the
  conclusion. They are obtained by continuity of `a` at `0`, so `r` is smaller than the radius that
  the specification leaves unspecified.
* The first coordinate of `ψ` is read as the one-variable derivative `deriv (fun x => ψ !₂[x, y]) x`
  of the slice, as `J_u` is read in FIN068.05 and FIN068.07. The point `(x, y)` is the element
  `!₂[x, y]` of `EuclideanSpace ℝ (Fin 2)`, as in FIN068.04. `ψ` is `quarticPsi_FIN066`.
* "Smoothness" of `x₀` is `ContDiffOn ℝ ∞ x₀ (Set.Ioo (-√r) (√r))`, and "evenness" is stated for all
  real `y` as `-4 + a ((-y)^2) = -4 + a (y^2)` (the exact identity `(-y)^2 = y^2`, with `x₀`
  written out). The critical equation and the quartic error bound are stated for `|y| < √r`.
* "The displayed quartic error bound" is read as `x₀(y) = -4 + d y^2/(32 A) + O(y^4)` of the frozen
  informal statement, with the explicit constant `M y^4 / 2`: `|x₀ y - (-4 + d y^2 / (32 A))| ≤
  M y^4 / 2`. `A > 0` is not needed in this packet except through FIN068.23.
-/

open DGPS.Models DGPS.Circle.BesselMoments DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff Topology

namespace DGPS.Frontier.FIN068

/-- Second-order bound on `[0, r]`: if `h 0 = 0` and `|h'(t)| ≤ M t` on `[0, r]`, then
`|h z| ≤ M z^2 / 2` there. -/
lemma taylor_pos_FIN06824 {h : ℝ → ℝ} {r M : ℝ} (hd : ∀ t ∈ Set.Icc 0 r, DifferentiableAt ℝ h t)
    (hb : ∀ t ∈ Set.Icc 0 r, |deriv h t| ≤ M * t) (h0 : h 0 = 0) :
    ∀ z ∈ Set.Icc 0 r, |h z| ≤ M * z ^ 2 / 2 := by
  intro z hz
  have hder : ∀ t ∈ Set.Icc 0 r, ∀ s : ℝ,
      HasDerivAt (fun t : ℝ => M * t ^ 2 / 2 + s * h t) (M * t + s * deriv h t) t := by
    intro t ht s
    have h1 : HasDerivAt (fun t : ℝ => M * t ^ 2 / 2) (M * t) t := by
      have := ((hasDerivAt_pow 2 t).const_mul M).div_const 2
      convert this using 1
      ring
    exact h1.add ((hd t ht).hasDerivAt.const_mul s)
  have hmono : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      MonotoneOn (fun t : ℝ => M * t ^ 2 / 2 + s * h t) (Set.Icc 0 r) := by
    intro s hs
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 r) ?_ ?_ ?_
    · intro t ht
      exact (hder t ht s).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hder t (Set.Ioo_subset_Icc_self ht) s).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht' : t ∈ Set.Icc 0 r := Set.Ioo_subset_Icc_self ht
      rw [(hder t ht' s).deriv]
      have := abs_le.1 (hb t ht')
      rcases hs with rfl | rfl <;> nlinarith [this.1, this.2]
  have hzero : ∀ s : ℝ, (fun t : ℝ => M * t ^ 2 / 2 + s * h t) 0 = 0 := by
    intro s
    simp [h0]
  have hr : 0 ∈ Set.Icc 0 r := ⟨le_refl 0, hz.1.trans hz.2⟩
  have e1 := hmono 1 (Or.inl rfl) hr hz hz.1
  have e2 := hmono (-1) (Or.inr rfl) hr hz hz.1
  rw [hzero 1] at e1
  rw [hzero (-1)] at e2
  rw [abs_le]
  constructor <;> simp only [one_mul, neg_one_mul] at e1 e2 <;> linarith

/-- Second-order bound on `[-r, r]`: if `h 0 = 0` and `|h'(t)| ≤ M |t|` on `[-r, r]`, then
`|h z| ≤ M z^2 / 2` there. -/
lemma taylor_symm_FIN06824 {h : ℝ → ℝ} {r M : ℝ}
    (hd : ∀ t ∈ Set.Icc (-r) r, DifferentiableAt ℝ h t)
    (hb : ∀ t ∈ Set.Icc (-r) r, |deriv h t| ≤ M * |t|) (h0 : h 0 = 0) :
    ∀ z ∈ Set.Icc (-r) r, |h z| ≤ M * z ^ 2 / 2 := by
  intro z hz
  rcases le_total 0 z with hz0 | hz0
  · refine taylor_pos_FIN06824 (h := h) (r := r) (fun t ht => hd t ⟨by linarith [ht.1, hz.1, hz.2, ht.2], ht.2⟩)
      (fun t ht => ?_) h0 z ⟨hz0, hz.2⟩
    have := hb t ⟨by linarith [ht.1, ht.2, hz.1, hz.2], ht.2⟩
    rwa [abs_of_nonneg ht.1] at this
  · have hneg := taylor_pos_FIN06824 (h := fun t => h (-t)) (r := r) (M := M)
      (fun t ht => (hd (-t) ⟨by linarith [ht.2], by linarith [ht.1, ht.2]⟩).comp t
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => -t) t))
      (fun t ht => ?_) (by simpa using h0) (-z) ⟨by linarith, by linarith [hz.1]⟩
    · simpa using hneg
    · have hb' := hb (-t) ⟨by linarith [ht.2], by linarith [ht.1, ht.2]⟩
      rw [deriv_comp_neg, abs_neg]
      rwa [abs_neg, abs_of_nonneg ht.1] at hb'

/-- The Taylor bound for a function `a`, `C^∞` on an open interval `(-δ, δ)` with `a 0 = 0`, and
`|a''| ≤ M` on `[-r, r]`, `0 ≤ r < δ`. -/
lemma taylor_curve_FIN06824 {a : ℝ → ℝ} {δ r M : ℝ} (ha : ContDiffOn ℝ ∞ a (Set.Ioo (-δ) δ))
    (hr0 : 0 ≤ r) (hr : r < δ) (ha0 : a 0 = 0)
    (hM : ∀ z ∈ Set.Icc (-r) r, |deriv (deriv a) z| ≤ M) :
    ∀ z : ℝ, |z| ≤ r → |a z - deriv a 0 * z| ≤ M * z ^ 2 / 2 := by
  have hsub : Set.Icc (-r) r ⊆ Set.Ioo (-δ) δ := by
    intro t ht
    exact ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hr⟩
  have hopen : IsOpen (Set.Ioo (-δ) δ) := isOpen_Ioo
  have hda : ∀ t ∈ Set.Icc (-r) r, DifferentiableAt ℝ a t := fun t ht =>
    (ha.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds (hsub ht))
  have hd1 : ContDiffOn ℝ ∞ (deriv a) (Set.Ioo (-δ) δ) :=
    ha.deriv_of_isOpen hopen (by simp)
  have hdd : ∀ t ∈ Set.Icc (-r) r, DifferentiableAt ℝ (deriv a) t := fun t ht =>
    (hd1.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds (hsub ht))
  have hmem0 : (0 : ℝ) ∈ Set.Icc (-r) r := ⟨by linarith, hr0⟩
  have hlin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => deriv a 0 * t) (deriv a 0) t := fun t => by
    simpa using (hasDerivAt_id t).const_mul (deriv a 0)
  have hderiv : ∀ t ∈ Set.Icc (-r) r,
      deriv (fun t : ℝ => a t - deriv a 0 * t) t = deriv a t - deriv a 0 := fun t ht =>
    ((hda t ht).hasDerivAt.sub (hlin t)).deriv
  have key := taylor_symm_FIN06824 (h := fun t : ℝ => a t - deriv a 0 * t) (r := r) (M := M)
    (fun t ht => (hda t ht).sub (hlin t).differentiableAt)
    (fun t ht => by
      rw [hderiv t ht]
      have := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv a) (C := M)
        (s := Set.Icc (-r) r) hdd hM (convex_Icc _ _) hmem0 ht
      simpa [Real.norm_eq_abs] using this)
    (by simp [ha0])
  intro z hz
  exact key z (abs_le.1 hz)

/-- Choice of the radius: `r` with `0 < r`, `r < δ`, `r < 1`, and `|a z| < 1` for `|z| ≤ r`. -/
lemma exists_radius_FIN06824 {a : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (ha : ContDiffOn ℝ ∞ a (Set.Ioo (-δ) δ)) (ha0 : a 0 = 0) :
    ∃ r : ℝ, 0 < r ∧ r < δ ∧ r < 1 ∧ ∀ z : ℝ, |z| ≤ r → |a z| < 1 := by
  have hmem : Set.Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hδ
  have hcont : ContinuousAt a 0 :=
    (ha.continuousOn.continuousAt hmem)
  have hev : ∀ᶠ z in 𝓝 (0 : ℝ), |a z| < 1 := by
    refine (continuous_abs.continuousAt.comp hcont).eventually_lt continuousAt_const ?_
    simp [ha0]
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨min (min (δ / 2) (1 / 2)) (ε / 2), by positivity, ?_, ?_, fun z hz => ?_⟩
  · calc min (min (δ / 2) (1 / 2)) (ε / 2) ≤ min (δ / 2) (1 / 2) := min_le_left _ _
      _ ≤ δ / 2 := min_le_left _ _
      _ < δ := by linarith
  · calc min (min (δ / 2) (1 / 2)) (ε / 2) ≤ min (δ / 2) (1 / 2) := min_le_left _ _
      _ ≤ 1 / 2 := min_le_right _ _
      _ < 1 := by norm_num
  · refine hball ?_
    rw [Real.dist_eq, sub_zero]
    calc |z| ≤ min (min (δ / 2) (1 / 2)) (ε / 2) := hz
      _ ≤ ε / 2 := min_le_right _ _
      _ < ε := by linarith

/-- The critical equation `ψ_x (-4 + a z, y) = 0` for `z = y^2`, when `|a z| < 1` and `z < 1`. -/
lemma critical_equation_FIN06824 {y u : ℝ} (hy : y ^ 2 < 1) (hu : |u| < 1)
    (hcrit : deriv (fun s : ℝ => liftPotential_FIN06804 s (y ^ 2)) u = 0) :
    deriv (fun x : ℝ => quarticPsi_FIN066 !₂[x, y]) (-4 + u) = 0 := by
  have hnhds : {x : ℝ | |x + 4| < 1} ∈ 𝓝 (-4 + u) := by
    refine (isOpen_lt (continuous_abs.comp (continuous_id.add continuous_const))
      continuous_const).mem_nhds ?_
    simpa using hu
  have hev : (fun x : ℝ => quarticPsi_FIN066 !₂[x, y]) =ᶠ[𝓝 (-4 + u)]
      fun x : ℝ => liftPotential_FIN06804 (x + 4) (y ^ 2) := by
    filter_upwards [hnhds] with x hx
    have h := (fin068_04_lift_two_ordinary_variables.2 (x + 4) y hx hy)
    simpa using h
  rw [hev.deriv_eq]
  have h2 := deriv_comp_add_const (f := fun s : ℝ => liftPotential_FIN06804 s (y ^ 2)) 4 (-4 + u)
  rw [show (-4 + u + 4 : ℝ) = u by ring] at h2
  exact h2.trans hcrit

/-- Main declaration. Curve Taylor bound and composition: the critical curve `a` of FIN068.07, with
`a'(0) = d / (32 A)` (FIN068.23), a radius `r` and a bound `M ≥ 0` of `|a''|` on `[-r, r]`, the bound
`|a z - d z / (32 A)| ≤ M z^2 / 2` for `|z| ≤ r`, and, for `x₀ y = -4 + a (y^2)` on `|y| < √r`:
smoothness, evenness, the critical equation `ψ_x (x₀ y, y) = 0`, and the quartic error bound
`|x₀ y - (-4 + d y^2 / (32 A))| ≤ M y^4 / 2`. -/
theorem fin068_24_curve_taylor_bound_composition :
    ∃ δu δz : ℝ, 0 < δu ∧ 0 < δz ∧ ∃ a : ℝ → ℝ,
      ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz) ∧ a 0 = 0 ∧
      (∀ z : ℝ, |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) (a z) = 0) ∧
      (∀ u z : ℝ, |u| < δu → |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) u = 0 → u = a z) ∧
      deriv a 0 =
        (quarticB - 4 * deriv besselRatio 4) / (32 * (quarticB / 5 - deriv besselRatio 4)) ∧
      ∃ r M : ℝ, 0 < r ∧ r < δz ∧ 0 ≤ M ∧
        (∀ z ∈ Set.Icc (-r) r, |deriv (deriv a) z| ≤ M) ∧
        (∀ z : ℝ, |z| ≤ r →
          |a z - (quarticB - 4 * deriv besselRatio 4) /
            (32 * (quarticB / 5 - deriv besselRatio 4)) * z| ≤ M * z ^ 2 / 2) ∧
        ContDiffOn ℝ ∞ (fun y : ℝ => -4 + a (y ^ 2)) (Set.Ioo (-Real.sqrt r) (Real.sqrt r)) ∧
        (∀ y : ℝ, -4 + a ((-y) ^ 2) = -4 + a (y ^ 2)) ∧
        (∀ y : ℝ, |y| < Real.sqrt r →
          deriv (fun x : ℝ => quarticPsi_FIN066 !₂[x, y]) (-4 + a (y ^ 2)) = 0) ∧
        (∀ y : ℝ, |y| < Real.sqrt r →
          |(-4 + a (y ^ 2)) - (-4 + (quarticB - 4 * deriv besselRatio 4) /
            (32 * (quarticB / 5 - deriv besselRatio 4)) * y ^ 2)| ≤ M * y ^ 4 / 2) := by
  obtain ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, h5⟩ := fin068_23_first_derivative_critical_curve
  obtain ⟨r, hr0, hrδ, hr1, hra⟩ := exists_radius_FIN06824 hz h1 h2
  -- the bound `M` of `a''` on `[-r, r]`
  have hopen : IsOpen (Set.Ioo (-δz) δz) := isOpen_Ioo
  have hd1 : ContDiffOn ℝ ∞ (deriv a) (Set.Ioo (-δz) δz) := h1.deriv_of_isOpen hopen (by simp)
  have hd2 : ContDiffOn ℝ ∞ (deriv (deriv a)) (Set.Ioo (-δz) δz) :=
    hd1.deriv_of_isOpen hopen (by simp)
  have hsub : Set.Icc (-r) r ⊆ Set.Ioo (-δz) δz := fun t ht =>
    ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hrδ⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -r) (b := r)).exists_bound_of_continuousOn
    (hd2.continuousOn.mono hsub)
  have hM : ∀ z ∈ Set.Icc (-r) r, |deriv (deriv a) z| ≤ max C 0 := fun z hz =>
    le_trans (by simpa [Real.norm_eq_abs] using hC z hz) (le_max_left C 0)
  have htay := taylor_curve_FIN06824 h1 hr0.le hrδ h2 hM
  rw [h5] at htay
  -- `y^2` lies in `[0, r)` for `|y| < √r`
  have hy2 : ∀ y : ℝ, |y| < Real.sqrt r → y ^ 2 < r := by
    intro y hy
    have := sq_lt_sq' (abs_lt.1 hy).1 (abs_lt.1 hy).2
    rwa [Real.sq_sqrt hr0.le] at this
  refine ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, h5, r, max C 0, hr0, hrδ, le_max_right _ _, hM, htay,
    ?_, fun y => by rw [neg_sq], fun y hy => ?_, fun y hy => ?_⟩
  · refine contDiffOn_const.add (h1.comp (by fun_prop : ContDiff ℝ ∞ fun y : ℝ => y ^ 2).contDiffOn ?_)
    intro y hy
    have hy' := hy2 y (abs_lt.2 hy)
    exact ⟨by nlinarith [sq_nonneg y], by linarith⟩
  · have hy' := hy2 y hy
    have hsq : 0 ≤ y ^ 2 := sq_nonneg y
    exact critical_equation_FIN06824 (by linarith) (hra (y ^ 2) (by rw [abs_of_nonneg hsq]; linarith))
      (h3 (y ^ 2) (by rw [abs_of_nonneg hsq]; linarith))
  · have hy' := hy2 y hy
    have hsq : 0 ≤ y ^ 2 := sq_nonneg y
    have := htay (y ^ 2) (by rw [abs_of_nonneg hsq]; linarith)
    have e : (-4 + a (y ^ 2)) - (-4 + (quarticB - 4 * deriv besselRatio 4) /
        (32 * (quarticB / 5 - deriv besselRatio 4)) * y ^ 2) =
        a (y ^ 2) - (quarticB - 4 * deriv besselRatio 4) /
          (32 * (quarticB / 5 - deriv besselRatio 4)) * y ^ 2 := by ring
    rw [e]
    calc _ ≤ max C 0 * (y ^ 2) ^ 2 / 2 := this
      _ = max C 0 * y ^ 4 / 2 := by ring

end DGPS.Frontier.FIN068
