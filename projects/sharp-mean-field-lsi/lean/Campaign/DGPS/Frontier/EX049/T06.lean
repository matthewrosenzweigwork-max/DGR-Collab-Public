import DGPS.Frontier.EX049.T05

/-!
# EX049.06: Pointwise correction derivative bounds

Task id and title: EX049.06, "Pointwise correction derivative bounds" (node EX049, frontier unit,
leaf formalization, prerequisite EX049.05).  For a real `h ≥ 2` let `A = 2 / (1 - e^{-2h})`,
`N u = A (1 - e^{-hu}) - u` and `Q u = N u / (u (2 - u))` on `(0,2)`.  Every smooth extension `g`
of `Q` to an open neighborhood of `[0,2]` satisfies `0 ≤ g` on `[0,2]`, `g ≤ 3h` on `[0,1]`,
`g ≤ 1` on `[1,2]` and `g ≤ 3/u` on `[1/h,1]`.  A smooth extension exists by EX049.05.

## Provides
* `DGPS.Frontier.EX049.ex049_06_pointwise_correction_derivative_bounds` : the main statement, for
  `2 ≤ h`, with two conjuncts.  (i) A smooth extension `g` of `Q` on an open `U ⊇ [0,2]` exists.
  (ii) For every smooth extension `g` of `Q` on a set `U ⊇ [0,2]` with `ContDiffOn ℝ ∞ g U`, the
  four bounds `0 ≤ g` on `[0,2]`, `g ≤ 3h` on `[0,1]`, `g ≤ 1` on `[1,2]` and `g ≤ 3/u` on
  `[1/h,1]` hold.
* `DGPS.Frontier.EX049.le_on_Icc_EX04906` : a pointwise inequality on `(a,b)` between functions
  continuous on `[a,b]` extends to `[a,b]`.
* `DGPS.Frontier.EX049.aConst_EX04906`, `numer_EX04906`, `quot_EX04906` : the constant `A`, the
  numerator `N` and the quotient `Q` at fixed `h`, as plain definitions used by the helpers.
* The remaining `..._EX04906` lemmas are the elementary inequalities (exponential chord,
  numerator bounds, quotient bounds on `(0,2)`) that the main proof combines.

## R5 notes
* The only hypothesis of the main statement is `2 ≤ h`, the specification's "for every `h ≥ 2`".
  No hypothesis is added beyond the universal quantifiers over `g` and `U`.
* The specification writes `r_h` for "the" smooth extension of `Q`.  Its bounds are stated for every
  smooth extension `g` on every set `U` with `[0,2] ⊆ U` and `ContDiffOn ℝ ∞ g U` that agrees with
  `Q` on `(0,2)`.  This is the literal reading once the values of `r_h` on `[0,2]` are determined by
  continuity from `(0,2)`, which is the content of EX049.05.  The bounds are not claimed for points
  outside `[0,2]`, where the extension is unconstrained.
* Conjunct (i) is a strengthening added so that the universal bounds of conjunct (ii) are not
  vacuous.  It is inherited from the first conjunct of EX049.05 and is not a new hypothesis.
* The `IsOpen U` hypothesis of EX049.05 is kept in the existence conjunct (i).  Conjunct (ii) keeps
  the open-set hypothesis as well, as written in the specification's "smooth extension".
* The bound `r_h ≤ 3/u` on `[1/h,1]` is proved on all of `(0,1]`, which contains `(1/h,1)`; the
  restriction to `[1/h,1]` is only the specification's stated range.  The bound `r_h ≤ 3h` on `[0,1]`
  is likewise proved on `(0,1]` and extended to `0` by continuity.
* The closed-interval bounds at the endpoints are derived from the open-interval bounds by the
  continuity helper `le_on_Icc_EX04906`, using the smooth extension and not a totalized quotient.
  The Lean division convention plays no role: `Q` enters only through its values on `(0,2)`, where
  the denominators `u` and `2 - u` are nonzero.
* The exponential chord inequality is obtained from convexity of `exp`, and the bound `e^{-2h} ≤ 1/5`
  from `1 + x ≤ e^x`.  No external sharp inequality is used.
* The binding of `r_h` to the campaign objects is not proved here.  It is the open task EX049.25,
  as stated in the specification.
-/

open scoped ContDiff
open Set Filter Topology

namespace DGPS.Frontier.EX049

/-- The constant `A = 2 / (1 - e^{-2h})`. -/
noncomputable def aConst_EX04906 (h : ℝ) : ℝ := 2 / (1 - Real.exp (-(2 * h)))

/-- The numerator `N u = A (1 - e^{-hu}) - u`. -/
noncomputable def numer_EX04906 (h u : ℝ) : ℝ := aConst_EX04906 h * (1 - Real.exp (-(h * u))) - u

/-- The quotient `Q u = N u / (u (2 - u))`. -/
noncomputable def quot_EX04906 (h u : ℝ) : ℝ := numer_EX04906 h u / (u * (2 - u))

/-- A pointwise inequality on `(a,b)` between functions continuous on `[a,b]` holds on `[a,b]`. -/
theorem le_on_Icc_EX04906 {f p : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hp : ContinuousOn p (Icc a b))
    (hle : ∀ t ∈ Ioo a b, f t ≤ p t) : ∀ u ∈ Icc a b, f u ≤ p u := by
  intro u hu
  have hcl : u ∈ closure (Ioo a b) := by
    rw [closure_Ioo (ne_of_lt hab)]
    exact hu
  have : (𝓝[Ioo a b] u).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hf' : Tendsto f (𝓝[Ioo a b] u) (𝓝 (f u)) :=
    (hf u hu).mono Set.Ioo_subset_Icc_self
  have hp' : Tendsto p (𝓝[Ioo a b] u) (𝓝 (p u)) :=
    (hp u hu).mono Set.Ioo_subset_Icc_self
  exact le_of_tendsto_of_tendsto hf' hp' (eventually_of_mem self_mem_nhdsWithin hle)

theorem exp_neg_two_lt_one_EX04906 (h : ℝ) (hh : 2 ≤ h) : Real.exp (-(2 * h)) < 1 := by
  have h1 : Real.exp (-(2 * h)) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
  rwa [Real.exp_zero] at h1

theorem one_sub_exp_pos_EX04906 (h : ℝ) (hh : 2 ≤ h) : 0 < 1 - Real.exp (-(2 * h)) := by
  have := exp_neg_two_lt_one_EX04906 h hh
  linarith

theorem exp_neg_two_le_fifth_EX04906 (h : ℝ) (hh : 2 ≤ h) :
    Real.exp (-(2 * h)) ≤ 1 / 5 := by
  have hX : 0 < Real.exp (-(2 * h)) := Real.exp_pos _
  have hY : 2 * h + 1 ≤ Real.exp (2 * h) := Real.add_one_le_exp (2 * h)
  have hXY : Real.exp (-(2 * h)) * Real.exp (2 * h) = 1 := by
    rw [← Real.exp_add]
    simp
  have h5 : Real.exp (-(2 * h)) * 5 ≤ Real.exp (-(2 * h)) * Real.exp (2 * h) :=
    mul_le_mul_of_nonneg_left (by linarith) hX.le
  linarith

theorem aConst_bounds_EX04906 (h : ℝ) (hh : 2 ≤ h) :
    0 < aConst_EX04906 h ∧ aConst_EX04906 h ≤ 3 := by
  have hs := one_sub_exp_pos_EX04906 h hh
  have hX := exp_neg_two_le_fifth_EX04906 h hh
  unfold aConst_EX04906
  constructor
  · exact div_pos (by norm_num) hs
  · rw [div_le_iff₀ hs]
    linarith

theorem aConst_mul_one_sub_EX04906 (h : ℝ) (hh : 2 ≤ h) :
    aConst_EX04906 h * (1 - Real.exp (-(2 * h))) = 2 := by
  have hne : (1 - Real.exp (-(2 * h))) ≠ 0 := (one_sub_exp_pos_EX04906 h hh).ne'
  unfold aConst_EX04906
  field_simp

/-- Convexity of `exp` on the chord from `0` to `-2h`, at the parameter `u/2` for `0 ≤ u ≤ 2`. -/
theorem exp_chord_EX04906 (h u : ℝ) (hu0 : 0 ≤ u) (hu2 : u ≤ 2) :
    Real.exp (-(h * u)) ≤ 1 - u / 2 * (1 - Real.exp (-(2 * h))) := by
  have ht0 : (0:ℝ) ≤ 1 - u / 2 := by linarith
  have ht1 : (0:ℝ) ≤ u / 2 := by linarith
  have hc := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-(2 * h))) ht0 ht1 (by ring)
  have key : (1 - u / 2) • (0:ℝ) + (u / 2) • (-(2 * h)) = -(h * u) := by
    simp only [smul_eq_mul]
    ring
  rw [key] at hc
  simp only [smul_eq_mul, Real.exp_zero, mul_one] at hc
  linarith

theorem numer_nonneg_EX04906 (h u : ℝ) (hh : 2 ≤ h) (hu0 : 0 ≤ u) (hu2 : u ≤ 2) :
    0 ≤ numer_EX04906 h u := by
  have hA : 0 ≤ aConst_EX04906 h := (aConst_bounds_EX04906 h hh).1.le
  have hc := exp_chord_EX04906 h u hu0 hu2
  have h1 : aConst_EX04906 h * (u / 2 * (1 - Real.exp (-(2 * h)))) ≤
      aConst_EX04906 h * (1 - Real.exp (-(h * u))) :=
    mul_le_mul_of_nonneg_left (by linarith) hA
  have key : aConst_EX04906 h * (u / 2 * (1 - Real.exp (-(2 * h)))) = u := by
    have := aConst_mul_one_sub_EX04906 h hh
    linear_combination (u / 2) * this
  unfold numer_EX04906
  linarith

theorem numer_le_two_sub_EX04906 (h u : ℝ) (hh : 2 ≤ h) (hu2 : u ≤ 2) :
    numer_EX04906 h u ≤ 2 - u := by
  have hA : 0 ≤ aConst_EX04906 h := (aConst_bounds_EX04906 h hh).1.le
  have hmono : Real.exp (-(2 * h)) ≤ Real.exp (-(h * u)) :=
    Real.exp_le_exp.2 (by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ h) (by linarith : (0:ℝ) ≤ 2 - u)])
  have h1 : aConst_EX04906 h * (1 - Real.exp (-(h * u))) ≤
      aConst_EX04906 h * (1 - Real.exp (-(2 * h))) :=
    mul_le_mul_of_nonneg_left (by linarith) hA
  have key := aConst_mul_one_sub_EX04906 h hh
  unfold numer_EX04906
  linarith

theorem numer_le_three_h_EX04906 (h u : ℝ) (hh : 2 ≤ h) (hu0 : 0 ≤ u) :
    numer_EX04906 h u ≤ 3 * (h * u) := by
  have hA : 0 ≤ aConst_EX04906 h := (aConst_bounds_EX04906 h hh).1.le
  have hA3 : aConst_EX04906 h ≤ 3 := (aConst_bounds_EX04906 h hh).2
  have hE : 1 - Real.exp (-(h * u)) ≤ h * u := by
    have := Real.add_one_le_exp (-(h * u))
    linarith
  have hhu : 0 ≤ h * u := mul_nonneg (by linarith) hu0
  have h1 : aConst_EX04906 h * (1 - Real.exp (-(h * u))) ≤ aConst_EX04906 h * (h * u) :=
    mul_le_mul_of_nonneg_left hE hA
  have h2 : aConst_EX04906 h * (h * u) ≤ 3 * (h * u) :=
    mul_le_mul_of_nonneg_right hA3 hhu
  unfold numer_EX04906
  linarith

theorem numer_le_three_EX04906 (h u : ℝ) (hh : 2 ≤ h) (hu0 : 0 ≤ u) :
    numer_EX04906 h u ≤ 3 := by
  have hA : 0 ≤ aConst_EX04906 h := (aConst_bounds_EX04906 h hh).1.le
  have hA3 : aConst_EX04906 h ≤ 3 := (aConst_bounds_EX04906 h hh).2
  have hE : 1 - Real.exp (-(h * u)) ≤ 1 := by
    have := Real.exp_pos (-(h * u))
    linarith
  have h1 : aConst_EX04906 h * (1 - Real.exp (-(h * u))) ≤ aConst_EX04906 h * 1 :=
    mul_le_mul_of_nonneg_left hE hA
  unfold numer_EX04906
  linarith

theorem quot_nonneg_EX04906 (h u : ℝ) (hh : 2 ≤ h) (hu0 : 0 < u) (hu2 : u < 2) :
    0 ≤ quot_EX04906 h u := by
  unfold quot_EX04906
  exact div_nonneg (numer_nonneg_EX04906 h u hh hu0.le hu2.le) (mul_pos hu0 (by linarith)).le

theorem quot_le_three_h_EX04906 (h u : ℝ) (hh : 2 ≤ h) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    quot_EX04906 h u ≤ 3 * h := by
  have hD : 0 < u * (2 - u) := mul_pos hu0 (by linarith)
  unfold quot_EX04906
  rw [div_le_iff₀ hD]
  have h1 := numer_le_three_h_EX04906 h u hh hu0.le
  have h2 : 0 ≤ 3 * h * (u * (1 - u)) :=
    mul_nonneg (by linarith) (mul_nonneg hu0.le (by linarith))
  nlinarith [h1, h2]

theorem quot_le_one_EX04906 (h u : ℝ) (hh : 2 ≤ h) (hu1 : 1 ≤ u) (hu2 : u < 2) :
    quot_EX04906 h u ≤ 1 := by
  have hD : 0 < u * (2 - u) := mul_pos (by linarith) (by linarith)
  unfold quot_EX04906
  rw [div_le_iff₀ hD]
  have h1 := numer_le_two_sub_EX04906 h u hh hu2.le
  have h2 : 0 ≤ (u - 1) * (2 - u) := mul_nonneg (by linarith) (by linarith)
  nlinarith [h1, h2]

theorem quot_le_three_div_EX04906 (h u : ℝ) (hh : 2 ≤ h) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    quot_EX04906 h u ≤ 3 / u := by
  have hD : 0 < u * (2 - u) := mul_pos hu0 (by linarith)
  have hN := numer_le_three_EX04906 h u hh hu0.le
  unfold quot_EX04906
  rw [div_le_div_iff₀ hD hu0]
  nlinarith [mul_le_mul_of_nonneg_right hN hu0.le, mul_nonneg hu0.le (by linarith : (0:ℝ) ≤ 1 - u)]

/-- The four pointwise bounds for any smooth extension of `quot_EX04906 h` on `[0,2]`. -/
theorem bounds_EX04906 (h : ℝ) (hh : 2 ≤ h) (g : ℝ → ℝ) (U : Set ℝ)
    (hI : Icc (0:ℝ) 2 ⊆ U) (hc : ContDiffOn ℝ ∞ g U)
    (hQg : ∀ u ∈ Ioo (0:ℝ) 2, g u = quot_EX04906 h u) :
    (∀ u ∈ Icc (0:ℝ) 2, 0 ≤ g u) ∧ (∀ u ∈ Icc (0:ℝ) 1, g u ≤ 3 * h) ∧
      (∀ u ∈ Icc (1:ℝ) 2, g u ≤ 1) ∧ (∀ u ∈ Icc (1 / h) 1, g u ≤ 3 / u) := by
  have hgc : ContinuousOn g (Icc (0:ℝ) 2) := hc.continuousOn.mono hI
  have hlow : (0:ℝ) < 1 / h := one_div_pos.2 (by linarith)
  have hlt : 1 / h < (1:ℝ) := by
    rw [div_lt_one (by linarith)]
    linarith
  have hg0 : ContinuousOn g (Icc (0:ℝ) 2) := hgc
  have hg1 : ContinuousOn g (Icc (0:ℝ) 1) := hgc.mono (Icc_subset_Icc le_rfl (by norm_num))
  have hg2 : ContinuousOn g (Icc (1:ℝ) 2) := hgc.mono (Icc_subset_Icc (by norm_num) le_rfl)
  have hg3 : ContinuousOn g (Icc (1 / h) 1) :=
    hgc.mono (Icc_subset_Icc (by linarith) (by norm_num))
  have hp3 : ContinuousOn (fun u : ℝ => 3 / u) (Icc (1 / h) 1) :=
    continuousOn_const.div continuousOn_id
      (fun u hu => (lt_of_lt_of_le hlow hu.1).ne')
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine le_on_Icc_EX04906 (f := fun _ => (0:ℝ)) (p := g) (by norm_num) continuousOn_const hg0 ?_
    intro t ht
    show (0:ℝ) ≤ g t
    rw [hQg t ht]
    exact quot_nonneg_EX04906 h t hh ht.1 ht.2
  · refine le_on_Icc_EX04906 (f := g) (p := fun _ => 3 * h) (by norm_num) hg1 continuousOn_const ?_
    intro t ht
    show g t ≤ 3 * h
    have ht2 : t ∈ Ioo (0:ℝ) 2 := ⟨ht.1, by linarith [ht.2]⟩
    rw [hQg t ht2]
    exact quot_le_three_h_EX04906 h t hh ht.1 ht.2.le
  · refine le_on_Icc_EX04906 (f := g) (p := fun _ => (1:ℝ)) (by norm_num) hg2 continuousOn_const ?_
    intro t ht
    show g t ≤ 1
    have ht2 : t ∈ Ioo (0:ℝ) 2 := ⟨by linarith [ht.1], ht.2⟩
    rw [hQg t ht2]
    exact quot_le_one_EX04906 h t hh ht.1.le ht.2
  · refine le_on_Icc_EX04906 (f := g) (p := fun u : ℝ => 3 / u) hlt hg3 hp3 ?_
    intro t ht
    show g t ≤ 3 / t
    have hu0 : 0 < t := lt_trans hlow ht.1
    have ht2 : t ∈ Ioo (0:ℝ) 2 := ⟨hu0, by linarith [ht.2]⟩
    rw [hQg t ht2]
    exact quot_le_three_div_EX04906 h t hh hu0 ht.2.le

/-- Pointwise correction derivative bounds.  For every real `h ≥ 2`, with `A`, `N` and `Q` as in
EX049.05: (i) a smooth extension of `Q` to an open neighborhood of `[0,2]` exists; (ii) every smooth
extension `g` of `Q` on a set `U ⊇ [0,2]` with `ContDiffOn ℝ ∞ g U` satisfies `0 ≤ g` on `[0,2]`,
`g ≤ 3h` on `[0,1]`, `g ≤ 1` on `[1,2]` and `g ≤ 3/u` on `[1/h,1]`. -/
theorem ex049_06_pointwise_correction_derivative_bounds (h : ℝ) (hh : 2 ≤ h) :
    let A : ℝ := 2 / (1 - Real.exp (-(2 * h)))
    let N : ℝ → ℝ := fun u => A * (1 - Real.exp (-(h * u))) - u
    let Q : ℝ → ℝ := fun u => N u / (u * (2 - u))
    (∃ g : ℝ → ℝ, ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (0:ℝ) 2 ⊆ U ∧ ContDiffOn ℝ ∞ g U ∧
        ∀ u ∈ Set.Ioo (0:ℝ) 2, g u = Q u) ∧
    (∀ g : ℝ → ℝ, ∀ U : Set ℝ, IsOpen U → Set.Icc (0:ℝ) 2 ⊆ U → ContDiffOn ℝ ∞ g U →
        (∀ u ∈ Set.Ioo (0:ℝ) 2, g u = Q u) →
        (∀ u ∈ Set.Icc (0:ℝ) 2, 0 ≤ g u) ∧
        (∀ u ∈ Set.Icc (0:ℝ) 1, g u ≤ 3 * h) ∧
        (∀ u ∈ Set.Icc (1:ℝ) 2, g u ≤ 1) ∧
        (∀ u ∈ Set.Icc (1 / h) 1, g u ≤ 3 / u)) := by
  intro A N Q
  obtain ⟨hex, -⟩ := ex049_05_smooth_removable_profile_primitive h hh
  obtain ⟨g₀, U₀, hU₀, hI₀, hc₀, hQ₀, -, -⟩ := hex
  refine ⟨⟨g₀, U₀, hU₀, hI₀, hc₀, hQ₀⟩, ?_⟩
  intro g U _ hI hc hQg
  exact bounds_EX04906 h hh g U hI hc hQg

end DGPS.Frontier.EX049
