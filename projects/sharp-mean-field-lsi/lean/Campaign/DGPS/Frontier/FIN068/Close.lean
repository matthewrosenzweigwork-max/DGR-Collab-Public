import DGPS.Frontier.FIN068.T06
import DGPS.Frontier.FIN068.T08
import DGPS.Frontier.FIN068.T09
import DGPS.Frontier.FIN068.T10
import DGPS.Frontier.FIN068.T11
import DGPS.Frontier.FIN068.T12
import DGPS.Frontier.FIN068.T13

/-!
Task id and title: FIN068.CLOSE, Closing unit: declare and prove
`DGPS.FiniteN.exact_negative_reduced_quartic_coefficient` (module `DGPS.Frontier.FIN068.Close`).

Provides:
* `DGPS.FiniteN.exact_negative_reduced_quartic_coefficient`: the frozen statement of node FIN068,
  as one closed existential. (1) Constants: `b, A, d > 0`, `4 A - d = -(b / 5)`, `c₄ = b d / (10240 A)
  > 0`. (2) Weighted expansion: `ψ(-4 + u, y) - ψ(-4, 0) = A u² / 2 - d u y² / 32 + d y⁴ / 512 + R`
  with `|R| ≤ M (|u| + y²)³` for `|u| ≤ δ`, `y² ≤ δ`. (3) One critical curve `a` (`C^∞` on
  `(-δz, δz)`, `a 0 = 0`, `J_u (a z, z) = 0`, unique zero in a window) with `a'(0) = d / (32 A)`; for
  `x₀ y = -4 + a (y²)`: `|a''| ≤ M` on `[-r, r]`, `|a z - d z / (32 A)| ≤ M z² / 2`, smoothness and
  evenness of `x₀`, `ψ_x (x₀ y, y) = 0`, `|x₀ y - (-4 + d y² / (32 A))| ≤ M y⁴ / 2`. (4) Reduced
  function `φ y = ψ(x₀ y, y)`: `|φ y - ψ(-4, 0) + c₄ y⁴| ≤ M₆ y⁶` and `φ'' y ≤ -c y²` for `y² ≤ ρ`,
  with `c > 0`. (5) The Morse patch: the full conclusion of FIN068.13 (`a₂`, signed coordinate `v`
  with `ψ = v² / 2 + φ(y)`, the open sets `U`, `N`, the rectangle `Q`, the inverse `X`, the source
  patch `W`, the Jacobian bounds and the energy-metric comparison), on a rectangle chosen so that
  every point of `W` has `y² ≤ ρ` and `φ'' y ≤ -c y²`.
* Helper declarations, all with suffix `_FIN068CLOSE` and not part of the interface:
  `weighted_expansion_FIN068CLOSE` (conjunct (2), from FIN068.06 and FIN068.04),
  `curve_FIN068CLOSE` (conjunct (3), the FIN068.24 argument for an arbitrary curve of the
  FIN068.07 type), `reduced_FIN068CLOSE` (conjunct (4), from FIN068.09, FIN068.10, FIN068.04).

Proof: every analytic clause is a prerequisite theorem; the only new work is to put them on one
curve and one patch. The curve `a` is taken from FIN068.13. The `_any` forms of FIN068.23 and
FIN068.09 apply to that `a`, so no uniqueness-based transport of a second curve is needed. The
reduced function `q z = J (a z, z)` is `C^∞` on `(-r, r)` by FIN068.04, a bound for the third
derivative of `q` on `[-r / 2, r / 2]` comes from compactness, and FIN068.10 gives the value
remainder and the bound `φ'' y ≤ -6 c₄ y²` for `y² ≤ min (r / 2) (6 c₄ / (5 max 1 M))`; and
`φ y = q (y²)` by FIN068.04 near each such `y`. The FIN068.13 rectangle `Q = (-ε, ε) × (-δ, δ)` is
replaced by `(-ε, ε) × (-δ', δ')`, `δ' = min δ (√ρ)`, and `W` by `N ∩ T⁻¹' Q'` with
`T p = (v p, p.2)`; each FIN068.13 clause restricts by monotonicity, and surjectivity onto `Q'`
follows from that onto `Q`.

R5 notes:
* The statement is authored here from the frozen informal text; the specification gives no Lean
  text. No hypothesis is added. It is closed and existential in all of its constants and objects.
* `A` and `d` are the campaign definitions `quarticA_FIN06803` and `quarticD_FIN06803` (FIN068.03),
  `ψ` is `quarticPsi_FIN066 !₂[x, y]`, `ψ(w₋)` is `quarticPsi_FIN066 !₂[-4, 0]`, `c₄` is written out
  as `quarticB * quarticD_FIN06803 / (10240 * quarticA_FIN06803)`, and `ψ_x` is the one-variable
  derivative `deriv (fun x => ψ !₂[x, y]) x`, as in FIN068.04, 05, 07.
* "Weighted `O(6)`" is read as a bound by `M (|u| + y²)³` on `|u| ≤ δ`, `y² ≤ δ`, with `δ < 1`.
  This is the FIN068.06 reading. The "O(y⁴)" and "O(y⁶)" are explicit bounds with constants
  `M y⁴ / 2` and `M₆ y⁶`, valid for `|y| < √r` and `y² ≤ ρ` respectively.
* `c` in `φ'' ≤ -c y²` is existential; the proof gives `c = 6 c₄`. "On the fixed patch" is the source
  patch `W`: every point of `W` satisfies `p.2 ^ 2 ≤ ρ` and `φ'' p.2 ≤ -c p.2 ^ 2`. To get this, the
  rectangle of FIN068.13 is shrunk in its second side to `δ' = min δ (√ρ)`, and `W` is the
  corresponding smaller source patch. This is the same patch construction, with all clauses of
  FIN068.13 restated on the smaller rectangle. `φ` is `fun t => ψ !₂[-4 + a (t ^ 2), t]`.
* The single curve `a` of the statement is the curve of FIN068.13; the curve prefix (smoothness,
  `a 0 = 0`, root equation, uniqueness) is as in FIN068.08. The informal "smooth local Morse
  coordinate with bounded positive Jacobian and uniformly comparable energy metric" is the FIN068.13
  conclusion, restated unchanged apart from the smaller rectangle.
* Interface gates FIN068.37 and FIN068.38 (identification of the campaign Bessel objects and of
  `quarticPsi_FIN066` with the named formulas) are inherited through FIN068.04 and not repaired here.
* The module also depends on FIN068.09 (module `DGPS.Frontier.FIN068.T09`), in addition to the six
  prerequisites listed in the brief. FIN068.11 and FIN068.12 are subsumed by FIN068.13.
-/

open DGPS.Models DGPS.Circle.BesselMoments DGPS.FiniteN.QuarticSaddleGlobalFIN066
open DGPS.Frontier.FIN068
open Filter Topology
open scoped ContDiff

namespace DGPS.FiniteN

/-- The weighted fourth-order expansion of the source potential at `w₋ = (-4, 0)`, with `u = x + 4`,
from the weighted Taylor remainder of FIN068.06. -/
lemma weighted_expansion_FIN068CLOSE :
    ∃ δ M : ℝ, 0 < δ ∧ δ < 1 ∧ 0 ≤ M ∧ ∀ u y : ℝ, |u| ≤ δ → y ^ 2 ≤ δ →
      |quarticPsi_FIN066 !₂[-4 + u, y] - quarticPsi_FIN066 !₂[-4, 0] -
        (quarticA_FIN06803 * u ^ 2 / 2 - quarticD_FIN06803 * u * y ^ 2 / 32 +
          quarticD_FIN06803 * y ^ 4 / 512)| ≤ M * (|u| + y ^ 2) ^ 3 := by
  obtain ⟨δ, hδ0, hδ1, -, -, M₃, hM₃, hM, -⟩ := fin068_06_weighted_taylor_remainder_exists
  refine ⟨δ, M₃ / 6, hδ0, hδ1, by positivity, fun u y hu hy => ?_⟩
  have h := fin068_06_weighted_taylor_remainder_weighted δ M₃ hδ1 hM u y hu hy
  have e1 := fin068_04_lift_two_ordinary_variables.2 u y (lt_of_le_of_lt hu hδ1)
    (lt_of_le_of_lt hy hδ1)
  have e0 : quarticPsi_FIN066 !₂[(-4 : ℝ), 0] = liftPotential_FIN06804 0 0 := by
    have := fin068_04_lift_two_ordinary_variables.2 0 0 (by norm_num) (by norm_num)
    simpa using this
  rw [e1, e0]
  have e2 : liftPotential_FIN06804 u (y ^ 2) - quadP_FIN06820 (u, y ^ 2) =
      liftPotential_FIN06804 u (y ^ 2) - liftPotential_FIN06804 0 0 -
        (quarticA_FIN06803 * u ^ 2 / 2 - quarticD_FIN06803 * u * y ^ 2 / 32 +
          quarticD_FIN06803 * y ^ 4 / 512) := by
    unfold quadP_FIN06820 constA_FIN06820 constD_FIN06820 quarticA_FIN06803 quarticD_FIN06803
    ring
  rw [e2] at h
  exact h


/-- The FIN068.24 expansion of the critical curve, for any curve of the FIN068.07 type. -/
lemma curve_FIN068CLOSE {δz : ℝ} (hz : 0 < δz) {a : ℝ → ℝ}
    (h1 : ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz)) (h2 : a 0 = 0)
    (h3 : ∀ z : ℝ, |z| < δz → deriv (fun s : ℝ => liftPotential_FIN06804 s z) (a z) = 0) :
    ∃ r M : ℝ, 0 < r ∧ r < δz ∧ 0 ≤ M ∧
      (∀ z ∈ Set.Icc (-r) r, |deriv (deriv a) z| ≤ M) ∧
      (∀ z : ℝ, |z| ≤ r →
        |a z - quarticD_FIN06803 / (32 * quarticA_FIN06803) * z| ≤ M * z ^ 2 / 2) ∧
      ContDiffOn ℝ ∞ (fun y : ℝ => -4 + a (y ^ 2)) (Set.Ioo (-Real.sqrt r) (Real.sqrt r)) ∧
      (∀ y : ℝ, -4 + a ((-y) ^ 2) = -4 + a (y ^ 2)) ∧
      (∀ y : ℝ, |y| < Real.sqrt r →
        deriv (fun x : ℝ => quarticPsi_FIN066 !₂[x, y]) (-4 + a (y ^ 2)) = 0) ∧
      (∀ y : ℝ, |y| < Real.sqrt r →
        |(-4 + a (y ^ 2)) - (-4 + quarticD_FIN06803 / (32 * quarticA_FIN06803) * y ^ 2)| ≤
          M * y ^ 4 / 2) := by
  have h5 : deriv a 0 = quarticD_FIN06803 / (32 * quarticA_FIN06803) :=
    fin068_23_first_derivative_critical_curve_any hz h1 h2 h3
  obtain ⟨r, hr0, hrδ, hr1, hra⟩ := exists_radius_FIN06824 hz h1 h2
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
  have hy2 : ∀ y : ℝ, |y| < Real.sqrt r → y ^ 2 < r := by
    intro y hy
    have := sq_lt_sq' (abs_lt.1 hy).1 (abs_lt.1 hy).2
    rwa [Real.sq_sqrt hr0.le] at this
  refine ⟨r, max C 0, hr0, hrδ, le_max_right _ _, hM, htay, ?_, fun y => by rw [neg_sq],
    fun y hy => ?_, fun y hy => ?_⟩
  · refine contDiffOn_const.add
      (h1.comp (by fun_prop : ContDiff ℝ ∞ fun y : ℝ => y ^ 2).contDiffOn ?_)
    intro y hy
    have hy' := hy2 y (abs_lt.2 hy)
    exact ⟨by nlinarith [sq_nonneg y], by linarith⟩
  · have hy' := hy2 y hy
    have hsq : 0 ≤ y ^ 2 := sq_nonneg y
    exact critical_equation_FIN06824 (by linarith)
      (hra (y ^ 2) (by rw [abs_of_nonneg hsq]; linarith))
      (h3 (y ^ 2) (by rw [abs_of_nonneg hsq]; linarith))
  · have hy' := hy2 y hy
    have hsq : 0 ≤ y ^ 2 := sq_nonneg y
    have := htay (y ^ 2) (by rw [abs_of_nonneg hsq]; linarith)
    have e : (-4 + a (y ^ 2)) - (-4 + quarticD_FIN06803 / (32 * quarticA_FIN06803) * y ^ 2) =
        a (y ^ 2) - quarticD_FIN06803 / (32 * quarticA_FIN06803) * y ^ 2 := by ring
    rw [e]
    calc _ ≤ max C 0 * (y ^ 2) ^ 2 / 2 := this
      _ = max C 0 * y ^ 4 / 2 := by ring


/-- The reduced quartic coefficient: value remainder and negative `φ''` for `φ y = ψ(x₀ y, y)`. -/
lemma reduced_FIN068CLOSE {δz : ℝ} (hz : 0 < δz) {a : ℝ → ℝ}
    (h1 : ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz)) (h2 : a 0 = 0)
    (h3 : ∀ z : ℝ, |z| < δz → deriv (fun s : ℝ => liftPotential_FIN06804 s z) (a z) = 0) :
    ∃ ρ M₆ c : ℝ, 0 < ρ ∧ 0 ≤ M₆ ∧ 0 < c ∧ ∀ y : ℝ, y ^ 2 ≤ ρ →
      |quarticPsi_FIN066 !₂[-4 + a (y ^ 2), y] - quarticPsi_FIN066 !₂[-4, 0] +
          quarticB * quarticD_FIN06803 / (10240 * quarticA_FIN06803) * y ^ 4| ≤ M₆ * y ^ 6 ∧
        deriv (deriv (fun t : ℝ => quarticPsi_FIN066 !₂[-4 + a (t ^ 2), t])) y ≤ -c * y ^ 2 := by
  obtain ⟨-, -, -, -, -, -, hc4⟩ := fin068_03_constants_exact_cancellation
  obtain ⟨hq0, hq1, hq2⟩ := fin068_09_reduced_quartic_coefficient_any hz h1 h2 h3
  obtain ⟨r, hr0, hrδ, hr1, hra⟩ := exists_radius_FIN06824 hz h1 h2
  set c₄ : ℝ := quarticB * quarticD_FIN06803 / (10240 * quarticA_FIN06803) with hc₄
  set q : ℝ → ℝ := fun z => liftPotential_FIN06804 (a z) z with hqdef
  have hsub : Set.Ioo (-r) r ⊆ Set.Ioo (-δz) δz := fun t ht =>
    ⟨by linarith [ht.1], lt_trans ht.2 hrδ⟩
  have hqU : ContDiffOn ℝ ∞ q (Set.Ioo (-r) r) := by
    have hf : ContDiffOn ℝ ∞ (fun z : ℝ => (a z, z)) (Set.Ioo (-r) r) :=
      (h1.mono hsub).prodMk contDiffOn_id
    refine fin068_04_lift_two_ordinary_variables.1.comp hf ?_
    intro z hz'
    have hza : |z| ≤ r := abs_le.2 ⟨hz'.1.le, hz'.2.le⟩
    have haz := abs_lt.1 (hra z hza)
    exact ⟨⟨haz.1, haz.2⟩, ⟨by linarith [hz'.1], by linarith [hz'.2]⟩⟩
  have hopen : IsOpen (Set.Ioo (-r) r) := isOpen_Ioo
  have hd1 : ContDiffOn ℝ ∞ (deriv q) (Set.Ioo (-r) r) := hqU.deriv_of_isOpen hopen (by simp)
  have hd2 : ContDiffOn ℝ ∞ (deriv (deriv q)) (Set.Ioo (-r) r) :=
    hd1.deriv_of_isOpen hopen (by simp)
  have hd3 : ContDiffOn ℝ ∞ (deriv (deriv (deriv q))) (Set.Ioo (-r) r) :=
    hd2.deriv_of_isOpen hopen (by simp)
  have hIcc : Set.Icc (-(r / 2)) (r / 2) ⊆ Set.Ioo (-r) r := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -(r / 2)) (b := r / 2)).exists_bound_of_continuousOn
    (hd3.continuousOn.mono hIcc)
  have hM : ∀ t ∈ Set.Icc (-(r / 2)) (r / 2), |deriv (deriv (deriv q)) t| ≤ max C 0 :=
    fun t ht => le_trans (by simpa [Real.norm_eq_abs] using hC t ht) (le_max_left C 0)
  have hT := fin068_10_value_remainder_negative_second_derivative q (Set.Ioo (-r) r) hopen
    (r / 2) c₄ (max C 0) hIcc hqU (le_max_right _ _) hM hq1 hq2
  have hMpos : 0 < 5 * max 1 (max C 0) := by positivity
  refine ⟨min (r / 2) (6 * c₄ / (5 * max 1 (max C 0))), max C 0, 6 * c₄,
    lt_min (by positivity) (by positivity), le_max_right _ _, by positivity, fun y hy => ?_⟩
  have hy1 : y ^ 2 ≤ r / 2 := hy.trans (min_le_left _ _)
  have hy2 : y ^ 2 ≤ 6 * c₄ / (5 * max 1 (max C 0)) := hy.trans (min_le_right _ _)
  have hyI : y ^ 2 ∈ Set.Icc (-(r / 2)) (r / 2) :=
    ⟨by nlinarith [sq_nonneg y], hy1⟩
  obtain ⟨hv, -, hdd⟩ := hT y hyI
  have hid : ∀ t : ℝ, t ^ 2 < r →
      quarticPsi_FIN066 !₂[-4 + a (t ^ 2), t] = q (t ^ 2) := by
    intro t ht
    have hsq : 0 ≤ t ^ 2 := sq_nonneg t
    have haz := hra (t ^ 2) (by rw [abs_of_nonneg hsq]; exact ht.le)
    exact fin068_04_lift_two_ordinary_variables.2 (a (t ^ 2)) t haz (by linarith)
  have hyr : y ^ 2 < r := by linarith
  have hq0' : q 0 = quarticPsi_FIN066 !₂[-4, 0] := by
    show liftPotential_FIN06804 (a 0) 0 = _
    exact hq0
  constructor
  · rw [hid y hyr, ← hq0']
    have e : (y ^ 2) ^ 2 = y ^ 4 := by ring
    rw [e] at hv
    calc _ ≤ max C 0 * |y| ^ 6 / 6 := hv
      _ ≤ max C 0 * y ^ 6 := by
        have h6 : |y| ^ 6 = y ^ 6 := by
          rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, pow_mul, sq_abs]
        rw [h6]
        nlinarith [le_max_right C 0, pow_two_nonneg (y ^ 3), show y ^ 6 = (y ^ 3) ^ 2 by ring]
  · have hnhds : {t : ℝ | t ^ 2 < r} ∈ nhds y :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds hyr
    have hev : (fun t : ℝ => quarticPsi_FIN066 !₂[-4 + a (t ^ 2), t]) =ᶠ[nhds y]
        fun t : ℝ => q (t ^ 2) := by
      filter_upwards [hnhds] with t ht using hid t ht
    rw [hev.deriv.deriv_eq]
    have := hdd hy2
    linarith


/-- Exact negative reduced quartic coefficient (FIN068 closing statement): see the module
docstring for the reading of each clause. -/
theorem exact_negative_reduced_quartic_coefficient :
    (0 < quarticB ∧ 0 < quarticA_FIN06803 ∧ 0 < quarticD_FIN06803 ∧
      4 * quarticA_FIN06803 - quarticD_FIN06803 = -(quarticB / 5) ∧
      0 < quarticB * quarticD_FIN06803 / (10240 * quarticA_FIN06803)) ∧
    (∃ δ M : ℝ, 0 < δ ∧ δ < 1 ∧ 0 ≤ M ∧ ∀ u y : ℝ, |u| ≤ δ → y ^ 2 ≤ δ →
      |quarticPsi_FIN066 !₂[-4 + u, y] - quarticPsi_FIN066 !₂[-4, 0] -
        (quarticA_FIN06803 * u ^ 2 / 2 - quarticD_FIN06803 * u * y ^ 2 / 32 +
          quarticD_FIN06803 * y ^ 4 / 512)| ≤ M * (|u| + y ^ 2) ^ 3) ∧
    ∃ δu δz : ℝ, 0 < δu ∧ 0 < δz ∧ ∃ a : ℝ → ℝ,
      ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz) ∧ a 0 = 0 ∧
      (∀ z : ℝ, |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) (a z) = 0) ∧
      (∀ u z : ℝ, |u| < δu → |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) u = 0 → u = a z) ∧
      deriv a 0 = quarticD_FIN06803 / (32 * quarticA_FIN06803) ∧
      (∃ r M : ℝ, 0 < r ∧ r < δz ∧ 0 ≤ M ∧
        (∀ z ∈ Set.Icc (-r) r, |deriv (deriv a) z| ≤ M) ∧
        (∀ z : ℝ, |z| ≤ r →
          |a z - quarticD_FIN06803 / (32 * quarticA_FIN06803) * z| ≤ M * z ^ 2 / 2) ∧
        ContDiffOn ℝ ∞ (fun y : ℝ => -4 + a (y ^ 2)) (Set.Ioo (-Real.sqrt r) (Real.sqrt r)) ∧
        (∀ y : ℝ, -4 + a ((-y) ^ 2) = -4 + a (y ^ 2)) ∧
        (∀ y : ℝ, |y| < Real.sqrt r →
          deriv (fun x : ℝ => quarticPsi_FIN066 !₂[x, y]) (-4 + a (y ^ 2)) = 0) ∧
        (∀ y : ℝ, |y| < Real.sqrt r →
          |(-4 + a (y ^ 2)) - (-4 + quarticD_FIN06803 / (32 * quarticA_FIN06803) * y ^ 2)| ≤
            M * y ^ 4 / 2)) ∧
      ∃ ρ M₆ c : ℝ, 0 < ρ ∧ 0 ≤ M₆ ∧ 0 < c ∧
      (∀ y : ℝ, y ^ 2 ≤ ρ →
        |quarticPsi_FIN066 !₂[-4 + a (y ^ 2), y] - quarticPsi_FIN066 !₂[-4, 0] +
            quarticB * quarticD_FIN06803 / (10240 * quarticA_FIN06803) * y ^ 4| ≤ M₆ * y ^ 6 ∧
          deriv (deriv (fun t : ℝ => quarticPsi_FIN066 !₂[-4 + a (t ^ 2), t])) y ≤ -c * y ^ 2) ∧
      ∃ δx δy : ℝ, 0 < δx ∧ 0 < δy ∧
        (∀ x y t : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
          t ∈ Set.Icc (0 : ℝ) 1 →
          (-4 + a (y ^ 2) + t * (x - (-4 + a (y ^ 2))), y) ∈
            Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1) ∧
        (∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
          deriv (fun s : ℝ => quarticPsi_FIN066 !₂[s, y]) (-4 + a (y ^ 2)) = 0) ∧
        ContDiffOn ℝ ∞ (fun y : ℝ => -4 + a (y ^ 2)) (Set.Ioo (-δy) δy) ∧
        deriv (fun y : ℝ => -4 + a (y ^ 2)) 0 = 0 ∧
        ContDiffOn ℝ ∞ (fun y : ℝ => quarticPsi_FIN066 !₂[-4 + a (y ^ 2), y])
          (Set.Ioo (-δy) δy) ∧
        ∃ a₂ : ℝ × ℝ → ℝ,
          (∀ p : ℝ × ℝ, a₂ p = 2 * ∫ t in (0 : ℝ)..1, (1 - t) *
            deriv (deriv (fun s : ℝ => quarticPsi_FIN066 !₂[s, p.2]))
              (-4 + a (p.2 ^ 2) + t * (p.1 - (-4 + a (p.2 ^ 2))))) ∧
          ContDiffOn ℝ ∞ a₂ (Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy) ∧
          a₂ (-4, 0) = quarticA_FIN06803 ∧
          (∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
            quarticA_FIN06803 / 2 ≤ a₂ (x, y) ∧ a₂ (x, y) ≤ 2 * quarticA_FIN06803) ∧
          (∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
            quarticPsi_FIN066 !₂[x, y] - quarticPsi_FIN066 !₂[-4 + a (y ^ 2), y] =
              (1 / 2) * (x - (-4 + a (y ^ 2))) ^ 2 * a₂ (x, y)) ∧
          ∃ v : ℝ × ℝ → ℝ,
            (∀ p : ℝ × ℝ, v p = (p.1 - (-4 + a (p.2 ^ 2))) * Real.sqrt (a₂ p)) ∧
            ContDiffOn ℝ ∞ v (Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy) ∧
            (∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
              quarticPsi_FIN066 !₂[x, y] =
                v (x, y) ^ 2 / 2 + quarticPsi_FIN066 !₂[-4 + a (y ^ 2), y]) ∧
            v (-4, 0) = 0 ∧
            fderiv ℝ v (-4, 0) (1, 0) = Real.sqrt quarticA_FIN06803 ∧
            fderiv ℝ v (-4, 0) (0, 1) = 0 ∧
            ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (-4, 0) ∈ U ∧
              U ⊆ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy ∧
              (∀ p ∈ U, Real.sqrt quarticA_FIN06803 / 2 ≤ fderiv ℝ v p (1, 0) ∧
                fderiv ℝ v p (1, 0) ≤ 2 * Real.sqrt quarticA_FIN06803 ∧
                |fderiv ℝ v p (0, 1)| ≤ 1) ∧
              ∃ N : Set (ℝ × ℝ), IsOpen N ∧ (-4, 0) ∈ N ∧ N ⊆ U ∧
                Set.InjOn (fun p : ℝ × ℝ => (v p, p.2)) N ∧
                IsOpen ((fun p : ℝ × ℝ => (v p, p.2)) '' N) ∧
                ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
                  closure (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ⊆
                    (fun p : ℝ × ℝ => (v p, p.2)) '' N ∧
                  ∃ X : ℝ × ℝ → ℝ, ContDiffOn ℝ ∞ X (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ∧
                    ∃ W : Set (ℝ × ℝ),
                      W = N ∩ (fun p : ℝ × ℝ => (v p, p.2)) ⁻¹'
                        (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ∧
                      IsOpen W ∧ (-4, 0) ∈ W ∧ W ⊆ N ∧
                      (∀ p ∈ W, Real.sqrt quarticA_FIN06803 / 2 ≤ fderiv ℝ v p (1, 0) ∧
                        fderiv ℝ v p (1, 0) ≤ 2 * Real.sqrt quarticA_FIN06803 ∧
                        |fderiv ℝ v p (0, 1)| ≤ 1) ∧
                      Set.BijOn (fun p : ℝ × ℝ => (v p, p.2)) W
                        (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ∧
                      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (v p, p.2)) W ∧
                      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => (X q, q.2))
                        (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ∧
                      (∀ q ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ, (X q, q.2) ∈ W) ∧
                      (∀ q ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ, v (X q, q.2) = q.1) ∧
                      (∀ p ∈ W, X (v p, p.2) = p.1) ∧
                      (∀ q ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ,
                        fderiv ℝ X q (1, 0) = 1 / fderiv ℝ v (X q, q.2) (1, 0) ∧
                        fderiv ℝ X q (0, 1) =
                          (-fderiv ℝ v (X q, q.2) (0, 1)) / fderiv ℝ v (X q, q.2) (1, 0)) ∧
                      (∀ q ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ,
                        1 / (2 * Real.sqrt quarticA_FIN06803) ≤ fderiv ℝ X q (1, 0) ∧
                        fderiv ℝ X q (1, 0) ≤ 2 / Real.sqrt quarticA_FIN06803) ∧
                      (∀ q ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ, ∀ ξ : Fin 2 → ℝ,
                        sqnorm_FIN06836 ξ / (1 + 8 / quarticA_FIN06803) ≤
                          sqnorm_FIN06836 ((Matrix.transpose
                            (Matrix.of ![![fderiv ℝ v (X q, q.2) (1, 0),
                              fderiv ℝ v (X q, q.2) (0, 1)], ![0, 1]])).mulVec ξ) ∧
                        sqnorm_FIN06836 ((Matrix.transpose
                            (Matrix.of ![![fderiv ℝ v (X q, q.2) (1, 0),
                              fderiv ℝ v (X q, q.2) (0, 1)], ![0, 1]])).mulVec ξ) ≤
                          (4 * quarticA_FIN06803 + 2) * sqnorm_FIN06836 ξ) ∧
                      (∀ p ∈ W, p.2 ^ 2 ≤ ρ ∧
                        deriv (deriv (fun t : ℝ => quarticPsi_FIN066 !₂[-4 + a (t ^ 2), t])) p.2 ≤
                          -c * p.2 ^ 2) := by
  obtain ⟨hb, -, hA, hD, -, hcancel, hc4⟩ := fin068_03_constants_exact_cancellation
  obtain ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, δx, δy, hδx, hδy, hseg, hcrit, hx0, hx0d, hφ, a₂,
    hdef, hsm, hbase, hbd, hfac, v, hvdef, hvsm, hen, hv0, hvx, hvy, U, hUo, hU0, hUP, hUb,
    N, hNo, hN0, hNU, hinj, himgo, ε, δ, hε, hδ, hcl, X, hX, W, hWdef, hWo, hW0, hWN, hWb,
    hbij, hTs, hXs, hXW, hXv, hXinv, hder, hjac, hener⟩ := fin068_13_jacobian_energy_metric
  obtain ⟨ρ, M₆, c, hρ, hM₆, hc, hred⟩ := reduced_FIN068CLOSE hz h1 h2 h3
  have hda : deriv a 0 = quarticD_FIN06803 / (32 * quarticA_FIN06803) :=
    fin068_23_first_derivative_critical_curve_any hz h1 h2 h3
  -- the shrunk rectangle
  set δ' : ℝ := min δ (Real.sqrt ρ) with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ (Real.sqrt_pos.2 hρ)
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hδ'ρ : δ' ≤ Real.sqrt ρ := min_le_right _ _
  have hQ : Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ') δ' ⊆ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ :=
    Set.prod_mono (subset_refl _) (Set.Ioo_subset_Ioo (neg_le_neg hδ'δ) hδ'δ)
  set T : ℝ × ℝ → ℝ × ℝ := fun p => (v p, p.2) with hT
  set W' : Set (ℝ × ℝ) := N ∩ T ⁻¹' (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ') δ') with hW'
  have hW'W : W' ⊆ W := by
    rw [hWdef]
    exact Set.inter_subset_inter_right _ (Set.preimage_mono hQ)
  have hW'N : W' ⊆ N := Set.inter_subset_left
  have hcont : ContinuousOn T N :=
    ((hvsm.mono (hNU.trans hUP)).continuousOn).prodMk continuousOn_snd
  have hW'o : IsOpen W' := hcont.isOpen_inter_preimage hNo (isOpen_Ioo.prod isOpen_Ioo)
  have hXW' : ∀ q ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ') δ', (X q, q.2) ∈ W' := by
    intro q hq
    refine ⟨hWN (hXW q (hQ hq)), ?_⟩
    show (v (X q, q.2), q.2) ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ') δ'
    rw [hXv q (hQ hq)]
    exact hq
  refine ⟨⟨hb, hA, hD, hcancel, hc4⟩, weighted_expansion_FIN068CLOSE, δu, δz, hu, hz, a, h1, h2, h3,
    h4, hda, curve_FIN068CLOSE hz h1 h2 h3, ρ, M₆, c, hρ, hM₆, hc, hred, δx, δy, hδx, hδy, hseg,
    hcrit, hx0, hx0d, hφ, a₂, hdef, hsm, hbase, hbd, hfac, v, hvdef, hvsm, hen, hv0, hvx, hvy, U,
    hUo, hU0, hUP, hUb, N, hNo, hN0, hNU, hinj, himgo, ε, δ', hε, hδ'pos,
    (closure_mono hQ).trans hcl, X, hX.mono hQ, W', rfl, hW'o, ⟨hN0, ?_⟩, hW'N,
    fun p hp => hWb p (hW'W hp), ⟨fun p hp => hp.2, hinj.mono hW'N, ?_⟩, hTs.mono hW'W,
    hXs.mono hQ, hXW', fun q hq => hXv q (hQ hq), fun p hp => hXinv p (hW'W hp),
    fun q hq => hder q (hQ hq), fun q hq => hjac q (hQ hq), fun q hq => hener q (hQ hq),
    fun p hp => ?_⟩
  · show (v (-4, 0), (0 : ℝ)) ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ') δ'
    rw [hv0]
    exact ⟨⟨by linarith, hε⟩, ⟨by linarith, hδ'pos⟩⟩
  · intro q hq
    obtain ⟨p, hp, hpq⟩ := hbij.2.2 (hQ hq)
    exact ⟨p, ⟨hWN hp, by rw [Set.mem_preimage]; rw [hpq]; exact hq⟩, hpq⟩
  · have hp2 : p.2 ∈ Set.Ioo (-δ') δ' := hp.2.2
    have hsq : p.2 ^ 2 ≤ ρ := by
      have := sq_le_sq' (by linarith [hp2.1, hδ'ρ] : -Real.sqrt ρ ≤ p.2)
        (by linarith [hp2.2, hδ'ρ] : p.2 ≤ Real.sqrt ρ)
      rwa [Real.sq_sqrt hρ.le] at this
    exact ⟨hsq, (hred p.2 hsq).2⟩

end DGPS.FiniteN
