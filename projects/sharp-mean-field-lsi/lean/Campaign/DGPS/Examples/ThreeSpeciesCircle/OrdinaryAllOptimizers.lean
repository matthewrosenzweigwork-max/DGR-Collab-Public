import DGPS.Examples.ThreeSpeciesCircle.ReducedQuartic

/-!
# STR028 (partial): the finite-dimensional asymptotic core of the all-optimizer scaling

This module proves the purely real-variable half of packet STR028.  Given the reduced
identity `F / R0² = 0` in the form

`-γ/2 - (9/20) h² - h q / 12 + R0²/48 + E = 0`, `q = (a³ - 3ab²)/(a²+b²)`,
`|E| ≤ K ((|h|+R0)³ + |γ|(|h|+R0) + γ²)`, `R0² = a²+b²`,

together with the trial-state inequality `γ ≤ -(16/15) h² + K₁ |h|³`, it proves
`|γ| + R0² ≤ 192 h²`, `R0 > |h|/2` (exclusion of the zero-amplitude endpoint, whose
correction `-9/10` is strictly above the trial `-16/15`), and that `(a/h, b/h)` lies within
`η` of one of the three minimizers `(2,0)`, `(-1,±√3)` of `reducedQuotient` for `|h|` small
(`allOptimizers_core`).

What is NOT proved here: producing this identity for an actual optimizer, i.e. the chart/Euler
translation (`rangeMap = 0` with `γ = quotient/(4π²) - 1`), the `R0²` factorization of the reduced
value with the stated remainder, and the explicit trial-state inequality.
-/

namespace DGPS.Examples.ThreeSpeciesCircle

theorem scaleCore_aux (K : ℝ) (hK : 0 ≤ K) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 1000 ∧ K * ε ≤ 1 / 1000 := by
  refine ⟨1 / (1000 * (K + 1)), by positivity, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  · rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith

theorem scaleCore (K : ℝ) (hK : 0 ≤ K) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 1000 ∧ ∀ h γ R q E : ℝ, |h| ≤ ε → R ≤ ε → |γ| ≤ ε → 0 ≤ R →
      γ ≤ 0 → |q| ≤ R →
      -γ / 2 - 9 / 20 * h ^ 2 - h * q / 12 + R ^ 2 / 48 + E = 0 →
      |E| ≤ K * ((|h| + R) ^ 3 + |γ| * (|h| + R) + γ ^ 2) →
      |γ| + R ^ 2 ≤ 192 * h ^ 2 := by
  obtain ⟨ε, hε, hε1, hKε⟩ := scaleCore_aux K hK
  refine ⟨ε, hε, hε1, ?_⟩
  intro h γ R q E hh hR hγ hR0 hγ0 hq heq hE
  have hs : |h| + R ≤ 2 * ε := by linarith
  have hs0 : 0 ≤ |h| + R := by positivity
  have h2 : (|h| + R) ^ 2 ≤ 2 * (h ^ 2 + R ^ 2) := by
    nlinarith [sq_abs h, sq_nonneg (|h| - R)]
  have e1 : K * (|h| + R) ^ 3 ≤ (2 / 1000) * (2 * (h ^ 2 + R ^ 2)) := by
    have : K * (|h| + R) ^ 3 = (K * (|h| + R)) * (|h| + R) ^ 2 := by ring
    rw [this]
    have : K * (|h| + R) ≤ 2 / 1000 := by nlinarith
    exact mul_le_mul this h2 (by positivity) (by norm_num)
  have e2 : K * (|γ| * (|h| + R)) ≤ (2 / 1000) * |γ| := by
    have : K * (|γ| * (|h| + R)) = |γ| * (K * (|h| + R)) := by ring
    rw [this]
    have : K * (|h| + R) ≤ 2 / 1000 := by nlinarith
    nlinarith [abs_nonneg γ]
  have e3 : K * γ ^ 2 ≤ (1 / 1000) * |γ| := by
    have : K * γ ^ 2 = |γ| * (K * |γ|) := by rw [← sq_abs]; ring
    rw [this]
    have : K * |γ| ≤ 1 / 1000 := by nlinarith [abs_nonneg γ]
    nlinarith [abs_nonneg γ]
  have hEb : |E| ≤ (4 / 1000) * (h ^ 2 + R ^ 2) + (3 / 1000) * |γ| := by
    have : K * ((|h| + R) ^ 3 + |γ| * (|h| + R) + γ ^ 2)
        = K * (|h| + R) ^ 3 + K * (|γ| * (|h| + R)) + K * γ ^ 2 := by ring
    rw [this] at hE
    nlinarith
  have hEl := abs_le.mp hEb
  have hγa : |γ| = -γ := abs_of_nonpos hγ0
  have hhq : |h * q| ≤ |h| * R := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hq (abs_nonneg h)
  have hhq' := abs_le.mp hhq
  have young : |h| * R ≤ R ^ 2 / 8 + 2 * h ^ 2 := by
    nlinarith [sq_abs h, sq_nonneg (R / 2 - 2 * |h|)]
  have hq2 := hhq'.1
  have hq3 := hhq'.2
  have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
  have hh2 : 0 ≤ h ^ 2 := sq_nonneg h
  have hg0 : 0 ≤ |γ| := abs_nonneg γ
  linarith [hEl.1, hEl.2]

theorem endpointExcluded (K K1 : ℝ) (hK : 0 ≤ K) (hK1 : 0 ≤ K1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h γ R q E : ℝ, 0 < |h| → |h| ≤ ε → R ≤ |h| / 2 → |γ| ≤ ε → 0 ≤ R →
      γ ≤ 0 → |q| ≤ R →
      -γ / 2 - 9 / 20 * h ^ 2 - h * q / 12 + R ^ 2 / 48 + E = 0 →
      |E| ≤ K * ((|h| + R) ^ 3 + |γ| * (|h| + R) + γ ^ 2) →
      γ ≤ -16 / 15 * h ^ 2 + K1 * |h| ^ 3 → False := by
  obtain ⟨ε0, hε0, hε01, hsc⟩ := scaleCore K hK
  refine ⟨min ε0 (1 / (24 * (K1 + 660 * K + 1))), lt_min hε0 (by positivity), ?_⟩
  intro h γ R q E hh0 hh hR hγ hR0 hγ0 hq heq hE htrial
  have hhε0 : |h| ≤ ε0 := hh.trans (min_le_left _ _)
  have hhε1 : |h| ≤ 1 / (24 * (K1 + 660 * K + 1)) := hh.trans (min_le_right _ _)
  have hγε0 : |γ| ≤ ε0 := hγ.trans (min_le_left _ _)
  have hRε : R ≤ ε0 := by linarith [abs_nonneg h]
  have hscale := hsc h γ R q E hhε0 hRε hγε0 hR0 hγ0 hq heq hE
  have hhs : |h| ^ 2 = h ^ 2 := sq_abs h
  have hh1 : |h| ≤ 1 := by linarith
  have hγa : |γ| = -γ := abs_of_nonpos hγ0
  have hγ2 : |γ| ≤ 192 * |h| ^ 2 := by have := sq_nonneg R; linarith
  have hs : |h| + R ≤ 3 / 2 * |h| := by linarith
  have hs0 : 0 ≤ |h| + R := by positivity
  have hh3 : 0 < |h| := hh0
  -- bound the remainder by 330 K |h|^3
  have t1 : (|h| + R) ^ 3 ≤ 4 * |h| ^ 3 := by
    have : (|h| + R) ^ 3 ≤ (3 / 2 * |h|) ^ 3 := pow_le_pow_left₀ hs0 hs 3
    nlinarith [pow_pos hh3 3]
  have t2 : |γ| * (|h| + R) ≤ 288 * |h| ^ 3 := by
    calc |γ| * (|h| + R) ≤ (192 * |h| ^ 2) * (3 / 2 * |h|) :=
          mul_le_mul hγ2 hs hs0 (by positivity)
      _ = 288 * |h| ^ 3 := by ring
  have t3 : γ ^ 2 ≤ 38 * |h| ^ 3 := by
    have : γ ^ 2 = |γ| ^ 2 := (sq_abs γ).symm
    rw [this]
    have h4 : |γ| ^ 2 ≤ (192 * |h| ^ 2) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hγ2 2
    have h5 : |h| ^ 4 ≤ |h| ^ 3 / 1000 := by
      have : |h| ≤ 1 / 1000 := hhε0.trans hε01
      nlinarith [pow_pos hh3 3]
    have := pow_pos hh3 3
    linarith
  have hEb : |E| ≤ 330 * K * |h| ^ 3 := by
    have : K * ((|h| + R) ^ 3 + |γ| * (|h| + R) + γ ^ 2) ≤ K * (330 * |h| ^ 3) :=
      mul_le_mul_of_nonneg_left (by linarith) hK
    linarith
  have hEl := abs_le.mp hEb
  have hhq : |h * q| ≤ |h| * R := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hq (abs_nonneg h)
  have hhq' := abs_le.mp hhq
  have hhR : |h| * R ≤ |h| * (|h| / 2) := mul_le_mul_of_nonneg_left hR (abs_nonneg h)
  have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
  have key : (1 / 12 : ℝ) * h ^ 2 ≤ (K1 + 660 * K) * |h| ^ 3 := by
    have := hhq'.1
    have := hhq'.2
    linarith
  have hM : 0 < K1 + 660 * K + 1 := by positivity
  have h3 : |h| ^ 3 = |h| * h ^ 2 := by rw [← hhs]; ring
  have hhpos : 0 < h ^ 2 := by rw [← hhs]; positivity
  have : (1 / 12 : ℝ) ≤ (K1 + 660 * K) * |h| := by
    have k2 : (1 / 12 : ℝ) * h ^ 2 ≤ ((K1 + 660 * K) * |h|) * h ^ 2 := by
      rw [h3] at key; linarith
    exact le_of_mul_le_mul_right k2 hhpos
  have h6 : (K1 + 660 * K + 1) * |h| ≤ 1 / 24 := by
    have := mul_le_mul_of_nonneg_left hhε1 hM.le
    have e : (K1 + 660 * K + 1) * (1 / (24 * (K1 + 660 * K + 1))) = 1 / 24 := by
      field_simp
    linarith
  nlinarith

theorem abs_cubic_div_le (a b : ℝ) (hS : 0 < a ^ 2 + b ^ 2) :
    |(a ^ 3 - 3 * a * b ^ 2) / (a ^ 2 + b ^ 2)| ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  set S := a ^ 2 + b ^ 2 with hSdef
  have hR := Real.sqrt_pos.mpr hS
  have hR2 : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS.le
  set R := Real.sqrt S
  have hP : (a ^ 3 - 3 * a * b ^ 2) ^ 2 ≤ (R ^ 3) ^ 2 := by
    have : (R ^ 3) ^ 2 = S ^ 3 := by rw [← pow_mul, mul_comm, pow_mul, hR2]
    rw [this, hSdef]; nlinarith [sq_nonneg (3 * a ^ 2 * b - b ^ 3)]
  have hP' : |a ^ 3 - 3 * a * b ^ 2| ≤ R ^ 3 := by
    exact abs_le_of_sq_le_sq hP (by positivity)
  rw [abs_div, abs_of_pos hS, div_le_iff₀ hS]
  calc |a ^ 3 - 3 * a * b ^ 2| ≤ R ^ 3 := hP'
    _ = R * S := by rw [← hR2]; ring

theorem quotient_gap (η : ℝ) (hη : 0 < η) :
    ∃ g0 : ℝ, 0 < g0 ∧ ∀ A B : ℝ, 1 / 4 ≤ A ^ 2 + B ^ 2 → A ^ 2 + B ^ 2 ≤ 192 →
      η ^ 2 ≤ (A - 2) ^ 2 + B ^ 2 → η ^ 2 ≤ (A + 1) ^ 2 + (B - Real.sqrt 3) ^ 2 →
      η ^ 2 ≤ (A + 1) ^ 2 + (B + Real.sqrt 3) ^ 2 →
      -16 / 15 + g0 ≤ reducedQuotient A B := by
  set T : Set (ℝ × ℝ) := {p | 1 / 4 ≤ p.1 ^ 2 + p.2 ^ 2 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ 192 ∧
      η ^ 2 ≤ (p.1 - 2) ^ 2 + p.2 ^ 2 ∧ η ^ 2 ≤ (p.1 + 1) ^ 2 + (p.2 - Real.sqrt 3) ^ 2 ∧
      η ^ 2 ≤ (p.1 + 1) ^ 2 + (p.2 + Real.sqrt 3) ^ 2} with hT
  by_cases hne : T.Nonempty
  · have hclosed : IsClosed T := by
      have c1 : Continuous fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2 := by fun_prop
      have c2 : Continuous fun p : ℝ × ℝ => (p.1 - 2) ^ 2 + p.2 ^ 2 := by fun_prop
      have c3 : Continuous fun p : ℝ × ℝ => (p.1 + 1) ^ 2 + (p.2 - Real.sqrt 3) ^ 2 := by
        fun_prop
      have c4 : Continuous fun p : ℝ × ℝ => (p.1 + 1) ^ 2 + (p.2 + Real.sqrt 3) ^ 2 := by
        fun_prop
      exact (isClosed_le continuous_const c1).inter ((isClosed_le c1 continuous_const).inter
        ((isClosed_le continuous_const c2).inter ((isClosed_le continuous_const c3).inter
        (isClosed_le continuous_const c4))))
    have hsub : T ⊆ Metric.closedBall (0 : ℝ × ℝ) 14 := by
      intro p hp
      obtain ⟨_, h2, _⟩ := hp
      rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
      constructor
      · nlinarith [abs_nonneg p.1, sq_abs p.1, sq_nonneg p.2]
      · nlinarith [abs_nonneg p.2, sq_abs p.2, sq_nonneg p.1]
    have hcomp : IsCompact T := (isCompact_closedBall (0 : ℝ × ℝ) 14).of_isClosed_subset hclosed hsub
    have hcont : ContinuousOn (fun p : ℝ × ℝ => reducedQuotient p.1 p.2) T := by
      unfold reducedQuotient
      apply ContinuousOn.sub
      · fun_prop
      · apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro p hp
        have := hp.1
        positivity
    obtain ⟨p0, hp0, hmin⟩ := hcomp.exists_isMinOn hne hcont
    obtain ⟨h1, h2, h3, h4, h5⟩ := hp0
    have hS0 : p0.1 ^ 2 + p0.2 ^ 2 ≠ 0 := by positivity
    obtain ⟨_, _, _, hq, hiff⟩ := reducedQuotient_exact_minimizers
    have hlow := (hq p0.1 p0.2 hS0).1
    have hne' : reducedQuotient p0.1 p0.2 ≠ -16 / 15 := by
      intro heq
      rcases (hq p0.1 p0.2 hS0).2.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [ha, hb] at h3; nlinarith
      · rw [ha, hb] at h4; nlinarith
      · rw [ha, hb] at h5; nlinarith
    refine ⟨reducedQuotient p0.1 p0.2 + 16 / 15, by
      have := lt_of_le_of_ne hlow (Ne.symm hne'); linarith, ?_⟩
    intro A B a1 a2 a3 a4 a5
    have := isMinOn_iff.mp hmin (A, B) (show (A, B) ∈ T from ⟨a1, a2, a3, a4, a5⟩)
    linarith
  · refine ⟨1, one_pos, ?_⟩
    intro A B a1 a2 a3 a4 a5
    exact absurd ⟨(A, B), a1, a2, a3, a4, a5⟩ hne

theorem reducedQuotient_scaled (a b h γ E : ℝ) (hh : h ≠ 0) (hS : 0 < a ^ 2 + b ^ 2)
    (heq : -γ / 2 - 9 / 20 * h ^ 2 - h * ((a ^ 3 - 3 * a * b ^ 2) / (a ^ 2 + b ^ 2)) / 12 +
      (a ^ 2 + b ^ 2) / 48 + E = 0) :
    reducedQuotient (a / h) (b / h) = (γ - 2 * E) / h ^ 2 := by
  have hS' : a ^ 2 + b ^ 2 ≠ 0 := hS.ne'
  have e : γ - 2 * E = -9 / 10 * h ^ 2 + (a ^ 2 + b ^ 2) / 24 -
      h * ((a ^ 3 - 3 * a * b ^ 2) / (a ^ 2 + b ^ 2)) / 6 := by linarith
  rw [e]
  unfold reducedQuotient
  field_simp

theorem remainder_6300 (K : ℝ) (hK : 0 ≤ K) (h γ R E : ℝ) (hh0 : 0 < |h|) (hh1000 : |h| ≤ 1 / 1000)
    (hR0 : 0 ≤ R) (hsc : |γ| + R ^ 2 ≤ 192 * h ^ 2)
    (hE : |E| ≤ K * ((|h| + R) ^ 3 + |γ| * (|h| + R) + γ ^ 2)) :
    |E| ≤ 6300 * K * |h| ^ 3 := by
  have hhs : |h| ^ 2 = h ^ 2 := sq_abs h
  have hh3 : 0 < |h| := hh0
  have hR14 : R ≤ 14 * |h| := by
    have h1 : R ^ 2 ≤ (14 * |h|) ^ 2 := by
      have := abs_nonneg γ
      have := hhs
      have := sq_nonneg h
      linarith
    exact (le_abs_self R).trans (abs_le_of_sq_le_sq h1 (by positivity))
  have hγ2 : |γ| ≤ 192 * |h| ^ 2 := by
    have := sq_nonneg R; linarith
  have hs : |h| + R ≤ 15 * |h| := by linarith
  have hs0 : 0 ≤ |h| + R := by positivity
  have t1 : (|h| + R) ^ 3 ≤ 3375 * |h| ^ 3 := by
    have : (|h| + R) ^ 3 ≤ (15 * |h|) ^ 3 := pow_le_pow_left₀ hs0 hs 3
    linarith
  have t2 : |γ| * (|h| + R) ≤ 2880 * |h| ^ 3 := by
    calc |γ| * (|h| + R) ≤ (192 * |h| ^ 2) * (15 * |h|) :=
          mul_le_mul hγ2 hs hs0 (by positivity)
      _ = 2880 * |h| ^ 3 := by ring
  have t3 : γ ^ 2 ≤ 38 * |h| ^ 3 := by
    have : γ ^ 2 = |γ| ^ 2 := (sq_abs γ).symm
    rw [this]
    have h4 : |γ| ^ 2 ≤ (192 * |h| ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hγ2 2
    have h5 : |h| ^ 4 ≤ |h| ^ 3 / 1000 := by nlinarith [pow_pos hh3 3]
    have := pow_pos hh3 3
    linarith
  have hEb : |E| ≤ 6300 * K * |h| ^ 3 := by
    have : K * ((|h| + R) ^ 3 + |γ| * (|h| + R) + γ ^ 2) ≤ K * (6300 * |h| ^ 3) :=
      mul_le_mul_of_nonneg_left (by have := pow_pos hh3 3; linarith) hK
    linarith
  exact hEb

theorem allOptimizers_core (K K1 : ℝ) (hK : 0 ≤ K) (hK1 : 0 ≤ K1) (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a b h γ E : ℝ, 0 < |h| → |h| ≤ ε → a ^ 2 + b ^ 2 ≤ ε ^ 2 → |γ| ≤ ε →
      0 < a ^ 2 + b ^ 2 →
      -γ / 2 - 9 / 20 * h ^ 2 - h * ((a ^ 3 - 3 * a * b ^ 2) / (a ^ 2 + b ^ 2)) / 12 +
        (a ^ 2 + b ^ 2) / 48 + E = 0 →
      |E| ≤ K * ((|h| + Real.sqrt (a ^ 2 + b ^ 2)) ^ 3 + |γ| * (|h| + Real.sqrt (a ^ 2 + b ^ 2)) +
        γ ^ 2) →
      γ ≤ -16 / 15 * h ^ 2 + K1 * |h| ^ 3 →
      |γ| + (a ^ 2 + b ^ 2) ≤ 192 * h ^ 2 ∧ |h| / 2 < Real.sqrt (a ^ 2 + b ^ 2) ∧
      ((a / h - 2) ^ 2 + (b / h) ^ 2 < η ^ 2 ∨
        (a / h + 1) ^ 2 + (b / h - Real.sqrt 3) ^ 2 < η ^ 2 ∨
        (a / h + 1) ^ 2 + (b / h + Real.sqrt 3) ^ 2 < η ^ 2) := by
  obtain ⟨g0, hg0, hgap⟩ := quotient_gap η hη
  obtain ⟨εB, hεB, hexcl⟩ := endpointExcluded K K1 hK hK1
  obtain ⟨εA, hεA, hεA1, hscale⟩ := scaleCore K hK
  refine ⟨min (min εA εB) (min (1 / (K1 + 1)) (g0 / (2 * (K1 + 12600 * K + 1)))),
    lt_min (lt_min hεA hεB) (lt_min (by positivity) (by positivity)), ?_⟩
  intro a b h γ E hh0 hh hab hγ hS heq hE htrial
  have hhA : |h| ≤ εA := hh.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hhB : |h| ≤ εB := hh.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhK : |h| ≤ 1 / (K1 + 1) := hh.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhG : |h| ≤ g0 / (2 * (K1 + 12600 * K + 1)) :=
    hh.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hγA : |γ| ≤ εA := hγ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγB : |γ| ≤ εB := hγ.trans ((min_le_left _ _).trans (min_le_right _ _))
  set ε := min (min εA εB) (min (1 / (K1 + 1)) (g0 / (2 * (K1 + 12600 * K + 1)))) with hεdef
  have hε0 : 0 < ε := lt_min (lt_min hεA hεB) (lt_min (by positivity) (by positivity))
  set S := a ^ 2 + b ^ 2 with hSdef
  set R := Real.sqrt S with hRdef
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = S := Real.sq_sqrt hS.le
  have hRε : R ≤ ε := (Real.sqrt_le_iff.mpr ⟨hε0.le, hab⟩)
  have hRA : R ≤ εA := hRε.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hq : |(a ^ 3 - 3 * a * b ^ 2) / S| ≤ R := abs_cubic_div_le a b hS
  -- sign of gamma
  have hhs : |h| ^ 2 = h ^ 2 := sq_abs h
  have hK1h : K1 * |h| ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hhK (by positivity : 0 ≤ K1 + 1)
    have e : (K1 + 1) * (1 / (K1 + 1)) = 1 := by field_simp
    nlinarith [abs_nonneg h]
  have hγ0 : γ ≤ 0 := by
    have h3 : K1 * |h| ^ 3 ≤ h ^ 2 := by
      have : K1 * |h| ^ 3 = (K1 * |h|) * h ^ 2 := by rw [← hhs]; ring
      rw [this]; nlinarith [sq_nonneg h]
    nlinarith [sq_nonneg h]
  have heqR : -γ / 2 - 9 / 20 * h ^ 2 - h * ((a ^ 3 - 3 * a * b ^ 2) / S) / 12 + R ^ 2 / 48 + E = 0 := by
    rw [hR2]; exact heq
  have hsc := hscale h γ R ((a ^ 3 - 3 * a * b ^ 2) / S) E hhA hRA hγA hR0 hγ0 hq heqR hE
  rw [hR2] at hsc
  have hlow : |h| / 2 < R := by
    by_contra hcon
    exact hexcl h γ R _ E hh0 hhB (not_lt.mp hcon) hγB hR0 hγ0 hq heqR hE htrial
  refine ⟨hsc, hlow, ?_⟩
  by_contra hcon
  simp only [not_or, not_lt] at hcon
  obtain ⟨c1, c2, c3⟩ := hcon
  have hh1 : h ≠ 0 := fun h0 => by simp [h0] at hh0
  have hhpos : 0 < h ^ 2 := by positivity
  -- scaled bounds
  have hA2 : (a / h) ^ 2 + (b / h) ^ 2 = S / h ^ 2 := by
    rw [hSdef]; field_simp
  have hlo : 1 / 4 ≤ (a / h) ^ 2 + (b / h) ^ 2 := by
    rw [hA2, le_div_iff₀ hhpos]
    have : (|h| / 2) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (by positivity) hlow.le 2
    linarith
  have hhi : (a / h) ^ 2 + (b / h) ^ 2 ≤ 192 := by
    rw [hA2, div_le_iff₀ hhpos]; linarith [sq_nonneg R, hsc, abs_nonneg γ]
  have hQ := hgap (a / h) (b / h) hlo hhi c1 c2 c3
  rw [reducedQuotient_scaled a b h γ E hh1 hS heq] at hQ
  -- remainder bound
  have hEb : |E| ≤ 6300 * K * |h| ^ 3 :=
    remainder_6300 K hK h γ R E hh0 (hhA.trans hεA1) hR0 (by rw [← hR2] at hsc; exact hsc) hE
  have hEl := abs_le.mp hEb
  -- conclude: (γ - 2E)/h² ≤ -16/15 + Λ|h|
  have hnum : γ - 2 * E ≤ (-16 / 15 + (K1 + 12600 * K) * |h|) * h ^ 2 := by
    have : (-16 / 15 + (K1 + 12600 * K) * |h|) * h ^ 2
        = -16 / 15 * h ^ 2 + K1 * |h| ^ 3 + 12600 * K * |h| ^ 3 := by
      rw [← hhs]; ring
    rw [this]; linarith [hEl.1, hEl.2]
  have hq2 : (γ - 2 * E) / h ^ 2 ≤ -16 / 15 + (K1 + 12600 * K) * |h| := by
    rw [div_le_iff₀ hhpos]; exact hnum
  have hΛ : (K1 + 12600 * K) * |h| ≤ g0 / 2 := by
    have hΛ0 : 0 < K1 + 12600 * K + 1 := by positivity
    have := mul_le_mul_of_nonneg_left hhG hΛ0.le
    have e : (K1 + 12600 * K + 1) * (g0 / (2 * (K1 + 12600 * K + 1))) = g0 / 2 := by
      field_simp
    rw [e] at this
    linarith [abs_nonneg h]
  linarith
end DGPS.Examples.ThreeSpeciesCircle
