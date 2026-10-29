import DGPS.FiniteN.FalseMinimumFIN079
import DGPS.FiniteN.FalseMinimumFIN084
import DGPS.FiniteN.Tools.PositiveRate

/-!
# FIN085: false-minimum exact Arrhenius row

For every fixed `κ > 2` and `0 < h < h_c(κ)` the three finite-`N` rates `λ_N`
(`particlePoincareRate`), `r_N^all` (`particleRateAll`) and `r_N^sym` (`particleRateSym`) of the
scalar cosine model satisfy `N⁻¹ log rate_N → -B`, where `B = ψ_h(t_b) - ψ_h(t_-) > 0` with
`t_b = -s₁` (the barrier top) and `t_- = -s₂` (the false minimum) from the FIN076 geometry.
Equivalently `rate_N = exp(-N B + o(N))`.

Route.
* Lower exponents (FIN079).  The published statement of `false_minimum_all_test_particle_lower_exponents`
  only asserts `∃ B > 0`; the number is `ψ(-s₁) - ψ(-s₂)` for the geometry produced inside FIN078,
  but that fact is not recorded in the statement.  To compare with the upper exponent of FIN084
  we therefore rerun the FIN079 constant chase (`lambda_lower_FIN079`, `rall_lower_N_FIN079`)
  from the FIN078 theorem, which exposes the geometry, with the exponent kept explicit.
* Upper exponents (FIN084).  `false_minimum_symmetric_quotient_upper_barrier` already bounds the
  `limsup` of all three rates by `-B'`, with `B' = ψ(-s₁') - ψ(-s₂')` for *its* geometry.
* Identification.  The FIN076 geometry is unique (`geometry_unique_FIN085`), hence `B = B'`.
* The symmetric lower bound follows from `r_all ≤ r_sym` (FIN001).
* `liminf ≥ -B` and `limsup ≤ -B` in `EReal` give convergence of the real sequence, and the
  remainder `o(N) = log rate_N + N B` is exponentiated using the strict positivity of the rates.
-/

open Filter Topology
open scoped ENNReal

namespace DGPS.FiniteN.FalseMinimumFIN085

open DGPS DGPS.Models DGPS.FiniteN.ScalarFoldFIN056 DGPS.FiniteN.FalseMinimumFIN076
  DGPS.FiniteN.FalseMinimumFIN079

/-! ### Uniqueness of the FIN076 geometry -/

/-- The FIN076 geometry `(s₁, s₂, t₊)` is determined by `(κ, h)`: the barrier top `-s₁` is the
unique critical point with negative second derivative, the false minimum `-s₂` the unique
critical point with positive second derivative other than the global minimum `t₊`, which is the
unique global minimizer.  Hence `B = ψ(-s₁) - ψ(-s₂)` does not depend on the chosen geometry. -/
theorem geometry_unique_FIN085 {κ h s1 s2 tp s1' s2' tp' : ℝ}
    (G : FalseMinimumGeometryFIN076 κ h s1 s2 tp)
    (G' : FalseMinimumGeometryFIN076 κ h s1' s2' tp') :
    s1 = s1' ∧ s2 = s2' ∧ tp = tp' := by
  obtain ⟨-, -, -, hc, h5, h6, h7, -, h9⟩ := G
  obtain ⟨-, -, -, hc', h5', h6', h7', -, h9'⟩ := G'
  have htp : tp = tp' := by
    by_contra hne
    have a := h7.2 tp' (Ne.symm hne)
    have b := h7'.2 tp hne
    linarith
  have hs1 : -s1' = -s1 := by
    have hcrit : deriv (scalarPsi κ h) (-s1') = 0 := (hc' (-s1')).2 (Or.inr (Or.inl rfl))
    rcases (hc (-s1')).1 hcrit with h1 | h1 | h1
    · exfalso
      have := h6'.1
      rw [h1] at this
      linarith [h5.1]
    · exact h1
    · exfalso
      have := h6'.1
      rw [h1] at this
      linarith [h7.1]
  have hs2 : -s2' = -s2 := by
    have hcrit : deriv (scalarPsi κ h) (-s2') = 0 := (hc' (-s2')).2 (Or.inl rfl)
    rcases (hc (-s2')).1 hcrit with h1 | h1 | h1
    · exact h1
    · exfalso
      have := h5'.1
      rw [h1] at this
      linarith [h6.1]
    · exfalso
      have := h9'.1
      rw [h1, ← htp] at this
      linarith
  exact ⟨by linarith, by linarith, htp⟩

/-! ### Lower exponents with the barrier kept explicit -/

/-- The FIN079 Poincare lower bound `λ_N ≥ c N⁻¹ e^{-N B}`, for any `B` and any auxiliary
Poincare lower bound `λ_aux ≥ c₀ e^{-N B}`.  (This is the constant chase of `lambda_lower_FIN079`
with the exponent exposed.) -/
theorem lambda_lower_gen_FIN085 (κ h : ℝ) (hκ : 2 < κ) {B c0 : ℝ} (hB : 0 < B) (hc0 : 0 < c0)
    (hr : ∀ N : ℝ, 1 ≤ N → ENNReal.ofReal (c0 * Real.exp (-(N * B))) ≤
      FalseMinimumFIN078.poincareRateFIN078 Set.univ
        (FalseMinimumFIN077.auxDensityFIN077 (scalarPsi κ h) N)) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ+,
      ENNReal.ofReal (c * (N : ℝ)⁻¹ * Real.exp (-((N : ℝ) * B))) ≤
        DGPS.particlePoincareRate (scalarCosine κ h) N := by
  have hKp := Kc_pos_FIN079 κ h
  have hc : 0 < (Kc_FIN079 κ h * (1 + 1 / c0))⁻¹ := by positivity
  refine ⟨_, hc, fun N => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hlam : 0 < c0 * Real.exp (-((N : ℝ) * B)) := by positivity
  have hmain := poincare_N_FIN079 (by linarith) h N hlam (hr N hN1)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmain
  have hE : 1 ≤ (N : ℝ) * Real.exp ((N : ℝ) * B) := by
    have : 1 ≤ Real.exp ((N : ℝ) * B) := Real.one_le_exp (by positivity)
    nlinarith
  have hEp : 0 < Real.exp ((N : ℝ) * B) := Real.exp_pos _
  have e1 : (Kc_FIN079 κ h * (1 + 1 / c0))⁻¹ * (N : ℝ)⁻¹ * Real.exp (-((N : ℝ) * B)) =
      (Kc_FIN079 κ h * (1 + 1 / c0) * ((N : ℝ) * Real.exp ((N : ℝ) * B)))⁻¹ := by
    rw [Real.exp_neg]
    field_simp
  rw [e1]
  apply inv_anti₀ (by positivity)
  have e2 : (N : ℝ) / (c0 * Real.exp (-((N : ℝ) * B))) =
      (N : ℝ) * Real.exp ((N : ℝ) * B) / c0 := by
    rw [Real.exp_neg]
    field_simp
  rw [e2]
  have : 1 + (N : ℝ) * Real.exp ((N : ℝ) * B) / c0 ≤
      (1 + 1 / c0) * ((N : ℝ) * Real.exp ((N : ℝ) * B)) := by
    have h3 : 0 < 1 / c0 := by positivity
    have h4 : (N : ℝ) * Real.exp ((N : ℝ) * B) / c0 =
        1 / c0 * ((N : ℝ) * Real.exp ((N : ℝ) * B)) := by ring
    rw [h4]
    nlinarith
  calc Kc_FIN079 κ h * (1 + (N : ℝ) * Real.exp ((N : ℝ) * B) / c0)
      ≤ Kc_FIN079 κ h * ((1 + 1 / c0) * ((N : ℝ) * Real.exp ((N : ℝ) * B))) :=
        mul_le_mul_of_nonneg_left this hKp.le
    _ = _ := by ring

/-- The FIN079 all-test lower bound `r_all ≥ c' N⁻² e^{-N B}` from the Poincare lower bound
`λ_N ≥ c N⁻¹ e^{-N B}` (the constant chase of `rall_lower_N_FIN079` with the exponent exposed). -/
theorem rall_lower_gen_FIN085 (κ h : ℝ) (hκ : 2 < κ) {B c : ℝ} (hB : 0 < B) (hc : 0 < c)
    (hlam : ∀ N : ℕ+, ENNReal.ofReal (c * (N : ℝ)⁻¹ * Real.exp (-((N : ℝ) * B))) ≤
      DGPS.particlePoincareRate (scalarCosine κ h) N) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ N : ℕ+,
      ENNReal.ofReal (c' * ((N : ℝ) ^ 2)⁻¹ * Real.exp (-((N : ℝ) * B))) ≤
        DGPS.particleRateAll (scalarCosine κ h) N := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set a : ℝ := 2 / (4 * Real.pi ^ 2) with ha
  have ha0 : 0 < a := by positivity
  set s : ℝ := |h| + κ with hs
  have hs0 : 0 ≤ s := by positivity
  set Q : ℝ := a + (s + 2) / c with hQ
  have hQ0 : 0 < Q := by positivity
  refine ⟨2 / Q, by positivity, fun N => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hEp : 0 < Real.exp ((N : ℝ) * B) := Real.exp_pos _
  have hE1 : 1 ≤ Real.exp ((N : ℝ) * B) := Real.one_le_exp (by positivity)
  have hr : 0 < c * (N : ℝ)⁻¹ * Real.exp (-((N : ℝ) * B)) := by positivity
  have hdef := DGPS.FiniteN.EntropyDefects.cos_entropy_defect N h (κ := κ) (by linarith)
  have hmain := rall_lower_FIN079 (scalarCosine κ h) N (a := a) (b := s * N) ha0.le
    (by positivity) hr hdef (hlam N)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmain
  have e1 : (s * N + 2) / (c * (N : ℝ)⁻¹ * Real.exp (-((N : ℝ) * B))) =
      (s * N + 2) * N * Real.exp ((N : ℝ) * B) / c := by
    rw [Real.exp_neg]
    field_simp
  rw [e1]
  have hle : a + (s * N + 2) * N * Real.exp ((N : ℝ) * B) / c ≤
      (N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B) * Q := by
    have h1 : (s * N + 2) * N * Real.exp ((N : ℝ) * B) / c ≤
        (s + 2) * ((N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B)) / c := by
      apply div_le_div_of_nonneg_right _ hc.le
      have : (s * N + 2) * N ≤ (s + 2) * (N : ℝ) ^ 2 := by nlinarith
      calc (s * N + 2) * N * Real.exp ((N : ℝ) * B)
          ≤ (s + 2) * (N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B) := by gcongr
        _ = _ := by ring
    have h2 : a ≤ a * ((N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B)) := by
      have : 1 ≤ (N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B) := by nlinarith
      nlinarith
    have h3 : (s + 2) * ((N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B)) / c =
        (s + 2) / c * ((N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B)) := by ring
    rw [h3] at h1
    calc _ ≤ a * ((N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B)) +
          (s + 2) / c * ((N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B)) := add_le_add h2 h1
      _ = _ := by rw [hQ]; ring
  have hpos : 0 < a + (s * N + 2) * N * Real.exp ((N : ℝ) * B) / c := by positivity
  have e2 : 2 / Q * ((N : ℝ) ^ 2)⁻¹ * Real.exp (-((N : ℝ) * B)) =
      2 / ((N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B) * Q) := by
    rw [Real.exp_neg]
    field_simp
  rw [e2]
  exact div_le_div_of_nonneg_left (by norm_num) hpos hle

/-- The FIN079 lower bounds with the FIN076 geometry, and hence the barrier
`B = ψ(-s₁) - ψ(-s₂)`, kept explicit. -/
theorem lower_exposed_FIN085 (κ h : ℝ) (hκ : 2 < κ) (hh0 : 0 < h)
    (hhc : h < scalarFoldField κ) :
    ∃ s1 s2 tp : ℝ, FalseMinimumGeometryFIN076 κ h s1 s2 tp ∧
      ∃ c : ℝ, 0 < c ∧ (∀ N : ℕ+,
        ENNReal.ofReal (c * (N : ℝ)⁻¹ *
            Real.exp (-((N : ℝ) * (scalarPsi κ h (-s1) - scalarPsi κ h (-s2))))) ≤
          DGPS.particlePoincareRate (scalarCosine κ h) N) ∧
      ∃ c' : ℝ, 0 < c' ∧ ∀ N : ℕ+,
        ENNReal.ofReal (c' * ((N : ℝ) ^ 2)⁻¹ *
            Real.exp (-((N : ℝ) * (scalarPsi κ h (-s1) - scalarPsi κ h (-s2))))) ≤
          DGPS.particleRateAll (scalarCosine κ h) N := by
  obtain ⟨s1, s2, tp, -, -, -, -, hgeom, c0, hc0, hr⟩ :=
    FalseMinimumFIN078.false_minimum_auxiliary_exponential_lower κ h hκ hh0 hhc
  have hB : 0 < scalarPsi κ h (-s1) - scalarPsi κ h (-s2) := hgeom.2.2.2.2.2.2.2.1.1
  obtain ⟨c, hc, hlam⟩ := lambda_lower_gen_FIN085 κ h hκ hB hc0 hr
  obtain ⟨c', hc', hall⟩ := rall_lower_gen_FIN085 κ h hκ hB hc hlam
  exact ⟨s1, s2, tp, hgeom, c, hc, hlam, c', hc', hall⟩

/-! ### From `liminf`/`limsup` bounds to the Arrhenius row -/

/-- A real sequence with `liminf ≥ -B` and `limsup ≤ -B` (in `EReal`) converges to `-B`. -/
theorem tendsto_of_liminf_limsup_FIN085 {u : ℕ+ → ℝ} {B : ℝ}
    (hinf : ((-B : ℝ) : EReal) ≤ liminf (fun N : ℕ+ => ((u N : ℝ) : EReal)) atTop)
    (hsup : limsup (fun N : ℕ+ => ((u N : ℝ) : EReal)) atTop ≤ ((-B : ℝ) : EReal)) :
    Tendsto u atTop (𝓝 (-B)) :=
  EReal.tendsto_coe.1 (tendsto_of_le_liminf_of_limsup_le hinf hsup)

/-- A strictly positive finite rate with `N⁻¹ log rate_N → -B` equals `exp(-N B + o(N))`, with
`o(N) = log rate_N + N B` and `o(N)/N → 0`. -/
theorem exp_remainder_FIN085 {R : ℕ+ → ℝ≥0∞} {B : ℝ} (hpos : ∀ N, 0 < (R N).toReal)
    (hbr : ∀ N, ENNReal.ofReal (R N).toReal = R N)
    (hT : Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹ * Real.log (R N).toReal) atTop (𝓝 (-B))) :
    ∃ o : ℕ+ → ℝ, Tendsto (fun N : ℕ+ => o N / ((N : ℕ) : ℝ)) atTop (𝓝 0) ∧
      ∀ N : ℕ+, R N = ENNReal.ofReal (Real.exp (-(((N : ℕ) : ℝ) * B) + o N)) := by
  refine ⟨fun N => Real.log (R N).toReal + ((N : ℕ) : ℝ) * B, ?_, fun N => ?_⟩
  · have h1 : Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹ * Real.log (R N).toReal + B) atTop
        (𝓝 (-B + B)) := hT.add_const B
    rw [neg_add_cancel] at h1
    refine h1.congr fun N => ?_
    have hN : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
    field_simp
  · have : -(((N : ℕ) : ℝ) * B) + (Real.log (R N).toReal + ((N : ℕ) : ℝ) * B) =
        Real.log (R N).toReal := by ring
    rw [this, Real.exp_log (hpos N), hbr N]

/-- **Row bundle**: for a strictly positive finite rate, `liminf ≥ -B` and `limsup ≤ -B` yield the
limit and the `exp(-N B + o(N))` form. -/
theorem row_of_bounds_FIN085 {R : ℕ+ → ℝ≥0∞} {B : ℝ} (hpos : ∀ N, 0 < (R N).toReal)
    (hbr : ∀ N, ENNReal.ofReal (R N).toReal = R N)
    (hinf : ((-B : ℝ) : EReal) ≤ liminf (fun N : ℕ+ =>
      ((((N : ℕ) : ℝ)⁻¹ * Real.log (R N).toReal : ℝ) : EReal)) atTop)
    (hsup : limsup (fun N : ℕ+ =>
      ((((N : ℕ) : ℝ)⁻¹ * Real.log (R N).toReal : ℝ) : EReal)) atTop ≤ ((-B : ℝ) : EReal)) :
    Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹ * Real.log (R N).toReal) atTop (𝓝 (-B)) ∧
      ∃ o : ℕ+ → ℝ, Tendsto (fun N : ℕ+ => o N / ((N : ℕ) : ℝ)) atTop (𝓝 0) ∧
        ∀ N : ℕ+, R N = ENNReal.ofReal (Real.exp (-(((N : ℕ) : ℝ) * B) + o N)) := by
  have hT := tendsto_of_liminf_limsup_FIN085 hinf hsup
  exact ⟨hT, exp_remainder_FIN085 hpos hbr hT⟩

end DGPS.FiniteN.FalseMinimumFIN085

namespace DGPS.FiniteN

open DGPS DGPS.Models DGPS.FiniteN.FalseMinimumFIN076 DGPS.FiniteN.FalseMinimumFIN085

/-- **False minimum: exact Arrhenius row.**  For every fixed `κ > 2` and `0 < h < h_c(κ)` there is
the FIN076 geometry `(s₁, s₂, t₊)` such that, with `B = ψ_h(-s₁) - ψ_h(-s₂) = ψ_h(t_b) - ψ_h(t_-)`
(`t_b = -s₁`, `t_- = -s₂`), one has `B > 0` and each of the Poincare rate `λ_N`, the all-test
rate `r_N^all` and the symmetric rate `r_N^sym` satisfies `N⁻¹ log rate_N → -B`; equivalently
`rate_N = exp(-N B + o(N))` with `o(N)/N → 0`.  No prefactor and no uniform near-fold window
is asserted. -/
theorem false_minimum_exact_arrhenius_row (κ h : ℝ) (hκ : 2 < κ) (hh0 : 0 < h)
    (hhc : h < scalarFoldField κ) :
    ∃ s1 s2 tp : ℝ, FalseMinimumGeometryFIN076 κ h s1 s2 tp ∧
      ∃ B : ℝ, B = scalarPsi κ h (-s1) - scalarPsi κ h (-s2) ∧ 0 < B ∧
        Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹ *
          Real.log (particlePoincareRate (scalarCosine κ h) N).toReal) atTop (𝓝 (-B)) ∧
        Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹ *
          Real.log (particleRateAll (scalarCosine κ h) N).toReal) atTop (𝓝 (-B)) ∧
        Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹ *
          Real.log (particleRateSym (scalarCosine κ h) N).toReal) atTop (𝓝 (-B)) ∧
        (∃ o : ℕ+ → ℝ, Tendsto (fun N : ℕ+ => o N / ((N : ℕ) : ℝ)) atTop (𝓝 0) ∧
          ∀ N : ℕ+, particlePoincareRate (scalarCosine κ h) N =
            ENNReal.ofReal (Real.exp (-(((N : ℕ) : ℝ) * B) + o N))) ∧
        (∃ o : ℕ+ → ℝ, Tendsto (fun N : ℕ+ => o N / ((N : ℕ) : ℝ)) atTop (𝓝 0) ∧
          ∀ N : ℕ+, particleRateAll (scalarCosine κ h) N =
            ENNReal.ofReal (Real.exp (-(((N : ℕ) : ℝ) * B) + o N))) ∧
        (∃ o : ℕ+ → ℝ, Tendsto (fun N : ℕ+ => o N / ((N : ℕ) : ℝ)) atTop (𝓝 0) ∧
          ∀ N : ℕ+, particleRateSym (scalarCosine κ h) N =
            ENNReal.ofReal (Real.exp (-(((N : ℕ) : ℝ) * B) + o N))) := by
  obtain ⟨s1, s2, tp, hG, c, hc, hlam, c', hc', hall⟩ := lower_exposed_FIN085 κ h hκ hh0 hhc
  obtain ⟨s1', s2', tp', hG', B', hB', hBpos, hP, hA, hS⟩ :=
    false_minimum_symmetric_quotient_upper_barrier κ h hκ hh0 hhc
  obtain ⟨e1, e2, -⟩ := geometry_unique_FIN085 hG hG'
  subst e1 e2
  set B : ℝ := scalarPsi κ h (-s1) - scalarPsi κ h (-s2) with hBdef
  have hBeq : B' = B := hB'
  rw [hBeq] at hP hA hS hBpos
  -- lower exponents (FIN079 chain with explicit `B`) and the positive real bridge (FIN001)
  have hinfP : ((-B : ℝ) : EReal) ≤ liminf (fun N : ℕ+ =>
      ((((N : ℕ) : ℝ)⁻¹ * Real.log (particlePoincareRate (scalarCosine κ h) N).toReal : ℝ) :
        EReal)) atTop := by
    refine FalseMinimumFIN079.liminf_lower_FIN079 (B := B) hc 1
      (fun N => (particlePoincareRate (scalarCosine κ h) N).toReal) (fun N => ?_)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hP'⟩ :=
      finite_positive_particle_rate_and_real_bridge (scalarCosine κ h) Nat.one_pos N
    have := (hP' _).1 (hlam N)
    simpa using this
  have hinfA : ((-B : ℝ) : EReal) ≤ liminf (fun N : ℕ+ =>
      ((((N : ℕ) : ℝ)⁻¹ * Real.log (particleRateAll (scalarCosine κ h) N).toReal : ℝ) :
        EReal)) atTop := by
    refine FalseMinimumFIN079.liminf_lower_FIN079 (B := B) hc' 2
      (fun N => (particleRateAll (scalarCosine κ h) N).toReal) (fun N => ?_)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hA', -, -⟩ :=
      finite_positive_particle_rate_and_real_bridge (scalarCosine κ h) Nat.one_pos N
    exact (hA' _).1 (hall N)
  have hinfS : ((-B : ℝ) : EReal) ≤ liminf (fun N : ℕ+ =>
      ((((N : ℕ) : ℝ)⁻¹ * Real.log (particleRateSym (scalarCosine κ h) N).toReal : ℝ) :
        EReal)) atTop := by
    refine FalseMinimumFIN079.liminf_lower_FIN079 (B := B) hc' 2
      (fun N => (particleRateSym (scalarCosine κ h) N).toReal) (fun N => ?_)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hS', -⟩ :=
      finite_positive_particle_rate_and_real_bridge (scalarCosine κ h) Nat.one_pos N
    exact (hS' _).1 ((hall N).trans (DGPS.particleRateAll_le_sym (scalarCosine κ h) N))
  have bridge : ∀ N : ℕ+,
      (0 < (particlePoincareRate (scalarCosine κ h) N).toReal ∧
        ENNReal.ofReal (particlePoincareRate (scalarCosine κ h) N).toReal =
          particlePoincareRate (scalarCosine κ h) N) ∧
      (0 < (particleRateAll (scalarCosine κ h) N).toReal ∧
        ENNReal.ofReal (particleRateAll (scalarCosine κ h) N).toReal =
          particleRateAll (scalarCosine κ h) N) ∧
      (0 < (particleRateSym (scalarCosine κ h) N).toReal ∧
        ENNReal.ofReal (particleRateSym (scalarCosine κ h) N).toReal =
          particleRateSym (scalarCosine κ h) N) := fun N => by
    obtain ⟨-, -, -, -, -, ⟨pa, ps, pp⟩, ba, bs, bp, -⟩ :=
      finite_positive_particle_rate_and_real_bridge (scalarCosine κ h) Nat.one_pos N
    exact ⟨⟨pp, bp⟩, ⟨pa, ba⟩, ⟨ps, bs⟩⟩
  obtain ⟨TP, EP⟩ := row_of_bounds_FIN085 (fun N => (bridge N).1.1) (fun N => (bridge N).1.2)
    hinfP hP
  obtain ⟨TA, EA⟩ := row_of_bounds_FIN085 (fun N => (bridge N).2.1.1) (fun N => (bridge N).2.1.2)
    hinfA hA
  obtain ⟨TS, ES⟩ := row_of_bounds_FIN085 (fun N => (bridge N).2.2.1) (fun N => (bridge N).2.2.2)
    hinfS hS
  exact ⟨s1, s2, tp, hG, B, rfl, hBpos, TP, TA, TS, EP, EA, ES⟩

end DGPS.FiniteN
