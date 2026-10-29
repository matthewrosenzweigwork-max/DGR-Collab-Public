import DGPS.FiniteN.CriticalXYLower
import DGPS.FiniteN.CriticalXYMoment
import DGPS.FiniteN.RotationalTools
import DGPS.FiniteN.Tools.Linearization
import DGPS.FiniteN.Tools.PositiveRate
import DGPS.Particle.Contractions

/-!
# Critical XY row power bounds (FIN033)

At `κ = 2`, `h = 0` (`IsCriticalXY`), the unrestricted Poincare rate `λ_N`
(`particlePoincareRate`) and the LSI rates `r_N^all`, `r_N^sym` (`particleRateAll`,
`particleRateSym`) are all `Θ_{1/2}` in `N`, in the normalisation `a0 * N^(-1/2)` (`a0 = 4 π²`).

* `ofReal_le_particlePoincareRate_of_rateAll` : `r_N^all ≤ λ_N` (a lower bound on `r_N^all` is a
  lower bound on `λ_N`); proved by truncating a general `H¹` test to a bounded one, applying the
  bounded-test linearization (FIN003), and passing to the limit.
* `critical_magnetization_quotient_limit` : the symmetric magnetization Poincare quotient
  `Q_N = a0 / (1 + (N-1) ∫ g² dη_N)` satisfies `√N Q_N → a0 √π / 2`.
* `critical_rates_le_magnetization_quotient` : each of the three rates is `≤ Q_N` (upper test
  constant only; no optimal prefactor is claimed).
* `critical_row_power_bounds` : the packaged two-sided `Θ_{1/2}` statement.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.FiniteN

/-- Truncation of a real number to `[-n, n]`. -/
noncomputable def clampNat (n : ℕ) (t : ℝ) : ℝ := max (min t (n : ℝ)) (-(n : ℝ))

theorem clampNat_continuous (n : ℕ) : Continuous (clampNat n) := by
  unfold clampNat; fun_prop

theorem abs_clampNat_le_self (n : ℕ) (t : ℝ) : |clampNat n t| ≤ |t| := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  unfold clampNat
  simp only [max_def, min_def]
  split_ifs <;> rw [abs_le] <;> constructor <;>
    linarith [le_abs_self t, neg_abs_le t, neg_le_abs t, abs_nonneg t]

theorem abs_clampNat_le (n : ℕ) (t : ℝ) : |clampNat n t| ≤ n := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  unfold clampNat
  rw [abs_le]
  constructor
  · exact le_max_right _ _
  · exact max_le (min_le_right _ _) (by linarith)

theorem clampNat_eventually_eq (t : ℝ) : ∀ᶠ n : ℕ in atTop, clampNat n t = t := by
  obtain ⟨m, hm⟩ := exists_nat_ge |t|
  filter_upwards [eventually_ge_atTop m] with n hn
  have h1 : |t| ≤ n := hm.trans (by exact_mod_cast hn)
  have := abs_le.1 h1
  unfold clampNat
  rw [min_eq_left this.2, max_eq_left this.1]

theorem ofReal_le_particlePoincareRate_of_rateAll {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (r : ℝ) (h : ENNReal.ofReal r ≤ particleRateAll A N) :
    ENNReal.ofReal r ≤ particlePoincareRate A N := by
  have hP : IsProbabilityMeasure (particleLaw A N) :=
    DGPS.Particle.particleLaw_isProbabilityMeasure' A N
  rw [le_particlePoincareRate_iff_forall]
  intro g _
  have hmg : MemLp g.1 2 (particleLaw A N) := g.2.choose_spec.memLp
  have hgm : AEStronglyMeasurable g.1 (particleLaw A N) := hmg.aestronglyMeasurable
  set u : ℕ → ParticleSpace d N → ℝ := fun n x => clampNat n (g.1 x) with hu
  have hum : ∀ n, AEStronglyMeasurable (u n) (particleLaw A N) := fun n =>
    (clampNat_continuous n).comp_aestronglyMeasurable hgm
  have hub : ∀ n x, |u n x| ≤ n := fun n x => abs_clampNat_le n _
  have huint : ∀ n, Integrable (u n) (particleLaw A N) := fun n =>
    Integrable.of_bound (hum n) n (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hub n x)
  have huL2 : ∀ n, MemLp (u n) 2 (particleLaw A N) := fun n =>
    memLp_of_bounded (a := -(n:ℝ)) (b := n) (Filter.Eventually.of_forall fun x => abs_le.1 (hub n x)) (hum n) 2
  have key : ∀ n : ℕ, r * ProbabilityTheory.variance (u n) (particleLaw A N) ≤
      particleEnergy A N g := by
    intro n
    have h1 : MemParticleH1 A N (fun x => min (g.1 x) (n:ℝ)) := g.2.min_const _
    have h2 : MemParticleH1 A N (u n) := h1.max_const _
    let g1 : ParticleH1 A N := ⟨_, h1⟩
    let g2 : ParticleH1 A N := ⟨u n, h2⟩
    have e1 : particleEnergy A N g1 ≤ particleEnergy A N g :=
      particleEnergy_min_const_le g g1 (n:ℝ) rfl
    have e2 : particleEnergy A N g2 ≤ particleEnergy A N g1 :=
      particleEnergy_max_const_le g1 g2 (-(n:ℝ)) rfl
    set m : ℝ := ∫ x, u n x ∂particleLaw A N with hm
    have h3 : MemParticleH1 A N (fun x => 1 * u n x + (-m)) := h2.affine 1 (-m)
    let F : ParticleH1 A N := ⟨_, h3⟩
    have e3 : particleEnergy A N F = 1 ^ 2 * particleEnergy A N g2 :=
      particleEnergy_affine g2 F 1 (-m) rfl
    have hFeq : F.1 = fun x => u n x + (-m) := by funext x; simp [F]
    have hvarF : ProbabilityTheory.variance F.1 (particleLaw A N) =
        ProbabilityTheory.variance (u n) (particleLaw A N) := by
      rw [hFeq]; exact ProbabilityTheory.variance_add_const (hum n) _
    have hm_abs : |m| ≤ n := by
      have := norm_integral_le_of_norm_le_const (μ := particleLaw A N) (f := u n) (C := (n:ℝ))
        (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hub n x)
      simpa [Real.norm_eq_abs, hm] using this
    have hFb : ∀ x, |F x| ≤ 2 * n := by
      intro x
      have : F x = u n x + (-m) := by simp [F]
      rw [this]
      calc |u n x + -m| ≤ |u n x| + |-m| := abs_add_le _ _
        _ ≤ n + n := by rw [abs_neg]; exact add_le_add (hub n x) hm_abs
        _ = 2 * n := by ring
    have hFmean : ∫ x, F x ∂particleLaw A N = 0 := by
      have : (fun x => F x) = fun x => u n x + (-m) := hFeq
      rw [this, integral_add (huint n) (integrable_const _)]
      simp [hm]
    by_cases hv : 0 < ProbabilityTheory.variance F.1 (particleLaw A N)
    · have hlin := (bounded_test_lsi_linearization A N F (2 * n) hFb hFmean hv).2.2.1
      have h' := h.trans hlin
      have hnn : 0 ≤ particleEnergy A N F / ProbabilityTheory.variance F.1 (particleLaw A N) :=
        div_nonneg (particleEnergy_nonneg F) hv.le
      have h'' := (ENNReal.ofReal_le_ofReal_iff hnn).1 h'
      rw [le_div_iff₀ hv, hvarF] at h''
      have : particleEnergy A N F ≤ particleEnergy A N g := by
        rw [e3]; linarith
      rw [← hvarF] at h'' ⊢
      linarith
    · have : ProbabilityTheory.variance (u n) (particleLaw A N) = 0 := by
        rw [← hvarF]
        exact le_antisymm (not_lt.1 hv) (ProbabilityTheory.variance_nonneg _ _)
      rw [this, mul_zero]
      exact particleEnergy_nonneg g
  -- convergence of the variances
  have hmean_tend : Tendsto (fun n : ℕ => ∫ x, u n x ∂particleLaw A N) atTop
      (𝓝 (∫ x, g.1 x ∂particleLaw A N)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖g.1 x‖) (fun n => hum n)
      (hmg.integrable one_le_two).norm (fun n => Filter.Eventually.of_forall fun x => ?_)
      (Filter.Eventually.of_forall fun x => ?_)
    · simpa [Real.norm_eq_abs] using abs_clampNat_le_self n (g.1 x)
    · exact tendsto_const_nhds.congr' ((clampNat_eventually_eq (g.1 x)).mono fun n hn => hn.symm)
  have hsq_tend : Tendsto (fun n : ℕ => ∫ x, (u n x) ^ 2 ∂particleLaw A N) atTop
      (𝓝 (∫ x, (g.1 x) ^ 2 ∂particleLaw A N)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => (g.1 x) ^ 2)
      (fun n => (hum n).pow 2) hmg.integrable_sq (fun n => Filter.Eventually.of_forall fun x => ?_)
      (Filter.Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_pow, ← sq_abs (g.1 x)]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_clampNat_le_self n _) 2
    · refine (tendsto_const_nhds (x := (g.1 x) ^ 2)).congr' ?_
      filter_upwards [clampNat_eventually_eq (g.1 x)] with n hn
      simp [hu, hn]
  have hvar_tend : Tendsto (fun n : ℕ => ProbabilityTheory.variance (u n) (particleLaw A N))
      atTop (𝓝 (ProbabilityTheory.variance g.1 (particleLaw A N))) := by
    have e : ∀ n, ProbabilityTheory.variance (u n) (particleLaw A N) =
        ∫ x, (u n x) ^ 2 ∂particleLaw A N - (∫ x, u n x ∂particleLaw A N) ^ 2 := fun n => by
      rw [ProbabilityTheory.variance_eq_sub (huL2 n)]; simp
    have e' : ProbabilityTheory.variance g.1 (particleLaw A N) =
        ∫ x, (g.1 x) ^ 2 ∂particleLaw A N - (∫ x, g.1 x ∂particleLaw A N) ^ 2 := by
      rw [ProbabilityTheory.variance_eq_sub hmg]; simp
    simp_rw [e]; rw [e']
    exact hsq_tend.sub (hmean_tend.pow 2)
  exact le_of_tendsto' (hvar_tend.const_mul r) key

/-! ### Magnetization upper test -/

open DGPS.Circle.BesselMoments

/-- The symmetric magnetization Poincare quotient `E(F)/Var(F)` for `F = ∑ᵢ cos(2π xᵢ)` at the
critical XY model. -/
noncomputable def criticalMagnetizationQuotient (N : ℕ+) : ℝ :=
  DGPS.Circle.AngularNormalization.a0 / (1 + ((N : ℝ) - 1) * ∫ z, besselRatio ‖z‖ ^ 2 ∂criticalAuxiliaryLaw (N : ℝ))

theorem critical_aux_sum_pos (N : ℕ+) :
    0 < 1 + ((N : ℝ) - 1) * ∫ z, besselRatio ‖z‖ ^ 2 ∂criticalAuxiliaryLaw (N : ℝ) := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hI : 0 ≤ ∫ z, besselRatio ‖z‖ ^ 2 ∂criticalAuxiliaryLaw (N : ℝ) :=
    integral_nonneg fun _ => sq_nonneg _
  have : 0 ≤ ((N : ℝ) - 1) * ∫ z, besselRatio ‖z‖ ^ 2 ∂criticalAuxiliaryLaw (N : ℝ) :=
    mul_nonneg (by linarith) hI
  linarith

theorem criticalMagnetizationQuotient_pos (N : ℕ+) : 0 < criticalMagnetizationQuotient N :=
  div_pos DGPS.Circle.AngularNormalization.a0_pos (critical_aux_sum_pos N)

theorem rpow_three_halves (N : ℕ+) : (N : ℝ) ^ (3 / 2 : ℝ) = (N : ℝ) * Real.sqrt (N : ℝ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hN, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

theorem rpow_neg_half (N : ℕ+) : (N : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (N : ℝ))⁻¹ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  rw [Real.rpow_neg hN.le, Real.sqrt_eq_rpow]

/-- `√N Q_N → DGPS.Circle.AngularNormalization.a0 √π / 2`: the magnetization quotient is asymptotic to `DGPS.Circle.AngularNormalization.a0 √π / (2 √N)`. -/
theorem critical_magnetization_quotient_limit :
    Tendsto (fun N : ℕ+ => Real.sqrt (N : ℝ) * criticalMagnetizationQuotient N) atTop
      (𝓝 (DGPS.Circle.AngularNormalization.a0 * Real.sqrt Real.pi / 2)) := by
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hinv := critical_variance_limit.inv₀ (by positivity : (1 / Real.sqrt Real.pi) ≠ 0)
  have h2 := hinv.const_mul (DGPS.Circle.AngularNormalization.a0 / 2)
  have hval : DGPS.Circle.AngularNormalization.a0 / 2 * (1 / Real.sqrt Real.pi)⁻¹ = DGPS.Circle.AngularNormalization.a0 * Real.sqrt Real.pi / 2 := by
    field_simp
  rw [hval] at h2
  refine h2.congr fun N => ?_
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hN
  have hS := critical_aux_sum_pos N
  unfold criticalMagnetizationQuotient
  rw [rpow_three_halves]
  field_simp

theorem critical_rates_le_magnetization_quotient {A : InteractionData 1} (hA : IsCriticalXY A)
    (N : ℕ+) :
    particleRateAll A N ≤ ENNReal.ofReal (criticalMagnetizationQuotient N) ∧
    particleRateSym A N ≤ ENNReal.ofReal (criticalMagnetizationQuotient N) ∧
    particlePoincareRate A N ≤ ENNReal.ofReal (criticalMagnetizationQuotient N) := by
  obtain ⟨f, hfeq, _, _, hsym, hmean, hvar, hE, hq⟩ :=
    rotational_symmetric_magnetization_variance_critical hA N
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hS := critical_aux_sum_pos N
  have hvpos : 0 < ProbabilityTheory.variance f.1 (particleLaw A N) := by
    rw [hvar]; positivity
  have hb : ∀ x, |f x| ≤ (N : ℝ) := by
    intro x
    have h1 : f x = ∑ i, (mode 1 (x i)).re := by
      have := congrFun hfeq x
      simpa using this
    rw [h1]
    calc |∑ i, (mode 1 (x i)).re| ≤ ∑ i, |(mode 1 (x i)).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
          rw [mode_apply]; simp [fourier_apply]
      _ = N := by simp
  have hquot : particleEnergy A N f / ProbabilityTheory.variance f.1 (particleLaw A N) =
      criticalMagnetizationQuotient N := by
    rw [hE, hvar]
    unfold criticalMagnetizationQuotient
    field_simp
  have hlin := bounded_test_lsi_linearization A N f (N : ℝ) hb hmean hvpos
  rw [hquot] at hlin
  refine ⟨hlin.2.2.1, hlin.2.2.2 hsym, ?_⟩
  refine (particlePoincareRate_le_quotient A N f hvpos).trans (le_of_eq ?_)
  rw [hq]; rfl

/-- The `Θ_{1/2}` window: uniform in the critical model, `c DGPS.Circle.AngularNormalization.a0 N^(-1/2) ≤ rate ≤ C DGPS.Circle.AngularNormalization.a0 N^(-1/2)`
for every `N ≥ N₀`, for `λ_N`, `r_N^all` and `r_N^sym` (real parts of the `ℝ≥0∞` rates). -/
theorem critical_row_power_bounds :
    Tendsto (fun N : ℕ+ => Real.sqrt (N : ℝ) * criticalMagnetizationQuotient N) atTop
      (𝓝 (DGPS.Circle.AngularNormalization.a0 * Real.sqrt Real.pi / 2)) ∧
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ A : InteractionData 1, IsCriticalXY A →
        (∀ N : ℕ+,
          (0 < (particlePoincareRate A N).toReal ∧ 0 < (particleRateAll A N).toReal ∧
            0 < (particleRateSym A N).toReal) ∧
          (particlePoincareRate A N).toReal ≤ criticalMagnetizationQuotient N ∧
          (particleRateAll A N).toReal ≤ criticalMagnetizationQuotient N ∧
          (particleRateSym A N).toReal ≤ criticalMagnetizationQuotient N ∧
          (particleRateAll A N).toReal ≤ (particleRateSym A N).toReal ∧
          (particleRateAll A N).toReal ≤ (particlePoincareRate A N).toReal ∧
          c * DGPS.Circle.AngularNormalization.a0 * (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (particleRateAll A N).toReal) ∧
        (∀ N : ℕ+, N₀ ≤ (N : ℕ) →
          ((particlePoincareRate A N).toReal ≤ C * DGPS.Circle.AngularNormalization.a0 * (N : ℝ) ^ (-(1 / 2 : ℝ)) ∧
            (particleRateAll A N).toReal ≤ C * DGPS.Circle.AngularNormalization.a0 * (N : ℝ) ^ (-(1 / 2 : ℝ)) ∧
            (particleRateSym A N).toReal ≤ C * DGPS.Circle.AngularNormalization.a0 * (N : ℝ) ^ (-(1 / 2 : ℝ)))) := by
  refine ⟨critical_magnetization_quotient_limit, ?_⟩
  obtain ⟨γ, c, hγ, hc, hlow⟩ := critical_unrestricted_lsi_lower_bound
  have ha0 := DGPS.Circle.AngularNormalization.a0_pos
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hev : ∀ᶠ N : ℕ+ in atTop,
      Real.sqrt (N : ℝ) * criticalMagnetizationQuotient N <
        DGPS.Circle.AngularNormalization.a0 * (Real.sqrt Real.pi / 2 + 1) :=
    critical_magnetization_quotient_limit.eventually
      (Iio_mem_nhds (by nlinarith [ha0]))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨c, Real.sqrt Real.pi / 2 + 1, hc, by positivity, (N0 : ℕ), N0.pos, ?_⟩
  intro A hA
  refine ⟨fun N => ?_, fun N hN => ?_⟩
  · obtain ⟨_, _, ⟨hAp, hAt⟩, ⟨hSp, hSt⟩, ⟨hPp, hPt⟩, ⟨hAr, hSr, hPr⟩, _, _, _, hAS, hAiff,
      _, _⟩ := finite_positive_particle_rate_and_real_bridge A (by norm_num : 0 < 1) N
    obtain ⟨hAQ, hSQ, hPQ⟩ := critical_rates_le_magnetization_quotient hA N
    have hQ := (criticalMagnetizationQuotient_pos N).le
    have hlowN := (hlow A hA N).2
    have hl : c * DGPS.Circle.AngularNormalization.a0 * (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (particleRateAll A N).toReal :=
      (hAiff _).1 hlowN
    have hPge : (particleRateAll A N).toReal ≤ (particlePoincareRate A N).toReal := by
      have h1 : ENNReal.ofReal (particleRateAll A N).toReal ≤ particleRateAll A N := by
        rw [ENNReal.ofReal_toReal hAt.ne]
      have h2 := ofReal_le_particlePoincareRate_of_rateAll A N _ h1
      exact (ENNReal.ofReal_le_iff_le_toReal hPt.ne).1 h2
    exact ⟨⟨hPr, hAr, hSr⟩, ENNReal.toReal_le_of_le_ofReal hQ hPQ,
      ENNReal.toReal_le_of_le_ofReal hQ hAQ, ENNReal.toReal_le_of_le_ofReal hQ hSQ, hAS, hPge, hl⟩
  · have hN' : N0 ≤ N := hN
    have hQb := hN0 N hN'
    have hNp : (0 : ℝ) < N := by exact_mod_cast N.pos
    have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNp
    obtain ⟨hAQ, hSQ, hPQ⟩ := critical_rates_le_magnetization_quotient hA N
    have hQ := (criticalMagnetizationQuotient_pos N).le
    have hQN : criticalMagnetizationQuotient N ≤
        (Real.sqrt Real.pi / 2 + 1) * DGPS.Circle.AngularNormalization.a0 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [rpow_neg_half, ← div_eq_mul_inv, le_div_iff₀ hs]
      nlinarith
    obtain ⟨_, _, ⟨_, hAt⟩, ⟨_, hSt⟩, ⟨_, hPt⟩, _⟩ :=
      finite_positive_particle_rate_and_real_bridge A (by norm_num : 0 < 1) N
    exact ⟨(ENNReal.toReal_le_of_le_ofReal hQ hPQ).trans hQN,
      (ENNReal.toReal_le_of_le_ofReal hQ hAQ).trans hQN,
      (ENNReal.toReal_le_of_le_ofReal hQ hSQ).trans hQN⟩

/-- `Θ_{1/2}` in the `ThetaScale` form for each of the three critical rates. -/
theorem critical_row_thetaScale {A : InteractionData 1} (hA : IsCriticalXY A) :
    ThetaScale (1 / 2) (fun n : ℕ => if h : 0 < n then (particlePoincareRate A ⟨n, h⟩).toReal
      else 0) ∧
    ThetaScale (1 / 2) (fun n : ℕ => if h : 0 < n then (particleRateAll A ⟨n, h⟩).toReal
      else 0) ∧
    ThetaScale (1 / 2) (fun n : ℕ => if h : 0 < n then (particleRateSym A ⟨n, h⟩).toReal
      else 0) := by
  obtain ⟨-, c, C, hc, hC, N₀, hN₀, h⟩ := critical_row_power_bounds
  have ha0 := DGPS.Circle.AngularNormalization.a0_pos
  obtain ⟨hlow, hup⟩ := h A hA
  refine ⟨⟨c * DGPS.Circle.AngularNormalization.a0, C * DGPS.Circle.AngularNormalization.a0, by positivity, by positivity, N₀, hN₀, fun n hn => ?_⟩,
    ⟨c * DGPS.Circle.AngularNormalization.a0, C * DGPS.Circle.AngularNormalization.a0, by positivity, by positivity, N₀, hN₀, fun n hn => ?_⟩,
    ⟨c * DGPS.Circle.AngularNormalization.a0, C * DGPS.Circle.AngularNormalization.a0, by positivity, by positivity, N₀, hN₀, fun n hn => ?_⟩⟩
  · have hn0 : 0 < n := lt_of_lt_of_le hN₀ hn
    obtain ⟨-, -, -, -, -, hAP, hlowA⟩ := hlow ⟨n, hn0⟩
    obtain ⟨hu1, -, -⟩ := hup ⟨n, hn0⟩ hn
    simp only [PNat.mk_coe] at hlowA hu1
    simp only [hn0, ↓reduceDIte]
    exact ⟨hlowA.trans hAP, hu1⟩
  · have hn0 : 0 < n := lt_of_lt_of_le hN₀ hn
    obtain ⟨-, -, -, -, -, -, hlowA⟩ := hlow ⟨n, hn0⟩
    obtain ⟨-, hu2, -⟩ := hup ⟨n, hn0⟩ hn
    simp only [PNat.mk_coe] at hlowA hu2
    simp only [hn0, ↓reduceDIte]
    exact ⟨hlowA, hu2⟩
  · have hn0 : 0 < n := lt_of_lt_of_le hN₀ hn
    obtain ⟨-, -, -, -, hAS, -, hlowA⟩ := hlow ⟨n, hn0⟩
    obtain ⟨-, -, hu3⟩ := hup ⟨n, hn0⟩ hn
    simp only [PNat.mk_coe] at hlowA hu3
    simp only [hn0, ↓reduceDIte]
    exact ⟨hlowA.trans hAS, hu3⟩

end DGPS.FiniteN
