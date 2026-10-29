import SharpSymmetricLSI.Infra.HeatCircle
import SharpSymmetricLSI.Infra.Mollify
import SharpSymmetricLSI.Infra.Heat

/-!
# The periodic heat kernel on `𝕋^ι` (I4, part 1)

The circle kernel `heatK t` of `Infra/HeatCircle` is smooth, `1`-periodic, positive, and has
Fourier coefficients `e^{-4π²n²t}`. The torus kernel is the product
`P_t(x) = ∏ₖ K_t(xₖ)` (`heatPL` on the lift, `heatP` on `𝕋^ι`); it is smooth, positive, bounded
below by a positive constant, and has Fourier coefficients `e^{-4π²|k|²t}`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped Real ContDiff

namespace SharpLSI

/-! ### The circle kernel -/

theorem contDiff_heatSeries {c : ℤ → ℂ} {C : ℝ} (hc : ∀ n, ‖c n‖ ≤ C) {t : ℝ} (ht : 0 < t) :
    ∀ (n : ℕ) (j : ℕ), ContDiff ℝ n (fun x => heatSeries c j t x) := by
  intro n
  induction n with
  | zero =>
    intro j
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x =>
      (hasDerivAt_heatSeries_x hc j ht x).continuousAt)
  | succ n ih =>
    intro j
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hasDerivAt_heatSeries_x hc j ht x).differentiableAt, by simp, ?_⟩
    have : deriv (fun x => heatSeries c j t x) = fun x => heatSeries c (j + 1) t x :=
      funext fun x => (hasDerivAt_heatSeries_x hc j ht x).deriv
    rw [this]
    exact ih (j + 1)

theorem contDiff_heatK {t : ℝ} (ht : 0 < t) : ContDiff ℝ ∞ (heatK t) := by
  have h : ContDiff ℝ ∞ (fun x => heatSeries (fun _ => (1 : ℂ)) 0 t x) :=
    contDiff_infty.2 fun n => contDiff_heatSeries (C := 1) (fun _ => by simp) ht n 0
  exact reCLM.contDiff.comp h

/-- The circle kernel is real: `(K_t(x) : ℂ) = ∑ₙ e^{-4π²n²t} e^{2πinx}`. -/
theorem heatK_coe (t x : ℝ) :
    ((heatK t x : ℝ) : ℂ) = heatSeries (fun _ => (1 : ℂ)) 0 t x := by
  rw [heatK, ← Complex.conj_eq_iff_re]
  unfold heatSeries
  rw [Complex.conj_tsum, ← (Equiv.neg ℤ).tsum_eq]
  congr 1; funext n
  simp only [Equiv.neg_apply, heatTerm, pow_zero, mul_one, map_mul, one_mul,
    Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  · push_cast; ring_nf
  · simp only [map_ofNat, Complex.conj_I, map_intCast]
    push_cast; ring

/-- Fourier coefficients of the circle kernel. -/
theorem heatK_fourier {t : ℝ} (ht : 0 < t) (m : ℤ) :
    ∫ x in (0 : ℝ)..1, (heatK t x : ℂ) * cexp (-(2 * π * I * m * x)) =
      (Real.exp (-(4 * π ^ 2) * m ^ 2 * t) : ℂ) := by
  simp_rw [heatK_coe]
  rw [heatCoeff_heatSeries (C := 1) (fun _ => by simp) ht m, one_mul]

theorem heatK_add_int (t x : ℝ) (m : ℤ) : heatK t (x + m) = heatK t x := by
  rw [periodic_eq_fract (heatK_add_one t) (x + m), Int.fract_add_intCast,
    ← periodic_eq_fract (heatK_add_one t) x]

theorem heatK_bdd {t : ℝ} (ht : 0 < t) : ∃ M, ∀ x, |heatK t x| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (contDiff_heatK ht).continuous.continuousOn
  refine ⟨M, fun x => ?_⟩
  rw [periodic_eq_fract (heatK_add_one t) x]
  exact hM _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

/-! ### The torus kernel -/

variable {ι : Type*} [Fintype ι]

/-- The torus heat kernel on the lift, `P_t(x) = ∏ₖ K_t(xₖ)`. -/
noncomputable def heatPL (t : ℝ) (x : ι → ℝ) : ℝ := ∏ k, heatK t (x k)

/-- The torus heat kernel `P_t` on `𝕋^ι`. -/
noncomputable def heatP (t : ℝ) (z : UnitAddTorus ι) : ℝ := heatPL t (secT z)

theorem heatPL_add_intVec (t : ℝ) (x : ι → ℝ) (m : ι → ℤ) :
    heatPL t (x + intVec m) = heatPL t x := by
  unfold heatPL
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Pi.add_apply, intVec]
  exact heatK_add_int t (x k) (m k)

theorem heatP_liftT (t : ℝ) (x : ι → ℝ) : heatP t (liftT x) = heatPL t x := by
  obtain ⟨m, hm⟩ := secT_liftT_eq x
  rw [heatP, hm, heatPL_add_intVec]

theorem contDiff_heatPL {t : ℝ} (ht : 0 < t) : ContDiff ℝ ∞ (heatPL (ι := ι) t) := by
  unfold heatPL
  exact contDiff_prod fun k _ => (contDiff_heatK ht).comp (contDiff_apply ℝ ℝ k)

theorem heatPL_pos {t : ℝ} (ht : 0 < t) (x : ι → ℝ) : 0 < heatPL t x :=
  Finset.prod_pos fun k _ => heatK_pos ht (x k)

theorem heatP_pos {t : ℝ} (ht : 0 < t) (z : UnitAddTorus ι) : 0 < heatP t z :=
  heatPL_pos ht _

/-- A positive lower bound for the torus kernel. -/
theorem heatP_lower {t : ℝ} (ht : 0 < t) : ∃ c > 0, ∀ z : UnitAddTorus ι, c ≤ heatP t z := by
  obtain ⟨m, hm, hle⟩ := heatK_lower ht le_rfl
  refine ⟨m ^ Fintype.card ι, by positivity, fun z => ?_⟩
  unfold heatP heatPL
  have : m ^ Fintype.card ι = ∏ _k : ι, m := by rw [Finset.prod_const, Finset.card_univ]
  rw [this]
  exact Finset.prod_le_prod₀ (fun _ _ => hm.le) fun k _ => hle t ⟨le_rfl, le_rfl⟩ _

theorem heatP_bdd {t : ℝ} (ht : 0 < t) : ∃ M, ∀ z : UnitAddTorus ι, |heatP t z| ≤ M := by
  obtain ⟨M, hM⟩ := heatK_bdd ht
  refine ⟨M ^ Fintype.card ι, fun z => ?_⟩
  unfold heatP heatPL
  have : M ^ Fintype.card ι = ∏ _k : ι, M := by rw [Finset.prod_const, Finset.card_univ]
  rw [Finset.abs_prod, this]
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun k _ => hM _

theorem continuous_heatP {t : ℝ} (ht : 0 < t) : Continuous (heatP (ι := ι) t) := by
  have hq : Topology.IsQuotientMap (liftT (ι := ι)) := by
    refine (IsOpenQuotientMap.isQuotientMap ?_)
    exact IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  rw [hq.continuous_iff]
  have : heatP t ∘ liftT = heatPL (ι := ι) t := funext fun x => heatP_liftT t x
  rw [this]
  exact (contDiff_heatPL ht).continuous

theorem measurable_heatP {t : ℝ} (ht : 0 < t) : Measurable (heatP (ι := ι) t) :=
  (continuous_heatP ht).measurable

end SharpLSI
