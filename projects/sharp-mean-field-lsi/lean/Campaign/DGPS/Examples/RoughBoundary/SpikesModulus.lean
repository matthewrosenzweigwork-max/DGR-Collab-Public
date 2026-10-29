import DGPS.Examples.RoughBoundary.Spikes

/-!
# Explicit sub-Lipschitz modulus and every strict Hölder exponent (RUF004)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 1.3.  For the common primitive
`gT` of RUF002 (`c = hMean`, `C₀ = modulusConst = e/(e-1) + 4c`):

* if `0 < δ = d_T(x,y) ≤ e^(-8)` (`d_T = DGPS.torusDist`) then
  `|g x - g y| ≤ C₀ δ exp((log (1/δ))^(1/3))`;
* for every `0 < α < 1`, `|g x - g y| ≤ max {C₀ exp(2/(3√(3(1-α)))), 2 c e^(8α)} · d_T(x,y)^α`
  for all `x y`, i.e. `[g]_{C^α} ≤ max {…} < ∞`.

Proof route: periodicity of the level-`n` spike indicator with period `1/M_n` gives
`∫_I h_n ≤ (M_n δ + 1) e^(-n)/(n M_n)` (slightly sharper than the source's `M_n δ + 2`), and
`∫_I h_n ≤ e^n δ` pointwise; split at `N = ⌊R^(1/3)⌋`, `R = log (1/δ)`.
Placed in this new module (not `Spikes.lean`) by campaign instruction; the interface name stays in
the namespace `DGPS.Examples.RoughBoundary.Spikes`.
-/

open MeasureTheory Set

namespace DGPS.Examples.RoughBoundary.Spikes

lemma pt_add_int (t : ℝ) (k : ℤ) : pt (t + k) = pt t := by
  funext i
  show (((t + k : ℝ)) : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ))
  rw [AddCircle.coe_add]
  have : ((k : ℝ) : AddCircle (1 : ℝ)) = 0 := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).2 ⟨k, by simp⟩
  rw [this, add_zero]

lemma pt_eq_iff {s t : ℝ} : pt s = pt t ↔ ∃ k : ℤ, t = s + k := by
  constructor
  · intro h
    have h2 : ((s : ℝ) : AddCircle (1 : ℝ)) = (t : ℝ) := congrFun h 0
    have h0 : ((t - s : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub, ← h2, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h0
    exact ⟨n, by simp at hn; linarith⟩
  · rintro ⟨k, rfl⟩
    exact (pt_add_int s k).symm

lemma pt_mem_E_iff {n : ℕ} (t : ℝ) :
    pt t ∈ E n ↔ ∃ j : ℤ, (j : ℝ) / M n ≤ t ∧ t < (j : ℝ) / M n + ell n := by
  have hM := M_real_pos (n := n)
  constructor
  · intro h
    rw [E_eq_image] at h
    obtain ⟨s, hs, hst⟩ := h
    obtain ⟨k, hk⟩ := pt_eq_iff.1 hst
    simp only [Ereal, mem_iUnion, Finset.mem_range, mem_Ico, exists_prop] at hs
    obtain ⟨j, hj, h1, h2⟩ := hs
    refine ⟨j + k * M n, ?_, ?_⟩
    · push_cast
      have : ((j : ℝ) + k * M n) / M n = j / M n + k := by field_simp
      rw [this]; linarith
    · push_cast
      have : ((j : ℝ) + k * M n) / M n = j / M n + k := by field_simp
      rw [this]; linarith
  · rintro ⟨j, h1, h2⟩
    have hMpos : (0 : ℤ) < M n := by exact_mod_cast (M_pos (n := n))
    set r := j % (M n : ℤ) with hr
    set q := j / (M n : ℤ) with hq
    have hjrq : j = r + (M n : ℤ) * q := (Int.emod_add_mul_ediv j _).symm
    have hr0 : 0 ≤ r := Int.emod_nonneg _ hMpos.ne'
    have hr1 : r < M n := Int.emod_lt_of_pos _ hMpos
    rw [E_eq_image]
    refine ⟨t - q, ?_, ?_⟩
    · simp only [Ereal, mem_iUnion, Finset.mem_range, mem_Ico, exists_prop]
      refine ⟨r.toNat, by omega, ?_, ?_⟩
      · have : ((r.toNat : ℕ) : ℝ) = (r : ℝ) := by
          have := Int.toNat_of_nonneg hr0
          exact_mod_cast this
        rw [this]
        have hj' : (j : ℝ) = r + M n * q := by exact_mod_cast hjrq
        rw [hj'] at h1
        have : ((r : ℝ) + M n * q) / M n = r / M n + q := by field_simp
        rw [this] at h1; linarith
      · have : ((r.toNat : ℕ) : ℝ) = (r : ℝ) := by
          have := Int.toNat_of_nonneg hr0
          exact_mod_cast this
        rw [this]
        have hj' : (j : ℝ) = r + M n * q := by exact_mod_cast hjrq
        rw [hj'] at h2
        have : ((r : ℝ) + M n * q) / M n = r / M n + q := by field_simp
        rw [this] at h2; linarith
    · have := pt_add_int (t - q) q
      simpa using this.symm

lemma h_pt_periodic (n : ℕ) : Function.Periodic (fun t : ℝ => h n (pt t)) (1 / (M n : ℝ)) := by
  have hM := M_real_pos (n := n)
  intro t
  have key : pt (t + 1 / (M n : ℝ)) ∈ E n ↔ pt t ∈ E n := by
    rw [pt_mem_E_iff, pt_mem_E_iff]
    constructor
    · rintro ⟨j, h1, h2⟩
      refine ⟨j - 1, ?_, ?_⟩ <;> push_cast <;> 
      · have : ((j : ℝ) - 1) / M n = j / M n - 1 / M n := by field_simp
        rw [this]; linarith
    · rintro ⟨j, h1, h2⟩
      refine ⟨j + 1, ?_, ?_⟩ <;> push_cast <;> 
      · have : ((j : ℝ) + 1) / M n = j / M n + 1 / M n := by field_simp
        rw [this]; linarith
  by_cases ht : pt t ∈ E n
  · have h2 := key.2 ht
    simp only [h, Set.indicator_of_mem ht, Set.indicator_of_mem h2]
  · have h2 : pt (t + 1 / (M n : ℝ)) ∉ E n := fun hh => ht (key.1 hh)
    simp only [h, Set.indicator_of_notMem ht, Set.indicator_of_notMem h2]


lemma h_pt_ii (n : ℕ) (a b : ℝ) : IntervalIntegrable (fun t : ℝ => h (n + 2) (pt t)) volume a b := by
  have hm : Measurable fun t : ℝ => h (n + 2) (pt t) := (h_meas n).comp measurable_pt
  refine (intervalIntegrable_const (c := A (n + 2))).mono_fun hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have h0 := h_nonneg (n + 2) (pt t)
  have h1 : h (n + 2) (pt t) ≤ A (n + 2) := by
    unfold h; exact Set.indicator_le_self' (fun _ _ => (Real.exp_pos _).le) _
  show ‖h (n + 2) (pt t)‖ ≤ ‖A (n + 2)‖
  rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (by unfold A; positivity)]; exact h1

lemma integral_h_pt_period (n : ℕ) :
    ∫ t in (0 : ℝ)..(1 / (M (n + 2) : ℝ)), h (n + 2) (pt t) =
      Real.exp (-((n + 2 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ) * M (n + 2)) := by
  have hM := M_real_pos (n := n + 2)
  have hper := h_pt_periodic (n + 2)
  have h1 := hper.intervalIntegral_add_zsmul_eq (M (n + 2) : ℤ) 0 (h_pt_ii n)
  have hT : ((M (n + 2) : ℤ) • (1 / (M (n + 2) : ℝ))) = 1 := by
    simp only [zsmul_eq_mul, Int.cast_natCast]; field_simp
  rw [hT, zero_add, zero_add] at h1
  have h2 : ∫ t in (0 : ℝ)..1, h (n + 2) (pt t) = Real.exp (-((n + 2 : ℕ) : ℝ)) / ((n + 2 : ℕ) : ℝ) := by
    rw [intervalIntegral.integral_of_le zero_le_one,
      ← integral_haar_eq (h_meas n).aestronglyMeasurable]
    exact (spike_grid_definition_and_exact_integrals (n + 2) (by omega)).2.2.2.2.2.2.2.1
  rw [h2, zsmul_eq_mul, Int.cast_natCast] at h1
  field_simp at h1 ⊢
  linarith

lemma integral_h_pt_le (n : ℕ) (a δ : ℝ) (hδ : 0 ≤ δ) :
    ∫ t in a..a + δ, h (n + 2) (pt t) ≤
      ((M (n + 2) : ℝ) * δ + 1) *
        (Real.exp (-((n + 2 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ) * M (n + 2))) := by
  have hM := M_real_pos (n := n + 2)
  have hper := h_pt_periodic (n + 2)
  set T : ℝ := 1 / (M (n + 2) : ℝ) with hTdef
  have hT0 : 0 < T := by positivity
  set k : ℕ := ⌈(M (n + 2) : ℝ) * δ⌉₊ with hk
  have hkδ : δ ≤ k * T := by
    have : (M (n + 2) : ℝ) * δ ≤ k := Nat.le_ceil _
    rw [hTdef]; rw [mul_one_div, le_div_iff₀ hM]; linarith
  have hk1 : (k : ℝ) ≤ (M (n + 2) : ℝ) * δ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hadj := intervalIntegral.integral_add_adjacent_intervals (h_pt_ii n a (a + δ))
    (h_pt_ii n (a + δ) (a + k * T))
  have hnn : 0 ≤ ∫ t in (a + δ)..(a + k * T), h (n + 2) (pt t) :=
    intervalIntegral.integral_nonneg (by linarith) fun t _ => h_nonneg _ _
  have hz := hper.intervalIntegral_add_zsmul_eq (k : ℤ) a (h_pt_ii n)
  rw [zsmul_eq_mul, Int.cast_natCast] at hz
  rw [hper.intervalIntegral_add_eq a 0, zero_add, integral_h_pt_period] at hz
  have hmain : ∫ t in a..a + δ, h (n + 2) (pt t) ≤ k * (Real.exp (-((n + 2 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ) * M (n + 2))) := by
    rw [zsmul_eq_mul, Int.cast_natCast] at hz
    rw [← hz]; linarith
  refine hmain.trans ?_
  have : 0 ≤ Real.exp (-((n + 2 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ) * M (n + 2)) := by positivity
  exact mul_le_mul_of_nonneg_right hk1 this


/-- Level-`n` integral over the arc `[a, a+δ]`. -/
lemma I_nonneg (n : ℕ) (a δ : ℝ) (hδ : 0 ≤ δ) : 0 ≤ ∫ t in a..a + δ, h (n + 2) (pt t) :=
  intervalIntegral.integral_nonneg (by linarith) fun t _ => h_nonneg _ _

lemma I_le_A (n : ℕ) (a δ : ℝ) (hδ : 0 ≤ δ) :
    ∫ t in a..a + δ, h (n + 2) (pt t) ≤ Real.exp ((n + 2 : ℕ) : ℝ) * δ := by
  have : ∫ t in a..a + δ, h (n + 2) (pt t) ≤ ∫ t in a..a + δ, A (n + 2) := by
    refine intervalIntegral.integral_mono_on (by linarith) (h_pt_ii n a (a + δ))
      intervalIntegrable_const fun t _ => ?_
    unfold h; exact Set.indicator_le_self' (fun _ _ => (Real.exp_pos _).le) _
  simpa [A, mul_comm] using this

lemma I_le_mean (n : ℕ) (a δ : ℝ) (hδ : 0 ≤ δ) :
    ∫ t in a..a + δ, h (n + 2) (pt t) ≤ (δ + 1 / (M (n + 2) : ℝ)) * meanTerm n := by
  have h1 := integral_h_pt_le n a δ hδ
  have hM := M_real_pos (n := n + 2)
  refine h1.trans (le_of_eq ?_)
  unfold meanTerm
  field_simp

lemma M_ge_exp (m : ℕ) : Real.exp ((m : ℝ) ^ 3) ≤ (M m : ℝ) := Nat.le_ceil _

lemma integral_hSum_le_aux (a δ : ℝ) (hδ : 0 < δ) (N : ℕ)
    (hN : ∀ n : ℕ, N < n + 2 → 1 / (M (n + 2) : ℝ) ≤ δ) :
    ∫ t in a..a + δ, hSum (pt t) ≤
      (∑ n ∈ Finset.range (N - 1), Real.exp ((n + 2 : ℕ) : ℝ)) * δ + 2 * δ * hMean := by
  set I : ℕ → ℝ := fun n => ∫ t in a..a + δ, h (n + 2) (pt t) with hI
  have hsum : Summable I := by
    refine Summable.of_nonneg_of_le (fun n => I_nonneg n a δ hδ.le) (fun n => ?_)
      (summable_meanTerm.mul_left (δ + 1))
    refine (I_le_mean n a δ hδ.le).trans ?_
    have hM1 : 1 / (M (n + 2) : ℝ) ≤ 1 := by
      rw [div_le_one M_real_pos]; exact_mod_cast (M_pos (n := n + 2))
    exact mul_le_mul_of_nonneg_right (by linarith) (meanTerm_nonneg n)
  have hint : ∫ t in a..a + δ, hSum (pt t) = ∑' n, I n := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    have := integral_tsum_of_summable_integral_norm (μ := volume.restrict (Ioc a (a + δ)))
      (F := fun (n : ℕ) (t : ℝ) => h (n + 2) (pt t))
      (fun n => ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1
        (h_pt_ii n a (a + δ)))) (by
        have : (fun n : ℕ => ∫ t in Ioc a (a + δ), ‖h (n + 2) (pt t)‖) = I := by
          funext n
          simp only [hI]
          rw [intervalIntegral.integral_of_le (by linarith)]
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          exact Real.norm_of_nonneg (h_nonneg _ _)
        rw [this]; exact hsum)
    have e : ∫ t in Ioc a (a + δ), hSum (pt t) = ∫ t in Ioc a (a + δ), ∑' n : ℕ, h (n + 2) (pt t) := rfl
    rw [e, ← this]
    simp only [hI, intervalIntegral.integral_of_le (by linarith : a ≤ a + δ)]
  rw [hint]
  set b1 : ℕ → ℝ := fun n => if n < N - 1 then Real.exp ((n + 2 : ℕ) : ℝ) * δ else 0 with hb1
  set b2 : ℕ → ℝ := fun n => 2 * δ * meanTerm n with hb2
  have hb2s : Summable b2 := summable_meanTerm.mul_left _
  have hb1s : Summable b1 := summable_of_ne_finset_zero (s := Finset.range (N - 1)) (by
    intro n hn
    simp only [Finset.mem_range] at hn
    simp [hb1, hn])
  have hle : ∀ n, I n ≤ b1 n + b2 n := by
    intro n
    by_cases hn : n < N - 1
    · have := I_le_A n a δ hδ.le
      have h2 : 0 ≤ b2 n := by simp only [hb2]; have := meanTerm_nonneg n; positivity
      simp only [hb1, hn, ite_true]; linarith
    · have hn' : N < n + 2 := by omega
      have h1 := I_le_mean n a δ hδ.le
      have h2 := hN n hn'
      have h3 : (δ + 1 / (M (n + 2) : ℝ)) * meanTerm n ≤ 2 * δ * meanTerm n :=
        mul_le_mul_of_nonneg_right (by linarith) (meanTerm_nonneg n)
      simp only [hb1, hn, ite_false, zero_add, hb2]; linarith
  have h1 := hsum.tsum_le_tsum hle (hb1s.add hb2s)
  rw [hb1s.tsum_add hb2s] at h1
  have e1 : ∑' n, b1 n = (∑ n ∈ Finset.range (N - 1), Real.exp ((n + 2 : ℕ) : ℝ)) * δ := by
    rw [tsum_eq_sum (s := Finset.range (N - 1)) (by
      intro n hn
      simp only [Finset.mem_range] at hn
      simp [hb1, hn]), Finset.sum_mul]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_range] at hn
    simp [hb1, hn]
  have e2 : ∑' n, b2 n = 2 * δ * hMean := by
    simp only [hb2]; rw [tsum_mul_left]; rfl
  rw [e1, e2] at h1; exact h1


lemma geom_low (K : ℕ) :
    (∑ n ∈ Finset.range (K + 1), Real.exp ((n + 2 : ℕ) : ℝ)) * (Real.exp 1 - 1) ≤
      Real.exp 1 * Real.exp ((K + 2 : ℕ) : ℝ) := by
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.2 one_pos
  induction K with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    norm_num
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith [Real.exp_pos 1]
  | succ K ih =>
    rw [Finset.sum_range_succ, add_mul]
    have e1 : Real.exp ((K + 1 + 2 : ℕ) : ℝ) = Real.exp ((K + 2 : ℕ) : ℝ) * Real.exp 1 := by
      rw [← Real.exp_add]; push_cast; ring_nf
    have e2 : Real.exp ((K + 1 + 2 : ℕ) : ℝ) = Real.exp ((K + 2 : ℕ) : ℝ) * Real.exp 1 := e1
    have e3 : Real.exp ((K + 1 : ℕ) + 2 : ℝ) = Real.exp ((K + 2 : ℕ) : ℝ) * Real.exp 1 := by
      rw [← Real.exp_add]; push_cast; ring_nf
    have e4 : ((K + 1 + 2 : ℕ) : ℝ) = (K : ℝ) + 3 := by push_cast; ring
    have e5 : (((K + 1 : ℕ)) + 2 : ℕ) = K + 1 + 2 := rfl
    rw [e5, e1]
    nlinarith [Real.exp_pos ((K + 2 : ℕ) : ℝ), Real.exp_pos 1]

lemma gLine_sub (a δ : ℝ) :
    gLine (a + δ) - gLine a = (∫ t in a..a + δ, hSum (pt t)) - hMean * δ := by
  unfold gLine
  rw [intervalIntegral.integral_interval_sub_left (fLine_ii 0 (a + δ)) (fLine_ii 0 a)]
  unfold fLine
  rw [intervalIntegral.integral_sub (hSumPt_ii a (a + δ)) intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left]
  ring

lemma rpow_third_cube {R : ℝ} (hR : 0 ≤ R) : (R ^ (1 / 3 : ℝ)) ^ 3 = R := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hR]; norm_num

/-- The explicit constant `C₀ = e/(e-1) + 4c`. -/
noncomputable def modulusConst : ℝ := Real.exp 1 / (Real.exp 1 - 1) + 4 * hMean

lemma gLine_modulus (a δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ Real.exp (-8)) :
    |gLine (a + δ) - gLine a| ≤
      modulusConst * δ * Real.exp ((Real.log (1 / δ)) ^ (1 / 3 : ℝ)) := by
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.2 one_pos
  have hc := hMean_pos
  set R := Real.log (1 / δ) with hR
  have hR8 : 8 ≤ R := by
    rw [hR, one_div, Real.log_inv]
    have := Real.log_le_log hδ0 hδ
    rw [Real.log_exp] at this; linarith
  have hR0 : 0 ≤ R := by linarith
  set s := R ^ (1 / 3 : ℝ) with hs
  have hs0 : 0 ≤ s := Real.rpow_nonneg hR0 _
  have hs3 : s ^ 3 = R := rpow_third_cube hR0
  have hs2 : 2 ≤ s := by
    by_contra h
    replace h := not_le.1 h
    have : s ^ 3 < 2 ^ 3 := pow_lt_pow_left₀ h hs0 (by norm_num)
    linarith
  set N := ⌊s⌋₊ with hN
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hs2)
  have hNs : (N : ℝ) ≤ s := Nat.floor_le hs0
  have hexpR : Real.exp R = 1 / δ := by
    rw [hR, Real.exp_log (by positivity)]
  have hMδ : ∀ n : ℕ, N < n + 2 → 1 / (M (n + 2) : ℝ) ≤ δ := by
    intro n hn
    have h1 : s < ((n + 2 : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one s
      have h2 : (N : ℝ) + 1 ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hn
      linarith
    have h3 : R < ((n + 2 : ℕ) : ℝ) ^ 3 := by
      rw [← hs3]; exact pow_lt_pow_left₀ h1 hs0 (by norm_num)
    have h4 : 1 / δ ≤ (M (n + 2) : ℝ) := by
      rw [← hexpR]
      exact (Real.exp_le_exp.2 h3.le).trans (M_ge_exp _)
    rw [div_le_iff₀ M_real_pos]
    rw [div_le_iff₀ hδ0] at h4
    linarith
  have hmain := integral_hSum_le_aux a δ hδ0 N hMδ
  obtain ⟨K, hK⟩ : ∃ K, N = K + 2 := ⟨N - 2, by omega⟩
  have hgeo := geom_low (N - 2)
  have hN1 : N - 1 = N - 2 + 1 := by omega
  rw [hN1] at hmain
  have hNe : N - 2 + 2 = N := by omega
  rw [hNe] at hgeo
  have hes : Real.exp (N : ℝ) ≤ Real.exp s := Real.exp_le_exp.2 hNs
  have hsum_le : (∑ n ∈ Finset.range (N - 2 + 1), Real.exp ((n + 2 : ℕ) : ℝ)) ≤
      Real.exp 1 / (Real.exp 1 - 1) * Real.exp s := by
    have hpos : 0 < Real.exp 1 - 1 := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    calc _ ≤ Real.exp 1 * Real.exp (N : ℝ) := hgeo
      _ ≤ Real.exp 1 * Real.exp s := by gcongr
  have hI0 : 0 ≤ ∫ t in a..a + δ, hSum (pt t) :=
    intervalIntegral.integral_nonneg (by linarith) fun t _ => hSum_nonneg _
  have hes1 : 1 ≤ Real.exp s := Real.one_le_exp hs0
  have hcδ : 0 ≤ hMean * δ := by positivity
  rw [gLine_sub]
  have habs : |(∫ t in a..a + δ, hSum (pt t)) - hMean * δ| ≤
      (∫ t in a..a + δ, hSum (pt t)) + hMean * δ := by
    rw [abs_le]; constructor <;> linarith
  refine habs.trans ?_
  have h1 : (∑ n ∈ Finset.range (N - 2 + 1), Real.exp ((n + 2 : ℕ) : ℝ)) * δ ≤
      Real.exp 1 / (Real.exp 1 - 1) * Real.exp s * δ :=
    mul_le_mul_of_nonneg_right hsum_le hδ0.le
  unfold modulusConst
  have h2 : 3 * hMean * δ ≤ 4 * hMean * δ * Real.exp s := by
    have : 0 ≤ hMean * δ := hcδ
    nlinarith
  nlinarith [mul_pos hδ0 (Real.exp_pos s)]


/-! ### Transfer to the torus -/

lemma torusDist_one (x y : Torus 1) : DGPS.torusDist x y = ‖x 0 - y 0‖ := by
  unfold DGPS.torusDist SharpLSI.flatDist
  simp

lemma exists_lifts (x y : Torus 1) :
    ∃ a b : ℝ, x = pt a ∧ y = pt b ∧ |b - a| = DGPS.torusDist x y := by
  have hpt : ∀ z : Torus 1, z = pt (SharpLSI.secT z 0) := by
    intro z
    funext i
    have : i = 0 := Subsingleton.elim _ _
    subst this
    exact (congrFun (SharpLSI.liftT_secT z) 0).symm
  set a := SharpLSI.secT x 0
  set b0 := SharpLSI.secT y 0
  refine ⟨a, b0 - round (b0 - a), hpt x, ?_, ?_⟩
  · rw [hpt y]
    have := pt_add_int b0 (-round (b0 - a))
    simpa [sub_eq_add_neg] using this.symm
  · rw [torusDist_one]
    have hx : x 0 = (a : AddCircle (1 : ℝ)) := (congrFun (hpt x) 0)
    have hy : y 0 = (b0 : AddCircle (1 : ℝ)) := (congrFun (hpt y) 0)
    rw [norm_sub_rev, hx, hy, ← AddCircle.coe_sub]
    have := UnitAddCircle.norm_eq (x := b0 - a)
    rw [this]
    congr 1
    ring

lemma gT_modulus_aux (x y : Torus 1) (h0 : 0 < DGPS.torusDist x y)
    (h8 : DGPS.torusDist x y ≤ Real.exp (-8)) :
    |gT x - gT y| ≤ modulusConst * DGPS.torusDist x y *
      Real.exp ((Real.log (1 / DGPS.torusDist x y)) ^ (1 / 3 : ℝ)) := by
  obtain ⟨a, b, rfl, rfl, hab⟩ := exists_lifts x y
  rw [gT_pt, gT_pt]
  rw [← hab] at h0 h8 ⊢
  rcases le_total a b with h | h
  · have e : b = a + |b - a| := by rw [abs_of_nonneg (by linarith)]; ring
    have := gLine_modulus a |b - a| h0 h8
    rw [abs_sub_comm, ← e] at this
    exact this
  · have e : a = b + |b - a| := by rw [abs_of_nonpos (by linarith)]; ring
    have := gLine_modulus b |b - a| h0 h8
    rw [← e] at this
    exact this

lemma sup_cubic_bound {β : ℝ} (hβ : 0 < β) (t : ℝ) (ht : 0 ≤ t) :
    t - β * t ^ 3 ≤ 2 / (3 * Real.sqrt (3 * β)) := by
  have hw : 0 < Real.sqrt (3 * β) := Real.sqrt_pos.2 (by positivity)
  have hw2 : Real.sqrt (3 * β) ^ 2 = 3 * β := Real.sq_sqrt (by positivity)
  set w := Real.sqrt (3 * β)
  rw [le_div_iff₀ (by positivity)]
  have hu : 0 ≤ w * t := by positivity
  have key : 0 ≤ (w * t - 1) ^ 2 * (w * t + 2) := mul_nonneg (sq_nonneg _) (by linarith)
  have : β = w ^ 2 / 3 := by linarith
  rw [this]
  nlinarith [key]

lemma gT_holder_aux (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (x y : Torus 1) :
    |gT x - gT y| ≤
      max (modulusConst * Real.exp (2 / (3 * Real.sqrt (3 * (1 - α)))))
        (2 * hMean * Real.exp (8 * α)) * DGPS.torusDist x y ^ α := by
  have hc := hMean_pos
  have hC0 : 0 < modulusConst := by
    unfold modulusConst
    have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.2 one_pos
    have : 0 < Real.exp 1 / (Real.exp 1 - 1) := div_pos (by linarith) (by linarith)
    linarith
  set δ := DGPS.torusDist x y with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ, DGPS.torusDist]; exact Real.sqrt_nonneg _
  rcases hδ0.eq_or_lt with h0 | h0
  · obtain ⟨a, b, rfl, rfl, hab⟩ := exists_lifts x y
    rw [← hδ, ← h0] at hab
    have : b = a := by simpa [sub_eq_zero] using hab
    subst this
    simp [← h0, Real.zero_rpow hα0.ne']
  by_cases h8 : δ ≤ Real.exp (-8)
  · have hmod := gT_modulus_aux x y h0 h8
    rw [← hδ] at hmod
    refine hmod.trans ?_
    set R := Real.log (1 / δ) with hR
    have hexpR : δ = Real.exp (-R) := by
      rw [hR, one_div, Real.log_inv, neg_neg, Real.exp_log h0]
    have hR8 : 8 ≤ R := by
      rw [hR, one_div, Real.log_inv]
      have := Real.log_le_log h0 h8
      rw [Real.log_exp] at this; linarith
    have hR0 : 0 ≤ R := by linarith
    set t := R ^ (1 / 3 : ℝ) with ht
    have ht0 : 0 ≤ t := Real.rpow_nonneg hR0 _
    have ht3 : t ^ 3 = R := rpow_third_cube hR0
    have hsup := sup_cubic_bound (sub_pos.2 hα1) t ht0
    have hδα : δ ^ α = Real.exp (-R * α) := by
      rw [hexpR, ← Real.exp_mul]
    have key : δ * Real.exp t ≤ Real.exp (2 / (3 * Real.sqrt (3 * (1 - α)))) * δ ^ α := by
      rw [hδα]
      conv_lhs => rw [hexpR]
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      rw [ht3] at hsup
      nlinarith
    calc modulusConst * δ * Real.exp t = modulusConst * (δ * Real.exp t) := by ring
      _ ≤ modulusConst * (Real.exp (2 / (3 * Real.sqrt (3 * (1 - α)))) * δ ^ α) :=
          mul_le_mul_of_nonneg_left key hC0.le
      _ = (modulusConst * Real.exp (2 / (3 * Real.sqrt (3 * (1 - α))))) * δ ^ α := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg h0.le _)
  · replace h8 := not_le.1 h8
    have hgx := abs_gT_le x
    have hgy := abs_gT_le y
    have hlow : Real.exp (-8 * α) ≤ δ ^ α := by
      rw [Real.exp_mul]
      exact Real.rpow_le_rpow (Real.exp_pos _).le h8.le hα0.le
    have h1 : |gT x - gT y| ≤ 2 * hMean := by
      rw [abs_le] at hgx hgy ⊢; constructor <;> linarith
    refine h1.trans ?_
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg h0.le _))
    calc 2 * hMean = 2 * hMean * (Real.exp (8 * α) * Real.exp (-8 * α)) := by
          rw [← Real.exp_add]; simp
      _ = 2 * hMean * Real.exp (8 * α) * Real.exp (-8 * α) := by ring
      _ ≤ 2 * hMean * Real.exp (8 * α) * δ ^ α :=
          mul_le_mul_of_nonneg_left hlow (by positivity)

/-- **RUF004.** Explicit sub-Lipschitz modulus and every strict Hölder exponent for the common
primitive `gT`, with `c = hMean` and `C₀ = e/(e-1) + 4c` (`modulusConst`). -/
theorem explicit_sub_lipschitz_modulus_and_every_strict_holder_exponent :
    modulusConst = Real.exp 1 / (Real.exp 1 - 1) + 4 * hMean ∧
    (∀ x y : Torus 1, 0 < DGPS.torusDist x y → DGPS.torusDist x y ≤ Real.exp (-8) →
      |gT x - gT y| ≤ modulusConst * DGPS.torusDist x y *
        Real.exp ((Real.log (1 / DGPS.torusDist x y)) ^ (1 / 3 : ℝ))) ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∀ x y : Torus 1,
      |gT x - gT y| ≤
        max (modulusConst * Real.exp (2 / (3 * Real.sqrt (3 * (1 - α)))))
          (2 * hMean * Real.exp (8 * α)) * DGPS.torusDist x y ^ α) :=
  ⟨rfl, gT_modulus_aux, gT_holder_aux⟩

end DGPS.Examples.RoughBoundary.Spikes
