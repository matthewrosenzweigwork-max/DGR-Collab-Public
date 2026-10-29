import SharpSymmetricLSI.Paper.FormLiminfS3

/-!
# (8.20) (lane s42): `E[T_k H(Z_k)] → E_γ[F H(z)]` under convergence in law

The assembly of Paper/FormLiminfS3: test functions `g_M(t, z) = clip_M(t) H(clip_M z)`, the
uniform truncation errors, and `tendsto_of_trunc` (Paper/GaussLaw6).
-/

noncomputable section
open MeasureTheory Filter Topology Finset
open scoped ENNReal BoundedContinuousFunction

namespace SharpLSI

/-- `g_M(t, z) = clip_{|M|}(t) H(clip_{|M|} z)` as a bounded continuous function. -/
def truncTest {J : ℕ} {H : (Fin J → ℝ) → ℝ} (hH : Continuous H) {A : ℝ}
    (hHb : ∀ z, |H z| ≤ A * (1 + ∑ j, |z j|)) (M : ℝ) : ℝ × (Fin J → ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun p => clipF |M| p.1 * H (clipV |M| p.2),
      ((continuous_clipF _).comp continuous_fst).mul
        (hH.comp ((continuous_clipV _).comp continuous_snd))⟩
    (2 * (|M| * (A * (1 + J * |M|)))) fun p q => by
      have hA := nonneg_of_growth hHb
      have hb : ∀ r : ℝ × (Fin J → ℝ), |clipF |M| r.1 * H (clipV |M| r.2)| ≤
          |M| * (A * (1 + J * |M|)) := fun r => by
        rw [abs_mul]
        refine mul_le_mul (abs_clipF_le (abs_nonneg M) _) ((hHb _).trans ?_) (abs_nonneg _)
          (abs_nonneg _)
        exact mul_le_mul_of_nonneg_left
          (add_le_add_right (sumAbs_clipV_le' (abs_nonneg M) r.2) 1) hA
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      linarith [abs_sub (clipF |M| p.1 * H (clipV |M| p.2)) (clipF |M| q.1 * H (clipV |M| q.2)),
        hb p, hb q]

theorem truncTest_apply {J : ℕ} {H : (Fin J → ℝ) → ℝ} (hH : Continuous H) {A : ℝ}
    (hHb : ∀ z, |H z| ≤ A * (1 + ∑ j, |z j|)) (M : ℝ) (p : ℝ × (Fin J → ℝ)) :
    truncTest hH hHb M p = clipF |M| p.1 * H (clipV |M| p.2) := rfl

/-- **Products with a law-convergent, uniformly square-integrable factor.** -/
theorem tendsto_integral_mul_of_law {α : ℕ → Type*} [∀ k, MeasurableSpace (α k)]
    (P : ∀ k, Measure (α k)) [∀ k, IsProbabilityMeasure (P k)] {J : ℕ}
    (T : ∀ k, α k → ℝ) (Z : ∀ k, α k → Fin J → ℝ)
    (hTm : ∀ k, AEStronglyMeasurable (T k) (P k)) (hZm : ∀ k, AEStronglyMeasurable (Z k) (P k))
    {γ : Measure (ℕ → ℝ)} [IsProbabilityMeasure γ] {F : (ℕ → ℝ) → ℝ} (hF : MemLp F 2 γ)
    (hlaw : ∀ g : ℝ × (Fin J → ℝ) →ᵇ ℝ, Tendsto (fun k => ∫ x, g (T k x, Z k x) ∂P k) atTop
      (𝓝 (∫ z, g (F z, fun j => z j) ∂γ)))
    (hUI : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ k, ∫⁻ x in {x | M < T k x ^ 2}, ENNReal.ofReal (T k x ^ 2) ∂P k ≤ ENNReal.ofReal ε)
    {K : ℝ} (hT2 : ∀ k, ∫ x, T k x ^ 2 ∂P k ≤ K)
    (hZ4 : ∀ k (j : Fin J), Integrable (fun x => Z k x j ^ 4) (P k) ∧ ∫ x, Z k x j ^ 4 ∂P k ≤ K)
    (hz4 : ∀ j : Fin J, MemLp (fun z : ℕ → ℝ => z j) 4 γ)
    {H : (Fin J → ℝ) → ℝ} (hH : Continuous H) {A : ℝ} (hHb : ∀ z, |H z| ≤ A * (1 + ∑ j, |z j|)) :
    Tendsto (fun k => ∫ x, T k x * H (Z k x) ∂P k) atTop (𝓝 (∫ z, F z * H (fun j => z j) ∂γ)) := by
  have hA := nonneg_of_growth hHb
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  -- `T_k ∈ L²`
  have hT2i : ∀ k, Integrable (fun x => T k x ^ 2) (P k) := fun k => by
    obtain ⟨M1, hM1⟩ := hUI 1 one_pos
    refine ⟨(hTm k).pow 2, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun x => sq_nonneg (T k x))).2 ?_⟩
    set S := {x | M1 < T k x ^ 2}
    calc ∫⁻ x, ENNReal.ofReal (T k x ^ 2) ∂P k
        ≤ ∫⁻ x, (ENNReal.ofReal (max M1 0) + S.indicator (fun x => ENNReal.ofReal (T k x ^ 2)) x)
          ∂P k := lintegral_mono fun x => by
          by_cases hx : x ∈ S
          · rw [Set.indicator_of_mem hx]; exact le_add_self
          · rw [Set.indicator_of_notMem hx, add_zero]
            exact ENNReal.ofReal_le_ofReal ((not_lt.mp hx).trans (le_max_left _ _))
      _ = ENNReal.ofReal (max M1 0) +
            ∫⁻ x, S.indicator (fun x => ENNReal.ofReal (T k x ^ 2)) x ∂P k := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (max M1 0) + ENNReal.ofReal 1 :=
          add_le_add le_rfl ((lintegral_indicator_le _ _).trans (hM1 k))
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩
  have hK0 : 0 ≤ K := (integral_nonneg fun _ => sq_nonneg _).trans (hT2 0)
  -- fourth moments
  set K4 := 8 * (1 + (J : ℝ) ^ 3 * (J * K))
  have hΦc : Continuous fun z : Fin J → ℝ => (1 + sumAbs z) ^ 4 :=
    (continuous_const.add continuous_sumAbs).pow 4
  have hΦk : ∀ k, Integrable (fun x => (1 + sumAbs (Z k x)) ^ 4) (P k) ∧
      ∫ x, (1 + sumAbs (Z k x)) ^ 4 ∂P k ≤ K4 := fun k => by
    have hdi : Integrable (fun x => 8 * (1 + (J : ℝ) ^ 3 * ∑ j, Z k x j ^ 4)) (P k) :=
      ((integrable_const 1).add ((integrable_finset_sum _ fun j _ => (hZ4 k j).1).const_mul _)
        ).const_mul 8
    have hle : ∀ x, (1 + sumAbs (Z k x)) ^ 4 ≤ 8 * (1 + (J : ℝ) ^ 3 * ∑ j, Z k x j ^ 4) :=
      fun x => one_add_pow_four_le _
    have hi : Integrable (fun x => (1 + sumAbs (Z k x)) ^ 4) (P k) :=
      hdi.mono' (hΦc.comp_aestronglyMeasurable (hZm k)) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hle x)
    refine ⟨hi, (integral_mono hi hdi hle).trans ?_⟩
    rw [integral_const_mul, integral_add (integrable_const _)
      ((integrable_finset_sum _ fun j _ => (hZ4 k j).1).const_mul _), integral_const,
      integral_const_mul, integral_finset_sum _ fun j _ => (hZ4 k j).1]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have : ∑ j : Fin J, ∫ x, Z k x j ^ 4 ∂P k ≤ J * K := by
      calc _ ≤ ∑ _j : Fin J, K := Finset.sum_le_sum fun j _ => (hZ4 k j).2
        _ = J * K := by simp
    have := mul_le_mul_of_nonneg_left this (pow_nonneg hJ 3)
    linarith
  -- the Gaussian side
  have hcoord : AEStronglyMeasurable (fun z : ℕ → ℝ => fun j : Fin J => z j) γ :=
    (continuous_pi fun j : Fin J =>
      (continuous_apply (j : ℕ) : Continuous fun z : ℕ → ℝ => z j)).aestronglyMeasurable
  have hz4i : ∀ j : Fin J, Integrable (fun z : ℕ → ℝ => z j ^ 4) γ := fun j => by
    have := (hz4 j).integrable_norm_rpow'
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [Real.norm_eq_abs]
    rw [show ((4 : ℝ≥0∞).toReal) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  have hΦγ : Integrable (fun z : ℕ → ℝ => (1 + sumAbs (fun j : Fin J => z j)) ^ 4) γ := by
    have hdi : Integrable (fun z : ℕ → ℝ => 8 * (1 + (J : ℝ) ^ 3 * ∑ j : Fin J, z j ^ 4)) γ :=
      ((integrable_const 1).add ((integrable_finset_sum _ fun j _ => hz4i j).const_mul _)
        ).const_mul 8
    exact hdi.mono' (hΦc.comp_aestronglyMeasurable hcoord) (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact one_add_pow_four_le (fun j : Fin J => z j))
  have hFi : Integrable (fun z => F z ^ 2) γ := hF.integrable_sq
  set Kγ := ∫ z, F z ^ 2 ∂γ
  set K4γ := ∫ z : ℕ → ℝ, (1 + sumAbs (fun j : Fin J => z j)) ^ 4 ∂γ
  have hKγ : 0 ≤ Kγ := integral_nonneg fun _ => sq_nonneg _
  have hK4γ : 0 ≤ K4γ := integral_nonneg fun _ => by positivity
  have hK4 : 0 ≤ K4 := by positivity
  -- truncation of `F`
  have hFtr : Tendsto (fun n : ℕ => ∫ z, (F z - clipF n (F z)) ^ 2 ∂γ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun z => F z ^ 2)
      (F := fun (n : ℕ) z => (F z - clipF n (F z)) ^ 2) (f := fun _ => 0)
      (fun n => (hF.aestronglyMeasurable.sub
        ((continuous_clipF _).comp_aestronglyMeasurable hF.aestronglyMeasurable)).pow 2) hFi
      (fun n => Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sub_clipF_sq_le (Nat.cast_nonneg n) _)
      (Eventually.of_forall fun z => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ⌈|F z|⌉₊] with n hn
        rw [clipF_eq ((Nat.le_ceil _).trans (by exact_mod_cast hn)), sub_self]
        norm_num)
    simpa using h
  -- truncation of `T_k`, uniformly in `k`
  have hTtr : ∀ ε0 : ℝ, 0 < ε0 → ∀ᶠ n : ℕ in atTop,
      ∀ k, ∫ x, (T k x - clipF n (T k x)) ^ 2 ∂P k ≤ ε0 := fun ε0 hε0 => by
    obtain ⟨M0, hM0⟩ := hUI ε0 hε0
    filter_upwards [eventually_ge_atTop ⌈Real.sqrt (max M0 0)⌉₊] with n hn k
    have hn' : M0 ≤ (n : ℝ) ^ 2 := by
      have h1 : Real.sqrt (max M0 0) ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      rw [Real.sq_sqrt (le_max_right _ _)] at h2
      exact (le_max_left _ _).trans h2
    have hi : Integrable (fun x => (T k x - clipF n (T k x)) ^ 2) (P k) :=
      (hT2i k).mono' (((hTm k).sub ((continuous_clipF _).comp_aestronglyMeasurable
        (hTm k))).pow 2) (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact sub_clipF_sq_le (Nat.cast_nonneg n) _)
    rw [← ENNReal.ofReal_le_ofReal_iff hε0.le, ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun _ => sq_nonneg _)]
    refine le_trans ?_ ((lintegral_indicator_le _ _).trans (hM0 k))
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ {x | M0 < T k x ^ 2}
    · rw [Set.indicator_of_mem hx]
      exact ENNReal.ofReal_le_ofReal (sub_clipF_sq_le (Nat.cast_nonneg n) _)
    · rw [Set.indicator_of_notMem hx]
      have hle : T k x ^ 2 ≤ (n : ℝ) ^ 2 := (not_lt.mp hx).trans hn'
      have habs : |T k x| ≤ n := by
        have := sq_le_sq.mp hle
        rwa [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] at this
      rw [clipF_eq habs, sub_self]
      simp
  -- the 3ε argument
  refine tendsto_of_trunc (b := fun M k => ∫ x, truncTest hH hHb M (T k x, Z k x) ∂P k)
    (b0 := fun M => ∫ z, truncTest hH hHb M (F z, fun j => z j) ∂γ)
    (fun M => hlaw (truncTest hH hHb M)) ?_
  intro ε hε
  set C1 := A ^ 2 * K4 / 2 + K / 2 + (A ^ 2 * K4γ / 2 + Kγ / 2) + 1 with hC1d
  have hC1 : 0 < C1 := by positivity
  set η := ε / (4 * C1)
  have hη : 0 < η := by positivity
  have hηC : η * C1 = ε / 4 := by simp only [η]; field_simp
  have hdiv : Tendsto (fun n : ℕ => η * (n : ℝ) ^ 2) atTop atTop :=
    Tendsto.const_mul_atTop hη ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
  have h3 : ∀ c : ℝ, ∀ᶠ n : ℕ in atTop, c / (η * (n : ℝ) ^ 2) ≤ ε / 4 := fun c =>
    (tendsto_const_nhds.div_atTop hdiv).eventually (ge_mem_nhds (by positivity))
  have hεη : 0 < ε * η / 2 := by positivity
  obtain ⟨n, hn1, hn2, hn3, hn4, hn5⟩ := ((hTtr _ hεη).and
    ((hFtr.eventually (ge_mem_nhds hεη)).and ((h3 (2 * A ^ 2 * K4)).and
      ((h3 (2 * A ^ 2 * K4γ)).and (eventually_ge_atTop 1))))).exists
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn5
  have habsn : |(n : ℝ)| = n := abs_of_pos hnpos
  refine ⟨n, fun k => ?_, ?_⟩
  · obtain ⟨-, herr⟩ := trunc_error hHb (P k) (hTm k) (hZm k) (hT2i k) (hΦk k).1 hH hnpos hη
    simp only [truncTest_apply, habsn]
    refine herr.trans ?_
    have e1 : (∫ x, (T k x - clipF n (T k x)) ^ 2 ∂P k) / (2 * η) ≤ ε / 4 := by
      rw [div_le_iff₀ (by positivity)]
      have := hn1 k
      linarith [show ε / 4 * (2 * η) = ε * η / 2 by ring]
    have e2 : η * A ^ 2 * (∫ x, (1 + sumAbs (Z k x)) ^ 4 ∂P k) / 2 +
        η * (∫ x, T k x ^ 2 ∂P k) / 2 ≤ ε / 4 := by
      rw [← hηC]
      have h1 := mul_le_mul_of_nonneg_left (hΦk k).2 (by positivity : (0 : ℝ) ≤ η * A ^ 2)
      have h2 := mul_le_mul_of_nonneg_left (hT2 k) hη.le
      have h3 : 0 ≤ η * (A ^ 2 * K4γ / 2 + Kγ / 2 + 1) := by positivity
      have h4 : η * C1 = η * A ^ 2 * K4 / 2 + η * K / 2 + η * (A ^ 2 * K4γ / 2 + Kγ / 2 + 1) := by
        rw [hC1d]; ring
      linarith
    have e3 : 2 * A ^ 2 * (∫ x, (1 + sumAbs (Z k x)) ^ 4 ∂P k) / (η * (n : ℝ) ^ 2) ≤ ε / 4 :=
      le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hΦk k).2
        (by positivity)) (by positivity)) hn3
    linarith
  · obtain ⟨-, herr⟩ := trunc_error hHb γ hF.aestronglyMeasurable hcoord hFi hΦγ hH hnpos hη
    simp only [truncTest_apply, habsn]
    refine herr.trans ?_
    have e1 : (∫ z, (F z - clipF n (F z)) ^ 2 ∂γ) / (2 * η) ≤ ε / 4 := by
      rw [div_le_iff₀ (by positivity)]
      linarith [show ε / 4 * (2 * η) = ε * η / 2 by ring]
    have e2 : η * A ^ 2 * K4γ / 2 + η * Kγ / 2 ≤ ε / 4 := by
      rw [← hηC]
      have h3 : 0 ≤ η * (A ^ 2 * K4 / 2 + K / 2 + 1) := by positivity
      have h4 : η * C1 = η * A ^ 2 * K4γ / 2 + η * Kγ / 2 + η * (A ^ 2 * K4 / 2 + K / 2 + 1) := by
        rw [hC1d]; ring
      linarith
    linarith

end SharpLSI
