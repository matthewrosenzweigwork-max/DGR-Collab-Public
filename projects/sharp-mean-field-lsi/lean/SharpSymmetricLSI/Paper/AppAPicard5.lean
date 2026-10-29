import SharpSymmetricLSI.Paper.AppAPicard4

/-!
# Lemma A.1, existence (5): convergence of the Picard iteration (lemma (b))

`exists_modMild`: for bounded measurable `ρ₀` (`|ρ₀| ≤ M`) there is a jointly measurable
`ρ : ℝ → 𝕋^d → ℝ` with `ρ 0 = ρ₀`, `|ρ_t| ≤ 2M e^{μt}` (`t ≥ 0`), solving the modified mild
equation `ρ_t = e^{tΔ}ρ₀ + ∫_{(0,t]} ∇·e^{(t-u)Δ} N(ρ_u) du` everywhere for `t > 0`.
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem picardSeq_of_nonpos {ρ₀ : Torus d → ℝ} {t : ℝ} (ht : t ≤ 0) (n : ℕ) :
    picardSeq V W ρ₀ n t = ρ₀ := by
  cases n with
  | zero => rfl
  | succ n => funext x; simp [picardSeq, picardMap, not_lt.2 ht]

theorem le_sqrt_of_sq_add_one {a : ℝ} (ha : 0 ≤ a) : a ≤ Real.sqrt (a ^ 2 + 1) := by
  calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ Real.sqrt (a ^ 2 + 1) := Real.sqrt_le_sqrt (by linarith)

/-- `d K L / √((2dL)²+1) ≤ K/2`. -/
theorem mul_div_sqrt_le_half {a K : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K) :
    a * K / Real.sqrt ((2 * a) ^ 2 + 1) ≤ K / 2 := by
  have hs : 0 < Real.sqrt ((2 * a) ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
  have h2 := le_sqrt_of_sq_add_one (by positivity : (0 : ℝ) ≤ 2 * a)
  rw [div_le_div_iff₀ hs two_pos]
  nlinarith

/-- **Lemma (b)**: global solution of the modified mild equation by Picard iteration. -/
theorem exists_modMild (hyp : Hyp V W KV KW) {ρ₀ : Torus d → ℝ} (hρ₀ : Measurable ρ₀) {M : ℝ}
    (hM : ∀ x, |ρ₀ x| ≤ M) :
    ∃ ρ : ℝ → Torus d → ℝ, Measurable (Function.uncurry ρ) ∧ ρ 0 = ρ₀ ∧
      ∃ μ : ℝ, 0 < μ ∧ (∀ t, 0 ≤ t → ∀ x, |ρ t x| ≤ 2 * M * Real.exp (μ * t)) ∧
      ∀ t, 0 < t → ∀ x, ρ t x = picardMap V W ρ₀ ρ t x := by
  -- constants
  set LV : ℝ := ((Real.toNNReal (KV * Fintype.card (Fin d) / 2) : NNReal) : ℝ)
  have hLV : ∀ x k, |lipGrad V x k| ≤ LV := fun x k => abs_lipGrad_le (lipschitz_V hyp (W := W)) x k
  have hLV0 : 0 ≤ LV := NNReal.coe_nonneg _
  obtain ⟨Cb₀, hCb₀⟩ := bGrad_bdd hyp (W := W)
  set Cb := max Cb₀ 0
  have hCb : ∀ x y k, |bGrad W x y k| ≤ Cb := fun x y k => (hCb₀ x y k).trans (le_max_left _ _)
  have hCb0 : 0 ≤ Cb := le_max_right _ _
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set A := LV + Cb with hAdef
  have hA : 0 ≤ A := add_nonneg hLV0 hCb0
  set seq := picardSeq V W ρ₀ with hseq
  have hmeas : ∀ n, Measurable (Function.uncurry (seq n)) := measurable_picardSeq hyp hρ₀
  -- the a priori bound
  set μ₁ := (2 * (d * A)) ^ 2 + 1 with hμ₁
  have hμ₁0 : 0 < μ₁ := by positivity
  have hbound : ∀ n t, 0 ≤ t → ∀ x, |seq n t x| ≤ 2 * M * Real.exp (μ₁ * t) := by
    intro n
    induction n with
    | zero =>
      intro t ht x
      have := Real.one_le_exp (mul_nonneg hμ₁0.le ht)
      simp only [hseq, picardSeq]
      nlinarith [hM x]
    | succ n ih =>
      intro t ht x
      rcases ht.eq_or_lt with h0 | hpos
      · subst h0
        rw [hseq, picardSeq_of_nonpos le_rfl]
        simp only [mul_zero, Real.exp_zero, mul_one]
        linarith [hM x]
      · have h := abs_picardMap_le hyp hρ₀ hM hLV0 hCb0 hLV hCb (hmeas n)
          (by positivity : 0 ≤ 2 * M) hμ₁0 ih hpos x
        have h2 : d * (A * (2 * M)) * Real.exp (μ₁ * t) / Real.sqrt μ₁ ≤
            M * Real.exp (μ₁ * t) := by
          have := mul_div_sqrt_le_half (mul_nonneg (Nat.cast_nonneg d) hA)
            (by positivity : 0 ≤ 2 * M * Real.exp (μ₁ * t))
          calc d * (A * (2 * M)) * Real.exp (μ₁ * t) / Real.sqrt μ₁
              = d * A * (2 * M * Real.exp (μ₁ * t)) / Real.sqrt ((2 * (d * A)) ^ 2 + 1) := by
                rw [hμ₁]; ring
            _ ≤ 2 * M * Real.exp (μ₁ * t) / 2 := this
            _ = M * Real.exp (μ₁ * t) := by ring
        have h3 := Real.one_le_exp (mul_nonneg hμ₁0.le hpos.le)
        show |picardMap V W ρ₀ (seq n) t x| ≤ _
        nlinarith
  -- the contraction on `[0,T]`
  have hcon : ∀ T, 0 ≤ T → ∃ C ν L : ℝ, 0 ≤ C ∧ 0 < ν ∧ 0 ≤ L ∧ d * L / Real.sqrt ν ≤ 1 / 2 ∧
      (∀ n, ∀ u ∈ Icc 0 T, ∀ y, |seq (n + 1) u y - seq n u y| ≤ C * (1 / 2) ^ n * Real.exp (ν * u)) ∧
      (∀ η ζ : ℝ → Torus d → ℝ, Measurable (Function.uncurry η) →
        Measurable (Function.uncurry ζ) → (∀ u ∈ Icc 0 T, ∀ y, |η u y| ≤ 2 * M * Real.exp (μ₁ * T)) →
        (∀ u ∈ Icc 0 T, ∀ y, |ζ u y| ≤ 2 * M * Real.exp (μ₁ * T)) → ∀ δ, 0 ≤ δ →
        (∀ u ∈ Icc 0 T, ∀ y, |η u y - ζ u y| ≤ δ * Real.exp (ν * u)) →
        ∀ t, 0 < t → t ≤ T → ∀ x, |picardMap V W ρ₀ η t x - picardMap V W ρ₀ ζ t x| ≤
          d * L * δ * Real.exp (ν * t) / Real.sqrt ν) := by
    intro T hT
    set KT := 2 * M * Real.exp (μ₁ * T)
    have hKT : 0 ≤ KT := by positivity
    set L := A + 2 * Cb * KT
    have hL : 0 ≤ L := by positivity
    set ν := (2 * (d * L)) ^ 2 + 1 with hν
    have hν0 : 0 < ν := by positivity
    have hhalf : d * L / Real.sqrt ν ≤ 1 / 2 := by
      have := mul_div_sqrt_le_half (mul_nonneg (Nat.cast_nonneg d) hL) zero_le_one
      simpa [hν, mul_one] using this
    have hstep : ∀ η ζ : ℝ → Torus d → ℝ, Measurable (Function.uncurry η) →
        Measurable (Function.uncurry ζ) → (∀ u ∈ Icc 0 T, ∀ y, |η u y| ≤ KT) →
        (∀ u ∈ Icc 0 T, ∀ y, |ζ u y| ≤ KT) → ∀ δ, 0 ≤ δ →
        (∀ u ∈ Icc 0 T, ∀ y, |η u y - ζ u y| ≤ δ * Real.exp (ν * u)) →
        ∀ t, 0 < t → t ≤ T → ∀ x, |picardMap V W ρ₀ η t x - picardMap V W ρ₀ ζ t x| ≤
          d * L * δ * Real.exp (ν * t) / Real.sqrt ν := by
      intro η ζ hη hζ hηb hζb δ hδ hd t ht htT x
      have := abs_picardMap_sub_le hyp hρ₀ hLV0 hCb0 hLV hCb hη hζ hKT hδ hν0 hηb hζb hd ht htT x
      calc _ ≤ _ := this
        _ = d * L * δ * Real.exp (ν * t) / Real.sqrt ν := by ring
    have hbT : ∀ n, ∀ u ∈ Icc 0 T, ∀ y, |seq n u y| ≤ KT := fun n u hu y =>
      (hbound n u hu.1 y).trans (by
        simp only [KT]
        gcongr
        exact hu.2)
    set C := 3 * M * Real.exp (μ₁ * T)
    refine ⟨C, ν, L, by positivity, hν0, hL, hhalf, ?_, hstep⟩
    intro n
    induction n with
    | zero =>
      intro u hu y
      have h1 := hbT 1 u hu y
      have h0 := hbT 0 u hu y
      have he := Real.one_le_exp (mul_nonneg hν0.le hu.1)
      have he' := Real.one_le_exp (mul_nonneg hμ₁0.le hT)
      simp only [pow_zero, mul_one]
      calc |seq 1 u y - seq 0 u y| ≤ |seq 1 u y| + |seq 0 u y| := abs_sub _ _
        _ ≤ KT + M := add_le_add h1 (by simp only [hseq, picardSeq]; exact hM y)
        _ ≤ C := by simp only [KT, C]; nlinarith
        _ ≤ C * Real.exp (ν * u) := le_mul_of_one_le_right (by positivity) he
    | succ n ih =>
      intro u hu y
      rcases hu.1.eq_or_lt with h0 | hpos
      · subst h0
        rw [hseq, picardSeq_of_nonpos le_rfl, picardSeq_of_nonpos le_rfl, sub_self, abs_zero]
        positivity
      · have h := hstep (seq (n + 1)) (seq n) (hmeas _) (hmeas _) (hbT _) (hbT _) _
          (by positivity) ih u hpos hu.2 y
        calc |seq (n + 1 + 1) u y - seq (n + 1) u y|
            ≤ d * L * (C * (1 / 2) ^ n) * Real.exp (ν * u) / Real.sqrt ν := h
          _ = (d * L / Real.sqrt ν) * (C * (1 / 2) ^ n * Real.exp (ν * u)) := by ring
          _ ≤ (1 / 2) * (C * (1 / 2) ^ n * Real.exp (ν * u)) :=
              mul_le_mul_of_nonneg_right hhalf (by positivity)
          _ = C * (1 / 2) ^ (n + 1) * Real.exp (ν * u) := by ring
  -- convergence
  have hcauchy : ∀ t x, CauchySeq fun n => seq n t x := by
    intro t x
    rcases lt_or_ge t 0 with hneg | hnn
    · have : (fun n => seq n t x) = fun _ => ρ₀ x := funext fun n => by
        rw [hseq, picardSeq_of_nonpos hneg.le]
      rw [this]; exact cauchySeq_const _
    · obtain ⟨C, ν, L, hC, hν, -, -, hc, -⟩ := hcon t hnn
      refine cauchySeq_of_le_geometric (1 / 2) (C * Real.exp (ν * t)) (by norm_num) fun n => ?_
      rw [Real.dist_eq, abs_sub_comm]
      calc |seq (n + 1) t x - seq n t x| ≤ C * (1 / 2) ^ n * Real.exp (ν * t) :=
            hc n t ⟨hnn, le_rfl⟩ x
        _ = C * Real.exp (ν * t) * (1 / 2) ^ n := by ring
  set sol : ℝ → Torus d → ℝ := fun t x => limUnder atTop fun n => seq n t x with hsol
  have hT : ∀ t x, Tendsto (fun n => seq n t x) atTop (𝓝 (sol t x)) := fun t x =>
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hcauchy t x))
  have hsolm : Measurable (Function.uncurry sol) :=
    measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 fun p => hT p.1 p.2)
  have hsol0 : sol 0 = ρ₀ := by
    funext x
    refine tendsto_nhds_unique (hT 0 x) ?_
    have : (fun n => seq n 0 x) = fun _ => ρ₀ x := funext fun n => by
      rw [hseq, picardSeq_of_nonpos le_rfl]
    rw [this]; exact tendsto_const_nhds
  have hsolb : ∀ t, 0 ≤ t → ∀ x, |sol t x| ≤ 2 * M * Real.exp (μ₁ * t) := fun t ht x =>
    le_of_tendsto ((continuous_abs.tendsto _).comp (hT t x))
      (Eventually.of_forall fun n => hbound n t ht x)
  refine ⟨sol, hsolm, hsol0, μ₁, hμ₁0, hsolb, fun t ht x => ?_⟩
  -- the fixed point
  obtain ⟨C, ν, L, hC, hν, hL, -, hc, hstep⟩ := hcon t ht.le
  have hKmono : ∀ u ∈ Icc 0 t, 2 * M * Real.exp (μ₁ * u) ≤ 2 * M * Real.exp (μ₁ * t) :=
    fun u hu => by gcongr; exact hu.2
  have hdist : ∀ n, ∀ u ∈ Icc 0 t, ∀ y, |sol u y - seq n u y| ≤
      2 * C * (1 / 2) ^ n * Real.exp (ν * u) := by
    intro n u hu y
    have := dist_le_of_le_geometric_of_tendsto (1 / 2) (C * Real.exp (ν * u)) (by norm_num)
      (fun m => by
        rw [Real.dist_eq, abs_sub_comm]
        calc |seq (m + 1) u y - seq m u y| ≤ C * (1 / 2) ^ m * Real.exp (ν * u) :=
              hc m u ⟨hu.1, hu.2⟩ y
          _ = C * Real.exp (ν * u) * (1 / 2) ^ m := by ring) (hT u y) n
    rw [Real.dist_eq, abs_sub_comm] at this
    calc |sol u y - seq n u y| ≤ C * Real.exp (ν * u) * (1 / 2) ^ n / (1 - 1 / 2) := this
      _ = 2 * C * (1 / 2) ^ n * Real.exp (ν * u) := by ring
  have hlim : Tendsto (fun n => seq (n + 1) t x) atTop (𝓝 (picardMap V W ρ₀ sol t x)) := by
    have hb : ∀ n, |seq (n + 1) t x - picardMap V W ρ₀ sol t x| ≤
        d * L * (2 * C * (1 / 2) ^ n) * Real.exp (ν * t) / Real.sqrt ν := fun n => by
      rw [abs_sub_comm]
      exact hstep sol (seq n) hsolm (hmeas n)
        (fun u hu y => (hsolb u hu.1 y).trans (hKmono u hu))
        (fun u hu y => (hbound n u hu.1 y).trans (hKmono u hu)) _ (by positivity)
        (hdist n) t ht le_rfl x
    have hz : Tendsto (fun n : ℕ => d * L * (2 * C * (1 / 2) ^ n) * Real.exp (ν * t) /
        Real.sqrt ν) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul (d * L * (2 * C))).mul_const (Real.exp (ν * t) / Real.sqrt ν)
      simp only [mul_zero, zero_mul] at this
      refine this.congr fun n => ?_
      ring
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by rw [Real.norm_eq_abs]; exact hb n) hz
  exact tendsto_nhds_unique ((hT t x).comp (tendsto_add_atTop_nat 1)) hlim

end SharpLSI
