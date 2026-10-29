import FullLabeledLSI.Paper.Thm11Basic

/-!
# Theorem 1.1 (FL), positive limiting entropy: one-`N` estimates

* `positive_key_ineq_all`: the integrated inequality (2.19) for one `N` (verbatim copy of
  `SharpSymmetricLSI/Paper/R7Positive.positive_key_ineq` with the symmetry hypotheses removed).
* `int_sq_posLog_le`: `∫ f² log⁺ f² ≤ Ent(f²) + 1` for `∫ f² = 1`.
* `dyadic_sum_le_posLog`, `tail_pigeon`: elementary replacement of the convergence in law of
  Section 2.3: along dyadic levels `s_j = 2^j L` one has
  `∑_{j<K} (s_j/2) ∫_{f² > e^{s_j}} f² ≤ ∫ f² log⁺ f²`, so some level `j < K` has
  `s_j ∫_{f² > e^{s_j}} f² ≤ 2 (∫ f² log⁺ f²)/K`.
* `positive_one`: the bound for one `N` and one level, from the bounded comparison at that level.
-/

noncomputable section
open MeasureTheory Set Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

set_option maxHeartbeats 1000000 in
/-- The integrated inequality (2.19) for one `N`. -/
theorem positive_key_ineq_all (hyp : Hyp V W KV KW) (hB1 : TruncationConclusion) {η : ℝ}
    (hη : 0 < η) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ M s : ℝ, Real.exp 1 ≤ M → 0 ≤ s →
      s ^ 2 * Real.log (s ^ 2) ≤ min s M ^ 2 * Real.log (min s M ^ 2) +
        (1 + η) * (max (s - M) 0 ^ 2 * Real.posLog (max (s - M) 0 ^ 2)) +
        C * Real.log (M ^ 2) * (4 / 3 * (s ^ 2 - min s (M / 2) ^ 2)))
    {r₀ : ℝ} (hr₀ : 0 < r₀) {B : NNReal} {N : ℕ}
    (hdef : ∀ u : Config N d → ℝ, MemH1C (gibbs V W N) u →
      ent (gibbs V W N) (fun X => u X ^ 2) ≤ ENNReal.ofReal (2 / r₀) * energy V W N u +
        (B : ℝ≥0∞) * ∫⁻ X, ENNReal.ofReal (u X ^ 2) ∂gibbs V W N)
    {f : Config N d → ℝ} (hmem : MemH1C (gibbs V W N) f)
    (hf0 : ∀ X, 0 ≤ f X) (hnorm : ∫ X, f X ^ 2 ∂gibbs V W N = 1)
    (hfin : ent (gibbs V W N) (fun X => f X ^ 2) ≠ ⊤) {M : ℝ} (hM : Real.exp 1 ≤ M)
    (hc : ∫ X, max (f X - M) 0 ^ 2 ∂gibbs V W N ≤ Real.exp (-1)) :
    (ent (gibbs V W N) (fun X => f X ^ 2)).toReal ≤
      (ent (gibbs V W N) (fun X => min (f X) M ^ 2)).toReal +
      (1 + η) * (2 / r₀ * ((energy V W N f).toReal -
        (energy V W N (fun X => min (f X) M)).toReal) +
        B * ∫ X, 4 / 3 * (f X ^ 2 - min (f X) (M / 2) ^ 2) ∂gibbs V W N) +
      C * Real.log (M ^ 2) * ∫ X, 4 / 3 * (f X ^ 2 - min (f X) (M / 2) ^ 2) ∂gibbs V W N := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  set P := gibbs V W N
  set g : Config N d → ℝ := fun X => min (f X) M with hgdef
  set t : Config N d → ℝ := fun X => max (f X - M) 0 with htdef
  have he1 : 1 < Real.exp 1 := by have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hfL := memLp_of_memH1C hyp hmem
  have hf2 : Integrable (fun X => f X ^ 2) P := hfL.integrable_sq
  have hgH := memH1C_min hyp hmem M
  have htH := memH1C_posPart_sub hyp hmem M
  have hgL := memLp_of_memH1C hyp hgH
  have htL := memLp_of_memH1C hyp htH
  have ht0 : ∀ X, 0 ≤ t X := fun X => le_max_right _ _
  have hg0 : ∀ X, 0 ≤ g X := fun X => le_min (hf0 X) hM0
  have hgM : ∀ X, g X ≤ M := fun X => min_le_right _ _
  obtain ⟨hΦi, hΦ⟩ := ent_toReal_eq_integral_Phi P hfL.aestronglyMeasurable hf2 hnorm hfin
  -- integrability
  have hcl : Continuous fun x : ℝ => x ^ 2 * Real.log (x ^ 2) :=
    Real.continuous_mul_log.comp (continuous_pow 2)
  have iF : Integrable (fun X => f X ^ 2 * Real.log (f X ^ 2)) P := by
    have := (hΦi.add hf2).sub (integrable_const (1 : ℝ))
    refine this.congr (Eventually.of_forall fun X => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, Phi]; ring
  have iG : Integrable (fun X => g X ^ 2 * Real.log (g X ^ 2)) P :=
    Integrable.mono' (integrable_const (1 + M ^ 2 * Real.log (M ^ 2)))
      (hcl.comp_aestronglyMeasurable hgL.aestronglyMeasurable)
      (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact abs_sq_log_sq_le (hg0 X) (hgM X) hM1)
  have iT2 : Integrable (fun X => t X ^ 2) P := htL.integrable_sq
  have iT1 : Integrable (fun X => t X ^ 2 * Real.posLog (t X ^ 2)) P := by
    refine Integrable.mono' (hΦi.add hf2) ?_ (Eventually.of_forall fun X => ?_)
    · have hc' : Continuous fun x : ℝ => x ^ 2 * Real.posLog (x ^ 2) :=
        (continuous_pow 2).mul (Real.continuous_posLog.comp (continuous_pow 2))
      exact hc'.comp_aestronglyMeasurable htL.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) Real.posLog_nonneg)]
      have h1 : t X ≤ f X := by
        simp only [htdef]; exact max_le (by linarith [hf0 X]) (hf0 X)
      exact (sq_posLog_sq_mono (ht0 X) h1).trans (sq_posLog_sq_le_Phi_add _ (hf0 X))
  have hhalf : MemLp (fun X => min (f X) (M / 2)) 2 P :=
    hfL.inf (memLp_const (M / 2))
  have iS : Integrable (fun X => 4 / 3 * (f X ^ 2 - min (f X) (M / 2) ^ 2)) P :=
    (hf2.sub hhalf.integrable_sq).const_mul _
  -- `h = ∫ f² log f²`
  have hh : (ent P (fun X => f X ^ 2)).toReal = ∫ X, f X ^ 2 * Real.log (f X ^ 2) ∂P := by
    rw [hΦ]
    have e : (fun X => f X ^ 2 * Real.log (f X ^ 2)) = fun X => (Phi (f X) + f X ^ 2) - 1 := by
      funext X; simp only [Phi]; ring
    have j : Integrable (fun X => Phi (f X) + f X ^ 2) P := hΦi.add hf2
    rw [e, integral_sub j (integrable_const 1), integral_add hΦi hf2, hnorm]
    simp
  -- integrate the pointwise bound
  have hI : ∫ X, f X ^ 2 * Real.log (f X ^ 2) ∂P ≤ ∫ X, g X ^ 2 * Real.log (g X ^ 2) ∂P +
      (1 + η) * ∫ X, t X ^ 2 * Real.posLog (t X ^ 2) ∂P +
      C * Real.log (M ^ 2) * ∫ X, 4 / 3 * (f X ^ 2 - min (f X) (M / 2) ^ 2) ∂P := by
    have j1 : Integrable (fun X => (1 + η) * (t X ^ 2 * Real.posLog (t X ^ 2))) P :=
      iT1.const_mul _
    have j2 : Integrable (fun X => C * Real.log (M ^ 2) *
        (4 / 3 * (f X ^ 2 - min (f X) (M / 2) ^ 2))) P := iS.const_mul _
    have j12 : Integrable (fun X => g X ^ 2 * Real.log (g X ^ 2) +
        (1 + η) * (t X ^ 2 * Real.posLog (t X ^ 2))) P := iG.add j1
    have jS : Integrable (fun X => g X ^ 2 * Real.log (g X ^ 2) +
        (1 + η) * (t X ^ 2 * Real.posLog (t X ^ 2)) +
        C * Real.log (M ^ 2) * (4 / 3 * (f X ^ 2 - min (f X) (M / 2) ^ 2))) P := j12.add j2
    calc ∫ X, f X ^ 2 * Real.log (f X ^ 2) ∂P ≤ ∫ X, (g X ^ 2 * Real.log (g X ^ 2) +
          (1 + η) * (t X ^ 2 * Real.posLog (t X ^ 2)) +
          C * Real.log (M ^ 2) * (4 / 3 * (f X ^ 2 - min (f X) (M / 2) ^ 2))) ∂P :=
          integral_mono iF jS fun X => hC M (f X) hM (hf0 X)
      _ = _ := by
          rw [integral_add j12 j2, integral_add iG j1, integral_const_mul, integral_const_mul]
  -- `∫ g² log g² ≤ Ent(g²)`
  have hEntg : ∫ X, g X ^ 2 * Real.log (g X ^ 2) ∂P ≤ (ent P (fun X => g X ^ 2)).toReal := by
    have hg2 : Integrable (fun X => g X ^ 2) P := hgL.integrable_sq
    rw [ent_eq_formula P _ (fun X => sq_nonneg _) hg2 iG]
    have hbar0 : 0 ≤ ∫ X, g X ^ 2 ∂P := integral_nonneg fun X => sq_nonneg _
    have hbar1 : ∫ X, g X ^ 2 ∂P ≤ 1 := by
      calc ∫ X, g X ^ 2 ∂P ≤ ∫ X, f X ^ 2 ∂P :=
            integral_mono hg2 hf2 fun X => pow_le_pow_left₀ (hg0 X) (min_le_left _ _) 2
        _ = 1 := hnorm
    have := Real.mul_log_nonpos hbar0 hbar1
    rw [ENNReal.toReal_ofReal']
    exact le_trans (by linarith) (le_max_left _ _)
  -- the defective inequality for `t` and Lemma B.1 (iii)
  have hB := hB1.2.2 (Config N d) P t ht0 iT2 hc
  have hdt := hdef t htH
  have hT2fin : ∫⁻ X, ENNReal.ofReal (t X ^ 2) ∂P ≠ ⊤ :=
    ((hasFiniteIntegral_iff_ofReal (f := fun X => t X ^ 2)
      (Eventually.of_forall fun X => sq_nonneg _)).mp iT2.2).ne
  have hRfin : ENNReal.ofReal (2 / r₀) * energy V W N t +
      (B : ℝ≥0∞) * ∫⁻ X, ENNReal.ofReal (t X ^ 2) ∂P ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (energy_lt_top hyp htH).ne,
      ENNReal.mul_ne_top ENNReal.coe_ne_top hT2fin⟩
  have hentt : ent P (fun X => t X ^ 2) ≠ ⊤ := ne_top_of_le_ne_top hRfin hdt
  have hT1 : ∫ X, t X ^ 2 * Real.posLog (t X ^ 2) ∂P ≤
      2 / r₀ * (energy V W N t).toReal + B * ∫ X, t X ^ 2 ∂P := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun X =>
      mul_nonneg (sq_nonneg _) Real.posLog_nonneg) iT1.aestronglyMeasurable]
    refine (ENNReal.toReal_mono hentt hB).trans ((ENNReal.toReal_mono hRfin hdt).trans ?_)
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (energy_lt_top hyp htH).ne)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hT2fin), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity),
      ← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun X => sq_nonneg _)
        iT2.aestronglyMeasurable]
    simp only [ENNReal.coe_toReal]
    exact le_rfl
  have hcS : ∫ X, t X ^ 2 ∂P ≤ ∫ X, 4 / 3 * (f X ^ 2 - min (f X) (M / 2) ^ 2) ∂P :=
    integral_mono iT2 iS fun X => posPart_sq_le_majorant (hf0 X) hM0
  -- energy split
  have hsplit := energy_eq_min_add_posPart hyp hmem M
  have hEg := energy_lt_top hyp hgH
  have hEt := energy_lt_top hyp htH
  have hsplitR : (energy V W N t).toReal = (energy V W N f).toReal - (energy V W N g).toReal := by
    rw [hsplit, ENNReal.toReal_add hEg.ne hEt.ne]; ring
  have hB0 : (0 : ℝ) ≤ B := B.2
  have hBc := mul_le_mul_of_nonneg_left hcS hB0
  rw [hsplitR] at hT1
  have hη1 : 0 ≤ 1 + η := by linarith
  have := mul_le_mul_of_nonneg_left hT1 hη1
  rw [hh]
  nlinarith [hI, hEntg, this, mul_le_mul_of_nonneg_left hBc hη1]


/-- `∫ f² log⁺ f² ≤ Ent(f²) + 1` for a normalized `f`. -/
theorem int_sq_posLog_le (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hmem : MemH1C (gibbs V W N) f) (hf0 : ∀ X, 0 ≤ f X)
    (hnorm : ∫ X, f X ^ 2 ∂gibbs V W N = 1)
    (hfin : ent (gibbs V W N) (fun X => f X ^ 2) ≠ ⊤) :
    Integrable (fun X => f X ^ 2 * Real.posLog (f X ^ 2)) (gibbs V W N) ∧
      ∫ X, f X ^ 2 * Real.posLog (f X ^ 2) ∂gibbs V W N ≤
        (ent (gibbs V W N) (fun X => f X ^ 2)).toReal + 1 := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  set P := gibbs V W N
  have hfL := memLp_of_memH1C hyp hmem
  have hf2 : Integrable (fun X => f X ^ 2) P := hfL.integrable_sq
  obtain ⟨hΦi, hΦ⟩ := ent_toReal_eq_integral_Phi P hfL.aestronglyMeasurable hf2 hnorm hfin
  have hint : Integrable (fun X => f X ^ 2 * Real.posLog (f X ^ 2)) P := by
    refine Integrable.mono' (hΦi.add hf2) ?_ (Eventually.of_forall fun X => ?_)
    · have hc : Continuous fun x : ℝ => x ^ 2 * Real.posLog (x ^ 2) :=
        (continuous_pow 2).mul (Real.continuous_posLog.comp (continuous_pow 2))
      exact hc.comp_aestronglyMeasurable hfL.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) Real.posLog_nonneg)]
      exact sq_posLog_sq_le_Phi_add _ (hf0 X)
  refine ⟨hint, ?_⟩
  have h1 : ∫ X, f X ^ 2 * Real.posLog (f X ^ 2) ∂P ≤ ∫ X, (Phi (f X) + f X ^ 2) ∂P :=
    integral_mono hint (hΦi.add hf2) fun X => sq_posLog_sq_le_Phi_add _ (hf0 X)
  have h2 : ∫ X, (Phi (f X) + f X ^ 2) ∂P = (ent P (fun X => f X ^ 2)).toReal + 1 := by
    rw [integral_add hΦi hf2, hnorm, hΦ]
  exact h1.trans h2.le

theorem geom_half_sum (L : ℝ) (K : ℕ) :
    ∑ j ∈ Finset.range K, (2 ^ j * L / 2) = (2 ^ K - 1) * L / 2 := by
  induction K with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- Dyadic levels: `∑_{j<K} (s_j/2) 1[e^{s_j} < y] ≤ log⁺ y` for `s_j = 2^j L`. -/
theorem dyadic_sum_le_posLog {L : ℝ} (hL : 0 < L) (y : ℝ) (K : ℕ) :
    ∑ j ∈ Finset.range K, (if Real.exp (2 ^ j * L) < y then 2 ^ j * L / 2 else 0) ≤
      Real.posLog y := by
  induction K with
  | zero => simp [Real.posLog_nonneg]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases hn : Real.exp (2 ^ n * L) < y
    · rw [if_pos hn]
      have hy0 : 0 < y := lt_trans (Real.exp_pos _) hn
      have hlog : 2 ^ n * L < Real.log y := (Real.lt_log_iff_exp_lt hy0).2 hn
      have hy1 : 1 ≤ |y| := by
        rw [abs_of_pos hy0]
        have : 1 < Real.exp (2 ^ n * L) := Real.one_lt_exp_iff.2 (by positivity)
        linarith
      have hall : ∀ j ∈ Finset.range n, (if Real.exp (2 ^ j * L) < y then 2 ^ j * L / 2 else 0) =
          2 ^ j * L / 2 := by
        intro j hj
        have hjn : j < n := Finset.mem_range.1 hj
        have : 2 ^ j * L ≤ 2 ^ n * L :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hjn.le) hL.le
        rw [if_pos]
        exact lt_of_le_of_lt (Real.exp_le_exp.2 this) hn
      rw [Finset.sum_congr rfl hall, geom_half_sum, Real.posLog_eq_log hy1]
      have h2 : (2 : ℝ) ^ n ≥ 1 := one_le_pow₀ (by norm_num)
      have : (2 ^ n - 1) * L / 2 + 2 ^ n * L / 2 = 2 ^ n * L - L / 2 := by ring
      linarith
    · rw [if_neg hn, add_zero]; exact ih

/-- The tail function `y ↦ y · 1[e^s < y]`. -/
def tailFun (s y : ℝ) : ℝ := if Real.exp s < y then y else 0

theorem measurable_tailFun (s : ℝ) : Measurable (tailFun s) :=
  Measurable.ite measurableSet_Ioi measurable_id measurable_const

theorem tailFun_nonneg {s y : ℝ} (hy : 0 ≤ y) : 0 ≤ tailFun s y := by
  unfold tailFun; split_ifs <;> linarith

theorem tailFun_le {s y : ℝ} (hy : 0 ≤ y) : tailFun s y ≤ y := by
  unfold tailFun; split_ifs <;> linarith

theorem integrable_tailFun {α : Type*} [MeasurableSpace α] {P : Measure α} {f : α → ℝ}
    (hf2 : Integrable (fun x => f x ^ 2) P) (s : ℝ) :
    Integrable (fun x => tailFun s (f x ^ 2)) P := by
  refine Integrable.mono' hf2 ?_ (Eventually.of_forall fun x => ?_)
  · exact ((measurable_tailFun s).comp_aemeasurable hf2.aemeasurable).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (tailFun_nonneg (sq_nonneg _))]
    exact tailFun_le (sq_nonneg _)

/-- The pigeonhole over dyadic levels. -/
theorem tail_pigeon {α : Type*} [MeasurableSpace α] (P : Measure α) {f : α → ℝ}
    (hf2 : Integrable (fun x => f x ^ 2) P)
    (hl : Integrable (fun x => f x ^ 2 * Real.posLog (f x ^ 2)) P) {A : ℝ}
    (hA : ∫ x, f x ^ 2 * Real.posLog (f x ^ 2) ∂P ≤ A) {L : ℝ} (hL : 0 < L) :
    (∀ K : ℕ, ∑ j ∈ Finset.range K,
        2 ^ j * L / 2 * ∫ x, tailFun (2 ^ j * L) (f x ^ 2) ∂P ≤ A) ∧
    ∀ K : ℕ, 0 < K → ∃ j < K,
      2 ^ j * L / 2 * ∫ x, tailFun (2 ^ j * L) (f x ^ 2) ∂P ≤ A / K := by
  have hsum : ∀ K : ℕ, ∑ j ∈ Finset.range K,
      2 ^ j * L / 2 * ∫ x, tailFun (2 ^ j * L) (f x ^ 2) ∂P ≤ A := by
    intro K
    have hi : ∀ j ∈ Finset.range K, Integrable (fun x => 2 ^ j * L / 2 *
        tailFun (2 ^ j * L) (f x ^ 2)) P := fun j _ => (integrable_tailFun hf2 _).const_mul _
    calc ∑ j ∈ Finset.range K, 2 ^ j * L / 2 * ∫ x, tailFun (2 ^ j * L) (f x ^ 2) ∂P
        = ∫ x, ∑ j ∈ Finset.range K, 2 ^ j * L / 2 * tailFun (2 ^ j * L) (f x ^ 2) ∂P := by
          rw [integral_finset_sum _ hi]
          exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm
      _ ≤ ∫ x, f x ^ 2 * Real.posLog (f x ^ 2) ∂P := by
          refine integral_mono (integrable_finset_sum _ hi) hl fun x => ?_
          have h1 := dyadic_sum_le_posLog hL (f x ^ 2) K
          have h2 : ∑ j ∈ Finset.range K, 2 ^ j * L / 2 * tailFun (2 ^ j * L) (f x ^ 2) =
              (∑ j ∈ Finset.range K,
                (if Real.exp (2 ^ j * L) < f x ^ 2 then 2 ^ j * L / 2 else 0)) * f x ^ 2 := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            unfold tailFun
            split_ifs <;> ring
          rw [h2, mul_comm]
          exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ ≤ A := hA
  refine ⟨hsum, fun K hK => ?_⟩
  by_contra hcon
  push Not at hcon
  have hne : (Finset.range K).Nonempty := ⟨0, Finset.mem_range.2 hK⟩
  have := Finset.sum_lt_sum_of_nonempty hne (fun j hj => hcon j (Finset.mem_range.1 hj))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rw [mul_div_cancel₀ _ hK'.ne'] at this
  exact absurd (hsum K) (not_le.2 this)

/-- The continuous majorant of the tail is dominated by the tail function. -/
theorem majorant_le_tailFun {f s : ℝ} (hf : 0 ≤ f) :
    4 / 3 * (f ^ 2 - min f (Real.exp (s / 2)) ^ 2) ≤ 4 / 3 * tailFun s (f ^ 2) := by
  have ha : Real.exp (s / 2) ^ 2 = Real.exp s := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have ha0 : 0 < Real.exp (s / 2) := Real.exp_pos _
  unfold tailFun
  rcases le_or_gt f (Real.exp (s / 2)) with h | h
  · rw [min_eq_left h]
    simp only [sub_self, mul_zero]
    split_ifs <;> nlinarith [sq_nonneg f]
  · rw [min_eq_right h.le]
    have h2 : Real.exp s < f ^ 2 := by rw [← ha]; exact pow_lt_pow_left₀ h ha0.le (by norm_num)
    rw [if_pos h2]
    nlinarith [sq_nonneg (Real.exp (s / 2))]


/-- The estimate for one `N` and one dyadic level `s`: the bounded comparison at the truncation
level `M = 2 e^{s/2}` and the key inequality give a bound by the tail integral
`ψ = ∫ f² 1[f² > e^s]`. -/
theorem positive_one (hyp : Hyp V W KV KW) {η : ℝ} (hη : 0 < η) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ M s : ℝ, Real.exp 1 ≤ M → 0 ≤ s →
      s ^ 2 * Real.log (s ^ 2) ≤ min s M ^ 2 * Real.log (min s M ^ 2) +
        (1 + η) * (max (s - M) 0 ^ 2 * Real.posLog (max (s - M) 0 ^ 2)) +
        C * Real.log (M ^ 2) * (4 / 3 * (s ^ 2 - min s (M / 2) ^ 2)))
    {r₀ : ℝ} (hr₀ : 0 < r₀) {B : NNReal} {N : ℕ}
    (hdef : ∀ u : Config N d → ℝ, MemH1C (gibbs V W N) u →
      ent (gibbs V W N) (fun X => u X ^ 2) ≤ ENNReal.ofReal (2 / r₀) * energy V W N u +
        (B : ℝ≥0∞) * ∫⁻ X, ENNReal.ofReal (u X ^ 2) ∂gibbs V W N)
    {f : Config N d → ℝ} (hmem : MemH1C (gibbs V W N) f) (hf0 : ∀ X, 0 ≤ f X)
    (hnorm : ∫ X, f X ^ 2 ∂gibbs V W N = 1)
    (hfin : ent (gibbs V W N) (fun X => f X ^ 2) ≠ ⊤) {s : ℝ} (hs : 3 ≤ s) {ε : ℝ}
    (hcomp : r₀ / 2 * (ent (gibbs V W N)
        (fun X => min (f X) (2 * Real.exp (s / 2)) ^ 2)).toReal ≤
      (energy V W N (fun X => min (f X) (2 * Real.exp (s / 2)))).toReal + ε)
    (hψs : 4 / 3 * ∫ X, tailFun s (f X ^ 2) ∂gibbs V W N ≤ Real.exp (-1)) :
    (ent (gibbs V W N) (fun X => f X ^ 2)).toReal ≤
      (1 + η) * (2 / r₀) * (energy V W N f).toReal + 2 / r₀ * ε +
        ((1 + η) * B + C * (2 * s)) * (4 / 3 * ∫ X, tailFun s (f X ^ 2) ∂gibbs V W N) := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  set P := gibbs V W N with hP
  set ψ := ∫ X, tailFun s (f X ^ 2) ∂P with hψ
  set a := Real.exp (s / 2) with ha
  set M := 2 * a with hMdef
  have ha0 : 0 < a := Real.exp_pos _
  have haM : M / 2 = a := by rw [hMdef]; ring
  have ha2 : a ^ 2 = Real.exp s := by
    rw [ha, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hexp1 : Real.exp 1 ≤ a := Real.exp_le_exp.2 (by linarith)
  have hM : Real.exp 1 ≤ M := by rw [hMdef]; linarith
  have hM1 : 1 ≤ M := le_trans (Real.one_le_exp (by norm_num)) hM
  have hfL := memLp_of_memH1C hyp hmem
  have hf2 : Integrable (fun X => f X ^ 2) P := hfL.integrable_sq
  have hhalf : MemLp (fun X => min (f X) (M / 2)) 2 P := hfL.inf (memLp_const _)
  have iS : Integrable (fun X => 4 / 3 * (f X ^ 2 - min (f X) (M / 2) ^ 2)) P :=
    (hf2.sub hhalf.integrable_sq).const_mul _
  have hψ0 : 0 ≤ ψ := integral_nonneg fun X => tailFun_nonneg (sq_nonneg _)
  have hSle : ∫ X, 4 / 3 * (f X ^ 2 - min (f X) (M / 2) ^ 2) ∂P ≤ 4 / 3 * ψ := by
    rw [hψ, ← integral_const_mul]
    refine integral_mono iS ((integrable_tailFun hf2 s).const_mul _) fun X => ?_
    rw [haM]; exact majorant_le_tailFun (hf0 X)
  have hS0 : 0 ≤ ∫ X, 4 / 3 * (f X ^ 2 - min (f X) (M / 2) ^ 2) ∂P :=
    integral_nonneg fun X => majorant_nonneg (hf0 X) (by linarith)
  have hc : ∫ X, max (f X - M) 0 ^ 2 ∂P ≤ Real.exp (-1) := by
    refine le_trans ?_ (hSle.trans hψs)
    exact integral_mono (((hfL.sub (memLp_const M)).sup (memLp_const 0)).integrable_sq) iS
      fun X => posPart_sq_le_majorant (hf0 X) (by linarith)
  have key := positive_key_ineq_all hyp lemma_B1 hη hC0 hC hr₀ hdef hmem hf0 hnorm hfin hM hc
  -- `log M² ≤ 2 s`
  have hM2 : M ^ 2 = 4 * Real.exp s := by rw [hMdef, mul_pow, ha2]; ring
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
  have hlogM : Real.log (M ^ 2) ≤ 2 * s := by
    rw [hM2, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]; linarith
  have hlogM0 : 0 ≤ Real.log (M ^ 2) := Real.log_nonneg (by nlinarith)
  -- arithmetic
  set Sx := ∫ X, 4 / 3 * (f X ^ 2 - min (f X) (M / 2) ^ 2) ∂P with hSx
  set Ef := (energy V W N f).toReal
  set Eg := (energy V W N (fun X => min (f X) M)).toReal
  set Entg := (ent P (fun X => min (f X) M ^ 2)).toReal
  have hEg0 : 0 ≤ Eg := ENNReal.toReal_nonneg
  have hB0 : (0 : ℝ) ≤ B := B.2
  have hq : 0 < 2 / r₀ := by positivity
  have hEntg : Entg ≤ 2 / r₀ * (Eg + ε) := by
    have h1 : r₀ / 2 * Entg ≤ Eg + ε := hcomp
    have h2 : 2 / r₀ * (r₀ / 2) = 1 := by field_simp
    calc Entg = 2 / r₀ * (r₀ / 2 * Entg) := by rw [← mul_assoc, h2, one_mul]
      _ ≤ 2 / r₀ * (Eg + ε) := mul_le_mul_of_nonneg_left h1 hq.le
  have hBS : (1 + η) * (B * Sx) ≤ (1 + η) * (B * (4 / 3 * ψ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSle hB0) (by linarith)
  have hCS : C * Real.log (M ^ 2) * Sx ≤ C * (2 * s) * (4 / 3 * ψ) := by
    calc C * Real.log (M ^ 2) * Sx ≤ C * Real.log (M ^ 2) * (4 / 3 * ψ) :=
          mul_le_mul_of_nonneg_left hSle (mul_nonneg hC0 hlogM0)
      _ ≤ C * (2 * s) * (4 / 3 * ψ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hlogM hC0
  have hEE : 2 / r₀ * Eg ≤ (1 + η) * (2 / r₀) * Eg := by
    have : 0 ≤ η * (2 / r₀) * Eg := by positivity
    nlinarith
  have key' : (ent P (fun X => f X ^ 2)).toReal ≤ Entg + (1 + η) * (2 / r₀ * (Ef - Eg) + B * Sx) +
      C * Real.log (M ^ 2) * Sx := key
  nlinarith [key', hEntg, hBS, hCS, hEE]

end SharpLSI.FL
