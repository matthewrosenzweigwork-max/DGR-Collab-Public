import SharpSymmetricLSI.Paper.R7Vanishing

/-!
# R7, positive limiting entropy (Section 2.3, (2.15)–(2.20))

`large_pointwise`: Lemma B.1 (i) in the form
`s² log s² ≤ g² log g² + (1+η) t² log⁺ t² + C log M² · (4/3)(s² - min(s, M/2)²)`
(`g = s ∧ M`, `t = (s - M)₊`), with the continuous majorant `(4/3)(s² - min(s, M/2)²)` of
`s² 1_{s > M}`. `positive_key_ineq`: the integrated inequality (2.19) for one `N`.
-/

open MeasureTheory Set Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem sq_indicator_le_majorant {s M : ℝ} (hs : 0 ≤ s) (hM : 0 ≤ M) (hsM : M < s) :
    s ^ 2 ≤ 4 / 3 * (s ^ 2 - min s (M / 2) ^ 2) := by
  rw [min_eq_right (by linarith)]; nlinarith

theorem majorant_nonneg {s M : ℝ} (hs : 0 ≤ s) (hM : 0 ≤ M) :
    0 ≤ 4 / 3 * (s ^ 2 - min s (M / 2) ^ 2) := by
  rcases le_total s (M / 2) with h | h
  · rw [min_eq_left h]; simp
  · rw [min_eq_right h]; nlinarith

theorem posPart_sq_le_majorant {s M : ℝ} (hs : 0 ≤ s) (hM : 0 ≤ M) :
    max (s - M) 0 ^ 2 ≤ 4 / 3 * (s ^ 2 - min s (M / 2) ^ 2) := by
  rcases le_total s M with h | h
  · rw [max_eq_right (by linarith)]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]; exact majorant_nonneg hs hM
  · rcases h.eq_or_lt with h' | h'
    · subst h'; rw [sub_self, max_self]; simp only [ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow]; exact majorant_nonneg hs hM
    · rw [max_eq_left (by linarith)]
      have := sq_indicator_le_majorant hs hM h'
      nlinarith

/-- Lemma B.1 (i), pointwise, with the continuous majorant. -/
theorem large_pointwise (hB1 : TruncationConclusion) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M s : ℝ, Real.exp 1 ≤ M → 0 ≤ s →
      s ^ 2 * Real.log (s ^ 2) ≤ min s M ^ 2 * Real.log (min s M ^ 2) +
        (1 + η) * (max (s - M) 0 ^ 2 * Real.posLog (max (s - M) 0 ^ 2)) +
        C * Real.log (M ^ 2) * (4 / 3 * (s ^ 2 - min s (M / 2) ^ 2)) := by
  obtain ⟨C₀, hC₀⟩ := hB1.1 η hη
  refine ⟨max C₀ 0, le_max_right _ _, fun M s hM hs => ?_⟩
  have he1 : 1 < Real.exp 1 := by have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith
  have hM0 : 0 < M := by linarith
  have hlogM : 0 ≤ Real.log (M ^ 2) := Real.log_nonneg (by nlinarith)
  have hmaj := majorant_nonneg (M := M) hs hM0.le
  have hpl : 0 ≤ max (s - M) 0 ^ 2 * Real.posLog (max (s - M) 0 ^ 2) :=
    mul_nonneg (sq_nonneg _) Real.posLog_nonneg
  rcases le_or_gt s M with h | h
  · rw [min_eq_left h]
    have : 0 ≤ max C₀ 0 * Real.log (M ^ 2) * (4 / 3 * (s ^ 2 - min s (M / 2) ^ 2)) :=
      mul_nonneg (mul_nonneg (le_max_right _ _) hlogM) hmaj
    nlinarith
  · rw [min_eq_right h.le, max_eq_left (by linarith)]
    have h1 := hC₀ M s hM h
    have h2 : C₀ * s ^ 2 * Real.log (M ^ 2) ≤ max C₀ 0 * Real.log (M ^ 2) *
        (4 / 3 * (s ^ 2 - min s (M / 2) ^ 2)) := by
      have h3 := sq_indicator_le_majorant hs hM0.le h
      calc C₀ * s ^ 2 * Real.log (M ^ 2) ≤ max C₀ 0 * s ^ 2 * Real.log (M ^ 2) := by
            gcongr; exact le_max_left _ _
        _ = max C₀ 0 * Real.log (M ^ 2) * s ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 (mul_nonneg (le_max_right _ _) hlogM)
    have h4 : (1 + η) * (s - M) ^ 2 * Real.posLog ((s - M) ^ 2) =
        (1 + η) * ((s - M) ^ 2 * Real.posLog ((s - M) ^ 2)) := by ring
    linarith

theorem abs_sq_log_sq_le {m M : ℝ} (hm : 0 ≤ m) (hmM : m ≤ M) (hM : 1 ≤ M) :
    |m ^ 2 * Real.log (m ^ 2)| ≤ 1 + M ^ 2 * Real.log (M ^ 2) := by
  have hM2 : 0 ≤ M ^ 2 * Real.log (M ^ 2) :=
    mul_nonneg (sq_nonneg _) (Real.log_nonneg (by nlinarith))
  rcases le_or_gt (m ^ 2) 1 with h | h
  · rcases (sq_nonneg m).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul, abs_zero]; linarith
    · have := Real.abs_log_mul_self_lt (m ^ 2) h0 h
      rw [mul_comm] at this; linarith
  · have h1 : m ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hm hmM 2
    have hl : 0 ≤ Real.log (m ^ 2) := Real.log_nonneg h.le
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hl)]
    have := Real.log_le_log (by linarith) h1
    nlinarith

set_option maxHeartbeats 1000000 in
/-- The integrated inequality (2.19) for one `N`. -/
theorem positive_key_ineq (hyp : Hyp V W KV KW) (hB1 : TruncationConclusion) {η : ℝ}
    (hη : 0 < η) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ M s : ℝ, Real.exp 1 ≤ M → 0 ≤ s →
      s ^ 2 * Real.log (s ^ 2) ≤ min s M ^ 2 * Real.log (min s M ^ 2) +
        (1 + η) * (max (s - M) 0 ^ 2 * Real.posLog (max (s - M) 0 ^ 2)) +
        C * Real.log (M ^ 2) * (4 / 3 * (s ^ 2 - min s (M / 2) ^ 2)))
    {r₀ : ℝ} (hr₀ : 0 < r₀) {B : NNReal} {N : ℕ}
    (hdef : ∀ u : Config N d → ℝ, MemH1C (gibbs V W N) u → IsSymmetric u →
      ent (gibbs V W N) (fun X => u X ^ 2) ≤ ENNReal.ofReal (2 / r₀) * energy V W N u +
        (B : ℝ≥0∞) * ∫⁻ X, ENNReal.ofReal (u X ^ 2) ∂gibbs V W N)
    {f : Config N d → ℝ} (hmem : MemH1C (gibbs V W N) f) (hsym : IsSymmetric f)
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
  have hdt := hdef t htH (hsym.comp_fun fun s => max (s - M) 0)
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

/-! ### Bounded continuous truncations -/

/-- `x ↦ min(|x|, M)²`. -/
noncomputable def psiSq (M : ℝ) (hM : 0 ≤ M) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min |x| M ^ 2)
    ((continuous_abs.min continuous_const).pow 2) (M ^ 2) (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (le_min (abs_nonneg _) hM) (min_le_right _ _) 2)

/-- `x ↦ m² log m²`, `m = min(|x|, M)`. -/
noncomputable def psiEnt (M : ℝ) (hM : 1 ≤ M) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => min |x| M ^ 2 * Real.log (min |x| M ^ 2))
    (Real.continuous_mul_log.comp ((continuous_abs.min continuous_const).pow 2))
    (1 + M ^ 2 * Real.log (M ^ 2)) (fun x => by
      rw [Real.norm_eq_abs]
      exact abs_sq_log_sq_le (le_min (abs_nonneg _) (by linarith)) (min_le_right _ _) hM)

theorem psiSq_apply (M : ℝ) (hM : 0 ≤ M) (x : ℝ) : psiSq M hM x = min |x| M ^ 2 := rfl

theorem psiEnt_apply (M : ℝ) (hM : 1 ≤ M) (x : ℝ) :
    psiEnt M hM x = min |x| M ^ 2 * Real.log (min |x| M ^ 2) := rfl

/-- The entropy of `min(|u|, M)²` through the two test functions. -/
theorem ent_trunc_toReal {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    {u : α → ℝ} (hu : AEStronglyMeasurable u P) {M : ℝ} (hM : 1 ≤ M) :
    (ent P (fun x => min |u x| M ^ 2)).toReal =
      max (∫ x, psiEnt M hM (u x) ∂P - (∫ x, psiSq M (by linarith) (u x) ∂P) *
        Real.log (∫ x, psiSq M (by linarith) (u x) ∂P)) 0 := by
  have hm : AEStronglyMeasurable (fun x => min |u x| M) P :=
    (continuous_abs.min continuous_const).comp_aestronglyMeasurable hu
  have i1 : Integrable (fun x => min |u x| M ^ 2) P :=
    Integrable.mono' (integrable_const (M ^ 2)) (hm.pow 2) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (le_min (abs_nonneg _) (by linarith)) (min_le_right _ _) 2)
  have i2 : Integrable (fun x => min |u x| M ^ 2 * Real.log (min |u x| M ^ 2)) P :=
    Integrable.mono' (integrable_const (1 + M ^ 2 * Real.log (M ^ 2)))
      (Real.continuous_mul_log.comp_aestronglyMeasurable (hm.pow 2))
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact abs_sq_log_sq_le (le_min (abs_nonneg _) (by linarith)) (min_le_right _ _) hM)
  rw [ent_eq_formula P _ (fun x => sq_nonneg _) i1 i2, ENNReal.toReal_ofReal']
  simp only [psiEnt_apply, psiSq_apply]

/-! ### Tails under `γ` -/

theorem eventually_min_abs_eq (x : ℝ) : ∀ᶠ n : ℕ in atTop, min |x| ((n : ℝ) / 2) = |x| := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge (2 * |x|)
  filter_upwards [eventually_ge_atTop n₀] with n hn
  apply min_eq_left
  have : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem tail_maj_tendsto {α : Type*} [MeasurableSpace α] {γ : Measure α} {F : α → ℝ}
    (hF : AEStronglyMeasurable F γ) (hF2 : Integrable (fun z => F z ^ 2) γ) :
    Tendsto (fun n : ℕ => ∫ z, 4 / 3 * (F z ^ 2 - min |F z| ((n : ℝ) / 2) ^ 2) ∂γ) atTop
      (𝓝 0) := by
  have := tendsto_integral_filter_of_dominated_convergence (μ := γ) (l := atTop)
    (F := fun (n : ℕ) z => 4 / 3 * (F z ^ 2 - min |F z| ((n : ℝ) / 2) ^ 2)) (f := fun _ => 0)
    (fun z => 4 / 3 * F z ^ 2)
    (Eventually.of_forall fun n => (hF.pow 2).sub
      (((continuous_abs.min continuous_const).pow 2).comp_aestronglyMeasurable hF) |>.const_mul _)
    (Eventually.of_forall fun n => Eventually.of_forall fun z => by
      have h1 : min |F z| ((n : ℝ) / 2) ^ 2 ≤ F z ^ 2 := by
        rw [← sq_abs (F z)]
        exact pow_le_pow_left₀ (le_min (abs_nonneg _) (by positivity)) (min_le_left _ _) 2
      rw [Real.norm_eq_abs, abs_of_nonneg (by nlinarith [sq_nonneg (min |F z| ((n : ℝ) / 2))])]
      nlinarith [sq_nonneg (min |F z| ((n : ℝ) / 2))])
    (hF2.const_mul _)
    (Eventually.of_forall fun z => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_min_abs_eq (F z)] with n hn
      rw [hn, sq_abs]; ring)
  simpa using this

theorem tail_log_maj_tendsto {α : Type*} [MeasurableSpace α] {γ : Measure α} {F : α → ℝ}
    (hF : AEStronglyMeasurable F γ) (hFl : Integrable (fun z => F z ^ 2 * Real.log (F z ^ 2)) γ) :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) ^ 2) *
      ∫ z, 4 / 3 * (F z ^ 2 - min |F z| ((n : ℝ) / 2) ^ 2) ∂γ) atTop (𝓝 0) := by
  simp_rw [← integral_const_mul]
  have := tendsto_integral_filter_of_dominated_convergence (μ := γ) (l := atTop)
    (F := fun (n : ℕ) z => Real.log ((n : ℝ) ^ 2) *
      (4 / 3 * (F z ^ 2 - min |F z| ((n : ℝ) / 2) ^ 2))) (f := fun _ => 0)
    (fun z => 8 / 3 * |F z ^ 2 * Real.log (F z ^ 2)|)
    (Eventually.of_forall fun n => (((hF.pow 2).sub
      (((continuous_abs.min continuous_const).pow 2).comp_aestronglyMeasurable hF)).const_mul
        _).const_mul _)
    (by
      filter_upwards [eventually_ge_atTop 4] with n hn
      refine Eventually.of_forall fun z => ?_
      have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
      have hlogn : 0 ≤ Real.log ((n : ℝ) ^ 2) := Real.log_nonneg (by nlinarith)
      rcases le_total |F z| ((n : ℝ) / 2) with h | h
      · rw [min_eq_left h, sq_abs, sub_self, mul_zero, mul_zero, norm_zero]; positivity
      · rw [min_eq_right h]
        have hF2 : (n : ℝ) ^ 2 / 4 ≤ F z ^ 2 := by
          have h1 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2) h 2
          rw [sq_abs] at h1
          have h2 : ((n : ℝ) / 2) ^ 2 = (n : ℝ) ^ 2 / 4 := by ring
          linarith
        have hF4 : 4 ≤ F z ^ 2 := by nlinarith
        have hlogF : 0 ≤ Real.log (F z ^ 2) := Real.log_nonneg (by linarith)
        have hlog : Real.log ((n : ℝ) ^ 2) ≤ 2 * Real.log (F z ^ 2) := by
          have e : Real.log ((n : ℝ) ^ 2) = Real.log 4 + Real.log ((n : ℝ) ^ 2 / 4) := by
            rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
          have h1 : Real.log 4 ≤ Real.log ((n : ℝ) ^ 2 / 4) :=
            Real.log_le_log (by norm_num) (by nlinarith)
          have h2 : Real.log ((n : ℝ) ^ 2 / 4) ≤ Real.log (F z ^ 2) :=
            Real.log_le_log (by positivity) hF2
          linarith
        have hm : 0 ≤ F z ^ 2 - ((n : ℝ) / 2) ^ 2 := by nlinarith
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
          abs_of_nonneg (mul_nonneg (by linarith) hlogF)]
        have : F z ^ 2 - ((n : ℝ) / 2) ^ 2 ≤ F z ^ 2 := by nlinarith
        calc Real.log ((n : ℝ) ^ 2) * (4 / 3 * (F z ^ 2 - ((n : ℝ) / 2) ^ 2))
            ≤ (2 * Real.log (F z ^ 2)) * (4 / 3 * F z ^ 2) := by
              apply mul_le_mul hlog (by linarith) (by positivity) (by linarith)
          _ = 8 / 3 * (F z ^ 2 * Real.log (F z ^ 2)) := by ring)
    (hFl.abs.const_mul _)
    (Eventually.of_forall fun z => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_min_abs_eq (F z)] with n hn
      rw [hn, sq_abs]; ring)
  simpa using this

theorem bcf_integrable_comp {α : Type*} [MeasurableSpace α] {P : Measure α} [IsFiniteMeasure P]
    (g : ℝ →ᵇ ℝ) {u : α → ℝ} (hu : AEStronglyMeasurable u P) :
    Integrable (fun x => g (u x)) P :=
  Integrable.mono' (integrable_const ‖g‖) (g.continuous.comp_aestronglyMeasurable hu)
    (Eventually.of_forall fun x => g.norm_coe_le_norm (u x))

theorem lipschitz_min_abs (M : ℝ) : LipschitzWith 1 (fun x : ℝ => min |x| M) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    calc |min |x| M - min |y| M| ≤ max |(|x| - |y|)| |M - M| := abs_min_sub_min_le_max _ _ _ _
      _ = |(|x| - |y|)| := by simp
      _ ≤ |x - y| := abs_abs_sub_abs_le_abs_sub x y

set_option maxHeartbeats 2000000 in
/-- **The positive-entropy case is impossible.** -/
theorem positive_contra (hyp : Hyp V W KV KW) (hB1 : TruncationConclusion) {r r₀ η : ℝ}
    (hr : 0 < r) (hη : 0 < η) (hrη : (1 + η) * r < r₀) {B : NNReal}
    (hdef : ∀ N, 1 ≤ N → ∀ u : Config N d → ℝ, MemH1C (gibbs V W N) u → IsSymmetric u →
      ent (gibbs V W N) (fun X => u X ^ 2) ≤ ENNReal.ofReal (2 / r₀) * energy V W N u +
        (B : ℝ≥0∞) * ∫⁻ X, ENNReal.ofReal (u X ^ 2) ∂gibbs V W N)
    {Ns : ℕ → ℕ} (hNs1 : ∀ k, 1 ≤ Ns k)
    {f : (k : ℕ) → Config (Ns k) d → ℝ} (hmem : ∀ k, MemH1C (gibbs V W (Ns k)) (f k))
    (hsym : ∀ k, IsSymmetric (f k)) (hf0 : ∀ k X, 0 ≤ f k X)
    (hnorm : ∀ k, ∫ X, f k X ^ 2 ∂gibbs V W (Ns k) = 1)
    (hfin : ∀ k, ent (gibbs V W (Ns k)) (fun X => f k X ^ 2) ≠ ⊤)
    (hviol : ∀ k, 2 * (energy V W (Ns k) (f k)).toReal <
      r * (ent (gibbs V W (Ns k)) (fun X => f k X ^ 2)).toReal)
    {h E : ℝ}
    (hh : Tendsto (fun k => (ent (gibbs V W (Ns k)) (fun X => f k X ^ 2)).toReal) atTop (𝓝 h))
    (hhpos : 0 < h) (hE : Tendsto (fun k => (energy V W (Ns k) (f k)).toReal) atTop (𝓝 E))
    {γ : Measure (ℕ → ℝ)} [IsProbabilityMeasure γ] {EInf : ((ℕ → ℝ) → ℝ) → ℝ≥0∞} {lG : ℝ≥0∞}
    (hlG : ENNReal.ofReal r₀ ≤ lG)
    (hLSI : ∀ F : (ℕ → ℝ) → ℝ, MemLp F 2 γ → ent γ (fun z => F z ^ 2) ≤ 2 / lG * EInf F)
    {F : (ℕ → ℝ) → ℝ} (hF : MemLp F 2 γ)
    (hlaw : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun k => ∫ X, g (f k X) ∂gibbs V W (Ns k)) atTop
      (𝓝 (∫ z, g (F z) ∂γ)))
    (hsq : Tendsto (fun k => ∫ X, f k X ^ 2 ∂gibbs V W (Ns k)) atTop (𝓝 (∫ z, F z ^ 2 ∂γ)))
    (hEF : EInf F ≤ liminf (fun k => energy V W (Ns k) (f k)) atTop)
    (hχ : ∀ χ : ℝ → ℝ, (∃ L, LipschitzWith L χ) →
      EInf (χ ∘ F) ≤ liminf (fun k => energy V W (Ns k) (χ ∘ f k)) atTop) : False := by
  have hr₀ : 0 < r₀ := by nlinarith
  set c0 := (1 + η) * (2 / r₀) with hc0
  have hc0pos : 0 < c0 := by positivity
  have hF1 : ∫ z, F z ^ 2 ∂γ = 1 :=
    tendsto_nhds_unique hsq (by simp_rw [hnorm]; exact tendsto_const_nhds)
  have hEfin : ∀ k, energy V W (Ns k) (f k) ≠ ⊤ := fun k => (energy_lt_top hyp (hmem k)).ne
  have hliminfE : liminf (fun k => energy V W (Ns k) (f k)) atTop = ENNReal.ofReal E := by
    have : Tendsto (fun k => energy V W (Ns k) (f k)) atTop (𝓝 (ENNReal.ofReal E)) := by
      have := ENNReal.tendsto_ofReal hE
      refine this.congr fun k => ?_
      exact ENNReal.ofReal_toReal (hEfin k)
    exact this.liminf_eq
  have hlG0 : lG ≠ 0 := by
    have : 0 < ENNReal.ofReal r₀ := ENNReal.ofReal_pos.mpr hr₀
    exact (lt_of_lt_of_le this hlG).ne'
  have h2lG : 2 / lG ≠ ⊤ := ENNReal.div_ne_top (by norm_num) hlG0
  have h2lGr : (2 / lG).toReal ≤ 2 / r₀ := by
    have h1 : 2 / lG ≤ 2 / ENNReal.ofReal r₀ := ENNReal.div_le_div_left hlG _
    have e : (2 : ℝ≥0∞) / ENNReal.ofReal r₀ = ENNReal.ofReal (2 / r₀) := by
      rw [ENNReal.ofReal_div_of_pos hr₀, ENNReal.ofReal_ofNat]
    rw [e] at h1
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hEFfin : EInf F ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hliminfE ▸ hEF)
  have hentF : ent γ (fun z => F z ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top h2lG hEFfin) (hLSI F hF)
  obtain ⟨hΦF, -⟩ := ent_toReal_eq_integral_Phi γ hF.aestronglyMeasurable hF.integrable_sq hF1
    hentF
  have hFlog : Integrable (fun z => F z ^ 2 * Real.log (F z ^ 2)) γ := by
    have := (hΦF.add hF.integrable_sq).sub (integrable_const (1 : ℝ))
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, Phi]; ring
  obtain ⟨C, hC0, hC⟩ := large_pointwise hB1 hη
  set Sinf : ℕ → ℝ := fun n => ∫ z, 4 / 3 * (F z ^ 2 - min |F z| ((n : ℝ) / 2) ^ 2) ∂γ with hSinf
  have hS0 := tail_maj_tendsto hF.aestronglyMeasurable hF.integrable_sq
  have hSlog := tail_log_maj_tendsto hF.aestronglyMeasurable hFlog
  have hbound : ∀ᶠ n : ℕ in atTop, h ≤ c0 * E + ((1 + η) * B + C * Real.log ((n : ℝ) ^ 2)) *
      Sinf n := by
    have hSe : ∀ᶠ n : ℕ in atTop, Sinf n < Real.exp (-1) :=
      (tendsto_order.mp hS0).2 _ (Real.exp_pos _)
    filter_upwards [hSe, eventually_ge_atTop 3] with n hSn hn3
    set M : ℝ := (n : ℝ) with hMdef
    have hM3 : (3 : ℝ) ≤ M := by rw [hMdef]; exact_mod_cast hn3
    have he3 : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; norm_num at this; linarith
    have hM : Real.exp 1 ≤ M := by linarith
    have hM1 : 1 ≤ M := by linarith
    have hM0 : 0 ≤ M := by linarith
    have hM2 : 0 ≤ M / 2 := by linarith
    have habs : ∀ k X, |f k X| = f k X := fun k X => abs_of_nonneg (hf0 k X)
    set P : (k : ℕ) → Measure (Config (Ns k) d) := fun k => gibbs V W (Ns k) with hPdef
    have hfL : ∀ k, MemLp (f k) 2 (P k) := fun k => memLp_of_memH1C hyp (hmem k)
    -- the majorant integrals
    set Sk : ℕ → ℝ := fun k => ∫ X, 4 / 3 * (f k X ^ 2 - min (f k X) (M / 2) ^ 2) ∂P k with hSk
    have hSkeq : ∀ k, Sk k = 4 / 3 * (∫ X, f k X ^ 2 ∂P k - ∫ X, psiSq (M / 2) hM2 (f k X) ∂P k) := by
      intro k
      have : IsProbabilityMeasure (P k) := gibbs_isProbabilityMeasure hyp (Ns k)
      have i1 : Integrable (fun X => f k X ^ 2) (P k) := (hfL k).integrable_sq
      have i2 := bcf_integrable_comp (P := P k) (psiSq (M / 2) hM2) (hfL k).aestronglyMeasurable
      rw [← integral_sub i1 i2, ← integral_const_mul]
      simp only [hSk]
      congr 1; funext X
      rw [psiSq_apply, habs]
    have hSinfeq : Sinf n = 4 / 3 * (∫ z, F z ^ 2 ∂γ - ∫ z, psiSq (M / 2) hM2 (F z) ∂γ) := by
      have i1 : Integrable (fun z => F z ^ 2) γ := hF.integrable_sq
      have i2 := bcf_integrable_comp (P := γ) (psiSq (M / 2) hM2) hF.aestronglyMeasurable
      rw [← integral_sub i1 i2, ← integral_const_mul]
      rfl
    have hSklim : Tendsto Sk atTop (𝓝 (Sinf n)) := by
      rw [hSinfeq, show Sk = fun k => 4 / 3 * (∫ X, f k X ^ 2 ∂P k -
        ∫ X, psiSq (M / 2) hM2 (f k X) ∂P k) from funext hSkeq]
      exact ((hsq.sub (hlaw (psiSq (M / 2) hM2))).const_mul _)
    -- the truncated entropies
    set Entk : ℕ → ℝ := fun k => (ent (P k) (fun X => min (f k X) M ^ 2)).toReal with hEntk
    set Entγ := (ent γ (fun z => min |F z| M ^ 2)).toReal with hEntγ
    have hEntkeq : ∀ k, Entk k = max (∫ X, psiEnt M hM1 (f k X) ∂P k -
        (∫ X, psiSq M hM0 (f k X) ∂P k) * Real.log (∫ X, psiSq M hM0 (f k X) ∂P k)) 0 := by
      intro k
      have : IsProbabilityMeasure (P k) := gibbs_isProbabilityMeasure hyp (Ns k)
      have e : (fun X => min (f k X) M ^ 2) = fun X => min |f k X| M ^ 2 := by
        funext X; rw [habs]
      simp only [hEntk]
      rw [e, ent_trunc_toReal (P k) (hfL k).aestronglyMeasurable hM1]
    have hEntγeq : Entγ = max (∫ z, psiEnt M hM1 (F z) ∂γ -
        (∫ z, psiSq M hM0 (F z) ∂γ) * Real.log (∫ z, psiSq M hM0 (F z) ∂γ)) 0 :=
      ent_trunc_toReal γ hF.aestronglyMeasurable hM1
    have hEntlim : Tendsto Entk atTop (𝓝 Entγ) := by
      rw [hEntγeq, show Entk = fun k => max (∫ X, psiEnt M hM1 (f k X) ∂P k -
        (∫ X, psiSq M hM0 (f k X) ∂P k) * Real.log (∫ X, psiSq M hM0 (f k X) ∂P k)) 0
        from funext hEntkeq]
      have ha := hlaw (psiSq M hM0)
      have hl := (Real.continuous_mul_log.tendsto _).comp ha
      exact ((hlaw (psiEnt M hM1)).sub hl).max tendsto_const_nhds
    -- the per-`k` inequality, eventually
    set Eg : ℕ → ℝ := fun k => (energy V W (Ns k) (fun X => min (f k X) M)).toReal with hEg
    set Ek : ℕ → ℝ := fun k => (energy V W (Ns k) (f k)).toReal with hEk
    set hk : ℕ → ℝ := fun k => (ent (P k) (fun X => f k X ^ 2)).toReal with hhk
    set Kc := (1 + η) * B + C * Real.log (M ^ 2) with hKc
    set Y : ℕ → ℝ := fun k => Entk k + c0 * Ek k + Kc * Sk k - hk k with hY
    have hev : ∀ᶠ k in atTop, c0 * Eg k ≤ Y k := by
      filter_upwards [(tendsto_order.mp hSklim).2 _ hSn] with k hk'
      have : IsProbabilityMeasure (P k) := gibbs_isProbabilityMeasure hyp (Ns k)
      have hc : ∫ X, max (f k X - M) 0 ^ 2 ∂P k ≤ Real.exp (-1) := by
        refine le_trans ?_ hk'.le
        exact integral_mono ((((hfL k).sub (memLp_const M)).sup (memLp_const 0)).integrable_sq)
          (((hfL k).integrable_sq.sub
            ((hfL k).inf (memLp_const (M / 2))).integrable_sq).const_mul _)
          fun X => posPart_sq_le_majorant (hf0 k X) hM0
      have := positive_key_ineq hyp hB1 hη hC0 hC hr₀ (hdef (Ns k) (hNs1 k)) (hmem k) (hsym k)
        (hf0 k) (hnorm k) (hfin k) hM hc
      simp only [hY, hEntk, hEk, hhk, hEg, hKc, hSk, hc0]
      nlinarith [this]
    have hYlim : Tendsto Y atTop (𝓝 (Entγ + c0 * E + Kc * Sinf n - h)) :=
      ((hEntlim.add (hE.const_mul c0)).add (hSklim.const_mul Kc)).sub hh
    set Yinf := Entγ + c0 * E + Kc * Sinf n - h with hYinf
    have hEg0 : ∀ k, 0 ≤ Eg k := fun k => ENNReal.toReal_nonneg
    have hYinf0 : 0 ≤ Yinf := by
      refine ge_of_tendsto hYlim ?_
      filter_upwards [hev] with k hk'
      exact le_trans (mul_nonneg hc0pos.le (hEg0 k)) hk'
    -- the `χ`-liminf for `χ = min(|·|, M)`
    set χ : ℝ → ℝ := fun x => min |x| M with hχdef
    have hχf : ∀ k, χ ∘ f k = fun X => min (f k X) M := fun k => by
      funext X; simp [hχdef, habs]
    have hEχ := hχ χ ⟨1, lipschitz_min_abs M⟩
    simp_rw [hχf] at hEχ
    have hEgfin : ∀ k, energy V W (Ns k) (fun X => min (f k X) M) ≠ ⊤ := fun k =>
      (energy_lt_top hyp (memH1C_min hyp (hmem k) M)).ne
    have hliminf : liminf (fun k => energy V W (Ns k) (fun X => min (f k X) M)) atTop ≤
        ENNReal.ofReal (Yinf / c0) := by
      have hle : ∀ᶠ k in atTop, energy V W (Ns k) (fun X => min (f k X) M) ≤
          ENNReal.ofReal (Y k / c0) := by
        filter_upwards [hev] with k hk'
        rw [← ENNReal.ofReal_toReal (hEgfin k)]
        apply ENNReal.ofReal_le_ofReal
        rw [le_div_iff₀ hc0pos]; linarith [hk']
      calc liminf (fun k => energy V W (Ns k) (fun X => min (f k X) M)) atTop
          ≤ liminf (fun k => ENNReal.ofReal (Y k / c0)) atTop := liminf_le_liminf hle
        _ = ENNReal.ofReal (Yinf / c0) :=
            (ENNReal.tendsto_ofReal (hYlim.div_const c0)).liminf_eq
    have hEInfG : EInf (χ ∘ F) ≤ ENNReal.ofReal (Yinf / c0) := hEχ.trans hliminf
    have hEInfGfin : EInf (χ ∘ F) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hEInfG
    have hEInfGr : (EInf (χ ∘ F)).toReal ≤ Yinf / c0 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hEInfG
      rwa [ENNReal.toReal_ofReal (div_nonneg hYinf0 hc0pos.le)] at this
    -- the Gaussian LSI for `χ ∘ F`
    have hGL : MemLp (χ ∘ F) 2 γ :=
      MemLp.of_bound ((lipschitz_min_abs M).continuous.comp_aestronglyMeasurable
        hF.aestronglyMeasurable) M (Eventually.of_forall fun z => by
          simp only [Function.comp_apply, hχdef, Real.norm_eq_abs]
          rw [abs_of_nonneg (le_min (abs_nonneg _) hM0)]; exact min_le_right _ _)
    have hLG := hLSI (χ ∘ F) hGL
    have hEntγle : Entγ ≤ 2 / r₀ * (EInf (χ ∘ F)).toReal := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top h2lG hEInfGfin) hLG
      rw [ENNReal.toReal_mul] at this
      calc Entγ = (ent γ (fun z => (χ ∘ F) z ^ 2)).toReal := rfl
        _ ≤ (2 / lG).toReal * (EInf (χ ∘ F)).toReal := this
        _ ≤ 2 / r₀ * (EInf (χ ∘ F)).toReal :=
            mul_le_mul_of_nonneg_right h2lGr ENNReal.toReal_nonneg
    have hfinal : Entγ ≤ Yinf := by
      have h1 : 2 / r₀ * (EInf (χ ∘ F)).toReal ≤ 2 / r₀ * (Yinf / c0) :=
        mul_le_mul_of_nonneg_left hEInfGr (by positivity)
      have h2 : 2 / r₀ * (Yinf / c0) ≤ Yinf := by
        rw [hc0]
        have : 2 / r₀ * (Yinf / ((1 + η) * (2 / r₀))) = Yinf / (1 + η) := by
          field_simp
        rw [this, div_le_iff₀ (by linarith)]
        nlinarith
      linarith
    rw [hYinf] at hfinal
    linarith
  -- let `n → ∞`
  have hlim : Tendsto (fun n : ℕ => c0 * E + ((1 + η) * B + C * Real.log ((n : ℝ) ^ 2)) * Sinf n)
      atTop (𝓝 (c0 * E)) := by
    have : Tendsto (fun n : ℕ => c0 * E + ((1 + η) * B * Sinf n +
        C * (Real.log ((n : ℝ) ^ 2) * Sinf n))) atTop (𝓝 (c0 * E + ((1 + η) * B * 0 + C * 0))) :=
      tendsto_const_nhds.add ((hS0.const_mul _).add (hSlog.const_mul _))
    simp only [mul_zero, add_zero] at this
    refine this.congr fun n => ?_
    ring
  have hhE : h ≤ c0 * E := ge_of_tendsto hlim hbound
  have h2E : 2 * E ≤ r * h :=
    le_of_tendsto_of_tendsto' (hE.const_mul 2) (hh.const_mul r) fun k => (hviol k).le
  have : c0 * E ≤ (1 + η) * r / r₀ * h := by
    rw [hc0]
    have : (1 + η) * (2 / r₀) * E = (1 + η) / r₀ * (2 * E) := by ring
    rw [this]
    have h1 : (1 + η) / r₀ * (2 * E) ≤ (1 + η) / r₀ * (r * h) :=
      mul_le_mul_of_nonneg_left h2E (by positivity)
    calc (1 + η) / r₀ * (2 * E) ≤ (1 + η) / r₀ * (r * h) := h1
      _ = (1 + η) * r / r₀ * h := by ring
  have hlt : (1 + η) * r / r₀ * h < h := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hr₀]
    nlinarith
  linarith

end SharpLSI
