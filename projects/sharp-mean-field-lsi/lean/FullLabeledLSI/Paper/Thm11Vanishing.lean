import FullLabeledLSI.Paper.Thm11Basic

/-!
# Theorem 1.1 (FL), vanishing limiting entropy (Section 2.3, (2.21)--(2.26)), no symmetry

`vanishing_key_ineq_all`: for one `N`, with `g = f ∧ b`, `t = (f - b)₊`, `c = ∫ t² ≤ e^{-1}` and
`λ_N^all ≥ ρ`,
`h ≤ 2(1+log b)(ℰ(g)/ρ + (∫g - 1)²) + (2/r₀)ℰ(t) + (B + 2(1+log(b+1))) c + Φ'(b) ∫ t`.
`vanishing_contra_all`: along a violating sequence with `h_N → 0` and uniformly integrable
`v_N² = (f_N - 1)²/h_N`, this contradicts `2ℰ(f_N) < r h_N`.
(Verbatim copy of `SharpSymmetricLSI/Paper/R7Vanishing` with the symmetry hypotheses removed and
`λ_N^sym` replaced by `λ_N^all`.)
-/

noncomputable section
open MeasureTheory Set Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The key inequality of the vanishing case**, for one `N`. -/
theorem vanishing_key_ineq_all (hyp : Hyp V W KV KW) (hB1 : TruncationConclusion) {r₀ : ℝ}
    (hr₀ : 0 < r₀) {B : NNReal} {N : ℕ}
    (hdef : ∀ u : Config N d → ℝ, MemH1C (gibbs V W N) u →
      ent (gibbs V W N) (fun X => u X ^ 2) ≤ ENNReal.ofReal (2 / r₀) * energy V W N u +
        (B : ℝ≥0∞) * ∫⁻ X, ENNReal.ofReal (u X ^ 2) ∂gibbs V W N)
    {f : Config N d → ℝ} (hmem : MemH1C (gibbs V W N) f)
    (hf0 : ∀ X, 0 ≤ f X) (hnorm : ∫ X, f X ^ 2 ∂gibbs V W N = 1)
    (hfin : ent (gibbs V W N) (fun X => f X ^ 2) ≠ ⊤) {b : ℝ} (hb : 1 < b) {ρ : ℝ} (hρ : 0 < ρ)
    (hlam : ENNReal.ofReal ρ ≤ lamAll V W N)
    (hc : ∫ X, max (f X - b) 0 ^ 2 ∂gibbs V W N ≤ Real.exp (-1)) :
    (ent (gibbs V W N) (fun X => f X ^ 2)).toReal ≤
      2 * (1 + Real.log b) * ((energy V W N (fun X => min (f X) b)).toReal / ρ +
        (∫ X, min (f X) b ∂gibbs V W N - 1) ^ 2) +
      2 / r₀ * (energy V W N (fun X => max (f X - b) 0)).toReal +
      (B + 2 * (1 + Real.log (b + 1))) * ∫ X, max (f X - b) 0 ^ 2 ∂gibbs V W N +
      deriv Phi b * ∫ X, max (f X - b) 0 ∂gibbs V W N := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  set P := gibbs V W N
  set g : Config N d → ℝ := fun X => min (f X) b with hgdef
  set t : Config N d → ℝ := fun X => max (f X - b) 0 with htdef
  have hfL := memLp_of_memH1C hyp hmem
  have hf2 : Integrable (fun X => f X ^ 2) P := hfL.integrable_sq
  have hgH := memH1C_min hyp hmem b
  have htH := memH1C_posPart_sub hyp hmem b
  have hgL := memLp_of_memH1C hyp hgH
  have htL := memLp_of_memH1C hyp htH
  have ht0 : ∀ X, 0 ≤ t X := fun X => le_max_right _ _
  obtain ⟨hΦi, hΦ⟩ := ent_toReal_eq_integral_Phi P hfL.aestronglyMeasurable hf2 hnorm hfin
  -- integrability of the pieces
  have iA : Integrable (fun X => (g X - 1) ^ 2) P := (hgL.sub (memLp_const 1)).integrable_sq
  have iT2 : Integrable (fun X => t X ^ 2) P := htL.integrable_sq
  have iT3 : Integrable t P := htL.integrable one_le_two
  have iT1 : Integrable (fun X => t X ^ 2 * Real.posLog (t X ^ 2)) P := by
    refine Integrable.mono' (hΦi.add hf2) ?_ (Eventually.of_forall fun X => ?_)
    · have hc : Continuous fun x : ℝ => x ^ 2 * Real.posLog (x ^ 2) :=
        (continuous_pow 2).mul (Real.continuous_posLog.comp (continuous_pow 2))
      exact hc.comp_aestronglyMeasurable htL.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) Real.posLog_nonneg)]
      have h1 : t X ≤ f X := by
        simp only [htdef]; exact max_le (by linarith [hf0 X]) (hf0 X)
      exact (sq_posLog_sq_mono (ht0 X) h1).trans (sq_posLog_sq_le_Phi_add _ (hf0 X))
  -- integrate the pointwise Taylor bound
  have hpt : ∀ X, Phi (f X) ≤ 2 * (1 + Real.log b) * (g X - 1) ^ 2 +
      (t X ^ 2 * Real.posLog (t X ^ 2) + 2 * (1 + Real.log (b + 1)) * t X ^ 2 +
        deriv Phi b * t X) := fun X => Phi_le_trunc hB1 hb (hf0 X)
  have hI : ∫ X, Phi (f X) ∂P ≤ 2 * (1 + Real.log b) * ∫ X, (g X - 1) ^ 2 ∂P +
      (∫ X, t X ^ 2 * Real.posLog (t X ^ 2) ∂P + 2 * (1 + Real.log (b + 1)) * ∫ X, t X ^ 2 ∂P +
        deriv Phi b * ∫ X, t X ∂P) := by
    have i1 : Integrable (fun X => 2 * (1 + Real.log b) * (g X - 1) ^ 2) P := iA.const_mul _
    have i2 : Integrable (fun X => 2 * (1 + Real.log (b + 1)) * t X ^ 2) P := iT2.const_mul _
    have i3 : Integrable (fun X => deriv Phi b * t X) P := iT3.const_mul _
    have iS : Integrable (fun X => 2 * (1 + Real.log b) * (g X - 1) ^ 2 +
        (t X ^ 2 * Real.posLog (t X ^ 2) + 2 * (1 + Real.log (b + 1)) * t X ^ 2 +
          deriv Phi b * t X)) P := i1.add ((iT1.add i2).add i3)
    calc ∫ X, Phi (f X) ∂P ≤ ∫ X, (2 * (1 + Real.log b) * (g X - 1) ^ 2 +
          (t X ^ 2 * Real.posLog (t X ^ 2) + 2 * (1 + Real.log (b + 1)) * t X ^ 2 +
            deriv Phi b * t X)) ∂P := integral_mono hΦi iS hpt
      _ = _ := by
          have j12 : Integrable (fun X => t X ^ 2 * Real.posLog (t X ^ 2) +
              2 * (1 + Real.log (b + 1)) * t X ^ 2) P := iT1.add i2
          have j123 : Integrable (fun X => t X ^ 2 * Real.posLog (t X ^ 2) +
              2 * (1 + Real.log (b + 1)) * t X ^ 2 + deriv Phi b * t X) P := j12.add i3
          rw [integral_add i1 j123, integral_add j12 i3, integral_add iT1 i2, integral_const_mul,
            integral_const_mul, integral_const_mul]
  -- Poincaré for `g`
  have hvar : (var P g).toReal ≤ (energy V W N g).toReal / ρ := by
    have h1 := var_mul_lamAll_le hyp hgH
    have h2 : var P g * ENNReal.ofReal ρ ≤ energy V W N g :=
      le_trans (by gcongr) h1
    have hvt : var P g ≠ ⊤ := (evariance_lt_top hgL).ne
    have h3 := ENNReal.toReal_mono (energy_lt_top hyp hgH).ne h2
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hρ.le] at h3
    rw [le_div_iff₀ hρ]; exact h3
  -- Lemma B.1 (iii) and the defective inequality for `t`
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
  rw [hΦ]
  rw [integral_sub_one_sq_eq hgL] at hI
  nlinarith [hvar, hT1, hI, Real.log_pos hb]

/-- **The vanishing case is impossible.** -/
theorem vanishing_contra_all (hyp : Hyp V W KV KW) (hB1 : TruncationConclusion) {r r₀ ρ : ℝ}
    (hr : 0 < r) (hrρ : r < ρ) (hρr₀ : ρ ≤ r₀) {B : NNReal}
    (hdef : ∀ N, 1 ≤ N → ∀ u : Config N d → ℝ, MemH1C (gibbs V W N) u →
      ent (gibbs V W N) (fun X => u X ^ 2) ≤ ENNReal.ofReal (2 / r₀) * energy V W N u +
        (B : ℝ≥0∞) * ∫⁻ X, ENNReal.ofReal (u X ^ 2) ∂gibbs V W N)
    {Ns : ℕ → ℕ} (hNs1 : ∀ k, 1 ≤ Ns k)
    (hlam : ∀ᶠ k in atTop, ENNReal.ofReal ρ ≤ lamAll V W (Ns k))
    {f : (k : ℕ) → Config (Ns k) d → ℝ} (hmem : ∀ k, MemH1C (gibbs V W (Ns k)) (f k))
    (hf0 : ∀ k X, 0 ≤ f k X)
    (hnorm : ∀ k, ∫ X, f k X ^ 2 ∂gibbs V W (Ns k) = 1)
    (hfin : ∀ k, ent (gibbs V W (Ns k)) (fun X => f k X ^ 2) ≠ ⊤)
    (hviol : ∀ k, 2 * (energy V W (Ns k) (f k)).toReal <
      r * (ent (gibbs V W (Ns k)) (fun X => f k X ^ 2)).toReal)
    (hh : Tendsto (fun k => (ent (gibbs V W (Ns k)) (fun X => f k X ^ 2)).toReal) atTop (𝓝 0))
    (hUI : ∀ ε > 0, ∃ M : ℝ, ∀ k, ∫⁻ X in {X | M < ((f k X - 1) /
        Real.sqrt (ent (gibbs V W (Ns k)) (fun X => f k X ^ 2)).toReal) ^ 2},
      ENNReal.ofReal (((f k X - 1) /
        Real.sqrt (ent (gibbs V W (Ns k)) (fun X => f k X ^ 2)).toReal) ^ 2) ∂gibbs V W (Ns k) ≤
        ENNReal.ofReal ε) : False := by
  set ρ₁ := (r + ρ) / 2 with hρ₁
  have hρ₁0 : 0 < ρ₁ := by rw [hρ₁]; linarith
  have hrρ₁ : r < ρ₁ := by rw [hρ₁]; linarith
  have hρ₁ρ : ρ₁ < ρ := by rw [hρ₁]; linarith
  set b := Real.exp (ρ / ρ₁ - 1) with hbdef
  have hlogb : Real.log b = ρ / ρ₁ - 1 := by rw [hbdef, Real.log_exp]
  have hb : 1 < b := by
    rw [hbdef]; apply Real.one_lt_exp_iff.mpr
    rw [sub_pos, one_lt_div hρ₁0]; exact hρ₁ρ
  have hb1 : 0 < b - 1 := by linarith
  set δ := (1 - r / ρ₁) / 2 with hδ
  have hδ0 : 0 < δ := by
    rw [hδ]; have : r / ρ₁ < 1 := (div_lt_one hρ₁0).mpr hrρ₁
    linarith
  set K := 2 * (1 + Real.log b) + (B + 2 * (1 + Real.log (b + 1))) +
    |deriv Phi b| / (b - 1) + 1 with hK
  have hK0 : 0 < K := by
    have : 0 < 1 + Real.log b := by rw [hlogb]; have := (one_lt_div hρ₁0).mpr hρ₁ρ; linarith
    have : 0 ≤ 1 + Real.log (b + 1) := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ b + 1); linarith
    have : 0 ≤ |deriv Phi b| / (b - 1) := div_nonneg (abs_nonneg _) hb1.le
    have : (0 : ℝ) ≤ B := B.2
    rw [hK]; linarith
  set ε := min (δ / K) 1 with hε
  have hε0 : 0 < ε := lt_min (div_pos hδ0 hK0) one_pos
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hεK : K * ε ≤ δ := by
    calc K * ε ≤ K * (δ / K) := mul_le_mul_of_nonneg_left (min_le_left _ _) hK0.le
      _ = δ := by field_simp
  obtain ⟨M, hM⟩ := hUI ε hε0
  set A := 1 / 2 + ε / (b - 1) with hA
  have hA0 : 0 < A := by positivity
  set η := min (min ((b - 1) ^ 2 / (|M| + 1)) (Real.exp (-1))) (ε / (A ^ 2 + 1)) with hη
  have hη0 : 0 < η := lt_min (lt_min (by positivity) (Real.exp_pos _)) (by positivity)
  obtain ⟨k, hk1, hk2⟩ := (hlam.and ((tendsto_order.mp hh).2 η hη0)).exists
  -- the data at `k`
  set P := gibbs V W (Ns k)
  have : IsProbabilityMeasure P := gibbs_isProbabilityMeasure hyp (Ns k)
  set h := (ent P (fun X => f k X ^ 2)).toReal with hhdef
  set E := (energy V W (Ns k) (f k)).toReal with hEdef
  have hE0 : 0 ≤ E := ENNReal.toReal_nonneg
  have hpos : 0 < h := by have := hviol k; nlinarith
  have hhη : h < η := hk2
  have hfL := memLp_of_memH1C hyp (hmem k)
  have hMh : M * h ≤ (b - 1) ^ 2 := by
    have h1 : h ≤ (b - 1) ^ 2 / (|M| + 1) := le_trans hhη.le (le_trans (min_le_left _ _)
      (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [le_abs_self M, abs_nonneg M]
  obtain ⟨hc, ht⟩ := tail_bounds hyp (hf0 k) hfL hpos hb hε0.le hMh (hM k)
  have hhe : h ≤ Real.exp (-1) := le_trans hhη.le (le_trans (min_le_left _ _) (min_le_right _ _))
  have hc1 : ∫ X, max (f k X - b) 0 ^ 2 ∂P ≤ Real.exp (-1) := by nlinarith
  have hkey := vanishing_key_ineq_all hyp hB1 (by linarith : 0 < r₀) (hdef (Ns k) (hNs1 k)) (hmem k)
    (hf0 k) (hnorm k) (hfin k) hb (by linarith : 0 < ρ) hk1 hc1
  -- energy split
  have hsplit := energy_eq_min_add_posPart hyp (hmem k) b
  have hEg := energy_lt_top hyp (memH1C_min hyp (hmem k) b)
  have hEt := energy_lt_top hyp (memH1C_posPart_sub hyp (hmem k) b)
  have hsplitR : E = (energy V W (Ns k) (fun X => min (f k X) b)).toReal +
      (energy V W (Ns k) (fun X => max (f k X - b) 0)).toReal := by
    rw [hEdef, hsplit, ENNReal.toReal_add hEg.ne hEt.ne]
  set Eg := (energy V W (Ns k) (fun X => min (f k X) b)).toReal
  set Et := (energy V W (Ns k) (fun X => max (f k X - b) 0)).toReal
  have hEt0 : 0 ≤ Et := ENNReal.toReal_nonneg
  have hEg0 : 0 ≤ Eg := ENNReal.toReal_nonneg
  -- the mean of `g`
  have hti : Integrable (fun X => max (f k X - b) 0) P :=
    ((hfL.sub (memLp_const b)).sup (memLp_const 0)).integrable one_le_two
  have hgmean : ∫ X, min (f k X) b ∂P - 1 =
      -(1 / 2) * ∫ X, (f k X - 1) ^ 2 ∂P - ∫ X, max (f k X - b) 0 ∂P := by
    have e : (fun X => min (f k X) b) = fun X => f k X - max (f k X - b) 0 := by
      funext X; rcases le_total (f k X) b with h' | h'
      · rw [min_eq_left h', max_eq_right (by linarith)]; ring
      · rw [min_eq_right h', max_eq_left (by linarith)]; ring
    rw [e, integral_sub (hfL.integrable one_le_two) hti]
    have := integral_sub_one_sq_of_norm hfL (hnorm k)
    linarith
  have hsq := integral_sub_one_sq_le_ent (hf0 k) hfL (hnorm k) (hfin k)
  have hsq0 : 0 ≤ ∫ X, (f k X - 1) ^ 2 ∂P := integral_nonneg fun X => sq_nonneg _
  have ht0 : 0 ≤ ∫ X, max (f k X - b) 0 ∂P := integral_nonneg fun X => le_max_right _ _
  have hgm : (∫ X, min (f k X) b ∂P - 1) ^ 2 ≤ ε * h := by
    have habs : |∫ X, min (f k X) b ∂P - 1| ≤ h * A := by
      rw [hgmean, abs_le]
      constructor
      · have h2 : ∫ X, max (f k X - b) 0 ∂P ≤ h * (ε / (b - 1)) := by
          calc _ ≤ h / (b - 1) * ε := ht
            _ = h * (ε / (b - 1)) := by ring
        rw [hA, mul_add]
        linarith only [h2, hsq, hsq0]
      · have : 0 ≤ h * A := mul_nonneg hpos.le hA0.le
        linarith only [this, hsq0, ht0]
    have hhA : h * A ^ 2 ≤ ε := by
      have h1 : h ≤ ε / (A ^ 2 + 1) := le_trans hhη.le (min_le_right _ _)
      rw [le_div_iff₀ (by positivity), mul_add, mul_one] at h1
      linarith only [h1, hpos]
    calc (∫ X, min (f k X) b ∂P - 1) ^ 2 = |∫ X, min (f k X) b ∂P - 1| ^ 2 := (sq_abs _).symm
      _ ≤ (h * A) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = h * (h * A ^ 2) := by ring
      _ ≤ h * ε := mul_le_mul_of_nonneg_left hhA hpos.le
      _ = ε * h := by ring
  -- assemble
  have hρ0 : ρ ≠ 0 := by linarith
  have h1b : 2 * (1 + Real.log b) / ρ = 2 / ρ₁ := by
    rw [hlogb]; field_simp; ring
  have hEt' : 2 / r₀ * Et ≤ 2 / ρ₁ * Et := by
    apply mul_le_mul_of_nonneg_right _ hEt0
    exact div_le_div_of_nonneg_left (by norm_num) hρ₁0 (by linarith)
  have hderiv : deriv Phi b * ∫ X, max (f k X - b) 0 ∂P ≤ |deriv Phi b| / (b - 1) * (ε * h) := by
    calc deriv Phi b * ∫ X, max (f k X - b) 0 ∂P ≤ |deriv Phi b| * ∫ X, max (f k X - b) 0 ∂P :=
          mul_le_mul_of_nonneg_right (le_abs_self _) ht0
      _ ≤ |deriv Phi b| * (h / (b - 1) * ε) := mul_le_mul_of_nonneg_left ht (abs_nonneg _)
      _ = |deriv Phi b| / (b - 1) * (ε * h) := by field_simp
  have hlb : 0 ≤ 1 + Real.log b := by rw [hlogb]; have := (one_lt_div hρ₁0).mpr hρ₁ρ; linarith
  have hlb1 : 0 ≤ 1 + Real.log (b + 1) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ b + 1); linarith
  have hcε : ∫ X, max (f k X - b) 0 ^ 2 ∂P ≤ ε * h := by linarith
  have hB0 : (0 : ℝ) ≤ B := B.2
  have hmain : h ≤ 2 / ρ₁ * E + K * ε * h := by
    have e1 : 2 * (1 + Real.log b) * (Eg / ρ + (∫ X, min (f k X) b ∂P - 1) ^ 2) =
        2 / ρ₁ * Eg + 2 * (1 + Real.log b) * (∫ X, min (f k X) b ∂P - 1) ^ 2 := by
      rw [mul_add, ← h1b]; field_simp
    have e2 := mul_le_mul_of_nonneg_left hgm (by linarith : 0 ≤ 2 * (1 + Real.log b))
    have e3 := mul_le_mul_of_nonneg_left hcε (by linarith : 0 ≤ (B : ℝ) + 2 * (1 + Real.log (b + 1)))
    rw [e1] at hkey
    have hεh : 0 ≤ ε * h := mul_nonneg hε0.le hpos.le
    rw [hsplitR, hK]
    linarith [hkey, e2, e3, hderiv, hEt', hεh]
  have hfinal : h ≤ 2 / ρ₁ * E + δ * h := by
    have := mul_le_mul_of_nonneg_right hεK hpos.le
    linarith
  have hEr : 2 / ρ₁ * E < r / ρ₁ * h := by
    have := hviol k
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_div_iff_of_pos_right hρ₁0]
    linarith
  have hq : r / ρ₁ * h < h := by
    have := mul_lt_mul_of_pos_right ((div_lt_one hρ₁0).mpr hrρ₁) hpos
    linarith
  have : r / ρ₁ * h + δ * h < h := by
    rw [hδ]; linarith
  linarith


end SharpLSI.FL
