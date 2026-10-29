import SharpSymmetricLSI.Infra.CZTorus1

/-!
# Directional Hilbert transforms on `𝕋^ι`: Cotlar's identity (R23 lane, CZ part 2)

For `ω ∈ ℝ^ι` generic (`k·ω ≠ 0` for `k ≠ 0`), `H_ω` is the multiplier `-i sgn(k·ω)`.
The half-spaces `{±k·ω > 0}` are closed under addition, so for mean-zero `c = c₊ + c₋`
(`H c₊ = -i c₊`, `H c₋ = i c₋`, and the same for `c₊²`, `c₋²`) one gets **Cotlar's identity**
`(H c)² = c² + 2 H(c · H c)` in `ℂ[ℤ^ι]`. With Hölder this gives, by induction on `m`,
`‖H_ω f‖_{2^{m+1}} ≤ C_m ‖f‖_{2^{m+1}}` with `C_m` independent of `ω` (`hilb_bound`).
-/

open MeasureTheory Complex
open scoped ENNReal ComplexConjugate
open UnitAddTorus

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `k · ω`. -/
def kdot (k : ι → ℤ) (ω : ι → ℝ) : ℝ := ∑ i, (k i : ℝ) * ω i

theorem kdot_add (k l : ι → ℤ) (ω : ι → ℝ) : kdot (k + l) ω = kdot k ω + kdot l ω := by
  simp only [kdot, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

@[simp] theorem kdot_zero (ω : ι → ℝ) : kdot (0 : ι → ℤ) ω = 0 := by simp [kdot]

/-- The sign function. -/
noncomputable def sgnR (t : ℝ) : ℝ := if 0 < t then 1 else if t < 0 then -1 else 0

/-- `ω` is generic: no nonzero lattice point is orthogonal to it. -/
def Generic (ω : ι → ℝ) : Prop := ∀ k : ι → ℤ, k ≠ 0 → kdot k ω ≠ 0

/-- The symbol `-i sgn(k·ω)` of the directional Hilbert transform. -/
noncomputable def hilbSym (ω : ι → ℝ) (k : ι → ℤ) : ℂ := -I * (sgnR (kdot k ω) : ℂ)

/-- The directional Hilbert transform `H_ω` on trigonometric polynomials. -/
noncomputable def hilb (ω : ι → ℝ) : TP ι →ₗ[ℂ] TP ι := mult (hilbSym ω)

theorem norm_hilbSym_le (ω : ι → ℝ) (k : ι → ℤ) : ‖hilbSym ω k‖ ≤ 1 := by
  unfold hilbSym sgnR
  split_ifs <;> simp

@[simp] theorem hilbSym_zero (ω : ι → ℝ) : hilbSym ω 0 = 0 := by
  simp [hilbSym, sgnR]

/-! ### The half-space decomposition -/

/-- The part of `c` with frequencies in `{k·ω > 0}`. -/
noncomputable def posPart (ω : ι → ℝ) (c : TP ι) : TP ι :=
  AddMonoidAlgebra.ofCoeff (c.coeff.filter fun k => 0 < kdot k ω)

/-- The part of `c` with frequencies in `{k·ω < 0}`. -/
noncomputable def negPart (ω : ι → ℝ) (c : TP ι) : TP ι :=
  AddMonoidAlgebra.ofCoeff (c.coeff.filter fun k => kdot k ω < 0)

theorem decomp {ω : ι → ℝ} (hω : Generic ω) {c : TP ι} (hc : c.coeff 0 = 0) :
    c = posPart ω c + negPart ω c := by
  apply AddMonoidAlgebra.coeff_injective
  ext k
  simp only [posPart, negPart, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_ofCoeff,
    Finsupp.add_apply, Finsupp.filter_apply]
  by_cases hk : k = 0
  · subst hk; simp [hc]
  · rcases lt_trichotomy (kdot k ω) 0 with h | h | h
    · simp [h, not_lt.mpr h.le]
    · exact absurd h (hω k hk)
    · simp [h, not_lt.mpr h.le]

theorem support_posPart (ω : ι → ℝ) (c : TP ι) :
    ∀ k ∈ (posPart ω c).coeff.support, 0 < kdot k ω := by
  intro k hk
  simp only [posPart, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.mem_support_iff,
    Finsupp.filter_apply, ne_eq, ite_eq_right_iff, Classical.not_imp] at hk
  exact hk.1

theorem support_negPart (ω : ι → ℝ) (c : TP ι) :
    ∀ k ∈ (negPart ω c).coeff.support, kdot k ω < 0 := by
  intro k hk
  simp only [negPart, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.mem_support_iff,
    Finsupp.filter_apply, ne_eq, ite_eq_right_iff, Classical.not_imp] at hk
  exact hk.1

theorem support_mul_of {ω : ι → ℝ} {P : ℝ → Prop} (hP : ∀ s t, P s → P t → P (s + t))
    {a b : TP ι} (ha : ∀ k ∈ a.coeff.support, P (kdot k ω))
    (hb : ∀ k ∈ b.coeff.support, P (kdot k ω)) :
    ∀ k ∈ (a * b).coeff.support, P (kdot k ω) := by
  intro k hk
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset a b hk)
  rw [kdot_add]
  exact hP _ _ (ha k₁ hk₁) (hb k₂ hk₂)

theorem hilb_of_pos {ω : ι → ℝ} {a : TP ι} (ha : ∀ k ∈ a.coeff.support, 0 < kdot k ω) :
    hilb ω a = (-I) • a :=
  mult_eq_smul_of_support fun k hk => by simp [hilbSym, sgnR, ha k hk]

theorem hilb_of_neg {ω : ι → ℝ} {a : TP ι} (ha : ∀ k ∈ a.coeff.support, kdot k ω < 0) :
    hilb ω a = I • a :=
  mult_eq_smul_of_support fun k hk => by
    simp [hilbSym, sgnR, ha k hk, not_lt.mpr (ha k hk).le]

/-- **Cotlar's identity** in `ℂ[ℤ^ι]`. -/
theorem cotlar {ω : ι → ℝ} (hω : Generic ω) {c : TP ι} (hc : c.coeff 0 = 0) :
    hilb ω c * hilb ω c = c * c + (2 : ℂ) • hilb ω (c * hilb ω c) := by
  set a := posPart ω c
  set b := negPart ω c
  have hab := decomp hω hc
  have hpa := support_posPart ω c
  have hnb := support_negPart ω c
  have hpaa : ∀ k ∈ (a * a).coeff.support, 0 < kdot k ω :=
    support_mul_of (P := fun x => 0 < x) (fun s t hs ht => add_pos hs ht) hpa hpa
  have hnbb : ∀ k ∈ (b * b).coeff.support, kdot k ω < 0 :=
    support_mul_of (P := fun x => x < 0) (fun s t hs ht => add_neg hs ht) hnb hnb
  have hHc : hilb ω c = (-I) • a + I • b := by
    conv_lhs => rw [hab]
    rw [map_add, hilb_of_pos hpa, hilb_of_neg hnb]
  have hcHc : c * hilb ω c = (-I) • (a * a) + I • (b * b) := by
    rw [hHc]
    conv_lhs => rw [hab]
    simp only [Algebra.smul_def, map_neg]
    ring
  have hHcHc : hilb ω (c * hilb ω c) = -(a * a) - b * b := by
    rw [hcHc, map_add, map_smul, map_smul, hilb_of_pos hpaa, hilb_of_neg hnbb, smul_smul,
      smul_smul]
    have h1 : (-I * -I : ℂ) = -1 := by rw [neg_mul_neg, I_mul_I]
    rw [h1, I_mul_I, neg_one_smul, neg_one_smul]
    abel
  rw [hHcHc, hHc]
  conv_rhs => rw [hab]
  have hJ : (algebraMap ℂ (TP ι) I) * (algebraMap ℂ (TP ι) I) = -1 := by
    rw [← map_mul, I_mul_I, map_neg, map_one]
  simp only [Algebra.smul_def, map_neg, map_ofNat]
  linear_combination (b * b - 2 * a * b + a * a) * hJ

/-! ### Norms -/

/-- Real-valued `L^p` norm on `𝕋^ι`. -/
noncomputable def nr (p : ℝ≥0∞) (f : UnitAddTorus ι → ℂ) : ℝ := (eLpNorm f p volume).toReal

theorem nr_nonneg (p : ℝ≥0∞) (f : UnitAddTorus ι → ℂ) : 0 ≤ nr p f := ENNReal.toReal_nonneg

theorem eLpNorm_synth_ne_top (c : TP ι) (p : ℝ≥0∞) : eLpNorm (synth c) p volume ≠ ⊤ :=
  (memLp_synth c p).eLpNorm_ne_top

theorem nr_add_le {p : ℝ≥0∞} (hp : 1 ≤ p) (a b : TP ι) :
    nr p (synth a + synth b) ≤ nr p (synth a) + nr p (synth b) := by
  unfold nr
  rw [← ENNReal.toReal_add (eLpNorm_synth_ne_top a p) (eLpNorm_synth_ne_top b p)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨eLpNorm_synth_ne_top a p,
    eLpNorm_synth_ne_top b p⟩) (eLpNorm_add_le hp)

theorem nr_smul (p : ℝ≥0∞) (z : ℂ) (f : UnitAddTorus ι → ℂ) : nr p (z • f) = ‖z‖ * nr p f := by
  unfold nr
  rw [eLpNorm_const_smul, ENNReal.toReal_mul]
  simp

theorem nr_mul_self {p : ℝ≥0∞} (c : TP ι) :
    nr p (synth c * synth c) = nr (p * 2) (synth c) ^ 2 := by
  unfold nr
  have hf := (continuous_synth c).aestronglyMeasurable (μ := (volume : Measure (UnitAddTorus ι)))
  have h1 : eLpNorm (synth c * synth c) p volume =
      eLpNorm (fun x => ‖synth c x‖ ^ (2 : ℝ)) p volume := by
    refine eLpNorm_congr_norm_ae ((continuous_synth c).mul (continuous_synth c)).aestronglyMeasurable
      ((continuous_synth c).norm.rpow_const fun _ => Or.inr zero_le_two).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply, norm_mul, Real.rpow_two, Real.norm_eq_abs, abs_pow, abs_norm]
    ring
  rw [h1, eLpNorm_norm_rpow _ hf (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat,
    ← ENNReal.toReal_rpow, Real.rpow_two]

instance holderTriple_two_mul (p : ℝ≥0∞) : ENNReal.HolderTriple (p * 2) (p * 2) p where
  inv_add_inv_eq_inv := by
    rcases eq_or_ne p 0 with rfl | hp0
    · simp
    rcases eq_or_ne p ⊤ with rfl | hpt
    · simp
    rw [ENNReal.mul_inv (Or.inl hp0) (Or.inl hpt), ← two_mul, ← mul_assoc, mul_comm 2,
      mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

theorem nr_mul_le (p : ℝ≥0∞) (a b : TP ι) :
    nr p (synth a * synth b) ≤ nr (p * 2) (synth a) * nr (p * 2) (synth b) := by
  unfold nr
  rw [← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (eLpNorm_synth_ne_top a _)
    (eLpNorm_synth_ne_top b _)) ?_
  have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (μ := (volume : Measure (UnitAddTorus ι)))
    (p := p * 2) (q := p * 2) (r := p) (fun x y : ℂ => x * y) 1 continuous_mul
    (continuous_synth a).aestronglyMeasurable (continuous_synth b).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simp [norm_mul])
  exact (by simpa using this : eLpNorm (fun x => synth a x * synth b x) p volume ≤ _)

theorem norm_coeff_zero_le {p : ℝ≥0∞} (hp : 1 ≤ p) (c : TP ι) :
    ‖c.coeff 0‖ ≤ nr p (synth c) := by
  rw [← integral_synth]
  unfold nr
  have h1 : ‖∫ x, synth c x‖ ≤ (eLpNorm (synth c) 1 volume).toReal := by
    have hf : AEStronglyMeasurable (synth c) (volume : Measure (UnitAddTorus ι)) :=
      (continuous_synth c).aestronglyMeasurable
    calc ‖∫ x, synth c x‖ ≤ ∫ x, ‖synth c x‖ := norm_integral_le_integral_norm _
      _ = (∫⁻ x, ‖synth c x‖ₑ).toReal := integral_norm_eq_lintegral_enorm hf
      _ = _ := by rw [eLpNorm_one_eq_lintegral_enorm hf]
  exact h1.trans (ENNReal.toReal_mono (eLpNorm_synth_ne_top c p)
    (eLpNorm_le_eLpNorm_of_exponent_le hp))

theorem synth_single_zero (z : ℂ) : synth (AddMonoidAlgebra.single (0 : ι → ℤ) z) = fun _ => z := by
  funext x
  rw [synth, AddMonoidAlgebra.lift_single]
  simp [charHom, mFourier_zero]

theorem nr_const (p : ℝ≥0∞) (hp : p ≠ 0) (z : ℂ) : nr p (fun _ : UnitAddTorus ι => z) = ‖z‖ := by
  unfold nr
  rw [eLpNorm_const _ hp (NeZero.ne _)]
  simp

/-- Scalar step of the induction. -/
theorem le_of_sq_le {x a C : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (h : x ^ 2 ≤ a ^ 2 + 2 * C * a * x) : x ≤ (2 * C + 1) * a := by
  by_cases hxa : x ≤ a
  · nlinarith
  · push Not at hxa
    have hx0 : 0 < x := lt_of_le_of_lt ha hxa
    by_contra hc
    push Not at hc
    nlinarith

/-- **`L^{2^{m+1}}` bound for directional Hilbert transforms**, uniform in generic `ω`. -/
theorem hilb_bound (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ω : ι → ℝ, Generic ω → ∀ c : TP ι,
    nr (2 ^ (m + 1)) (synth (hilb ω c)) ≤ C * nr (2 ^ (m + 1)) (synth c) := by
  induction m with
  | zero =>
    refine ⟨1, zero_le_one, fun ω _ c => ?_⟩
    rw [one_mul]
    unfold nr
    simp only [zero_add, pow_one]
    rw [(memLp_synth _ 2).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
      (memLp_synth c 2).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
    refine Real.rpow_le_rpow (integral_nonneg fun _ => by positivity) ?_ (by norm_num)
    simp_rw [Real.rpow_two]
    exact integral_normSq_synth_mult_le (norm_hilbSym_le ω) c
  | succ m ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    refine ⟨2 * (2 * C + 1), by positivity, fun ω hω c => ?_⟩
    set p : ℝ≥0∞ := 2 ^ (m + 1) with hp
    have hp1 : 1 ≤ p := one_le_pow₀ (by norm_num)
    have hp2 : (2 : ℝ≥0∞) ^ (m + 1 + 1) = p * 2 := by rw [hp, pow_succ]
    rw [hp2]
    set c' := c - AddMonoidAlgebra.single (0 : ι → ℤ) (c.coeff 0) with hc'
    have hc'0 : c'.coeff 0 = 0 := by simp [hc', AddMonoidAlgebra.coeff_sub]
    have hHc : hilb ω c' = hilb ω c := by
      rw [hc', map_sub, sub_eq_self]
      apply AddMonoidAlgebra.coeff_injective
      ext k
      simp only [hilb, mult_coeff, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_zero,
        Finsupp.coe_zero, Pi.zero_apply]
      by_cases hk : k = 0
      · subst hk; simp
      · simp [Finsupp.single_apply, Ne.symm hk]
    -- the identity for `c'`
    have hid := congrArg synth (cotlar hω hc'0)
    simp only [map_add, map_mul, map_smul] at hid
    set F := synth c'
    set G := synth (hilb ω c')
    set x := nr (p * 2) G
    set a := nr (p * 2) F
    have hx0 : 0 ≤ x := nr_nonneg _ _
    have ha0 : 0 ≤ a := nr_nonneg _ _
    have key : x ^ 2 ≤ a ^ 2 + 2 * C * a * x := by
      have e1 : x ^ 2 = nr p (G * G) := (nr_mul_self _).symm
      have e2 : nr p (F * F) = a ^ 2 := nr_mul_self _
      have e3 : nr p ((2 : ℂ) • synth (hilb ω (c' * hilb ω c'))) ≤ 2 * (C * (a * x)) := by
        rw [nr_smul]
        simp only [norm_ofNat]
        refine mul_le_mul_of_nonneg_left ((hC ω hω _).trans ?_) (by norm_num)
        refine mul_le_mul_of_nonneg_left ?_ hC0
        rw [map_mul]
        exact nr_mul_le p c' (hilb ω c')
      have e4 : nr p (F * F + (2 : ℂ) • synth (hilb ω (c' * hilb ω c'))) ≤
          nr p (F * F) + nr p ((2 : ℂ) • synth (hilb ω (c' * hilb ω c'))) := by
        have := nr_add_le hp1 (c' * c') ((2 : ℂ) • hilb ω (c' * hilb ω c'))
        simpa only [map_mul, map_smul] using this
      rw [e1, hid]
      nlinarith
    have hxa := le_of_sq_le hx0 ha0 hC0 key
    have hp21 : 1 ≤ p * 2 := hp1.trans (le_mul_of_one_le_right' (by norm_num))
    have haN : a ≤ 2 * nr (p * 2) (synth c) := by
      have h1 : F = synth c + synth (-(AddMonoidAlgebra.single (0 : ι → ℤ) (c.coeff 0))) := by
        rw [← map_add, ← sub_eq_add_neg]
      have h2 := nr_add_le (p := p * 2) hp21 c (-(AddMonoidAlgebra.single (0 : ι → ℤ) (c.coeff 0)))
      have h3 : nr (p * 2) (synth (-(AddMonoidAlgebra.single (0 : ι → ℤ) (c.coeff 0)))) ≤
          nr (p * 2) (synth c) := by
        rw [map_neg, synth_single_zero (ι := ι)]
        have : (-fun _ : UnitAddTorus ι => c.coeff 0) = fun _ => -c.coeff 0 := rfl
        rw [this, nr_const (ι := ι) _ (by positivity) _, norm_neg]
        exact norm_coeff_zero_le hp21 c
      show nr (p * 2) F ≤ _
      rw [h1]; linarith
    show nr (p * 2) (synth (hilb ω c)) ≤ _
    rw [← hHc]
    calc x ≤ (2 * C + 1) * a := hxa
      _ ≤ (2 * C + 1) * (2 * nr (p * 2) (synth c)) :=
          mul_le_mul_of_nonneg_left haN (by positivity)
      _ = 2 * (2 * C + 1) * nr (p * 2) (synth c) := by ring

end SharpLSI
