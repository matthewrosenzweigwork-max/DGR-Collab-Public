import Mathlib
import SharpSymmetricLSI.Infra.Entropy

/-!
# The centering inequality (Phase 3, lane C; Lemma `lem:cosine-centering`)

For a probability measure `P` and `f ∈ L²(P)`:
`Ent_P(f²) ≤ 2 Ent_P((f - E f)²) + 8 Var_P(f)`.
Both steps are pointwise inequalities for the normalized integrands `M klFun(·/M)`:
the two-point bound `½(θ(u₊)+θ(u₋)) ≤ θ(g²+c²) + 4g²` (`θ(s) = s log s`), and the log-sum
inequality `(s+b) log((s+b)/(V+b)) ≤ s log(s/V)`.
-/

open MeasureTheory InformationTheory Set Filter

namespace SharpLSI

/-- `M klFun(x/M) = x log x - x log M - x + M` for `M > 0`, `x ≥ 0`. -/
theorem mul_klFun_div {M x : ℝ} (hM : 0 < M) (hx : 0 ≤ x) :
    M * klFun (x / M) = x * Real.log x - x * Real.log M - x + M := by
  rw [klFun_apply]
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  · rw [Real.log_div h.ne' hM.ne']; field_simp; ring

/-- The two-point inequality. -/
theorem two_point (g c : ℝ) :
    ((g + c) ^ 2 * Real.log ((g + c) ^ 2) + (g - c) ^ 2 * Real.log ((g - c) ^ 2)) / 2 ≤
      (g ^ 2 + c ^ 2) * Real.log (g ^ 2 + c ^ 2) + 4 * g ^ 2 := by
  set s := (g + c) ^ 2
  set t := (g - c) ^ 2
  set Q := g ^ 2 + c ^ 2
  have hQ : Q = (s + t) / 2 := by simp only [s, t, Q]; ring
  rcases (show 0 ≤ Q by positivity).eq_or_lt with hQ0 | hQ0
  · have hg : g = 0 := by nlinarith [sq_nonneg g, sq_nonneg c]
    have hc : c = 0 := by nlinarith [sq_nonneg g, sq_nonneg c]
    simp [s, t, Q, hg, hc]
  have key : ∀ x, 0 ≤ x → x * Real.log x - x * Real.log Q ≤ x * (x / Q - 1) := fun x hx => by
    rcases hx.eq_or_lt with h | h
    · subst h; simp
    · rw [← mul_sub, ← Real.log_div h.ne' hQ0.ne']
      exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos h hQ0)) h.le
  have h1 := key s (sq_nonneg _)
  have h2 := key t (sq_nonneg _)
  have hst : (s - t) ^ 2 = 16 * c ^ 2 * g ^ 2 := by simp only [s, t]; ring
  have h3 : s * (s / Q - 1) + t * (t / Q - 1) = (s - t) ^ 2 / (2 * Q) := by
    have hQne : Q ≠ 0 := hQ0.ne'
    field_simp
    rw [hQ]; ring
  have h4 : (s - t) ^ 2 / (2 * Q) ≤ 8 * g ^ 2 := by
    rw [hst, div_le_iff₀ (by positivity)]
    simp only [Q]; nlinarith [sq_nonneg g, sq_nonneg c, mul_nonneg (sq_nonneg g) (sq_nonneg g)]
  have h5 : s * Real.log Q + t * Real.log Q = 2 * (Q * Real.log Q) := by rw [hQ]; ring
  linarith

/-- The log-sum inequality `(s+b) log((s+b)/(V+b)) ≤ s log(s/V)`. -/
theorem log_sum_le {s V b : ℝ} (hs : 0 ≤ s) (hV : 0 < V) (hb : 0 ≤ b) :
    (s + b) * Real.log ((s + b) / (V + b)) ≤ s * Real.log (s / V) := by
  have hVb : 0 < V + b := by linarith
  have hconv := Real.convexOn_mul_log.2 (mem_Ici.mpr (div_nonneg hs hV.le))
    (mem_Ici.mpr zero_le_one) (div_nonneg hV.le hVb.le) (div_nonneg hb hVb.le)
    (by field_simp)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hconv
  have e : V / (V + b) * (s / V) + b / (V + b) * 1 = (s + b) / (V + b) := by field_simp
  rw [e] at hconv
  have := mul_le_mul_of_nonneg_left hconv hVb.le
  have e2 : (V + b) * ((s + b) / (V + b) * Real.log ((s + b) / (V + b))) =
      (s + b) * Real.log ((s + b) / (V + b)) := by field_simp
  have e3 : (V + b) * (V / (V + b) * (s / V * Real.log (s / V))) = s * Real.log (s / V) := by
    field_simp
  rw [e2, e3] at this
  exact this

/-- **Centering**: `Ent_P(f²) ≤ 2 Ent_P((f - E f)²) + 8 Var_P(f)`. -/
theorem ent_centering {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    {f : α → ℝ} (hf : MemLp f 2 P) :
    ent P (fun x => f x ^ 2) ≤ 2 * ent P (fun x => (f x - ∫ y, f y ∂P) ^ 2) + 8 * var P f := by
  set c := ∫ y, f y ∂P with hc
  have hg : MemLp (fun x => f x - c) 2 P := hf.sub (memLp_const c)
  set V := ∫ x, (f x - c) ^ 2 ∂P with hV
  set M := ∫ x, f x ^ 2 ∂P with hMdef
  have hfi : Integrable f P := hf.integrable one_le_two
  have hM : M = V + c ^ 2 := by
    have e : ∀ x, f x ^ 2 = (f x - c) ^ 2 + 2 * c * (f x - c) + c ^ 2 := fun x => by ring
    simp_rw [hMdef, e]
    have i1 : Integrable (fun x => 2 * c * (f x - c)) P := (hfi.sub (integrable_const c)).const_mul _
    have i2 : Integrable (fun x => (f x - c) ^ 2 + 2 * c * (f x - c)) P := hg.integrable_sq.add i1
    rw [integral_add (f := fun x => (f x - c) ^ 2 + 2 * c * (f x - c)) (g := fun _ => c ^ 2) i2
      (integrable_const _), integral_add (f := fun x => (f x - c) ^ 2)
      (g := fun x => 2 * c * (f x - c)) hg.integrable_sq i1, integral_const_mul,
      integral_sub (f := f) (g := fun _ => c) hfi (integrable_const c)]
    simp [← hc]
    rfl
  have hV0 : 0 ≤ V := integral_nonneg fun x => sq_nonneg _
  have hvar : var P f = ∫⁻ x, ENNReal.ofReal ((f x - c) ^ 2) ∂P := by
    unfold var ProbabilityTheory.evariance
    congr 1; funext x
    rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
  unfold ent
  rw [if_pos hf.integrable_sq, if_pos hg.integrable_sq, hvar]
  beta_reduce
  rw [← hMdef, ← hV]
  rcases (show 0 ≤ M from integral_nonneg fun x => sq_nonneg _).eq_or_lt with hM0 | hMpos
  · rw [← hM0]; simp
  -- pointwise
  have hA : ∀ x, M * klFun (f x ^ 2 / M) + M * klFun ((f x - c - c) ^ 2 / M) ≤
      2 * (M * klFun (((f x - c) ^ 2 + c ^ 2) / M)) + 8 * (f x - c) ^ 2 := fun x => by
    have h2 := two_point (f x - c) c
    rw [mul_klFun_div hMpos (sq_nonneg _), mul_klFun_div hMpos (sq_nonneg _),
      mul_klFun_div hMpos (by positivity)]
    rw [show f x - c + c = f x by ring] at h2
    nlinarith
  have hB : ∀ᵐ x ∂P, M * klFun (((f x - c) ^ 2 + c ^ 2) / M) ≤ V * klFun ((f x - c) ^ 2 / V) := by
    rcases hV0.eq_or_lt with hV0' | hVpos
    · have hz : (fun x => (f x - c) ^ 2) =ᵐ[P] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hg.integrable_sq).mp hV0'.symm
      filter_upwards [hz] with x hx
      simp only [Pi.zero_apply] at hx
      rw [hx, zero_add, ← hV0', zero_mul, show c ^ 2 = M by rw [hM, ← hV0', zero_add],
        div_self hMpos.ne', klFun_one, mul_zero]
    · refine Eventually.of_forall fun x => ?_
      have hl := log_sum_le (sq_nonneg (f x - c)) hVpos (sq_nonneg c)
      rw [← hM] at hl
      simp only [klFun_apply]
      have e1 : M * (((f x - c) ^ 2 + c ^ 2) / M * Real.log (((f x - c) ^ 2 + c ^ 2) / M) + 1 -
          ((f x - c) ^ 2 + c ^ 2) / M) = ((f x - c) ^ 2 + c ^ 2) *
            Real.log (((f x - c) ^ 2 + c ^ 2) / M) + M - ((f x - c) ^ 2 + c ^ 2) := by
        field_simp
      have e2 : V * ((f x - c) ^ 2 / V * Real.log ((f x - c) ^ 2 / V) + 1 - (f x - c) ^ 2 / V) =
          (f x - c) ^ 2 * Real.log ((f x - c) ^ 2 / V) + V - (f x - c) ^ 2 := by
        field_simp
      rw [e1, e2]
      linarith
  have hpt : ∀ᵐ x ∂P, M * klFun (f x ^ 2 / M) ≤
      2 * (V * klFun ((f x - c) ^ 2 / V)) + 8 * (f x - c) ^ 2 := by
    filter_upwards [hB] with x hx
    have h0 : 0 ≤ M * klFun ((f x - c - c) ^ 2 / M) :=
      mul_nonneg hMpos.le (klFun_nonneg (div_nonneg (sq_nonneg _) hMpos.le))
    linarith [hA x]
  calc ∫⁻ x, ENNReal.ofReal (M * klFun (f x ^ 2 / M)) ∂P
      ≤ ∫⁻ x, (2 * ENNReal.ofReal (V * klFun ((f x - c) ^ 2 / V)) +
          8 * ENNReal.ofReal ((f x - c) ^ 2)) ∂P := by
        refine lintegral_mono_ae (hpt.mono fun x hx => ?_)
        have hn1 : 0 ≤ V * klFun ((f x - c) ^ 2 / V) :=
          mul_nonneg hV0 (klFun_nonneg (div_nonneg (sq_nonneg _) hV0))
        calc ENNReal.ofReal (M * klFun (f x ^ 2 / M))
            ≤ ENNReal.ofReal (2 * (V * klFun ((f x - c) ^ 2 / V)) + 8 * (f x - c) ^ 2) :=
              ENNReal.ofReal_le_ofReal hx
          _ = _ := by
              rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) hn1) (by positivity),
                ENNReal.ofReal_mul (p := 2) (by norm_num),
                ENNReal.ofReal_mul (p := 8) (by norm_num)]
              norm_num
    _ = 2 * ∫⁻ x, ENNReal.ofReal (V * klFun ((f x - c) ^ 2 / V)) ∂P +
          8 * ∫⁻ x, ENNReal.ofReal ((f x - c) ^ 2) ∂P := by
        rw [lintegral_add_left' (f := fun x => 2 * ENNReal.ofReal (V * klFun ((f x - c) ^ 2 / V)))
          ((ENNReal.measurable_ofReal.comp_aemeasurable
          ((continuous_const.mul continuous_klFun).comp_aestronglyMeasurable
            (hg.integrable_sq.div_const V).aestronglyMeasurable).aemeasurable).const_mul 2),
          lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]

end SharpLSI
