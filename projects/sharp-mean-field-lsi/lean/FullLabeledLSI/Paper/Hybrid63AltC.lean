import Mathlib

/-!
# Proposition 6.3, step R4b (7.21): a Young-type bound for quadratic forms

For a probability space `(Ω, P)`, a function `f` with a bounded eighth moment, and two families of
random variables `Z i`, `Z' i` (`i ∈ s`) with `Z + Z'` bounded in `L⁴` and `Z - Z'` small in `L²`,
`∫ f² (quad Z - quad Z')` is small, where `quad z = ∑_{i,j ∈ s} Q_{ij} z_i z_j`.
The proof is pointwise Young: `f² |d| |s| ≤ (t/4)(f⁸ + s⁴) + d²/(2t)`.
-/

open MeasureTheory

noncomputable section

namespace SharpLSI.FL

/-- The quadratic form `∑_{i,j ∈ s} Q_{ij} z_i z_j`. -/
def quadFA (s : Finset ℕ) (Q : ℕ → ℕ → ℝ) (z : ℕ → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, Q i j * z i * z j

theorem young_pt_alt (a b c t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (ht : 0 < t) :
    a ^ 2 * b * c ≤ (t / 4) * (a ^ 8 + c ^ 4) + b ^ 2 / (2 * t) := by
  have h1 : (a ^ 2 * c) ^ 2 ≤ (a ^ 8 + c ^ 4) / 2 := by
    nlinarith [sq_nonneg (a ^ 4 - c ^ 2)]
  have h2 : (a ^ 2 * c) * b ≤ (t * (a ^ 2 * c) ^ 2 + b ^ 2 / t) / 2 := by
    have : 0 ≤ (t * (a ^ 2 * c) - b) ^ 2 := sq_nonneg _
    have h3 : 2 * t * ((a ^ 2 * c) * b) ≤ t ^ 2 * (a ^ 2 * c) ^ 2 + b ^ 2 := by nlinarith
    have h4 : (a ^ 2 * c) * b ≤ (t ^ 2 * (a ^ 2 * c) ^ 2 + b ^ 2) / (2 * t) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    calc (a ^ 2 * c) * b ≤ (t ^ 2 * (a ^ 2 * c) ^ 2 + b ^ 2) / (2 * t) := h4
      _ = (t * (a ^ 2 * c) ^ 2 + b ^ 2 / t) / 2 := by field_simp
  calc a ^ 2 * b * c = (a ^ 2 * c) * b := by ring
    _ ≤ (t * (a ^ 2 * c) ^ 2 + b ^ 2 / t) / 2 := h2
    _ ≤ (t * ((a ^ 8 + c ^ 4) / 2) + b ^ 2 / t) / 2 := by gcongr
    _ = (t / 4) * (a ^ 8 + c ^ 4) + b ^ 2 / (2 * t) := by field_simp; ring

section young
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem young_int {f D S : Ω → ℝ} (hf : Measurable f) (hD : Measurable D) (hS : Measurable S)
    (hf8 : Integrable (fun ω => |f ω| ^ 8) P) (hS4 : Integrable (fun ω => |S ω| ^ 4) P)
    (hD2 : Integrable (fun ω => |D ω| ^ 2) P) {M8 M4 κ : ℝ}
    (h8 : ∫ ω, |f ω| ^ 8 ∂P ≤ M8) (h4 : ∫ ω, |S ω| ^ 4 ∂P ≤ M4) (h2 : ∫ ω, |D ω| ^ 2 ∂P ≤ κ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun ω => f ω ^ 2 * (D ω * S ω)) P ∧
      |∫ ω, f ω ^ 2 * (D ω * S ω) ∂P| ≤ (t / 4) * (M8 + M4) + κ / (2 * t) := by
  set g : Ω → ℝ := fun ω => (t / 4) * (|f ω| ^ 8 + |S ω| ^ 4) + |D ω| ^ 2 / (2 * t) with hg
  have hgi : Integrable g P :=
    ((hf8.add hS4).const_mul (t / 4)).add (hD2.div_const (2 * t))
  have hpt : ∀ ω, ‖f ω ^ 2 * (D ω * S ω)‖ ≤ g ω := by
    intro ω
    have := young_pt_alt |f ω| |D ω| |S ω| t (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) ht
    calc ‖f ω ^ 2 * (D ω * S ω)‖ = |f ω| ^ 2 * |D ω| * |S ω| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]; ring
      _ ≤ g ω := this
  have hmeas : Measurable fun ω => f ω ^ 2 * (D ω * S ω) :=
    (hf.pow_const 2).mul (hD.mul hS)
  refine ⟨hgi.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hpt), ?_⟩
  have h := norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall hpt)
  rw [Real.norm_eq_abs] at h
  refine h.trans ?_
  have hI : ∫ ω, g ω ∂P = (t / 4) * (∫ ω, |f ω| ^ 8 ∂P + ∫ ω, |S ω| ^ 4 ∂P) +
      (∫ ω, |D ω| ^ 2 ∂P) / (2 * t) := by
    simp only [hg]
    rw [integral_add (f := fun ω => t / 4 * (|f ω| ^ 8 + |S ω| ^ 4))
      (g := fun ω => |D ω| ^ 2 / (2 * t)) ((hf8.add hS4).const_mul (t / 4)) (hD2.div_const (2 * t)),
      integral_const_mul, integral_add hf8 hS4, integral_div]
  rw [hI]
  have : (t / 4) * (∫ ω, |f ω| ^ 8 ∂P + ∫ ω, |S ω| ^ 4 ∂P) ≤ (t / 4) * (M8 + M4) := by
    gcongr
  have h' : (∫ ω, |D ω| ^ 2 ∂P) / (2 * t) ≤ κ / (2 * t) := by gcongr
  linarith

theorem quad_diff_bound {f : Ω → ℝ} {Z Z' : ℕ → Ω → ℝ} (s : Finset ℕ) (Q : ℕ → ℕ → ℝ)
    (hf : Measurable f) (hZ : ∀ i ∈ s, Measurable (Z i)) (hZ' : ∀ i ∈ s, Measurable (Z' i))
    {M8 M4 κ : ℝ} (hf8 : Integrable (fun ω => |f ω| ^ 8) P) (h8 : ∫ ω, |f ω| ^ 8 ∂P ≤ M8)
    (hS4 : ∀ i ∈ s, Integrable (fun ω => |Z i ω + Z' i ω| ^ 4) P)
    (h4 : ∀ i ∈ s, ∫ ω, |Z i ω + Z' i ω| ^ 4 ∂P ≤ M4)
    (hD2 : ∀ i ∈ s, Integrable (fun ω => |Z i ω - Z' i ω| ^ 2) P)
    (h2 : ∀ i ∈ s, ∫ ω, |Z i ω - Z' i ω| ^ 2 ∂P ≤ κ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun ω => f ω ^ 2 * (quadFA s Q (fun i => Z i ω) - quadFA s Q (fun i => Z' i ω))) P ∧
    |∫ ω, f ω ^ 2 * (quadFA s Q (fun i => Z i ω) - quadFA s Q (fun i => Z' i ω)) ∂P| ≤
      (∑ i ∈ s, ∑ j ∈ s, |Q i j|) * ((t / 4) * (M8 + M4) + κ / (2 * t)) := by
  set T : ℝ := (t / 4) * (M8 + M4) + κ / (2 * t) with hT
  -- the elementary terms
  have key : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun ω => f ω ^ 2 * ((Z i ω - Z' i ω) * (Z j ω + Z' j ω))) P ∧
        |∫ ω, f ω ^ 2 * ((Z i ω - Z' i ω) * (Z j ω + Z' j ω)) ∂P| ≤ T := by
    intro i hi j hj
    exact young_int hf ((hZ i hi).sub (hZ' i hi)) ((hZ j hj).add (hZ' j hj)) hf8 (hS4 j hj)
      (hD2 i hi) h8 (h4 j hj) (h2 i hi) ht
  -- the integrand decomposition
  have hdecomp : ∀ ω, f ω ^ 2 * (quadFA s Q (fun i => Z i ω) - quadFA s Q (fun i => Z' i ω)) =
      ∑ i ∈ s, ∑ j ∈ s, (Q i j / 2) *
        (f ω ^ 2 * ((Z i ω - Z' i ω) * (Z j ω + Z' j ω)) +
          f ω ^ 2 * ((Z j ω - Z' j ω) * (Z i ω + Z' i ω))) := by
    intro ω
    unfold quadFA
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hterm : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun ω => (Q i j / 2) *
        (f ω ^ 2 * ((Z i ω - Z' i ω) * (Z j ω + Z' j ω)) +
          f ω ^ 2 * ((Z j ω - Z' j ω) * (Z i ω + Z' i ω)))) P := by
    intro i hi j hj
    exact ((key i hi j hj).1.add (key j hj i hi).1).const_mul _
  have hint : Integrable (fun ω => f ω ^ 2 *
      (quadFA s Q (fun i => Z i ω) - quadFA s Q (fun i => Z' i ω))) P := by
    simp_rw [hdecomp]
    exact integrable_finsetSum _ fun i hi => integrable_finsetSum _ fun j hj => hterm i hi j hj
  refine ⟨hint, ?_⟩
  simp_rw [hdecomp]
  rw [integral_finsetSum _ fun i hi => integrable_finsetSum _ fun j hj => hterm i hi j hj]
  have hin : ∀ i ∈ s, ∫ ω, ∑ j ∈ s, (Q i j / 2) *
        (f ω ^ 2 * ((Z i ω - Z' i ω) * (Z j ω + Z' j ω)) +
          f ω ^ 2 * ((Z j ω - Z' j ω) * (Z i ω + Z' i ω))) ∂P =
      ∑ j ∈ s, ∫ ω, (Q i j / 2) *
        (f ω ^ 2 * ((Z i ω - Z' i ω) * (Z j ω + Z' j ω)) +
          f ω ^ 2 * ((Z j ω - Z' j ω) * (Z i ω + Z' i ω))) ∂P := fun i hi =>
    integral_finsetSum _ fun j hj => hterm i hi j hj
  rw [Finset.sum_congr rfl hin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [integral_const_mul, integral_add (key i hi j hj).1 (key j hj i hi).1, abs_mul]
  have h1 := (key i hi j hj).2
  have h2 := (key j hj i hi).2
  have hT0 : 0 ≤ T := (abs_nonneg _).trans h1
  have habs : |∫ ω, f ω ^ 2 * ((Z i ω - Z' i ω) * (Z j ω + Z' j ω)) ∂P +
      ∫ ω, f ω ^ 2 * ((Z j ω - Z' j ω) * (Z i ω + Z' i ω)) ∂P| ≤ 2 * T :=
    (abs_add_le _ _).trans (by linarith)
  rw [abs_div, abs_two]
  calc |Q i j| / 2 * |∫ ω, f ω ^ 2 * ((Z i ω - Z' i ω) * (Z j ω + Z' j ω)) ∂P +
      ∫ ω, f ω ^ 2 * ((Z j ω - Z' j ω) * (Z i ω + Z' i ω)) ∂P|
      ≤ |Q i j| / 2 * (2 * T) := by gcongr
    _ = |Q i j| * T := by ring

end young

end SharpLSI.FL

end
