import DGRHS.Decoupling.Prop33TailInduction
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Proposition 3.3 (de la Peña–Montgomery-Smith) as printed: general `k ≥ 2`, Banach values

TeX `prop:decoup`, `source/extracted/DGR_PFunc_Current_20260902_145019_UTC.tex` lines 1095-1104.

For every `k ≥ 2` there is a constant `C_k ≥ 1` depending only on `k` (here `tailConst k`, an
explicit recursion in `k` independent of the space `S` and the Banach space `E`) such that, for
independent, not necessarily identically distributed, coordinates `ξ_1,…,ξ_n` in a measurable
space `S`, `k` independent copies `ξ^{(1)},…,ξ^{(k)}` of the sequence, arbitrary ordered
tuple-dependent measurable kernels `f_{i₁…i_k} : S^k → E` (no symmetry, no centering, no
integrability) with values in a Banach space `E`, every `n ≥ k` and every `t > 0`,

`P(‖∑_{i₁≠…≠i_k} f(ξ^{(1)}_{i₁},…,ξ^{(1)}_{i_k})‖ ≥ t)
   ≤ C_k P(C_k ‖∑_{i₁≠…≠i_k} f(ξ^{(1)}_{i₁},…,ξ^{(k)}_{i_k})‖ ≥ t)`.

## Qualification on the target space (the only difference from the printed statement)
The probability of the event `{‖∑ …‖ ≥ t}` is only meaningful for the Lean proof when that event
is measurable, and in a non-separable Banach space a sum of measurable maps need not be
measurable. The Lean statements therefore assume `[MeasurableAdd₂ E] [OpensMeasurableSpace E]`
(automatic for the Borel σ-algebra of a separable `E`, in particular for every separable Banach
space and every finite-dimensional space). Completeness of `E` is not used, and a complex Banach
space is a real normed space by restriction of scalars.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace DGRHS.Decoupling.Prop33

section Product
variable {S E : Type*} [MeasurableSpace S] [MeasurableSpace E] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [OpensMeasurableSpace E] [MeasurableAdd₂ E]

/-- **Proposition 3.3, tail form, on product laws.** The coordinates have laws
`marginal i` (independent); `Measure.pi marginal` is the law of the sequence and
`Measure.pi (fun _ : Fin k => Measure.pi marginal)` the joint law of `k` independent copies. -/
theorem prop33_banach_tail_product (k : ℕ) (hk : 2 ≤ k) {n : ℕ} (hkn : k ≤ n)
    (marginal : Fin n → Measure S) [∀ i, IsProbabilityMeasure (marginal i)]
    (f : OrderedTuple n k → (Fin k → S) → E) (hf : ∀ a, Measurable (f a))
    {t : ℝ} (ht : 0 < t) :
    Measure.pi marginal
        {x : Fin n → S | t ≤ ‖∑ a : OrderedTuple n k, f a (fun j => x (a.1 j))‖} ≤
      ENNReal.ofReal (tailConst k) *
        Measure.pi (fun _ : Fin k => Measure.pi marginal)
          {z : Fin k → Fin n → S |
            t ≤ tailConst k * ‖∑ a : OrderedTuple n k, f a (fun j => z j (a.1 j))‖} :=
  sourceUniformTail_tailConst (S := S) (E := E) k (by omega) marginal hkn f hf t ht

/-- **Proposition 3.3, moment form `Φ(x) = x^p`, on product laws**, derived from the tail form by
the layer-cake formula: `E‖U‖^p ≤ C_k E (C_k‖Ũ‖)^p` (as an inequality in `[0, ∞]`). -/
theorem prop33_banach_moment_product (k : ℕ) (hk : 2 ≤ k) {n : ℕ} (hkn : k ≤ n)
    (marginal : Fin n → Measure S) [∀ i, IsProbabilityMeasure (marginal i)]
    (f : OrderedTuple n k → (Fin k → S) → E) (hf : ∀ a, Measurable (f a))
    {p : ℝ} (hp : 0 < p) :
    ∫⁻ x : Fin n → S,
        ENNReal.ofReal (‖∑ a : OrderedTuple n k, f a (fun j => x (a.1 j))‖ ^ p)
        ∂Measure.pi marginal ≤
      ENNReal.ofReal (tailConst k) *
        ∫⁻ z : Fin k → Fin n → S,
          ENNReal.ofReal ((tailConst k *
            ‖∑ a : OrderedTuple n k, f a (fun j => z j (a.1 j))‖) ^ p)
          ∂Measure.pi (fun _ : Fin k => Measure.pi marginal) := by
  classical
  set C := tailConst k with hC
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (one_le_tailConst k)
  set μ := Measure.pi marginal with hμ
  set ρ := Measure.pi (fun _ : Fin k => Measure.pi marginal) with hρ
  have hU := measurable_sourceOrderStatistic f hf
  have hV := measurable_sourceOrderDecoupledStatistic f hf
  have hUn : Measurable (fun x : Fin n → S => ‖sourceOrderStatistic f x‖) := hU.norm
  have hVn : Measurable (fun z : Fin k → Fin n → S => C * ‖sourceOrderDecoupledStatistic f z‖) :=
    hV.norm.const_mul C
  have e1 := lintegral_rpow_eq_lintegral_meas_le_mul μ
    (f := fun x : Fin n → S => ‖sourceOrderStatistic f x‖)
    (Filter.Eventually.of_forall fun x => norm_nonneg _) hUn.aemeasurable hp
  have e2 := lintegral_rpow_eq_lintegral_meas_le_mul ρ
    (f := fun z : Fin k → Fin n → S => C * ‖sourceOrderDecoupledStatistic f z‖)
    (Filter.Eventually.of_forall fun z => mul_nonneg hCpos.le (norm_nonneg _))
    hVn.aemeasurable hp
  change ∫⁻ x, ENNReal.ofReal (‖sourceOrderStatistic f x‖ ^ p) ∂μ ≤
    ENNReal.ofReal C * ∫⁻ z, ENNReal.ofReal ((C * ‖sourceOrderDecoupledStatistic f z‖) ^ p) ∂ρ
  rw [e1, e2]
  have hmono : ∫⁻ t in Set.Ioi (0 : ℝ),
        μ {a | t ≤ ‖sourceOrderStatistic f a‖} * ENNReal.ofReal (t ^ (p - 1)) ≤
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal C *
        (ρ {a | t ≤ C * ‖sourceOrderDecoupledStatistic f a‖} *
          ENNReal.ofReal (t ^ (p - 1))) := by
    apply setLIntegral_mono' measurableSet_Ioi
    intro t ht
    rw [← mul_assoc]
    gcongr
    exact prop33_banach_tail_product k hk hkn marginal f hf ht
  calc ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0 : ℝ),
        μ {a | t ≤ ‖sourceOrderStatistic f a‖} * ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal C *
        (ρ {a | t ≤ C * ‖sourceOrderDecoupledStatistic f a‖} *
          ENNReal.ofReal (t ^ (p - 1))) := by gcongr
    _ = ENNReal.ofReal C * (ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0 : ℝ),
        ρ {a | t ≤ C * ‖sourceOrderDecoupledStatistic f a‖} *
          ENNReal.ofReal (t ^ (p - 1))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      ring

end Product


section RandomVariables
variable {S E Ω : Type*} [MeasurableSpace S] [MeasurableSpace E] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [OpensMeasurableSpace E] [MeasurableAdd₂ E] [MeasurableSpace Ω]

/-- Laws of the copies: if the `k` rows `(ξ j i)_i` are independent of each other, the coordinates
within each row are independent, and `ξ j i` has law `μ i`, then each row has law `Measure.pi μ`
and the whole family of rows has law `Measure.pi (fun _ => Measure.pi μ)`. -/
theorem map_copies_eq_pi {n k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Fin n → Measure S) (ξ : Fin k → Fin n → Ω → S) (hξ : ∀ j i, Measurable (ξ j i))
    (hlaw : ∀ j i, P.map (ξ j i) = μ i) (hrow : ∀ j, iIndepFun (fun i => ξ j i) P)
    (hcopies : iIndepFun (fun j ω i => ξ j i ω) P) :
    (∀ j, P.map (fun ω i => ξ j i ω) = Measure.pi μ) ∧
      P.map (fun ω j i => ξ j i ω) = Measure.pi (fun _ : Fin k => Measure.pi μ) := by
  have hrowLaw : ∀ j, P.map (fun ω i => ξ j i ω) = Measure.pi μ := by
    intro j
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hξ j i).aemeasurable)).1 (hrow j)]
    simp only [hlaw]
  refine ⟨hrowLaw, ?_⟩
  have hm : ∀ j, Measurable (fun ω i => ξ j i ω) := fun j => Measurable.of_eval (hξ j)
  rw [(iIndepFun_iff_map_fun_eq_pi_map (fun j => (hm j).aemeasurable)).1 hcopies]
  simp only [hrowLaw]

/-- **Proposition 3.3 as printed (tail form), general `k ≥ 2`, Banach values.**
`ξ j i` is the `i`-th coordinate of the `j`-th independent copy (`j` ranges over the `k` copies,
copy `0` playing the role of `ξ^{(1)}` and of the original sequence). -/
theorem prop33_banach_tail (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (hk : 2 ≤ k) {n : ℕ} (hkn : k ≤ n)
    (μ : Fin n → Measure S) [∀ i, IsProbabilityMeasure (μ i)]
    (ξ : Fin k → Fin n → Ω → S) (hξ : ∀ j i, Measurable (ξ j i))
    (hlaw : ∀ j i, P.map (ξ j i) = μ i) (hrow : ∀ j, iIndepFun (fun i => ξ j i) P)
    (hcopies : iIndepFun (fun j ω i => ξ j i ω) P)
    (f : OrderedTuple n k → (Fin k → S) → E) (hf : ∀ a, Measurable (f a))
    {t : ℝ} (ht : 0 < t) :
    P {ω | t ≤ ‖∑ a : OrderedTuple n k, f a (fun j => ξ ⟨0, by omega⟩ (a.1 j) ω)‖} ≤
      ENNReal.ofReal (tailConst k) *
        P {ω | t ≤ tailConst k * ‖∑ a : OrderedTuple n k, f a (fun j => ξ j (a.1 j) ω)‖} := by
  obtain ⟨hrowLaw, hall⟩ := map_copies_eq_pi P μ ξ hξ hlaw hrow hcopies
  have hR : Measurable (fun ω j i => ξ j i ω) :=
    measurable_pi_iff.mpr fun j => Measurable.of_eval (hξ j)
  have hR0 : Measurable (fun ω i => ξ ⟨0, by omega⟩ i ω) := Measurable.of_eval (hξ _)
  have hU := measurable_sourceOrderStatistic f hf
  have hV := measurable_sourceOrderDecoupledStatistic f hf
  have hBU : MeasurableSet {x : Fin n → S | t ≤ ‖sourceOrderStatistic f x‖} :=
    measurableSet_le measurable_const hU.norm
  have hBV : MeasurableSet {z : Fin k → Fin n → S |
      t ≤ tailConst k * ‖sourceOrderDecoupledStatistic f z‖} :=
    measurableSet_le measurable_const (hV.norm.const_mul _)
  have h1 : P {ω | t ≤ ‖∑ a : OrderedTuple n k, f a (fun j => ξ ⟨0, by omega⟩ (a.1 j) ω)‖} =
      Measure.pi μ {x : Fin n → S | t ≤ ‖sourceOrderStatistic f x‖} := by
    rw [← hrowLaw ⟨0, by omega⟩, Measure.map_apply hR0 hBU]
    rfl
  have h2 : P {ω | t ≤ tailConst k * ‖∑ a : OrderedTuple n k, f a (fun j => ξ j (a.1 j) ω)‖} =
      Measure.pi (fun _ : Fin k => Measure.pi μ) {z : Fin k → Fin n → S |
        t ≤ tailConst k * ‖sourceOrderDecoupledStatistic f z‖} := by
    rw [← hall, Measure.map_apply hR hBV]
    rfl
  rw [h1, h2]
  exact prop33_banach_tail_product k hk hkn μ f hf ht

/-- **Moment form of Proposition 3.3 (`Φ(x) = x^p`), general `k ≥ 2`, Banach values**, derived from
the tail form by the layer-cake formula: `E‖U‖^p ≤ C_k E (C_k ‖Ũ‖)^p`, as an inequality in `[0, ∞]`
(no integrability is assumed). -/
theorem prop33_banach_moment (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (hk : 2 ≤ k) {n : ℕ} (hkn : k ≤ n)
    (μ : Fin n → Measure S) [∀ i, IsProbabilityMeasure (μ i)]
    (ξ : Fin k → Fin n → Ω → S) (hξ : ∀ j i, Measurable (ξ j i))
    (hlaw : ∀ j i, P.map (ξ j i) = μ i) (hrow : ∀ j, iIndepFun (fun i => ξ j i) P)
    (hcopies : iIndepFun (fun j ω i => ξ j i ω) P)
    (f : OrderedTuple n k → (Fin k → S) → E) (hf : ∀ a, Measurable (f a))
    {p : ℝ} (hp : 0 < p) :
    ∫⁻ ω, ENNReal.ofReal
        (‖∑ a : OrderedTuple n k, f a (fun j => ξ ⟨0, by omega⟩ (a.1 j) ω)‖ ^ p) ∂P ≤
      ENNReal.ofReal (tailConst k) *
        ∫⁻ ω, ENNReal.ofReal
          ((tailConst k * ‖∑ a : OrderedTuple n k, f a (fun j => ξ j (a.1 j) ω)‖) ^ p) ∂P := by
  obtain ⟨hrowLaw, hall⟩ := map_copies_eq_pi P μ ξ hξ hlaw hrow hcopies
  have hR : Measurable (fun ω j i => ξ j i ω) :=
    measurable_pi_iff.mpr fun j => Measurable.of_eval (hξ j)
  have hR0 : Measurable (fun ω i => ξ ⟨0, by omega⟩ i ω) := Measurable.of_eval (hξ _)
  have hU := measurable_sourceOrderStatistic f hf
  have hV := measurable_sourceOrderDecoupledStatistic f hf
  have hgU : Measurable (fun x : Fin n → S =>
      ENNReal.ofReal (‖sourceOrderStatistic f x‖ ^ p)) :=
    ENNReal.measurable_ofReal.comp (hU.norm.pow_const p)
  have hgV : Measurable (fun z : Fin k → Fin n → S =>
      ENNReal.ofReal ((tailConst k * ‖sourceOrderDecoupledStatistic f z‖) ^ p)) :=
    ENNReal.measurable_ofReal.comp ((hV.norm.const_mul _).pow_const p)
  have h1 : ∫⁻ ω, ENNReal.ofReal
        (‖∑ a : OrderedTuple n k, f a (fun j => ξ ⟨0, by omega⟩ (a.1 j) ω)‖ ^ p) ∂P =
      ∫⁻ x, ENNReal.ofReal (‖sourceOrderStatistic f x‖ ^ p) ∂Measure.pi μ := by
    rw [← hrowLaw ⟨0, by omega⟩, lintegral_map hgU hR0]
    rfl
  have h2 : ∫⁻ ω, ENNReal.ofReal
        ((tailConst k * ‖∑ a : OrderedTuple n k, f a (fun j => ξ j (a.1 j) ω)‖) ^ p) ∂P =
      ∫⁻ z, ENNReal.ofReal ((tailConst k * ‖sourceOrderDecoupledStatistic f z‖) ^ p)
        ∂Measure.pi (fun _ : Fin k => Measure.pi μ) := by
    rw [← hall, lintegral_map hgV hR]
    rfl
  rw [h1, h2]
  exact prop33_banach_moment_product k hk hkn μ f hf hp

end RandomVariables

#print axioms DGRHS.Decoupling.Prop33.prop33_banach_tail_product
#print axioms DGRHS.Decoupling.Prop33.prop33_banach_moment_product
#print axioms DGRHS.Decoupling.Prop33.map_copies_eq_pi
#print axioms DGRHS.Decoupling.Prop33.prop33_banach_tail
#print axioms DGRHS.Decoupling.Prop33.prop33_banach_moment

end DGRHS.Decoupling.Prop33
