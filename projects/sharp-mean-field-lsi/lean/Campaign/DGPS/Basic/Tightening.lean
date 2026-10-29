import DGPS.Basic.EntropyUniformIntegrability
import DGPS.Particle.Contractions
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Bornology

/-!
# Abstract tightening hypotheses and bounded violating sequence (LIP079)

Abstract setting (the "small explicit record" of the blueprint): for each `n : ℕ` a probability
space `(Ω n, P n)`, an unscaled energy form `E n : (Ω n → ℝ) → ℝ` and a class `S n` of admissible
tests.

* `DGPS.Analysis.TighteningHyp P E S R`: the record of hypotheses
  - admissible tests are measurable with integrable square, energies are nonnegative;
  - stability of `S` under the contractions `|f|`, `max (f, c)`, `min (f, c)`, `a f + b`, with the
    energy inequalities of FOU011 (`E` does not increase under the three contractions, and
    `E (a f + b) = a² E f`);
  - `R > 0`;
  - uniform defective LSI: for every `0 < r0 < R` there is `C` with
    `Ent(f²) ≤ 2 E f / r0 + C ‖f‖²` for all `n` and all `f ∈ S n`;
  - bounded-observable comparison at a rate `a ≥ R`;
  - Poincaré liminf `≥ R`.
* `DGPS.Analysis.abstract_tightening_hypotheses_and_bounded_violating_sequence`: if `0 < r < R` and
  the exact LSI `Ent(f²) ≤ 2 E f / r` is not eventual, there are indices `N_k → ∞` and nonnegative
  normalized admissible `f_k` with `h_k = Ent(f_k²) > 0` and `2 E_k < r h_k`; moreover
  `(1 - r/r0) h_k ≤ C_{r0}` for every `r < r0 < R`, entropies and energies are bounded, the squares
  are uniformly integrable (LIP050), and `(h_k, E_k)` has a convergent subsequence.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Analysis

/-- The abstract tightening hypotheses of LIP079. -/
structure TighteningHyp {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    (E : ∀ n, (Ω n → ℝ) → ℝ) (S : ∀ n, Set (Ω n → ℝ)) (R : ℝ) : Prop where
  measurable : ∀ n, ∀ f ∈ S n, Measurable f
  sq_integrable : ∀ n, ∀ f ∈ S n, Integrable (fun x => f x ^ 2) (P n)
  energy_nonneg : ∀ n, ∀ f ∈ S n, 0 ≤ E n f
  abs_mem : ∀ n, ∀ f ∈ S n, (fun x => |f x|) ∈ S n
  max_mem : ∀ n, ∀ f ∈ S n, ∀ c : ℝ, (fun x => max (f x) c) ∈ S n
  min_mem : ∀ n, ∀ f ∈ S n, ∀ c : ℝ, (fun x => min (f x) c) ∈ S n
  affine_mem : ∀ n, ∀ f ∈ S n, ∀ a b : ℝ, (fun x => a * f x + b) ∈ S n
  energy_abs_le : ∀ n, ∀ f ∈ S n, E n (fun x => |f x|) ≤ E n f
  energy_max_le : ∀ n, ∀ f ∈ S n, ∀ c : ℝ, E n (fun x => max (f x) c) ≤ E n f
  energy_min_le : ∀ n, ∀ f ∈ S n, ∀ c : ℝ, E n (fun x => min (f x) c) ≤ E n f
  energy_affine : ∀ n, ∀ f ∈ S n, ∀ a b : ℝ, E n (fun x => a * f x + b) = a ^ 2 * E n f
  R_pos : 0 < R
  /-- Uniform defective LSI `Ent(f²) ≤ 2E(f)/r0 + C_{r0} ‖f‖₂²`. -/
  defective : ∀ r0 : ℝ, 0 < r0 → r0 < R → ∃ C : ℝ, ∀ n, ∀ f ∈ S n,
    homogeneousEntropy (P n) (fun x => f x ^ 2)
      ≤ ENNReal.ofReal (2 * E n f / r0 + C * ∫ x, f x ^ 2 ∂P n)
  /-- Bounded-observable comparison at some rate `a ≥ R`: for bounded `f` of bounded energy,
  `(a/2) Ent(f²) ≤ E f + ε` for all large `n`. -/
  bounded_comparison : ∃ a : ℝ, R ≤ a ∧ ∀ M E0 ε : ℝ, 0 < M → 0 < E0 → 0 < ε →
    ∃ N0 : ℕ, ∀ n ≥ N0, ∀ f ∈ S n, (∀ x, |f x| ≤ M) → E n f ≤ E0 →
      ENNReal.ofReal (a / 2) * homogeneousEntropy (P n) (fun x => f x ^ 2)
        ≤ ENNReal.ofReal (E n f + ε)
  /-- Poincaré rate `liminf ≥ R`: for every `ρ < R`, eventually `ρ Var(f) ≤ E f`. -/
  poincare : ∀ ρ : ℝ, ρ < R → ∃ N0 : ℕ, ∀ n ≥ N0, ∀ f ∈ S n,
    ρ * (∫ x, f x ^ 2 ∂P n - (∫ x, f x ∂P n) ^ 2) ≤ E n f

/-- One normalization step: a violator of the exact `r`-LSI yields a nonnegative mass-one
violator in the same class with entropy `h > 0` and `2E < r h`. -/
theorem exists_normalized_violator {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)] {E : ∀ n, (Ω n → ℝ) → ℝ}
    {S : ∀ n, Set (Ω n → ℝ)} {R : ℝ} (hyp : TighteningHyp P E S R) {r : ℝ} (hr : 0 < r)
    (hrR : r < R) {n : ℕ} {f : Ω n → ℝ} (hf : f ∈ S n)
    (hv : ENNReal.ofReal (2 * E n f / r) < homogeneousEntropy (P n) (fun x => f x ^ 2)) :
    ∃ g ∈ S n, (∀ x, 0 ≤ g x) ∧ ∫ x, g x ^ 2 ∂P n = 1 ∧
      ∃ h : ℝ, homogeneousEntropy (P n) (fun x => g x ^ 2) = ENNReal.ofReal h ∧ 0 < h ∧
        2 * E n g < r * h := by
  obtain ⟨C0, hC0⟩ := hyp.defective ((r + R) / 2) (by linarith) (by linarith)
  set m : ℝ := ∫ x, f x ^ 2 ∂P n with hmdef
  set Ent := homogeneousEntropy (P n) (fun x => f x ^ 2) with hEnt
  have hfin : Ent ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC0 n f hf)
  have hE0 := hyp.energy_nonneg n f hf
  have hpos : 0 < Ent := lt_of_le_of_lt bot_le hv
  have hm : 0 < m := by
    rcases (integral_nonneg (f := fun x => f x ^ 2) (fun x => sq_nonneg (f x))).eq_or_lt with h | h
    · exfalso
      rw [hEnt, homogeneousEntropy_of_integral_eq_zero h.symm] at hpos
      exact lt_irrefl _ hpos
    · exact h
  set a : ℝ := 1 / Real.sqrt m with ha
  have hsq : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm.le
  have ha2 : a ^ 2 * m = 1 := by
    rw [ha, div_pow, hsq]; field_simp
  have ha2pos : 0 < a ^ 2 := by
    have : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
    positivity
  have hapos : 0 ≤ a := by positivity
  have hmem := hyp.affine_mem n _ (hyp.abs_mem n f hf) a 0
  simp only [add_zero] at hmem
  have hen := hyp.energy_affine n _ (hyp.abs_mem n f hf) a 0
  simp only [add_zero] at hen
  have hlt : 2 * E n f / r < Ent.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hfin).mp hv
  have hlt2 : 2 * E n f < r * Ent.toReal := by
    rw [div_lt_iff₀ hr] at hlt; linarith
  have hentpos : 0 < Ent.toReal := lt_of_le_of_lt (by positivity) hlt
  refine ⟨fun x => a * |f x|, hmem, fun x => by positivity, ?_, a ^ 2 * Ent.toReal, ?_, ?_, ?_⟩
  · have : (fun x => (a * |f x|) ^ 2) = fun x => a ^ 2 * f x ^ 2 := by
      funext x; rw [mul_pow, sq_abs]
    simp only [this]
    rw [integral_const_mul, ← hmdef, ha2]
  · have e1 : (fun x => (a * |f x|) ^ 2) = fun x => (a * (fun y => |f y|) x) ^ 2 := rfl
    rw [e1, homogeneousEntropy_sq_const_mul]
    have e2 : (fun x => (fun y => |f y|) x ^ 2) = fun x => f x ^ 2 := by
      funext x; exact sq_abs _
    rw [e2, ← hEnt, ENNReal.ofReal_mul (sq_nonneg a), ENNReal.ofReal_toReal hfin]
  · positivity
  · have h1 : E n (fun x => a * |f x|) ≤ a ^ 2 * E n f := by
      rw [hen]; exact mul_le_mul_of_nonneg_left (hyp.energy_abs_le n f hf) (sq_nonneg a)
    calc 2 * E n (fun x => a * |f x|) ≤ 2 * (a ^ 2 * E n f) := by linarith
      _ = a ^ 2 * (2 * E n f) := by ring
      _ < a ^ 2 * (r * Ent.toReal) := mul_lt_mul_of_pos_left hlt2 ha2pos
      _ = r * (a ^ 2 * Ent.toReal) := by ring

/-- LIP079.  Under the abstract tightening hypotheses, if the exact LSI with constant `r < R` is
not eventual, there is a sequence `N_k → ∞` of nonnegative normalized admissible `f_k` with
`h_k = Ent(f_k²) > 0` and `2 E_k < r h_k`; for every `r < r0 < R`, `(1 - r/r0) h_k ≤ C_{r0}`;
entropies and energies are bounded, the squares are uniformly integrable, and `(h_k, E_k)` has a
convergent subsequence. -/
theorem abstract_tightening_hypotheses_and_bounded_violating_sequence
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)] {E : ∀ n, (Ω n → ℝ) → ℝ}
    {S : ∀ n, Set (Ω n → ℝ)} {R : ℝ} (hyp : TighteningHyp P E S R) {r : ℝ} (hr : 0 < r)
    (hrR : r < R)
    (hne : ¬ ∃ N0 : ℕ, ∀ n ≥ N0, ∀ f ∈ S n,
      homogeneousEntropy (P n) (fun x => f x ^ 2) ≤ ENNReal.ofReal (2 * E n f / r)) :
    ∃ (n : ℕ → ℕ) (f : ∀ k, Ω (n k) → ℝ) (h : ℕ → ℝ), StrictMono n ∧
      (∀ k, f k ∈ S (n k) ∧ (∀ x, 0 ≤ f k x) ∧ ∫ x, f k x ^ 2 ∂P (n k) = 1 ∧
        homogeneousEntropy (P (n k)) (fun x => f k x ^ 2) = ENNReal.ofReal (h k) ∧ 0 < h k ∧
        2 * E (n k) (f k) < r * h k) ∧
      (∀ r0 : ℝ, r < r0 → r0 < R → ∃ C : ℝ, ∀ k, (1 - r / r0) * h k ≤ C) ∧
      (∃ H : ℝ, ∀ k, h k ≤ H) ∧
      (∃ B : ℝ, ∀ k, 0 ≤ E (n k) (f k) ∧ E (n k) (f k) ≤ B) ∧
      UniformSquareIntegrable (fun k => P (n k)) f ∧
      ∃ (φ : ℕ → ℕ) (hinf einf : ℝ), StrictMono φ ∧
        Tendsto (fun j => h (φ j)) atTop (𝓝 hinf) ∧
        Tendsto (fun j => E (n (φ j)) (f (φ j))) atTop (𝓝 einf) := by
  have hfreq : ∃ᶠ n in atTop, ∃ f ∈ S n,
      ENNReal.ofReal (2 * E n f / r) < homogeneousEntropy (P n) (fun x => f x ^ 2) := by
    rw [Filter.frequently_atTop]
    intro N0
    by_contra hcon
    apply hne
    refine ⟨N0, fun n hn f hf => ?_⟩
    by_contra hlt
    exact hcon ⟨n, hn, f, hf, not_le.mp hlt⟩
  obtain ⟨n, hn, hviol⟩ := Filter.extraction_of_frequently_atTop hfreq
  choose f0 hf0 hv0 using hviol
  have hstep := fun k => exists_normalized_violator hyp hr hrR (hf0 k) (hv0 k)
  choose f hfS hnn hmass h hent hpos hlt using hstep
  -- the bound `(1 - r/r0) h_k ≤ C_{r0}`
  have hbound : ∀ r0 : ℝ, r < r0 → r0 < R → ∃ C : ℝ, ∀ k, (1 - r / r0) * h k ≤ C := by
    intro r0 hr0 hr0R
    have hr0pos : 0 < r0 := lt_trans hr hr0
    obtain ⟨C, hC⟩ := hyp.defective r0 hr0pos hr0R
    refine ⟨C, fun k => ?_⟩
    have h1 := hC (n k) (f k) (hfS k)
    rw [hent k, hmass k, mul_one] at h1
    have h2 : h k ≤ 2 * E (n k) (f k) / r0 + C := by
      rcases (ENNReal.ofReal_le_ofReal_iff' ).mp h1 with h3 | h3
      · exact h3
      · exact absurd h3 (not_le.mpr (hpos k))
    have h3 : 2 * E (n k) (f k) / r0 ≤ r * h k / r0 :=
      div_le_div_of_nonneg_right (hlt k).le hr0pos.le
    have e : (1 - r / r0) * h k = h k - r * h k / r0 := by ring
    rw [e]; linarith
  obtain ⟨C0, hC0⟩ := hbound ((r + R) / 2) (by linarith) (by linarith)
  have hcoef : 0 < 1 - r / ((r + R) / 2) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hH : ∀ k, h k ≤ C0 / (1 - r / ((r + R) / 2)) := fun k =>
    (le_div_iff₀ hcoef).mpr (by linarith [hC0 k])
  set H : ℝ := C0 / (1 - r / ((r + R) / 2)) with hHdef
  have hEnn : ∀ k, 0 ≤ E (n k) (f k) := fun k => hyp.energy_nonneg _ _ (hfS k)
  have hEb : ∀ k, E (n k) (f k) ≤ r * H / 2 := fun k => by
    have := mul_le_mul_of_nonneg_left (hH k) hr.le
    linarith [hlt k]
  have hUI : UniformSquareIntegrable (fun k => P (n k)) f := by
    obtain ⟨Cd, hCd⟩ := hyp.defective ((r + R) / 2) (by linarith) (by linarith)
    refine uniform_square_integrability_from_a_defective_entropy_bound P E S
      (2 / ((r + R) / 2)) Cd hyp.measurable hyp.sq_integrable ?_ n f hfS 1 (r * H / 2)
      (fun k => (hmass k).le) (fun k => ?_)
    · intro m g hg
      rw [show 2 / ((r + R) / 2) * E m g = 2 * E m g / ((r + R) / 2) by ring]
      exact hCd m g hg
    · rw [abs_of_nonneg (hEnn k)]; exact hEb k
  have hmem : ∀ k, (h k, E (n k) (f k)) ∈ Set.Icc ((0 : ℝ), (0 : ℝ)) (H, r * H / 2) := fun k =>
    ⟨Prod.mk_le_mk.2 ⟨(hpos k).le, hEnn k⟩, Prod.mk_le_mk.2 ⟨hH k, hEb k⟩⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_Icc _ _) hmem
  exact ⟨n, f, h, hn, fun k => ⟨hfS k, hnn k, hmass k, hent k, hpos k, hlt k⟩, hbound,
    ⟨H, hH⟩, ⟨r * H / 2, fun k => ⟨hEnn k, hEb k⟩⟩, hUI, φ, a.1, a.2, hφ,
    (continuous_fst.tendsto a).comp hlim, (continuous_snd.tendsto a).comp hlim⟩

end DGPS.Analysis
