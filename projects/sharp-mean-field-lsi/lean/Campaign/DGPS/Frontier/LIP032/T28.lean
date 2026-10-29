import DGPS.Frontier.LIP032.T26
import DGPS.Frontier.LIP032.T27

/-!
# LIP032.28: Real free energy and uniform gap

Task id and title: LIP032.28, "Real free energy and uniform gap" (node LIP032, contractibility of
the minimizer set; leaf formalization, pure density/energy task, no positive-rate, flow or
Lipschitz hypothesis is used).

## Provides
* `DGPS.Frontier.LIP032.realFreeEnergy_LIP03228` : the real number
  `E(f) = ∫ f log f dm + ∫ A.V dμ_f + (1/2) ∫ A.W d(μ_f ⊗ μ_f)` attached to a real density `f`.
* `DGPS.Frontier.LIP032.lip032_28_real_free_energy_uniform_gap` : the main statement. For minimizers
  `μ, ν` and `s ∈ [0,1]`, with `f = f_{ν,s}` and `q = p_μ`: (a) the probability `μ_f` has extended free
  energy `freeEnergy A μ_f = ↑(E f)`; (b) `μ_q = μ`, `freeEnergy A μ = ↑(E q)` and
  `freeEnergyMinimum A = ↑(E q)`; (c) `0 ≤ E f - E q ≤ log C + 2 M_V + M_W`, `C = exp (2 (M_V + M_W))`.
* `DGPS.Frontier.LIP032.lip032_28_real_free_energy_uniform_gap_density` : part (a) for any continuous
  mass-one density with `c ≤ f ≤ C`, `0 < c`.
* `DGPS.Frontier.LIP032.lip032_28_real_free_energy_uniform_gap_bounds` : the two real bounds
  `-M_V - M_W/2 ≤ E f ≤ log C + M_V + M_W/2` for such a density.

## R5 notes
* `μ_f` is `densityMeasure_LIP03218 f` (LIP032.18). `freeEnergy` takes a `ProbabilityMeasure`, so
  part (a) is stated as: there is a `P : ProbabilityMeasure (Torus d)` whose underlying measure is
  `μ_f` (it is a probability measure by LIP032.22) and `freeEnergy A P = ↑(E f)`. `P` is unique
  (determined by its measure), so this is the statement "the free energy of `μ_f`". The same device
  gives `μ_q`; for `q` the probability is `μ` itself, because `μ_q = μ` (LIP032.18).
* `E(f)` is a Lean definition `realFreeEnergy_LIP03228 A f` whose body is the displayed formula
  verbatim: entropy as `∫ f log f dm` (real), `∫ A.V d μ_f`, and `(1/2) * ∫ A.W p.1 p.2 d(μ_f.prod μ_f)`.
* `E(q) = F_*` is stated as `freeEnergyMinimum A = ↑(E q)` (equality in `EReal` with a finite real
  coercion), together with `freeEnergy A μ = ↑(E q)`; it uses `μ ∈ S` and `μ_q = μ`.
* Minimality `E(f) ≥ E(q)` uses `ν`, `s`, `μ` only through LIP032.22 (density bounds); it needs the
  hypothesis `freeEnergy A μ = freeEnergyMinimum A` (membership `μ ∈ S`). The membership of `ν`
  in `S` is a binder `_hν` kept to match the specification and LIP032.22; it is unused.
* Hypotheses are those of the specification context: `A`, pointwise bounds `|A.V| ≤ M_V`,
  `|A.W| ≤ M_W` (the "choose bounds" step; `M_V, M_W ≥ 0` is not assumed, it is not needed), the
  minimizers, and `s ∈ [0,1]`. `G_0` is written `log C + 2 M_V + M_W` with `C = exp (2 (M_V + M_W))`,
  literally as in the specification (`log (exp x)` is not simplified in the statement).
* Entropy: the specification uses `H(μ_f | m) = ∫ f log f dm` and nonnegativity; here both come from
  LIP032.26 (`0 ≤ ∫ f log f ≤ log C`), not from an extended-infimum argument, so no `∞ - ∞` occurs.
* The extended free energy is rewritten as a finite real via `EReal.coe_ennreal_ofReal` (valid as
  the entropy integral is nonnegative) and `EReal.coe_add`. The inequality `E(f) ≥ E(q)` is
  transferred from `EReal` to `ℝ` by `EReal.coe_le_coe_iff`.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- The real free energy `E(f) = ∫ f log f dm + ∫ A.V dμ_f + (1/2) ∫ A.W d(μ_f ⊗ μ_f)` of a
density `f`. -/
noncomputable def realFreeEnergy_LIP03228 (A : InteractionData d) (f : Torus d → ℝ) : ℝ :=
  ∫ x, f x * Real.log (f x) ∂haar d + ∫ x, A.V x ∂densityMeasure_LIP03218 f +
    (1 / 2 : ℝ) * ∫ p, A.W p.1 p.2
      ∂((densityMeasure_LIP03218 f).prod (densityMeasure_LIP03218 f))

/-- Part (a) for one density: any probability whose measure is `μ_f` has free energy `↑(E f)`. -/
theorem lip032_28_real_free_energy_uniform_gap_density (A : InteractionData d)
    {f : Torus d → ℝ} (hf : Continuous f) (h1 : ∫ x, f x ∂haar d = 1) {c C : ℝ} (hc : 0 < c)
    (hb : ∀ x, c ≤ f x ∧ f x ≤ C) (P : ProbabilityMeasure (Torus d))
    (hP : (P : Measure (Torus d)) = densityMeasure_LIP03218 f) :
    freeEnergy A P = ((realFreeEnergy_LIP03228 A f : ℝ) : EReal) := by
  obtain ⟨hH, -, hlow, -⟩ :=
    lip032_26_finite_entropy_bounded_positive_densities hf h1 hc hb
  unfold freeEnergy
  rw [hP, hH, EReal.coe_ennreal_ofReal, max_eq_left hlow, ← EReal.coe_add, ← EReal.coe_add]
  rfl

/-- The two real bounds for `E(f)`: `-M_V - M_W/2 ≤ E f ≤ log C + M_V + M_W/2`. -/
theorem lip032_28_real_free_energy_uniform_gap_bounds (A : InteractionData d)
    (M_V M_W : ℝ) (hV : ∀ x, |A.V x| ≤ M_V) (hW : ∀ x y, |A.W x y| ≤ M_W)
    {f : Torus d → ℝ} (hf : Continuous f) (h1 : ∫ x, f x ∂haar d = 1) {c C : ℝ} (hc : 0 < c)
    (hb : ∀ x, c ≤ f x ∧ f x ≤ C) :
    -M_V - M_W / 2 ≤ realFreeEnergy_LIP03228 A f ∧
      realFreeEnergy_LIP03228 A f ≤ Real.log C + M_V + M_W / 2 := by
  have h0 : ∀ x, 0 ≤ f x := fun x => (hc.trans_le (hb x).1).le
  have := isProbabilityMeasure_density_LIP03218 hf h0 h1
  obtain ⟨-, -, hlow, hup⟩ :=
    lip032_26_finite_entropy_bounded_positive_densities hf h1 hc hb
  obtain ⟨-, -, hVb, hWb⟩ :=
    lip032_27_uniform_potential_interaction_bounds A M_V M_W hV hW (densityMeasure_LIP03218 f)
  have hVb' := abs_le.mp hVb
  have hWb' := abs_le.mp hWb
  unfold realFreeEnergy_LIP03228
  constructor <;> linarith [hVb'.1, hVb'.2, hWb'.1, hWb'.2]

/-- **LIP032.28.** Real free energy and uniform gap: for the interpolation density
`f_{ν,s}` and `q = p_μ`, the extended free energies are finite reals, `E(q) = F_*`, and
`0 ≤ E(f) - E(q) ≤ log C + 2 M_V + M_W`. -/
theorem lip032_28_real_free_energy_uniform_gap
    (A : InteractionData d) (M_V M_W : ℝ) (hV : ∀ x, |A.V x| ≤ M_V)
    (hW : ∀ x y, |A.W x y| ≤ M_W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (ν : ProbabilityMeasure (Torus d)) (_hν : freeEnergy A ν = freeEnergyMinimum A)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∃ P : ProbabilityMeasure (Torus d),
      (P : Measure (Torus d)) = densityMeasure_LIP03218 (interpolDensity_LIP03222 A μ ν s) ∧
        freeEnergy A P
          = ((realFreeEnergy_LIP03228 A (interpolDensity_LIP03222 A μ ν s) : ℝ) : EReal)) ∧
    ((μ : Measure (Torus d))
        = densityMeasure_LIP03218 (DGPS.Lipschitz.gibbsDensity A (μ : Measure (Torus d))) ∧
      freeEnergy A μ
        = ((realFreeEnergy_LIP03228 A (DGPS.Lipschitz.gibbsDensity A (μ : Measure (Torus d))) : ℝ)
          : EReal) ∧
      freeEnergyMinimum A
        = ((realFreeEnergy_LIP03228 A (DGPS.Lipschitz.gibbsDensity A (μ : Measure (Torus d))) : ℝ)
          : EReal)) ∧
    0 ≤ realFreeEnergy_LIP03228 A (interpolDensity_LIP03222 A μ ν s) -
        realFreeEnergy_LIP03228 A (DGPS.Lipschitz.gibbsDensity A (μ : Measure (Torus d))) ∧
    realFreeEnergy_LIP03228 A (interpolDensity_LIP03222 A μ ν s) -
        realFreeEnergy_LIP03228 A (DGPS.Lipschitz.gibbsDensity A (μ : Measure (Torus d))) ≤
      Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W := by
  obtain ⟨hfc, hf1, hfb, hfP⟩ :=
    lip032_22_interpolation_bounded_density A M_V M_W hV hW μ hμ ν _hν s hs0 hs1
  obtain ⟨hqc, hqb, hq1⟩ := gibbs_bounds_LIP03222 A M_V M_W hV hW μ
  have hc : 0 < Real.exp (-(2 * (M_V + M_W))) := Real.exp_pos _
  obtain ⟨-, -, -, hqμ⟩ := lip032_18_density_probability_test_integral_bridge_gibbs A μ hμ
  -- the probability attached to `μ_f`
  let P : ProbabilityMeasure (Torus d) := ⟨densityMeasure_LIP03218
    (interpolDensity_LIP03222 A μ ν s), hfP⟩
  have hPf : freeEnergy A P
      = ((realFreeEnergy_LIP03228 A (interpolDensity_LIP03222 A μ ν s) : ℝ) : EReal) :=
    lip032_28_real_free_energy_uniform_gap_density A hfc hf1 hc hfb P rfl
  have hμq : freeEnergy A μ
      = ((realFreeEnergy_LIP03228 A (DGPS.Lipschitz.gibbsDensity A (μ : Measure (Torus d))) : ℝ)
        : EReal) :=
    lip032_28_real_free_energy_uniform_gap_density A hqc hq1 hc hqb μ hqμ.symm
  have hmin : freeEnergy A μ ≤ freeEnergy A P := by
    rw [hμ]; exact iInf_le _ P
  obtain ⟨hElow, hEup⟩ := lip032_28_real_free_energy_uniform_gap_bounds A M_V M_W hV hW
    hfc hf1 hc hfb
  obtain ⟨hQlow, -⟩ := lip032_28_real_free_energy_uniform_gap_bounds A M_V M_W hV hW
    hqc hq1 hc hqb
  have hCexp : Real.log (Real.exp (2 * (M_V + M_W))) = 2 * (M_V + M_W) := Real.log_exp _
  refine ⟨⟨P, rfl, hPf⟩, ⟨hqμ.symm, hμq, hμ.symm.trans hμq⟩, ?_, ?_⟩
  · rw [hμq, hPf, EReal.coe_le_coe_iff] at hmin
    linarith
  · rw [hCexp]
    linarith

end DGPS.Frontier.LIP032
