import DGPS.Analysis.RelativeFisher
import DGPS.Analysis.WeakConvolution

/-!
# Frozen Gibbs map and exact frozen-rate infimum (DEF023)

INTERFACES/definitions.md §5, common_lemmas.md DEF023, 02_NORMALIZATION_AND_DEFINITIONS.md §8.

For every probability `ν` on the torus (including singular `ν`) and continuous model data
`A = (V, W)`, the frozen Gibbs law is `P_ν = p_ν m` with
`p_ν = exp(-V - W*ν) / ∫ exp(-V - W*ν) dm`, where `(W*ν)(x) = ∫ W(x, y) dν(y)` is defined
pointwise.

* `frozenGibbs A ν : BoundedPositiveReference d` is `P_ν`; it exists for every continuous data
  (no Lipschitz hypothesis), with a bound `frozenSupBound A` uniform in `ν`.
* `ordinaryLSRate P = inf_{f ∈ H¹(P), Ent_P(f²) > 0} 2 ∫|∇f|² dP / Ent_P(f²)` in `ℝ≥0∞`
  (the ordinary logarithmic Sobolev rate `r_LS(P)`, with `2E/Ent`, not the Poincaré rate).
* `frozenLSRateInf A = ⨅ ν : ProbabilityMeasure (Torus d), ordinaryLSRate (frozenGibbs A ν)`,
  the infimum over all Borel probabilities (`ℝ≥0∞`-valued complete-lattice infimum).

Bounds lemmas: `frozenGibbs_uniform_bounds` (uniform positive two-sided bounds, valid for every
continuous data) and `frozenGibbs_lipschitz` (uniform Lipschitz bound under `LipschitzData A`),
packaged in `frozenGibbs_hasPositiveLipschitzDensity`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace DGPS

variable {d : ℕ}

/-! ### The ordinary logarithmic Sobolev rate -/

open Classical in
/-- The ordinary logarithmic Sobolev rate `r_LS(P) = inf_{Ent_P(f²) > 0} 2 ∫|∇f|² dP / Ent_P(f²)`,
over the full weighted weak `H¹(P)` domain, valued in `ℝ≥0∞` (`2E/Ent`; not the Poincaré rate). -/
noncomputable def ordinaryLSRate (P : BoundedPositiveReference d) : ℝ≥0∞ :=
  ⨅ f : {f : Torus d → ℝ // f ∈ WeightedH1 P ∧
      0 < homogeneousEntropy P.measure (fun x => f x ^ 2)},
    2 * (∫⁻ x, ‖weightedGradient P f.1 f.2.1 x‖ₑ ^ 2 ∂P.measure) /
      homogeneousEntropy P.measure (fun x => f.1 x ^ 2)

/-! ### The frozen Gibbs density -/

/-- The frozen potential `V + W*ν`, with `(W*ν)(x) = ∫ W(x, y) dν(y)` defined pointwise. -/
noncomputable def frozenPotential (A : InteractionData d) (ν : Measure (Torus d)) (x : Torus d) :
    ℝ :=
  A.V x + ∫ y, A.W x y ∂ν

/-- The normalization `∫ exp(-V - W*ν) dm`. -/
noncomputable def frozenPartition (A : InteractionData d) (ν : Measure (Torus d)) : ℝ :=
  ∫ x, Real.exp (-frozenPotential A ν x) ∂haar d

/-- The frozen density `p_ν = exp(-V - W*ν) / ∫ exp(-V - W*ν) dm`. -/
noncomputable def frozenDensity (A : InteractionData d) (ν : Measure (Torus d)) (x : Torus d) :
    ℝ :=
  Real.exp (-frozenPotential A ν x) / frozenPartition A ν

/-- A uniform sup-bound `|V| + |W| ≤ K` for the model data. -/
noncomputable def frozenSupBound (A : InteractionData d) : ℝ :=
  A.V_bounded.choose + A.W_bounded.choose

theorem frozenPotential_continuous (A : InteractionData d) (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] : Continuous (frozenPotential A ν) := by
  have h : Continuous (fun x => ∫ y in (univ : Set (Torus d)), A.W x y ∂ν) :=
    continuous_parametric_integral_of_continuous (f := A.W) A.W_continuous isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact A.V_continuous.add h

theorem abs_frozenPotential_le (A : InteractionData d) (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] (x : Torus d) : |frozenPotential A ν x| ≤ frozenSupBound A := by
  have hV := A.V_bounded.choose_spec x
  have hW : ‖∫ y, A.W x y ∂ν‖ ≤ A.W_bounded.choose := by
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun y => A.W x y)
      (C := A.W_bounded.choose) (Eventually.of_forall fun y => by
        simpa using A.W_bounded.choose_spec x y)
    simpa using this
  rw [Real.norm_eq_abs] at hW
  unfold frozenPotential frozenSupBound
  exact (abs_add_le _ _).trans (add_le_add hV hW)

theorem integrable_exp_neg_frozenPotential (A : InteractionData d) (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] : Integrable (fun x => Real.exp (-frozenPotential A ν x)) (haar d) :=
  ((frozenPotential_continuous A ν).neg.rexp).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem exp_neg_frozenPotential_bounds (A : InteractionData d) (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] (x : Torus d) :
    Real.exp (-frozenSupBound A) ≤ Real.exp (-frozenPotential A ν x) ∧
      Real.exp (-frozenPotential A ν x) ≤ Real.exp (frozenSupBound A) := by
  have h := abs_le.1 (abs_frozenPotential_le A ν x)
  exact ⟨Real.exp_le_exp.2 (by linarith [h.2]), Real.exp_le_exp.2 (by linarith [h.1])⟩

theorem frozenPartition_bounds (A : InteractionData d) (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] :
    Real.exp (-frozenSupBound A) ≤ frozenPartition A ν ∧
      frozenPartition A ν ≤ Real.exp (frozenSupBound A) := by
  have hi := integrable_exp_neg_frozenPotential A ν
  constructor
  · have := integral_mono (integrable_const (Real.exp (-frozenSupBound A))) hi
      (fun x => (exp_neg_frozenPotential_bounds A ν x).1)
    simpa [frozenPartition] using this
  · have := integral_mono hi (integrable_const (Real.exp (frozenSupBound A)))
      (fun x => (exp_neg_frozenPotential_bounds A ν x).2)
    simpa [frozenPartition] using this

theorem frozenPartition_pos (A : InteractionData d) (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] : 0 < frozenPartition A ν :=
  lt_of_lt_of_le (Real.exp_pos _) (frozenPartition_bounds A ν).1

theorem frozenDensity_continuous (A : InteractionData d) (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] : Continuous (frozenDensity A ν) :=
  ((frozenPotential_continuous A ν).neg.rexp).div_const _

theorem frozenDensity_bounds (A : InteractionData d) (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] (x : Torus d) :
    Real.exp (-(2 * frozenSupBound A)) ≤ frozenDensity A ν x ∧
      frozenDensity A ν x ≤ Real.exp (2 * frozenSupBound A) := by
  have hZ := frozenPartition_bounds A ν
  have hZp := frozenPartition_pos A ν
  have hE := exp_neg_frozenPotential_bounds A ν x
  have e1 : Real.exp (-(2 * frozenSupBound A)) =
      Real.exp (-frozenSupBound A) / Real.exp (frozenSupBound A) := by
    rw [← Real.exp_sub]; congr 1; ring
  have e2 : Real.exp (2 * frozenSupBound A) =
      Real.exp (frozenSupBound A) / Real.exp (-frozenSupBound A) := by
    rw [← Real.exp_sub]; congr 1; ring
  unfold frozenDensity
  constructor
  · rw [e1]
    exact div_le_div₀ (Real.exp_pos _).le hE.1 hZp hZ.2
  · rw [e2]
    exact div_le_div₀ (Real.exp_pos _).le hE.2 (Real.exp_pos _) hZ.1

theorem integral_frozenDensity (A : InteractionData d) (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] : ∫ x, frozenDensity A ν x ∂haar d = 1 := by
  unfold frozenDensity
  rw [integral_div]
  exact div_self (frozenPartition_pos A ν).ne'

/-- **DEF023 (frozen Gibbs map).** For continuous model data `A` and every Borel probability `ν`
(including singular ones), the frozen Gibbs law `P_ν = p_ν m`,
`p_ν = exp(-V - W*ν) / ∫ exp(-V - W*ν) dm`, as a bounded positive reference.  The bounds
`exp(-2K) ≤ p_ν ≤ exp(2K)`, `K = frozenSupBound A`, are uniform in `ν`. -/
noncomputable def frozenGibbs (A : InteractionData d) (ν : ProbabilityMeasure (Torus d)) :
    BoundedPositiveReference d where
  density := frozenDensity A (ν : Measure (Torus d))
  measurable_density := (frozenDensity_continuous A (ν : Measure (Torus d))).measurable
  lower := Real.exp (-(2 * frozenSupBound A))
  upper := Real.exp (2 * frozenSupBound A)
  lower_pos := Real.exp_pos _
  lower_le := Eventually.of_forall fun x => (frozenDensity_bounds A (ν : Measure (Torus d)) x).1
  le_upper := Eventually.of_forall fun x => (frozenDensity_bounds A (ν : Measure (Torus d)) x).2
  mass_one := integral_frozenDensity A (ν : Measure (Torus d))

/-- **DEF023 (exact frozen-rate infimum).** `ℓ = inf_ν r_LS(P_ν)` over all Borel probability
measures `ν` on the torus, including singular ones; valued in `ℝ≥0∞` (complete-lattice infimum). -/
noncomputable def frozenLSRateInf (A : InteractionData d) : ℝ≥0∞ :=
  ⨅ ν : ProbabilityMeasure (Torus d), ordinaryLSRate (frozenGibbs A ν)

theorem frozenGibbs_density (A : InteractionData d) (ν : ProbabilityMeasure (Torus d)) :
    (frozenGibbs A ν).density = fun x =>
      Real.exp (-(A.V x + ∫ y, A.W x y ∂(ν : Measure (Torus d)))) /
        ∫ z, Real.exp (-(A.V z + ∫ y, A.W z y ∂(ν : Measure (Torus d)))) ∂haar d := rfl

theorem frozenLSRateInf_le (A : InteractionData d) (ν : ProbabilityMeasure (Torus d)) :
    frozenLSRateInf A ≤ ordinaryLSRate (frozenGibbs A ν) :=
  iInf_le (fun ν : ProbabilityMeasure (Torus d) => ordinaryLSRate (frozenGibbs A ν)) ν

theorem le_frozenLSRateInf_iff (A : InteractionData d) (r : ℝ≥0∞) :
    r ≤ frozenLSRateInf A ↔ ∀ ν : ProbabilityMeasure (Torus d),
      r ≤ ordinaryLSRate (frozenGibbs A ν) :=
  le_iInf_iff

/-! ### Uniform positive and Lipschitz bounds -/

/-- **Uniform positive bounds.** For every probability `ν` (singular allowed), the frozen density
is bounded between the same two positive constants, depending only on the model data. -/
theorem frozenGibbs_uniform_bounds (A : InteractionData d) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ (ν : ProbabilityMeasure (Torus d)) (x : Torus d),
      c ≤ (frozenGibbs A ν).density x ∧ (frozenGibbs A ν).density x ≤ C := by
  have hK : 0 ≤ frozenSupBound A := by
    have := abs_frozenPotential_le A (haar d) 0
    exact (abs_nonneg _).trans this
  exact ⟨Real.exp (-(2 * frozenSupBound A)), Real.exp (2 * frozenSupBound A), Real.exp_pos _,
    Real.exp_le_exp.2 (by linarith), fun ν x => frozenDensity_bounds A (ν : Measure (Torus d)) x⟩

/-- The exponential is Lipschitz with constant `exp K` on `(-∞, K]`, in the form needed here. -/
theorem abs_exp_neg_sub_exp_neg_le {a b K : ℝ} (ha : -K ≤ a) (hb : -K ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ Real.exp K * |a - b| := by
  have key : ∀ {u v : ℝ}, u ≤ K → v ≤ u → Real.exp u - Real.exp v ≤ Real.exp K * (u - v) := by
    intro u v hu hvu
    have h1 := Real.add_one_le_exp (v - u)
    have h2 : Real.exp v = Real.exp u * Real.exp (v - u) := by rw [← Real.exp_add]; congr 1; ring
    have h3 : Real.exp u * (u - v) ≤ Real.exp K * (u - v) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hu) (by linarith)
    nlinarith [Real.exp_pos u]
  have P : ∀ a b : ℝ, -K ≤ a → -K ≤ b → a ≤ b →
      |Real.exp (-a) - Real.exp (-b)| ≤ Real.exp K * |a - b| := by
    intro a b ha hb hab
    rw [abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 (neg_le_neg hab))),
      abs_of_nonpos (sub_nonpos.2 hab)]
    calc Real.exp (-a) - Real.exp (-b) ≤ Real.exp K * (-a - -b) :=
          key (by linarith) (by linarith)
      _ = _ := by ring
  rcases le_total a b with hab | hab
  · exact P a b ha hb hab
  · rw [abs_sub_comm (Real.exp (-a)), abs_sub_comm a b]
    exact P b a hb ha hab

/-- **Uniform Lipschitz bound.** Under Lipschitz model data, every frozen density
is Lipschitz with one constant depending only on the model data (not on `ν`). -/
theorem frozenGibbs_lipschitz (A : InteractionData d) (hLip : LipschitzData A) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ν : ProbabilityMeasure (Torus d),
      TorusLipschitzWith L (frozenGibbs A ν).density := by
  obtain ⟨LW, hLW0, -, -, -, -, -, -, -, hconv⟩ := weakGradient_convolution A hLip
  obtain ⟨LV, hLV0, hV⟩ := hLip.exists_V_const
  set K := frozenSupBound A with hKdef
  refine ⟨Real.exp K * (LV + LW) * Real.exp K, by positivity, fun ν x y => ?_⟩
  have hν : IsProbabilityMeasure (ν : Measure (Torus d)) := inferInstance
  have hW := hconv (ν : Measure (Torus d)) hν
  have hpot : TorusLipschitzWith (LV + LW) (frozenPotential A (ν : Measure (Torus d))) := by
    intro x y
    have := abs_add_le (A.V x - A.V y)
      ((∫ z, A.W x z ∂(ν : Measure (Torus d))) - ∫ z, A.W y z ∂(ν : Measure (Torus d)))
    have h1 := hV x y
    have h2 := hW x y
    unfold frozenPotential
    calc |A.V x + ∫ z, A.W x z ∂(ν : Measure (Torus d)) -
          (A.V y + ∫ z, A.W y z ∂(ν : Measure (Torus d)))|
        = |(A.V x - A.V y) + ((∫ z, A.W x z ∂(ν : Measure (Torus d))) -
            ∫ z, A.W y z ∂(ν : Measure (Torus d)))| := by congr 1; ring
      _ ≤ _ := this
      _ ≤ (LV + LW) * torusDist x y := by nlinarith
  have hbx := abs_le.1 (abs_frozenPotential_le A (ν : Measure (Torus d)) x)
  have hby := abs_le.1 (abs_frozenPotential_le A (ν : Measure (Torus d)) y)
  have hZ := (frozenPartition_bounds A (ν : Measure (Torus d))).1
  have hZp := frozenPartition_pos A (ν : Measure (Torus d))
  have hexp := abs_exp_neg_sub_exp_neg_le (K := K) (a := frozenPotential A (ν : Measure (Torus d)) x)
    (b := frozenPotential A (ν : Measure (Torus d)) y) (by linarith) (by linarith)
  show |frozenDensity A (ν : Measure (Torus d)) x - frozenDensity A (ν : Measure (Torus d)) y| ≤ _
  unfold frozenDensity
  have hinv : (frozenPartition A (ν : Measure (Torus d)))⁻¹ ≤ Real.exp K := by
    have := inv_anti₀ (Real.exp_pos _) hZ
    rwa [← Real.exp_neg, neg_neg] at this
  have hnum : |Real.exp (-frozenPotential A (ν : Measure (Torus d)) x) -
      Real.exp (-frozenPotential A (ν : Measure (Torus d)) y)| ≤
      Real.exp K * ((LV + LW) * torusDist x y) :=
    hexp.trans (mul_le_mul_of_nonneg_left (hpot x y) (Real.exp_pos _).le)
  rw [← sub_div, abs_div, abs_of_pos hZp, div_eq_mul_inv]
  calc _ ≤ (Real.exp K * ((LV + LW) * torusDist x y)) * Real.exp K :=
        mul_le_mul hnum hinv (inv_nonneg.2 hZp.le)
          (mul_nonneg (Real.exp_pos _).le
            (mul_nonneg (add_nonneg hLV0 hLW0) (Real.sqrt_nonneg _)))
    _ = _ := by ring

theorem frozenGibbs_hasPositiveLipschitzDensity (A : InteractionData d) (hLip : LipschitzData A)
    (ν : ProbabilityMeasure (Torus d)) : (frozenGibbs A ν).hasPositiveLipschitzDensity := by
  obtain ⟨L, -, hL⟩ := frozenGibbs_lipschitz A hLip
  obtain ⟨c, C, hc, -, hb⟩ := frozenGibbs_uniform_bounds A
  exact ⟨L, c, hc, fun x => (hb ν x).1, hL ν⟩

end DGPS
