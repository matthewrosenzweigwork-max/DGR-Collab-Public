import DGPS.Frontier.LIP032.T19
import DGPS.Frontier.LIP032.T21
import DGPS.Frontier.LIP032.T23
import DGPS.Frontier.LIP032.T24

/-!
# LIP032.25: Exact interpolation L1 estimate

Task id and title: LIP032.25, "Exact interpolation L1 estimate" (node LIP032, contractibility of
the minimizer set; pure density task, no positive-rate or flow hypothesis is used).

## Provides
* `DGPS.Frontier.LIP032.minimizerSet_LIP03225` : the set `S` of free-energy minimizers as the
  subtype of `ProbabilityMeasure (Torus d)` with `freeEnergy A ν = freeEnergyMinimum A`, carrying the
  subspace topology of the weak topology.
* `DGPS.Frontier.LIP032.lip032_25_exact_interpolation_l1_estimate` : the main estimate. For
  minimizers `ν, η` (and the fixed base point `μ`) and `s, t ∈ [0,1]`,
  `∫ |f_{ν,s} - f_{η,t}| dm ≤ ‖p_ν - p_η‖_∞ + 2 |s - t|`, with `f_{ν,s} = interpolDensity_LIP03222`.
* `DGPS.Frontier.LIP032.lip032_25_exact_interpolation_l1_estimate_representative` : the same
  estimate for the coercions (representatives) of the `L²(m)` classes of LIP032.23.
* `DGPS.Frontier.LIP032.lip032_25_exact_interpolation_l1_estimate_ennreal` : the extended `L¹`
  norm of the difference of the two representatives equals `ofReal` of the real integral
  (LIP032.24) and is at most `ofReal` of the right-hand side of the estimate.
* `DGPS.Frontier.LIP032.lip032_25_exact_interpolation_l1_estimate_continuous` : continuity of the
  parameter map `(ν, s) ↦ f_{ν,s}` for the real `L¹` distance, at every point of
  `S × [0,1]` (weak topology on `S`).
* `DGPS.Frontier.LIP032.lip032_25_exact_interpolation_l1_estimate_continuous_representative` :
  the same continuity statement on the representatives of the classes of LIP032.23.

## R5 notes
* Hypotheses of the main statement are those of LIP032.22 and LIP032.23: `A : InteractionData d`;
  reals `M_V`, `M_W` with `|A.V| ≤ M_V` and `|A.W| ≤ M_W` (no nonnegativity assumed, none needed);
  the fixed base point `μ` and the two minimizers `ν`, `η` (memberships in `S`, unused in the proof
  because the bounds hold for every probability, hence bound as `_hμ`, `_hν`, `_hη`); and
  `s, t ∈ [0,1]`. No hypothesis was added. The proof uses only `0 ≤ s ≤ 1`, so the bounds
  `0 ≤ t`, `t ≤ 1` are accepted but unused (binders `_ht0`, `_ht1`); the statement keeps the
  specified range.
* `‖p_ν - p_η‖_∞` is read as the real supremum `⨆ x, |p_ν x - p_η x|`, as in LIP032.21. It is the
  true supremum because the Gibbs densities are continuous on the compact torus (the junk value of
  the supremum of an unbounded family is never used).
* `‖f‖_1` is the real integral `∫ |f| dm` with `m = haar d`. The right-hand side keeps the mass-one
  bound `2` for the second term (the integral of `q + p_η`), not the weaker pointwise bound `2 C`.
* `q = p_μ` and `p_ν` are `DGPS.Lipschitz.gibbsDensity` of the coerced measures, and
  `f_{ν,s}` is `interpolDensity_LIP03222`, exactly as in LIP032.22.
* The estimate is proved for abstract continuous nonnegative mass-one densities first (helper
  `interpol_abs_le_LIP03225`), then specialized to the Gibbs densities.
* "The parameter map is continuous in this real `L¹` distance" is formalized as follows. The domain
  is `S × [0,1]` with the product of the weak subspace topology on `S` and the subspace topology
  on `[0,1]` (`Set.Icc 0 1`). Continuity at a point `(ν₀, s₀)` is the statement that the real
  distance `∫ |f_{ν,s} - f_{ν₀,s₀}| dm` tends to `0` along the neighborhood filter of `(ν₀, s₀)`.
  A real `L¹` distance on functions is not a topology on the function type, so this form (a
  distance tending to zero at every point) is the faithful reading.
* The continuity proof follows the specification: the sup-norm term is controlled by LIP032.21
  (`2 C ‖K_ν - K_{ν₀}‖_∞`) and LIP032.19 (weak-to-uniform continuity of the kernel integral); the
  scalar term `2 |s - s₀|` is elementary.
* The representative statements use `l2Class_LIP03223` and its coercion to a function; the
  transfer is the a.e. equality of LIP032.23 together with a.e.-invariance of the integral. The
  extended-norm form uses the identification of LIP032.24.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- The set `S` of free-energy minimizers, with the subspace topology of the weak topology. -/
abbrev minimizerSet_LIP03225 (A : InteractionData d) : Type :=
  {ν : ProbabilityMeasure (Torus d) // freeEnergy A ν = freeEnergyMinimum A}

/-- The Gibbs density of the packet is the normalized exponential of LIP032.17. -/
theorem gibbsDensity_eq_normExp_LIP03225 (A : InteractionData d) (ν : Measure (Torus d)) :
    DGPS.Lipschitz.gibbsDensity A ν =
      normExp_LIP03217 (fun x => A.V x + ∫ y, A.W x y ∂ν) := rfl

/-- The real `L¹` distance of continuous functions is at most their sup distance. -/
theorem integral_abs_sub_le_iSup_LIP03225 {f g : Torus d → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    ∫ x, |f x - g x| ∂haar d ≤ ⨆ x, |f x - g x| := by
  have hc : Continuous fun x => |f x - g x| := (hf.sub hg).abs
  have hb : BddAbove (Set.range fun x => |f x - g x|) := (isCompact_range hc).bddAbove
  calc ∫ x, |f x - g x| ∂haar d ≤ ∫ _x, (⨆ x, |f x - g x|) ∂haar d :=
        integral_mono (integrable_continuous_LIP03218 hc) (integrable_const _)
          (fun x => le_ciSup hb x)
    _ = ⨆ x, |f x - g x| := by simp

/-- The exact interpolation estimate for abstract continuous nonnegative mass-one densities. -/
theorem interpol_abs_le_LIP03225 {pν pη q : Torus d → ℝ} (hpν : Continuous pν)
    (hpη : Continuous pη) (hq : Continuous q) (h0η : ∀ x, 0 ≤ pη x) (h0q : ∀ x, 0 ≤ q x)
    (hiη : ∫ x, pη x ∂haar d = 1) (hiq : ∫ x, q x ∂haar d = 1)
    {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∫ x, |((1 - s) * pν x + s * q x) - ((1 - t) * pη x + t * q x)| ∂haar d ≤
      (⨆ x, |pν x - pη x|) + 2 * |s - t| := by
  have hs1' : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have hA : Integrable (fun x => |pν x - pη x|) (haar d) :=
    integrable_continuous_LIP03218 (hpν.sub hpη).abs
  have hqη : Integrable (fun x => q x + pη x) (haar d) :=
    (integrable_continuous_LIP03218 hq).add (integrable_continuous_LIP03218 hpη)
  have hB : Integrable (fun x => |s - t| * (q x + pη x)) (haar d) := hqη.const_mul _
  have hcont : Continuous fun x =>
      |((1 - s) * pν x + s * q x) - ((1 - t) * pη x + t * q x)| := by fun_prop
  have hle : ∫ x, |((1 - s) * pν x + s * q x) - ((1 - t) * pη x + t * q x)| ∂haar d ≤
      ∫ x, (|pν x - pη x| + |s - t| * (q x + pη x)) ∂haar d := by
    refine integral_mono (integrable_continuous_LIP03218 hcont) (hA.add hB) fun x => ?_
    have e : ((1 - s) * pν x + s * q x) - ((1 - t) * pη x + t * q x) =
        (1 - s) * (pν x - pη x) + (s - t) * (q x - pη x) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hs1']
    have h1 : (1 - s) * |pν x - pη x| ≤ |pν x - pη x| := by
      nlinarith [abs_nonneg (pν x - pη x)]
    have h2 : |q x - pη x| ≤ q x + pη x :=
      abs_le.mpr ⟨by linarith [h0q x, h0η x], by linarith [h0q x, h0η x]⟩
    have h3 := mul_le_mul_of_nonneg_left h2 (abs_nonneg (s - t))
    linarith
  have hval : ∫ x, (|pν x - pη x| + |s - t| * (q x + pη x)) ∂haar d =
      ∫ x, |pν x - pη x| ∂haar d + |s - t| * 2 := by
    rw [integral_add hA hB, integral_const_mul,
      integral_add (integrable_continuous_LIP03218 hq) (integrable_continuous_LIP03218 hpη),
      hiq, hiη]
    norm_num
  have hsup := integral_abs_sub_le_iSup_LIP03225 hpν hpη
  rw [hval] at hle
  linarith

/-- Continuity of the interpolation density. -/
theorem continuous_interpol_LIP03225 (A : InteractionData d) (M_V M_W : ℝ)
    (hV : ∀ x, |A.V x| ≤ M_V) (hW : ∀ x y, |A.W x y| ≤ M_W)
    (μ ν : ProbabilityMeasure (Torus d)) (s : ℝ) :
    Continuous (interpolDensity_LIP03222 A μ ν s) := by
  obtain ⟨hpc, -, -⟩ := gibbs_bounds_LIP03222 A M_V M_W hV hW ν
  obtain ⟨hqc, -, -⟩ := gibbs_bounds_LIP03222 A M_V M_W hV hW μ
  exact (continuous_const.mul hpc).add (continuous_const.mul hqc)

/-- **LIP032.25.** For minimizers `ν, η ∈ S` (with the fixed base point `μ ∈ S`, `q = p_μ`) and
`s, t ∈ [0,1]`, `‖f_{ν,s} - f_{η,t}‖_1 ≤ ‖p_ν - p_η‖_∞ + 2 |s - t|`. -/
theorem lip032_25_exact_interpolation_l1_estimate
    (A : InteractionData d) (M_V M_W : ℝ) (hV : ∀ x, |A.V x| ≤ M_V)
    (hW : ∀ x y, |A.W x y| ≤ M_W)
    (μ : ProbabilityMeasure (Torus d)) (_hμ : freeEnergy A μ = freeEnergyMinimum A)
    (ν : ProbabilityMeasure (Torus d)) (_hν : freeEnergy A ν = freeEnergyMinimum A)
    (η : ProbabilityMeasure (Torus d)) (_hη : freeEnergy A η = freeEnergyMinimum A)
    (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (_ht0 : 0 ≤ t) (_ht1 : t ≤ 1) :
    ∫ x, |interpolDensity_LIP03222 A μ ν s x - interpolDensity_LIP03222 A μ η t x| ∂haar d ≤
      (⨆ x, |DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)) x -
        DGPS.Lipschitz.gibbsDensity A (η : Measure (Torus d)) x|) + 2 * |s - t| := by
  obtain ⟨hpc, -, -⟩ := gibbs_bounds_LIP03222 A M_V M_W hV hW ν
  obtain ⟨hec, heb, hei⟩ := gibbs_bounds_LIP03222 A M_V M_W hV hW η
  obtain ⟨hqc, hqb, hqi⟩ := gibbs_bounds_LIP03222 A M_V M_W hV hW μ
  unfold interpolDensity_LIP03222
  exact interpol_abs_le_LIP03225 hpc hec hqc
    (fun x => (Real.exp_pos _).le.trans (heb x).1) (fun x => (Real.exp_pos _).le.trans (hqb x).1)
    hei hqi hs0 hs1

/-- The real `L¹` distance of the representatives of the classes equals that of the densities. -/
theorem integral_abs_l2Class_eq_LIP03225 {f g : Torus d → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    ∫ x, |(l2Class_LIP03223 f) x - (l2Class_LIP03223 g) x| ∂haar d =
      ∫ x, |f x - g x| ∂haar d := by
  refine integral_congr_ae ?_
  filter_upwards [l2Class_coe_ae_LIP03223 (memLp_two_of_continuous_LIP03223 hf),
    l2Class_coe_ae_LIP03223 (memLp_two_of_continuous_LIP03223 hg)] with x h1 h2
  rw [h1, h2]

/-- **LIP032.25**, on the representatives of the `L²(m)` classes of LIP032.23. -/
theorem lip032_25_exact_interpolation_l1_estimate_representative
    (A : InteractionData d) (M_V M_W : ℝ) (hV : ∀ x, |A.V x| ≤ M_V)
    (hW : ∀ x y, |A.W x y| ≤ M_W)
    (μ : ProbabilityMeasure (Torus d)) (_hμ : freeEnergy A μ = freeEnergyMinimum A)
    (ν : ProbabilityMeasure (Torus d)) (_hν : freeEnergy A ν = freeEnergyMinimum A)
    (η : ProbabilityMeasure (Torus d)) (_hη : freeEnergy A η = freeEnergyMinimum A)
    (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (_ht0 : 0 ≤ t) (_ht1 : t ≤ 1) :
    ∫ x, |(l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) x -
        (l2Class_LIP03223 (interpolDensity_LIP03222 A μ η t)) x| ∂haar d ≤
      (⨆ x, |DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)) x -
        DGPS.Lipschitz.gibbsDensity A (η : Measure (Torus d)) x|) + 2 * |s - t| := by
  rw [integral_abs_l2Class_eq_LIP03225 (continuous_interpol_LIP03225 A M_V M_W hV hW μ ν s)
    (continuous_interpol_LIP03225 A M_V M_W hV hW μ η t)]
  exact lip032_25_exact_interpolation_l1_estimate A M_V M_W hV hW μ _hμ ν _hν η _hη s t hs0 hs1
    _ht0 _ht1

/-- **LIP032.25**, extended-norm form (via LIP032.24): the extended `L¹` norm of the difference of
the representatives is `ofReal` of the real integral, and is at most `ofReal` of the bound. -/
theorem lip032_25_exact_interpolation_l1_estimate_ennreal
    (A : InteractionData d) (M_V M_W : ℝ) (hV : ∀ x, |A.V x| ≤ M_V)
    (hW : ∀ x y, |A.W x y| ≤ M_W)
    (μ : ProbabilityMeasure (Torus d)) (_hμ : freeEnergy A μ = freeEnergyMinimum A)
    (ν : ProbabilityMeasure (Torus d)) (_hν : freeEnergy A ν = freeEnergyMinimum A)
    (η : ProbabilityMeasure (Torus d)) (_hη : freeEnergy A η = freeEnergyMinimum A)
    (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (_ht0 : 0 ≤ t) (_ht1 : t ≤ 1) :
    eLpNorm (fun x => (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) x -
        (l2Class_LIP03223 (interpolDensity_LIP03222 A μ η t)) x) 1 (haar d) =
      ENNReal.ofReal (∫ x, |(l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) x -
        (l2Class_LIP03223 (interpolDensity_LIP03222 A μ η t)) x| ∂haar d) ∧
    eLpNorm (fun x => (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) x -
        (l2Class_LIP03223 (interpolDensity_LIP03222 A μ η t)) x) 1 (haar d) ≤
      ENNReal.ofReal ((⨆ x, |DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)) x -
        DGPS.Lipschitz.gibbsDensity A (η : Measure (Torus d)) x|) + 2 * |s - t|) := by
  have hnorm := eLpNorm_one_eq_ofReal_integral_abs_LIP03224
    (integrable_sub_l2s_LIP03224 (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))
      (l2Class_LIP03223 (interpolDensity_LIP03222 A μ η t)))
  refine ⟨hnorm, ?_⟩
  rw [hnorm]
  exact ENNReal.ofReal_le_ofReal
    (lip032_25_exact_interpolation_l1_estimate_representative A M_V M_W hV hW μ _hμ ν _hν η _hη
      s t hs0 hs1 _ht0 _ht1)

/-- The sup distance of Gibbs densities is controlled by the sup distance of the kernel integrals
(LIP032.21), which is at most the norm of the difference of the bundled kernels. -/
theorem iSup_gibbs_le_LIP03225 (A : InteractionData d) (M_V M_W : ℝ)
    (hV : ∀ x, |A.V x| ≤ M_V) (hW : ∀ x y, |A.W x y| ≤ M_W)
    (ν η : ProbabilityMeasure (Torus d)) :
    (⨆ x, |DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)) x -
        DGPS.Lipschitz.gibbsDensity A (η : Measure (Torus d)) x|) ≤
      2 * Real.exp (2 * (M_V + M_W)) *
        ‖kernelMap_LIP03219 A ν - kernelMap_LIP03219 A η‖ := by
  refine (lip032_21_exact_2c_density_bound_interaction A M_V M_W hV hW
    (ν : Measure (Torus d)) (η : Measure (Torus d))).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.iSup_le (fun x => ?_) (norm_nonneg _)) (by positivity)
  have h := ContinuousMap.norm_coe_le_norm (kernelMap_LIP03219 A ν - kernelMap_LIP03219 A η) x
  simpa [kernelMap_apply_LIP03219, Real.norm_eq_abs] using h

/-- The kernel norm difference tends to zero in the weak topology (LIP032.19). -/
theorem tendsto_kernel_LIP03225 (A : InteractionData d) (ν₀ : ProbabilityMeasure (Torus d)) :
    Tendsto (fun ν : ProbabilityMeasure (Torus d) =>
      ‖kernelMap_LIP03219 A ν - kernelMap_LIP03219 A ν₀‖) (𝓝 ν₀) (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨N, hN, h⟩ := lip032_19_finite_net_weak_uniform_continuity A ν₀ ε hε
  filter_upwards [hN] with ν hν
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  exact h ν hν

/-- **LIP032.25.** The parameter map `(ν, s) ↦ f_{ν,s}` is continuous for the real `L¹` distance at
every point `(ν₀, s₀)` of `S × [0,1]`: the distance `∫ |f_{ν,s} - f_{ν₀,s₀}| dm` tends to `0`. -/
theorem lip032_25_exact_interpolation_l1_estimate_continuous
    (A : InteractionData d) (M_V M_W : ℝ) (hV : ∀ x, |A.V x| ≤ M_V)
    (hW : ∀ x y, |A.W x y| ≤ M_W)
    (μ : ProbabilityMeasure (Torus d)) (_hμ : freeEnergy A μ = freeEnergyMinimum A)
    (ν₀ : minimizerSet_LIP03225 A) (s₀ : Set.Icc (0 : ℝ) 1) :
    Tendsto (fun z : minimizerSet_LIP03225 A × Set.Icc (0 : ℝ) 1 =>
      ∫ x, |interpolDensity_LIP03222 A μ z.1.1 z.2 x -
        interpolDensity_LIP03222 A μ ν₀.1 s₀ x| ∂haar d)
      (𝓝 (ν₀, s₀)) (𝓝 0) := by
  have hcoe : Tendsto (fun z : minimizerSet_LIP03225 A × Set.Icc (0 : ℝ) 1 => z.1.1)
      (𝓝 (ν₀, s₀)) (𝓝 ν₀.1) :=
    (continuous_subtype_val.comp continuous_fst).tendsto (ν₀, s₀)
  have hK := (tendsto_kernel_LIP03225 A ν₀.1).comp hcoe
  have hs : Tendsto (fun z : minimizerSet_LIP03225 A × Set.Icc (0 : ℝ) 1 =>
      |(z.2 : ℝ) - (s₀ : ℝ)|) (𝓝 (ν₀, s₀)) (𝓝 0) := by
    have hc : Continuous fun z : minimizerSet_LIP03225 A × Set.Icc (0 : ℝ) 1 =>
        |(z.2 : ℝ) - (s₀ : ℝ)| :=
      ((continuous_subtype_val.comp continuous_snd).sub continuous_const).abs
    simpa using hc.tendsto (ν₀, s₀)
  have hb := (hK.const_mul (2 * Real.exp (2 * (M_V + M_W)))).add (hs.const_mul 2)
  rw [mul_zero, mul_zero, add_zero] at hb
  refine squeeze_zero (fun z => integral_nonneg fun x => abs_nonneg _) (fun z => ?_) hb
  refine (lip032_25_exact_interpolation_l1_estimate A M_V M_W hV hW μ _hμ z.1.1 z.1.2 ν₀.1 ν₀.2
    z.2 s₀ z.2.2.1 z.2.2.2 s₀.2.1 s₀.2.2).trans ?_
  have := iSup_gibbs_le_LIP03225 A M_V M_W hV hW z.1.1 ν₀.1
  simp only [Function.comp]
  linarith

/-- **LIP032.25**, continuity of the parameter map on the representatives of the `L²(m)` classes
of LIP032.23. -/
theorem lip032_25_exact_interpolation_l1_estimate_continuous_representative
    (A : InteractionData d) (M_V M_W : ℝ) (hV : ∀ x, |A.V x| ≤ M_V)
    (hW : ∀ x y, |A.W x y| ≤ M_W)
    (μ : ProbabilityMeasure (Torus d)) (_hμ : freeEnergy A μ = freeEnergyMinimum A)
    (ν₀ : minimizerSet_LIP03225 A) (s₀ : Set.Icc (0 : ℝ) 1) :
    Tendsto (fun z : minimizerSet_LIP03225 A × Set.Icc (0 : ℝ) 1 =>
      ∫ x, |(l2Class_LIP03223 (interpolDensity_LIP03222 A μ z.1.1 z.2)) x -
        (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₀.1 s₀)) x| ∂haar d)
      (𝓝 (ν₀, s₀)) (𝓝 0) := by
  refine Tendsto.congr (fun z => (integral_abs_l2Class_eq_LIP03225
    (continuous_interpol_LIP03225 A M_V M_W hV hW μ z.1.1 z.2)
    (continuous_interpol_LIP03225 A M_V M_W hV hW μ ν₀.1 s₀)).symm) ?_
  exact lip032_25_exact_interpolation_l1_estimate_continuous A M_V M_W hV hW μ _hμ ν₀ s₀

end DGPS.Frontier.LIP032
