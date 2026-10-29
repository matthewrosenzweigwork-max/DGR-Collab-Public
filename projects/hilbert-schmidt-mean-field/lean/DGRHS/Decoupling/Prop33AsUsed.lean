import DGRHS.Decoupling.Moment

/-!
# Proposition 3.3 (decoupling) in the form the paper consumes

Source: arXiv:2609.02743v1, Proposition 3.3 (`prop:decoup`, TeX lines 1095-1104, a cited external
result of de la Pena and Montgomery-Smith, no proof supplied in the paper), Remark 3.4
(`rem:decoupMoment`, TeX lines 1106-1122), and the two places where the paper uses decoupling:
`eq:Ustattail` (TeX 1127-1134: `k = 2`, `E = R`, tail form, consumed by the master layer-cake
chain) and the moment form with `Phi(x) = x^(2k)` in Section 6.

**Scope statement (read this first).**

* Not formalized here: the printed tail-to-tail inequality `eq:decoupTail` for general `k >= 2`,
  general Banach-space values `E`, and non-canonical kernels, and the general nondecreasing convex
  `Phi` of Remark 3.4 (only `Phi(x) = x^(2k)` is stated); in particular non-identically distributed
  coordinates and index-dependent kernels `f_ij` are not covered (iid coordinates with a common law `μ`,
  a single kernel `h`).  By owner decision (Tier 3) those are not
  in the formal target.  A tail-to-tail inequality `P(|U| >= t) <= C P(C |V| >= t)` is not derivable
  from moment comparison alone, so no such statement is claimed.
* Formalized here: the `k = 2` (two-sample / order-two U-statistic), real-valued forms that the
  paper's chain actually consumes: (i) the even-moment comparison with constant `4^(2k)` (the
  `Phi(x) = x^(2k)` instance of Remark 3.4), re-recorded as
  `decoupling_moment_k2_real`; (ii) a Markov tail corollary
  `decoupling_tail_from_moment_k2`; and (iii) versions of (i) and (ii) for iid random variables on an
  abstract probability space (`decoupling_moment_k2_iid`, `decoupling_tail_from_moment_k2_iid`), with
  two independent iid sequences on a possibly different probability space for the decoupled sum.
* The sums are over ordered pairs of distinct *labels* `i != j` (`offDiagonalSum`), so coincident sample
  values are kept.  The statements hold for every finite index type, including empty and
  singleton ones (both sides vanish), hence in particular for every `N >= 2`.

The recorded counterpart in the registered alias file is
`DGRHS.Original.prop_decoup.Decoupling_scalar_even_moment_decoupling`
(`proof/DGRHS/Original/OriginalResultsConcentration.lean`, alias of
`DGRHS.Decoupling.scalar_even_moment_decoupling`); that alias file also carries the second alias
`DGRHS.Original.rem_decoupMoment.Decoupling_scalar_even_moment_decoupling`, the more exact match for
`decoupling_moment_k2_real`.

Consumers: `DGRHS.Concentration.iid_master_tail` (via `iid_actual_extended_rate_tail` and the
moment decoupling of `DGRHS.Decoupling.coupled_even_moment_le`), hence
`DGRHS.Concentration.master_exponential_moment_large` and the master layer-cake chain.  The
self-proved even-moment four-scale bound plus Markov replaces the paper's use of Proposition 3.3
followed by Proposition 3.1.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace DGRHS.Decoupling

section Canonical

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable (μ : Measure S) [IsProbabilityMeasure μ]

lemma measurable_coupledSum_pi (h : S × S → ℝ) (hm : Measurable h) :
    Measurable (fun x : ι → S ↦ offDiagonalSum (fun i j ↦ h (x i, x j))) := by
  unfold offDiagonalSum
  apply Finset.measurable_sum
  intro i hi
  apply Finset.measurable_sum
  intro j hj
  by_cases hij : i ≠ j
  · simp_rw [ite_eq_left hij]
    exact hm.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
  · simp_rw [ite_eq_right hij]
    exact measurable_const

lemma measurable_decoupledSum_pi (h : S × S → ℝ) (hm : Measurable h) :
    Measurable (fun p : (ι → S) × (ι → S) ↦ offDiagonalSum (fun i j ↦ h (p.1 i, p.2 j))) := by
  unfold offDiagonalSum
  apply Finset.measurable_sum
  intro i hi
  apply Finset.measurable_sum
  intro j hj
  by_cases hij : i ≠ j
  · simp_rw [ite_eq_left hij]
    exact hm.comp (((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd))
  · simp_rw [ite_eq_right hij]
    exact measurable_const

lemma measurable_coupledPow_pi (h : S × S → ℝ) (hm : Measurable h) (k : ℕ) :
    Measurable (fun x : ι → S ↦ |offDiagonalSum (fun i j ↦ h (x i, x j))| ^ (2 * k)) :=
  (continuous_pow (2 * k)).measurable.comp
    (continuous_abs.measurable.comp (measurable_coupledSum_pi h hm))

lemma measurable_decoupledPow_pi (h : S × S → ℝ) (hm : Measurable h) (k : ℕ) :
    Measurable (fun p : (ι → S) × (ι → S) ↦
      |offDiagonalSum (fun i j ↦ h (p.1 i, p.2 j))| ^ (2 * k)) :=
  (continuous_pow (2 * k)).measurable.comp
    (continuous_abs.measurable.comp (measurable_decoupledSum_pi h hm))

/-- The `2k`-th power of the coupled off-diagonal sum is integrable on the iid product space. -/
lemma integrable_coupledPow_pi (h : S × S → ℝ) (k : ℕ)
    (hh : MemLp h (2 * k : ℕ) (μ.prod μ)) :
    Integrable (fun x : ι → S ↦ |offDiagonalSum (fun i j ↦ h (x i, x j))| ^ (2 * k))
      (Measure.pi (fun _ : ι ↦ μ)) := by
  have hmem : MemLp (fun x : ι → S ↦ offDiagonalSum (fun i j ↦ h (x i, x j))) (2 * k : ℕ)
      (Measure.pi (fun _ : ι ↦ μ)) := by
    unfold offDiagonalSum
    apply memLp_finsetSum
    intro i hi
    apply memLp_finsetSum
    intro j hj
    by_cases hij : i ≠ j
    · simp_rw [ite_eq_left hij]
      exact memLp_coupled_term μ h _ hh i j hij
    · simp_rw [ite_eq_right hij]
      simp
  simpa only [Real.norm_eq_abs] using hmem.integrable_norm_pow'

/-- **Remark 3.4 with `Phi(x) = x^(2k)`, real values, `k = 2`-sample form.**  Even-moment decoupling
with the explicit constant `4^(2k)`, for a measurable kernel in `L^(2k)(mu x mu)` with both
marginal means zero almost everywhere.  This is `scalar_even_moment_decoupling`, recorded under
the name of the paper's use. -/
theorem decoupling_moment_k2_real (h : S × S → ℝ) (hm : Measurable h)
    (k : ℕ) (hk : 1 ≤ k) (hh : MemLp h (2 * k : ℕ) (μ.prod μ))
    (hr0 : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
    (hl0 : ∀ᵐ y ∂μ, (∫ x, h (x, y) ∂μ) = 0) :
    (∫ x : ι → S, |offDiagonalSum (fun i j ↦ h (x i, x j))| ^ (2 * k)
      ∂Measure.pi (fun _ : ι ↦ μ)) ≤
      4 ^ (2 * k) * ∫ p : (ι → S) × (ι → S),
        |offDiagonalSum (fun i j ↦ h (p.1 i, p.2 j))| ^ (2 * k)
          ∂(Measure.pi (fun _ : ι ↦ μ)).prod (Measure.pi (fun _ : ι ↦ μ)) :=
  scalar_even_moment_decoupling μ h hm k hk hh hr0 hl0

/-- Chebyshev/Markov tail corollary of the moment decoupling (the form of `eq:decoupTail` that
moment comparison yields): for every `t > 0`,
`P(|sum_{i != j} h(xi_i, xi_j)| >= t) <= 4^(2k) E|sum_{i != j} h(xi_i^(1), xi_j^(2))|^(2k) / t^(2k)`.
This is *not* the printed tail-to-tail inequality of Proposition 3.3. -/
theorem decoupling_tail_from_moment_k2 (h : S × S → ℝ) (hm : Measurable h)
    (k : ℕ) (hk : 1 ≤ k) (hh : MemLp h (2 * k : ℕ) (μ.prod μ))
    (hr0 : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
    (hl0 : ∀ᵐ y ∂μ, (∫ x, h (x, y) ∂μ) = 0) (t : ℝ) (ht : 0 < t) :
    (Measure.pi (fun _ : ι ↦ μ)).real
        {x : ι → S | t ≤ |offDiagonalSum (fun i j ↦ h (x i, x j))|} ≤
      4 ^ (2 * k) * (∫ p : (ι → S) × (ι → S),
        |offDiagonalSum (fun i j ↦ h (p.1 i, p.2 j))| ^ (2 * k)
          ∂(Measure.pi (fun _ : ι ↦ μ)).prod (Measure.pi (fun _ : ι ↦ μ))) / t ^ (2 * k) := by
  have hmom := decoupling_moment_k2_real (ι := ι) μ h hm k hk hh hr0 hl0
  have hI := integrable_coupledPow_pi (ι := ι) μ h k hh
  have hsub : {x : ι → S | t ≤ |offDiagonalSum (fun i j ↦ h (x i, x j))|} ⊆
      {x : ι → S | t ^ (2 * k) ≤ |offDiagonalSum (fun i j ↦ h (x i, x j))| ^ (2 * k)} := by
    intro x hx
    exact pow_le_pow_left₀ ht.le hx _
  have hmono := measureReal_mono (μ := Measure.pi (fun _ : ι ↦ μ)) hsub
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := Measure.pi (fun _ : ι ↦ μ))
    (f := fun x : ι → S ↦ |offDiagonalSum (fun i j ↦ h (x i, x j))| ^ (2 * k))
    (Filter.Eventually.of_forall fun x ↦ pow_nonneg (abs_nonneg _) _) hI (t ^ (2 * k))
  rw [le_div_iff₀ (pow_pos ht _)]
  calc (Measure.pi (fun _ : ι ↦ μ)).real
        {x : ι → S | t ≤ |offDiagonalSum (fun i j ↦ h (x i, x j))|} * t ^ (2 * k)
      ≤ (Measure.pi (fun _ : ι ↦ μ)).real
        {x : ι → S | t ^ (2 * k) ≤ |offDiagonalSum (fun i j ↦ h (x i, x j))| ^ (2 * k)} *
          t ^ (2 * k) := mul_le_mul_of_nonneg_right hmono (by positivity)
    _ = t ^ (2 * k) * (Measure.pi (fun _ : ι ↦ μ)).real
        {x : ι → S | t ^ (2 * k) ≤ |offDiagonalSum (fun i j ↦ h (x i, x j))| ^ (2 * k)} :=
          mul_comm _ _
    _ ≤ ∫ x : ι → S, |offDiagonalSum (fun i j ↦ h (x i, x j))| ^ (2 * k)
          ∂Measure.pi (fun _ : ι ↦ μ) := hmarkov
    _ ≤ _ := hmom

end Canonical

section RandomVariables

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable (μ : Measure S) [IsProbabilityMeasure μ]
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- An independent family of random variables, each with law `mu`, has joint law `mu^(iota)`. -/
lemma map_iid_eq_pi (ξ : ι → Ω → S) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ P) (hlaw : ∀ i, P.map (ξ i) = μ) :
    P.map (fun ω i ↦ ξ i ω) = Measure.pi (fun _ : ι ↦ μ) := by
  rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i ↦ (hξ i).aemeasurable)).1 hind]
  simp only [hlaw]

/-- Two independent iid sequences with common law `mu` have joint law `mu^(iota) x mu^(iota)`. -/
lemma map_pair_eq_prod (ξ₁ ξ₂ : ι → Ω → S) (h₁ : ∀ i, Measurable (ξ₁ i))
    (h₂ : ∀ i, Measurable (ξ₂ i)) (hi₁ : iIndepFun ξ₁ P) (hi₂ : iIndepFun ξ₂ P)
    (hl₁ : ∀ i, P.map (ξ₁ i) = μ) (hl₂ : ∀ i, P.map (ξ₂ i) = μ)
    (hind : IndepFun (fun ω i ↦ ξ₁ i ω) (fun ω i ↦ ξ₂ i ω) P) :
    P.map (fun ω ↦ ((fun i ↦ ξ₁ i ω), (fun i ↦ ξ₂ i ω))) =
      (Measure.pi (fun _ : ι ↦ μ)).prod (Measure.pi (fun _ : ι ↦ μ)) := by
  have hm₁ : Measurable (fun ω i ↦ ξ₁ i ω) := Measurable.of_eval h₁
  have hm₂ : Measurable (fun ω i ↦ ξ₂ i ω) := Measurable.of_eval h₂
  rw [(indepFun_iff_map_prod_eq_prod_map_map hm₁.aemeasurable hm₂.aemeasurable).1 hind,
    map_iid_eq_pi μ P ξ₁ h₁ hi₁ hl₁, map_iid_eq_pi μ P ξ₂ h₂ hi₂ hl₂]

/-- **Remark 3.4 (`Phi(x) = x^(2k)`) for iid random variables.**  `xi` is an independent family
with common law `mu` on `(Omega, P)`; `xi₁, xi₂` are two independent iid sequences with law `mu` on
`(Omega', P')` (independent copies).  The kernel is measurable, in `L^(2k)(mu x mu)`, with
marginal means zero a.e. -/
theorem decoupling_moment_k2_iid
    (ξ : ι → Ω → S) (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = μ)
    (ξ₁ ξ₂ : ι → Ω' → S) (h₁ : ∀ i, Measurable (ξ₁ i)) (h₂ : ∀ i, Measurable (ξ₂ i))
    (hi₁ : iIndepFun ξ₁ P') (hi₂ : iIndepFun ξ₂ P')
    (hl₁ : ∀ i, P'.map (ξ₁ i) = μ) (hl₂ : ∀ i, P'.map (ξ₂ i) = μ)
    (hind₁₂ : IndepFun (fun ω i ↦ ξ₁ i ω) (fun ω i ↦ ξ₂ i ω) P')
    (h : S × S → ℝ) (hm : Measurable h)
    (k : ℕ) (hk : 1 ≤ k) (hh : MemLp h (2 * k : ℕ) (μ.prod μ))
    (hr0 : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
    (hl0 : ∀ᵐ y ∂μ, (∫ x, h (x, y) ∂μ) = 0) :
    (∫ ω, |offDiagonalSum (fun i j ↦ h (ξ i ω, ξ j ω))| ^ (2 * k) ∂P) ≤
      4 ^ (2 * k) * ∫ ω, |offDiagonalSum (fun i j ↦ h (ξ₁ i ω, ξ₂ j ω))| ^ (2 * k) ∂P' := by
  have hX : Measurable (fun ω i ↦ ξ i ω) := Measurable.of_eval hξ
  have hY : Measurable (fun ω ↦ ((fun i ↦ ξ₁ i ω), (fun i ↦ ξ₂ i ω))) :=
    (Measurable.of_eval h₁).prodMk (Measurable.of_eval h₂)
  have hmap := map_iid_eq_pi μ P ξ hξ hind hlaw
  have hmap' := map_pair_eq_prod μ P' ξ₁ ξ₂ h₁ h₂ hi₁ hi₂ hl₁ hl₂ hind₁₂
  have e1 : (∫ ω, |offDiagonalSum (fun i j ↦ h (ξ i ω, ξ j ω))| ^ (2 * k) ∂P) =
      ∫ x : ι → S, |offDiagonalSum (fun i j ↦ h (x i, x j))| ^ (2 * k)
        ∂Measure.pi (fun _ : ι ↦ μ) := by
    have := integral_map (μ := P) hX.aemeasurable
      (f := fun x : ι → S ↦ |offDiagonalSum (fun i j ↦ h (x i, x j))| ^ (2 * k))
      (by rw [hmap]; exact (measurable_coupledPow_pi h hm k).aestronglyMeasurable)
    rw [hmap] at this
    exact this.symm
  have e2 : (∫ ω, |offDiagonalSum (fun i j ↦ h (ξ₁ i ω, ξ₂ j ω))| ^ (2 * k) ∂P') =
      ∫ p : (ι → S) × (ι → S), |offDiagonalSum (fun i j ↦ h (p.1 i, p.2 j))| ^ (2 * k)
        ∂(Measure.pi (fun _ : ι ↦ μ)).prod (Measure.pi (fun _ : ι ↦ μ)) := by
    have := integral_map (μ := P') hY.aemeasurable
      (f := fun p : (ι → S) × (ι → S) ↦
        |offDiagonalSum (fun i j ↦ h (p.1 i, p.2 j))| ^ (2 * k))
      (by rw [hmap']; exact (measurable_decoupledPow_pi h hm k).aestronglyMeasurable)
    rw [hmap'] at this
    exact this.symm
  rw [e1, e2]
  exact decoupling_moment_k2_real (ι := ι) μ h hm k hk hh hr0 hl0

/-- Markov tail corollary for iid random variables: for every `t > 0`,
`P(|sum_{i != j} h(xi_i, xi_j)| >= t) <= 4^(2k) E|sum_{i != j} h(xi_i^(1), xi_j^(2))|^(2k) / t^(2k)`.
Not the printed tail-to-tail inequality of Proposition 3.3. -/
theorem decoupling_tail_from_moment_k2_iid
    (ξ : ι → Ω → S) (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = μ)
    (ξ₁ ξ₂ : ι → Ω' → S) (h₁ : ∀ i, Measurable (ξ₁ i)) (h₂ : ∀ i, Measurable (ξ₂ i))
    (hi₁ : iIndepFun ξ₁ P') (hi₂ : iIndepFun ξ₂ P')
    (hl₁ : ∀ i, P'.map (ξ₁ i) = μ) (hl₂ : ∀ i, P'.map (ξ₂ i) = μ)
    (hind₁₂ : IndepFun (fun ω i ↦ ξ₁ i ω) (fun ω i ↦ ξ₂ i ω) P')
    (h : S × S → ℝ) (hm : Measurable h)
    (k : ℕ) (hk : 1 ≤ k) (hh : MemLp h (2 * k : ℕ) (μ.prod μ))
    (hr0 : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
    (hl0 : ∀ᵐ y ∂μ, (∫ x, h (x, y) ∂μ) = 0) (t : ℝ) (ht : 0 < t) :
    P.real {ω | t ≤ |offDiagonalSum (fun i j ↦ h (ξ i ω, ξ j ω))|} ≤
      4 ^ (2 * k) * (∫ ω, |offDiagonalSum (fun i j ↦ h (ξ₁ i ω, ξ₂ j ω))| ^ (2 * k) ∂P') /
        t ^ (2 * k) := by
  have hX : Measurable (fun ω i ↦ ξ i ω) := Measurable.of_eval hξ
  have hY : Measurable (fun ω ↦ ((fun i ↦ ξ₁ i ω), (fun i ↦ ξ₂ i ω))) :=
    (Measurable.of_eval h₁).prodMk (Measurable.of_eval h₂)
  have hmap := map_iid_eq_pi μ P ξ hξ hind hlaw
  have hmap' := map_pair_eq_prod μ P' ξ₁ ξ₂ h₁ h₂ hi₁ hi₂ hl₁ hl₂ hind₁₂
  have hset : MeasurableSet {x : ι → S | t ≤ |offDiagonalSum (fun i j ↦ h (x i, x j))|} :=
    measurableSet_le measurable_const
      (continuous_abs.measurable.comp (measurable_coupledSum_pi h hm))
  have e1 : P.real {ω | t ≤ |offDiagonalSum (fun i j ↦ h (ξ i ω, ξ j ω))|} =
      (Measure.pi (fun _ : ι ↦ μ)).real
        {x : ι → S | t ≤ |offDiagonalSum (fun i j ↦ h (x i, x j))|} := by
    rw [measureReal_def, measureReal_def, ← hmap, Measure.map_apply hX hset]
    rfl
  have e2 : (∫ ω, |offDiagonalSum (fun i j ↦ h (ξ₁ i ω, ξ₂ j ω))| ^ (2 * k) ∂P') =
      ∫ p : (ι → S) × (ι → S), |offDiagonalSum (fun i j ↦ h (p.1 i, p.2 j))| ^ (2 * k)
        ∂(Measure.pi (fun _ : ι ↦ μ)).prod (Measure.pi (fun _ : ι ↦ μ)) := by
    have := integral_map (μ := P') hY.aemeasurable
      (f := fun p : (ι → S) × (ι → S) ↦
        |offDiagonalSum (fun i j ↦ h (p.1 i, p.2 j))| ^ (2 * k))
      (by rw [hmap']; exact (measurable_decoupledPow_pi h hm k).aestronglyMeasurable)
    rw [hmap'] at this
    exact this.symm
  rw [e1, e2]
  exact decoupling_tail_from_moment_k2 (ι := ι) μ h hm k hk hh hr0 hl0 t ht

end RandomVariables

#print axioms DGRHS.Decoupling.measurable_coupledSum_pi
#print axioms DGRHS.Decoupling.measurable_decoupledSum_pi
#print axioms DGRHS.Decoupling.measurable_coupledPow_pi
#print axioms DGRHS.Decoupling.measurable_decoupledPow_pi
#print axioms DGRHS.Decoupling.integrable_coupledPow_pi
#print axioms DGRHS.Decoupling.decoupling_moment_k2_real
#print axioms DGRHS.Decoupling.decoupling_tail_from_moment_k2
#print axioms DGRHS.Decoupling.map_iid_eq_pi
#print axioms DGRHS.Decoupling.map_pair_eq_prod
#print axioms DGRHS.Decoupling.decoupling_moment_k2_iid
#print axioms DGRHS.Decoupling.decoupling_tail_from_moment_k2_iid

end DGRHS.Decoupling
