import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import DGPS.Frontier.STR029.T37

/-!
# STR029.38: Uniform subsequence preserving the energy liminf

Task id and title: STR029.38, "Uniform subsequence preserving the energy liminf" (node STR029).
Fix `|h| ≤ 1/1000`. A sequence of data satisfying the hypotheses of STR029.06 (square roots `gₙ ≥ 0` of
probability densities against `q_h m`, periodic `H¹`, positive entropy `Hₙ`, quotient hypothesis
`4 Eₙ / (2 Hₙ) ≤ 2`) has a strictly increasing subsequence `σ` such that the continuous periodic
representatives `F (σ n)` converge uniformly on `ℝ` to a continuous `2π`-periodic `G ≥ 0` with
`∫ G² q_h dm = 1`, and the energies `E (σ n)` converge to `liminf E`, the liminf of the original
energies.

## Provides

* `DGPS.Frontier.STR029.str029_38_uniform_subsequence_preserving_energy_liminf`: the main statement.
  For any sequence of STR029.06 data with continuous `2π`-periodic representatives `F n` of `g n`
  (almost-everywhere equal on `(0, 2π]`), there are a strictly increasing `σ : ℕ → ℕ` and a continuous
  periodic `G ≥ 0` with `normInt (G² q_h) = 1`, such that `F (σ n) → G` uniformly on `ℝ` and
  `E (σ n) → liminf E`.
* `DGPS.Frontier.STR029.str029_38_uniform_subsequence_preserving_energy_liminf_exists_representatives`:
  the same conclusion with the representatives produced by STR029.06 (EX049.32) rather than supplied.

## R5 notes

* Carriers. The weighted integrals use the STR029.04 carriers `normInt_STR02904` (the normalized circle
  integral `∫ · dm = (2π)⁻¹ ∫₀^{2π}`) and `qT_STR02904 h` (the reference density `q_h`). The periodic weak
  derivative is the STR029.33 predicate `IsPeriodicWeakDerivative_STR02933 g g'`, with the almost-everywhere
  convention of STR029.06 (measure `volume.restrict (Ioc 0 (2π))`). The unit does not touch the optimizer
  chart, the Euler or variational range maps, `AbsoluteDensity`, or any entropy/Fisher/deficit convention
  beyond the entropy integral `H` that appears in the STR029.06 hypotheses and is used only through
  them.
* Sequence data. "A sequence satisfying .06" is read as sequences `g g' : ℕ → ℝ → ℝ`, `E H : ℕ → ℝ`, all
  satisfying the hypotheses of `str029_06_information_bound_low_quotients` for the same fixed `h` with
  `|h| ≤ 1/1000` and the same constants `K = 8π² e^{1/500}`, `A = log (K + 2)`. Each hypothesis is the
  `ℕ`-indexed form of the corresponding STR029.06 hypothesis; none is added or dropped.
* Representatives (non-literal reading). Uniform convergence of `H¹` functions refers to their continuous
  representatives. The main statement therefore takes, for each `n`, a continuous `2π`-periodic `F n`
  almost everywhere equal to `g n` on `(0, 2π]`. By the EX049.32 uniqueness such a representative is unique,
  so supplying it is not an extra assumption; the main statement holds for every admissible choice, and the
  second public declaration removes the supplied representatives by choosing them with STR029.06.
* Uniform convergence is stated on all of `ℝ` (`TendstoUniformly` along `atTop`). For `2π`-periodic functions
  this is equivalent to uniform convergence on the compact period `[0, 2π]`.
* Arzelà–Ascoli. The "compact interval" of the specification is realised by the compact quotient circle
  `AddCircle (2π)`. The representatives `F n` descend to bounded continuous functions on the circle, whose
  distance is the circular distance `circDist_STR02937` of STR029.37 (`dist_coe_circle_STR02938`). Uniform
  equicontinuity (STR029.37) and the common bound `1 + 2π e^{1/1000} √(4 (A + 1))` (STR029.06 with
  `E ≤ 4 (A + 1)`) feed the pinned Mathlib theorem `BoundedContinuousFunction.arzela_ascoli`. Periodicity of
  the limit is then automatic; this is the "endpoint equality" of the specification's proof.
* Energy liminf. `liminf E` is `Filter.liminf E Filter.atTop` for the real sequence `E`, which satisfies
  `0 ≤ E n ≤ 4 (A + 1)`, so it is the genuine finite liminf. A subsequence realising it is extracted first
  (`MapClusterPt.liminf`), then Arzelà–Ascoli is applied to that subsequence; the composite subsequence keeps
  the energy limit.
* Nonnegativity. `G ≥ 0` holds pointwise. Each continuous representative `F n` is nonnegative everywhere
  (`rep_nonneg_STR02938`: a negative value would hold on a nonempty open subset of `(0, 2π)`, a set of
  positive measure on which `F n = g n ≥ 0` almost everywhere), and pointwise limits preserve `≥ 0`.
* Normalization. `∫ G² q_h dm = 1` is obtained from dominated convergence on `[0, 2π]` with the constant
  bound `M² e^{2|h|}`, where `M` is the common sup bound and `q_h ≤ e^{2|h|}` (STR029.04); the integrals of
  `F n² q_h` equal `1` by almost-everywhere agreement with `g n`. Squaring is not tracked by an explicit
  Lipschitz constant: pointwise convergence of the squares plus the common bound suffices.
* Helpers. Every helper carries the suffix `_STR02938`; public declarations carry the prefix
  `str029_38_uniform_subsequence_preserving_energy_liminf`.
-/

open MeasureTheory Set Filter Topology
open scoped Real BoundedContinuousFunction

namespace DGPS.Frontier.STR029

/-- The distance on `AddCircle (2π)` between the classes of `t` and `s` is the circular distance
`circDist_STR02937 t s`. -/
lemma dist_coe_circle_STR02938 (t s : ℝ) :
    dist (t : AddCircle (2 * π)) (s : AddCircle (2 * π)) = circDist_STR02937 t s := by
  have hp : (0 : ℝ) < 2 * π := by positivity
  rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq' (2 * π) hp]
  unfold circDist_STR02937
  rw [← abs_of_pos hp, ← abs_mul]
  congr 1
  rw [abs_of_pos hp]
  field_simp

/-- A continuous `2π`-periodic function descends continuously to `AddCircle (2π)`. -/
lemma lift_cont_STR02938 {f : ℝ → ℝ} (hc : Continuous f) (hp : Function.Periodic f (2 * π)) :
    Continuous (hp.lift : AddCircle (2 * π) → ℝ) := by
  refine continuous_coinduced_dom.mpr ?_
  convert hc using 1
  funext t
  exact hp.lift_coe t

/-- Arzelà–Ascoli for uniformly bounded, uniformly equicontinuous (for the circular distance)
continuous `2π`-periodic functions: a strictly increasing subsequence converges uniformly on `ℝ` to a
continuous `2π`-periodic function. -/
lemma arzela_ascoli_circle_STR02938 {f : ℕ → ℝ → ℝ} {M : ℝ}
    (hc : ∀ n, Continuous (f n)) (hp : ∀ n, Function.Periodic (f n) (2 * π))
    (hb : ∀ n t, |f n t| ≤ M)
    (heq : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ n t s, circDist_STR02937 t s < δ → |f n t - f n s| < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℝ → ℝ, Continuous G ∧ Function.Periodic G (2 * π) ∧
      TendstoUniformly (fun n => f (φ n)) G atTop := by
  have : Fact (0 < 2 * π) := ⟨by positivity⟩
  let L : ℕ → (AddCircle (2 * π) →ᵇ ℝ) := fun n =>
    BoundedContinuousFunction.mkOfCompact ⟨(hp n).lift, lift_cont_STR02938 (hc n) (hp n)⟩
  have hL : ∀ n (t : ℝ), L n (t : AddCircle (2 * π)) = f n t := fun n t => (hp n).lift_coe t
  have hsurj : ∀ x : AddCircle (2 * π), ∃ t : ℝ, (t : AddCircle (2 * π)) = x :=
    fun x => QuotientAddGroup.mk_surjective x
  have hEq : Equicontinuous (((↑) : Set.range L → AddCircle (2 * π) → ℝ)) := by
    apply UniformEquicontinuous.equicontinuous
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := heq ε hε
    refine ⟨δ, hδ, ?_⟩
    rintro x y hxy ⟨_, ⟨n, rfl⟩⟩
    obtain ⟨t, rfl⟩ := hsurj x
    obtain ⟨s, rfl⟩ := hsurj y
    rw [dist_coe_circle_STR02938] at hxy
    show dist (L n _) (L n _) < ε
    rw [hL, hL, Real.dist_eq]
    exact hδ' n t s hxy
  have hcomp := BoundedContinuousFunction.arzela_ascoli (Icc (-M) M) isCompact_Icc (Set.range L)
    (by
      rintro F x ⟨n, rfl⟩
      obtain ⟨t, rfl⟩ := hsurj x
      rw [hL]
      exact abs_le.1 (hb n t)) hEq
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩)
  have hcoe : Continuous (fun t : ℝ => (t : AddCircle (2 * π))) := continuous_quotient_mk'
  refine ⟨φ, hφ, fun t => a (t : AddCircle (2 * π)), a.continuous.comp hcoe, ?_, ?_⟩
  · intro t
    simp only [AddCircle.coe_add, AddCircle.coe_period, add_zero]
  · have h1 := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1 hlim).comp
      (fun t : ℝ => (t : AddCircle (2 * π)))
    have e : (fun n => f (φ n)) =
        fun n => ⇑((L ∘ φ) n) ∘ fun t : ℝ => (t : AddCircle (2 * π)) := by
      funext n t
      exact (hL _ t).symm
    rw [e]
    exact h1

/-- A continuous `2π`-periodic function almost everywhere equal on `(0, 2π]` to a nonnegative function is
nonnegative everywhere. -/
lemma rep_nonneg_STR02938 {F g : ℝ → ℝ} (hFc : Continuous F) (hFp : Function.Periodic F (2 * π))
    (hg0 : ∀ t, 0 ≤ g t) (hFg : F =ᵐ[volume.restrict (Ioc 0 (2 * π))] g) : ∀ t, 0 ≤ F t := by
  have hT : (0 : ℝ) < 2 * π := by positivity
  have hae : ∀ᵐ t ∂volume, t ∈ Ioc 0 (2 * π) → F t = g t :=
    (ae_restrict_iff' measurableSet_Ioc).1 hFg
  have hIoo : ∀ t ∈ Ioo 0 (2 * π), 0 ≤ F t := by
    by_contra hcon
    simp only [not_forall, not_le] at hcon
    obtain ⟨t0, ht0, hneg⟩ := hcon
    have hopen : IsOpen (Ioo 0 (2 * π) ∩ F ⁻¹' Iio 0) :=
      isOpen_Ioo.inter (isOpen_Iio.preimage hFc)
    have hnull : volume (Ioo 0 (2 * π) ∩ F ⁻¹' Iio 0) = 0 := by
      refine measure_eq_zero_iff_ae_notMem.2 (hae.mono ?_)
      rintro t ht ⟨hI, hneg'⟩
      have := ht (Ioo_subset_Ioc_self hI)
      have h2 : F t < 0 := hneg'
      linarith [hg0 t]
    have hemp := (hopen.measure_eq_zero_iff volume).1 hnull
    have hmem : t0 ∈ Ioo 0 (2 * π) ∩ F ⁻¹' Iio 0 := ⟨ht0, hneg⟩
    rw [hemp] at hmem
    exact hmem
  have hIcc : ∀ t ∈ Icc 0 (2 * π), 0 ≤ F t := by
    have hcl : IsClosed {t | 0 ≤ F t} := isClosed_le continuous_const hFc
    have hsub : Icc 0 (2 * π) ⊆ {t | 0 ≤ F t} := by
      rw [← closure_Ioo hT.ne]
      exact closure_minimal hIoo hcl
    exact fun t ht => hsub ht
  intro t
  have hmem := toIocMod_mem_Ioc hT 0 t
  rw [zero_add] at hmem
  have h1 := hIcc (toIocMod hT 0 t) (Ioc_subset_Icc_self hmem)
  have h2 : F (toIocMod hT 0 t) = F t := by
    rw [toIocMod]
    exact hFp.sub_zsmul_eq _
  rwa [h2] at h1

/-- The weighted energy of a function is nonnegative. -/
lemma energy_nonneg_STR02938 (h : ℝ) (w : ℝ → ℝ) :
    0 ≤ normInt_STR02904 (fun t => w t ^ 2 * qT_STR02904 h t) := by
  have hT : (0 : ℝ) < 2 * π := by positivity
  exact mul_nonneg (inv_nonneg.2 hT.le) (intervalIntegral.integral_nonneg_of_forall hT.le
    (fun t => mul_nonneg (sq_nonneg _) (qT_pos_STR02904 h t).le))

/-- A bounded real sequence has a strictly increasing subsequence converging to its liminf. -/
lemma liminf_subseq_STR02938 {E : ℕ → ℝ} {B : ℝ} (h0 : ∀ n, 0 ≤ E n) (hB : ∀ n, E n ≤ B) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ Tendsto (fun n => E (τ n)) atTop (𝓝 (liminf E atTop)) := by
  have hbd : IsBoundedUnder (· ≥ ·) atTop E := isBoundedUnder_of ⟨0, h0⟩
  have hco : IsCoboundedUnder (· ≥ ·) atTop E := isCoboundedUnder_ge_of_le atTop hB
  exact (MapClusterPt.liminf (hc := hco) (hb := hbd)).tendsto_subseq

/-- **STR029.38.** Fix `|h| ≤ 1/1000` and a sequence of STR029.06 data `(g n, g' n, E n, H n)` with
continuous `2π`-periodic representatives `F n` of `g n`. Then a strictly increasing subsequence `σ` of the
representatives converges uniformly on `ℝ` to a continuous `2π`-periodic `G ≥ 0` with
`∫ G² q_h dm = 1`, and the energies along `σ` converge to the liminf of the original energies. -/
theorem str029_38_uniform_subsequence_preserving_energy_liminf
    {h : ℝ} (hh : |h| ≤ 1 / 1000) {g g' F : ℕ → ℝ → ℝ} {E H : ℕ → ℝ} {K A : ℝ}
    (hg0 : ∀ n t, 0 ≤ g n t)
    (hH1 : ∀ n, IsPeriodicWeakDerivative_STR02933 (g n) (g' n))
    (hnorm : ∀ n, normInt_STR02904 (fun t => g n t ^ 2 * qT_STR02904 h t) = 1)
    (hE : ∀ n, E n = normInt_STR02904 (fun t => g' n t ^ 2 * qT_STR02904 h t))
    (hH : ∀ n, H n = normInt_STR02904
      (fun t => g n t ^ 2 * Real.log (g n t ^ 2) * qT_STR02904 h t))
    (hHpos : ∀ n, 0 < H n) (hquot : ∀ n, 4 * E n / (2 * H n) ≤ 2)
    (hK : K = 8 * π ^ 2 * Real.exp (1 / 500)) (hA : A = Real.log (K + 2))
    (hFc : ∀ n, Continuous (F n)) (hFp : ∀ n, Function.Periodic (F n) (2 * π))
    (hFg : ∀ n, F n =ᵐ[volume.restrict (Ioc 0 (2 * π))] g n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ G : ℝ → ℝ, Continuous G ∧ Function.Periodic G (2 * π) ∧
      (∀ t, 0 ≤ G t) ∧ normInt_STR02904 (fun t => G t ^ 2 * qT_STR02904 h t) = 1 ∧
      TendstoUniformly (fun n => F (σ n)) G atTop ∧
      Tendsto (fun n => E (σ n)) atTop (𝓝 (liminf E atTop)) := by
  have hT : (0 : ℝ) < 2 * π := by positivity
  have hmono : volume.restrict (Ioo 0 (2 * π)) ≤ volume.restrict (Ioc 0 (2 * π)) :=
    Measure.restrict_mono Ioo_subset_Ioc_self le_rfl
  -- energy bounds from STR029.06
  have hEA : ∀ n, E n ≤ 4 * (A + 1) := fun n =>
    (str029_06_information_bound_low_quotients hh (hg0 n) (hH1 n) (hnorm n) (hE n) (hH n)
      (hHpos n) (hquot n) hK hA).1
  have hE0 : ∀ n, 0 ≤ E n := fun n => by
    rw [hE n]
    exact energy_nonneg_STR02938 h (g' n)
  -- common sup bound
  have hbd : ∀ n t, |F n t| ≤ 1 + 2 * π * Real.exp (1 / 1000) * Real.sqrt (4 * (A + 1)) := by
    intro n t
    have h1 := str029_06_information_bound_low_quotients_unique hh (hg0 n) (hH1 n) (hnorm n)
      (hE n) (hH n) (hHpos n) (hquot n) hK hA (hFc n) (hFp n) (hFg n) t
    have h2 : Real.sqrt (E n) ≤ Real.sqrt (4 * (A + 1)) := Real.sqrt_le_sqrt (hEA n)
    have h3 : 0 ≤ 2 * π * Real.exp (1 / 1000) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  -- uniform equicontinuity from STR029.37
  have heq := str029_37_uniform_equicontinuity_low_quotient_square_roots_equicontinuous hh hK hA
  -- subsequence preserving the energy liminf
  obtain ⟨τ, hτ, hτE⟩ := liminf_subseq_STR02938 hE0 hEA
  -- Arzelà–Ascoli along that subsequence
  obtain ⟨φ, hφ, G, hGc, hGp, hGu⟩ := arzela_ascoli_circle_STR02938
    (f := fun n => F (τ n)) (fun n => hFc (τ n)) (fun n => hFp (τ n)) (fun n t => hbd (τ n) t)
    (by
      intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ := heq ε hε
      exact ⟨δ, hδ, fun n t s hts =>
        hδ' (hg0 (τ n)) (hH1 (τ n)) (hnorm (τ n)) (hE (τ n)) (hH (τ n)) (hHpos (τ n))
          (hquot (τ n)) (hFc (τ n)) (hFp (τ n)) (hFg (τ n)) t s hts⟩)
  have hGu' : TendstoUniformly (fun n => F (τ (φ n))) G atTop := hGu
  refine ⟨fun n => τ (φ n), hτ.comp hφ, G, hGc, hGp, ?_, ?_, hGu', hτE.comp hφ.tendsto_atTop⟩
  · -- nonnegativity passes to the pointwise limit
    intro t
    exact ge_of_tendsto' (hGu'.tendsto_at t)
      (fun n => rep_nonneg_STR02938 (hFc _) (hFp _) (hg0 _) (hFg _) t)
  · -- normalization passes to the limit by dominated convergence
    have hq : ∀ t, qT_STR02904 h t ≤ Real.exp (2 * |h|) := fun t =>
      (qT_bounds_STR02904 h t).2
    have hn : ∀ n, normInt_STR02904 (fun t => F (τ (φ n)) t ^ 2 * qT_STR02904 h t) = 1 := by
      intro n
      rw [← hnorm (τ (φ n))]
      refine normInt_congr_ae_STR02906 ?_
      filter_upwards [(hFg (τ (φ n))).filter_mono (ae_mono hmono)] with t ht
      rw [ht]
    have hlim : Tendsto (fun n => normInt_STR02904 (fun t => F (τ (φ n)) t ^ 2 * qT_STR02904 h t))
        atTop (𝓝 (normInt_STR02904 (fun t => G t ^ 2 * qT_STR02904 h t))) := by
      unfold normInt_STR02904
      refine Tendsto.const_mul _ ?_
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun _ => (1 + 2 * π * Real.exp (1 / 1000) * Real.sqrt (4 * (A + 1))) ^ 2 *
          Real.exp (2 * |h|)) ?_ ?_ intervalIntegrable_const ?_
      · exact Eventually.of_forall fun n =>
          (((hFc (τ (φ n))).pow 2).mul (continuous_qT_STR02904 h)).aestronglyMeasurable
      · refine Eventually.of_forall fun n => Eventually.of_forall fun t _ => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (qT_pos_STR02904 h t)]
        exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hbd _ t) 2) (hq t)
          (qT_pos_STR02904 h t).le (sq_nonneg _)
      · refine Eventually.of_forall fun t _ => ?_
        exact ((hGu'.tendsto_at t).pow 2).mul_const _
    have hlim1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
        (𝓝 (normInt_STR02904 (fun t => G t ^ 2 * qT_STR02904 h t))) :=
      hlim.congr (fun n => hn n)
    exact tendsto_nhds_unique hlim1 tendsto_const_nhds

/-- The conclusion of `str029_38_uniform_subsequence_preserving_energy_liminf` with the continuous
periodic representatives chosen by STR029.06 (EX049.32) instead of supplied. -/
theorem str029_38_uniform_subsequence_preserving_energy_liminf_exists_representatives
    {h : ℝ} (hh : |h| ≤ 1 / 1000) {g g' : ℕ → ℝ → ℝ} {E H : ℕ → ℝ} {K A : ℝ}
    (hg0 : ∀ n t, 0 ≤ g n t)
    (hH1 : ∀ n, IsPeriodicWeakDerivative_STR02933 (g n) (g' n))
    (hnorm : ∀ n, normInt_STR02904 (fun t => g n t ^ 2 * qT_STR02904 h t) = 1)
    (hE : ∀ n, E n = normInt_STR02904 (fun t => g' n t ^ 2 * qT_STR02904 h t))
    (hH : ∀ n, H n = normInt_STR02904
      (fun t => g n t ^ 2 * Real.log (g n t ^ 2) * qT_STR02904 h t))
    (hHpos : ∀ n, 0 < H n) (hquot : ∀ n, 4 * E n / (2 * H n) ≤ 2)
    (hK : K = 8 * π ^ 2 * Real.exp (1 / 500)) (hA : A = Real.log (K + 2)) :
    ∃ F : ℕ → ℝ → ℝ, (∀ n, Continuous (F n) ∧ Function.Periodic (F n) (2 * π) ∧
        F n =ᵐ[volume.restrict (Ioc 0 (2 * π))] g n) ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ G : ℝ → ℝ, Continuous G ∧ Function.Periodic G (2 * π) ∧
        (∀ t, 0 ≤ G t) ∧ normInt_STR02904 (fun t => G t ^ 2 * qT_STR02904 h t) = 1 ∧
        TendstoUniformly (fun n => F (σ n)) G atTop ∧
        Tendsto (fun n => E (σ n)) atTop (𝓝 (liminf E atTop)) := by
  have hrep : ∀ n, ∃ F : ℝ → ℝ, Continuous F ∧ Function.Periodic F (2 * π) ∧
      F =ᵐ[volume.restrict (Ioc 0 (2 * π))] g n := fun n => by
    obtain ⟨-, F, hFc, hFp, -, hFg, -⟩ :=
      str029_06_information_bound_low_quotients hh (hg0 n) (hH1 n) (hnorm n) (hE n) (hH n)
        (hHpos n) (hquot n) hK hA
    exact ⟨F, hFc, hFp, hFg⟩
  choose F hFc hFp hFg using hrep
  exact ⟨F, fun n => ⟨hFc n, hFp n, hFg n⟩,
    str029_38_uniform_subsequence_preserving_energy_liminf hh hg0 hH1 hnorm hE hH hHpos hquot hK hA
      hFc hFp hFg⟩

end DGPS.Frontier.STR029
