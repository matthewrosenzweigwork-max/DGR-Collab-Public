import DGRHS.Original.SourcePathTightness
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.LinearMap

/-! RECORDS-ONLY / UNCOMPILED Claude candidate (chain `chaos`, PATH-01,
2026-10-04). No compiler has evaluated this file.

Concrete instance of rem:pathSpaceCLT in the separable continuous-path space
`C([0,T], E)`, `E` a complete separable normed space (e.g. the negative-regularity
Hilbert space carrying the fluctuation fields, TeX 3998). The tests are pairs
(time, continuous linear functional); a countable dense set of times and a
countable point-separating family of functionals is the concrete
measure-determining class. The separation of PATHS is PROVED from these two
premises by continuity; the measure-determining property then follows from
`sourcePath_generate_of_polish_separating`.

Elaboration risk (isolated to this file): the `PolishSpace C(Icc 0 T, E)` instance
is obtained by `inferInstance` from pinned instances
(`ContinuousMap.instSeparableSpace`, the compact-domain metric on `C(_, _)`,
completeness, `MetricSpace.toIsCompletelyMetrizableSpace`, and the Polish instance
in Topology/MetricSpace/Polish.lean). If instance search fails, the main file
`SourcePathTightness.lean` is unaffected. -/
noncomputable section
open MeasureTheory Filter Topology Set
namespace DGRHS.Original

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E]

/-- Time/test evaluation of a continuous path. -/
def sourceContinuousPathEval (T : ℝ) {Q J : Type*}
    (τ : Q → Icc (0:ℝ) T) (ℓ : J → E →L[ℝ] ℝ) :
    Q × J → C(Icc (0:ℝ) T, E) → ℝ :=
  fun p ω => ℓ p.2 (ω (τ p.1))

lemma sourceContinuousPathEval_continuous (T : ℝ) {Q J : Type*}
    (τ : Q → Icc (0:ℝ) T) (ℓ : J → E →L[ℝ] ℝ) (p : Q × J) :
    Continuous (sourceContinuousPathEval T τ ℓ p) := by
  unfold sourceContinuousPathEval
  exact (ℓ p.2).continuous.comp (continuous_eval_const (τ p.1))

/-- Dense times and point-separating functionals separate continuous paths. -/
lemma sourceContinuousPathEval_separates (T : ℝ) {Q J : Type*}
    (τ : Q → Icc (0:ℝ) T) (hτ : DenseRange τ) (ℓ : J → E →L[ℝ] ℝ)
    (hℓ : ∀ x y : E, (∀ j, ℓ j x = ℓ j y) → x = y)
    (ω ω' : C(Icc (0:ℝ) T, E))
    (h : ∀ p, sourceContinuousPathEval T τ ℓ p ω = sourceContinuousPathEval T τ ℓ p ω') :
    ω = ω' := by
  have hpt : ∀ q, ω (τ q) = ω' (τ q) := fun q => hℓ _ _ (fun j => h (q, j))
  have hfun : (ω : Icc (0:ℝ) T → E) = ω' := by
    apply Continuous.ext_on hτ ω.continuous ω'.continuous
    rintro _ ⟨q, rfl⟩
    exact hpt q
  ext s
  exact congrFun hfun s

/-- **Path-law convergence in `C([0,T],E)`** from source tightness, Gaussian
finite-dimensional limits and Gaussian path regularity (`G`), with the
measure-determining property proved from countable dense times and a countable
separating family of functionals. -/
theorem sourceContinuousPath_tendsto_of_isTight (T : ℝ) {Q J : Type*}
    [Countable Q] [Countable J]
    [MeasurableSpace C(Icc (0:ℝ) T, E)] [BorelSpace C(Icc (0:ℝ) T, E)]
    (τ : Q → Icc (0:ℝ) T) (hτ : DenseRange τ) (ℓ : J → E →L[ℝ] ℝ)
    (hℓ : ∀ x y : E, (∀ j, ℓ j x = ℓ j y) → x = y)
    (μ : ℕ → ProbabilityMeasure C(Icc (0:ℝ) T, E))
    (htight : IsTightMeasureSet (Set.range fun N => (μ N : Measure C(Icc (0:ℝ) T, E))))
    (γ : ∀ I : Finset (Q × J), ProbabilityMeasure (I → ℝ))
    (hfdd : ∀ I : Finset (Q × J),
      Tendsto (fun N => (μ N).map (sourcePathFdd (sourceContinuousPathEval T τ ℓ) I))
        atTop (𝓝 (γ I)))
    (G : ProbabilityMeasure C(Icc (0:ℝ) T, E))
    (hG : ∀ I, G.map (sourcePathFdd (sourceContinuousPathEval T τ ℓ) I) = γ I) :
    Tendsto μ atTop (𝓝 G) := by
  haveI : PolishSpace C(Icc (0:ℝ) T, E) := inferInstance
  exact sourcePath_tendsto_of_isTight_polish (sourceContinuousPathEval T τ ℓ)
    (sourceContinuousPathEval_continuous T τ ℓ)
    (sourceContinuousPathEval_separates T τ hτ ℓ hℓ) μ htight γ hfdd G hG

end DGRHS.Original
