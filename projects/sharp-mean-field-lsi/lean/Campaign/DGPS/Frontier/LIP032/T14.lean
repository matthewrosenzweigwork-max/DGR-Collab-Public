import DGPS.Frontier.LIP032.T43
import DGPS.Frontier.LIP032.T46
import DGPS.Frontier.LIP032.T47

/-!
# LIP032.14: Failure of connectedness and contraction

Task id and title: LIP032.14, "Failure of connectedness and contraction" (node LIP032,
contractibility of the minimizer set; leaf formalization on the explicit counterexample model
`A_*`, which assumes no positive-rate, flow or LIP031 hypothesis).

## Provides
* `DGPS.Frontier.LIP032.momentOnS_LIP03214` : the cosine moment `M(ν) = ∫ γ dν` of a point `ν` of
  the minimizing set `S_*`, as a real function on the subtype `↥minimizerSetStar_LIP03244`.
* `DGPS.Frontier.LIP032.sPlus_LIP03214` : the subset `S_{*,+} = {ν ∈ S_* | 0 < M(ν)}`.
* `DGPS.Frontier.LIP032.sMinus_LIP03214` : the subset `S_{*,-} = {ν ∈ S_* | M(ν) < 0}`.
* `DGPS.Frontier.LIP032.lip032_14_failure_connectedness_contraction_separation` : the sets
  `S_{*,+}` and `S_{*,-}` are nonempty, disjoint, relatively open and relatively closed in `S_*`,
  and their union is `S_*`.
* `DGPS.Frontier.LIP032.lip032_14_failure_connectedness_contraction_no_homotopy` : for every
  `μ_* ∈ S_*` there is no continuous `H_* : S_* × [0,1] → S_*` with `H_*(ν, 0) = ν` and
  `H_*(ν, 1) = μ_*` for every `ν ∈ S_*`.
* `DGPS.Frontier.LIP032.lip032_14_failure_connectedness_contraction` : MAIN. The conjunction of the
  separation statement and the no-homotopy statement.

## R5 notes
* Scope. The statement concerns only the explicit model `A_* = interactionDataStar_LIP03241` of
  LIP032.41 on `𝕋¹ = Torus 1`: `γ(x) = cos(2πx)`, `V_* = -4γ²`, `W_*(x, y) = 4(γ x - γ y)²`. It is
  the counterexample task of the node, not the general contractibility claim of the frozen LIP032
  text. It shows that the unconditional reading of that claim fails for `A_*`. It does not prove the
  conditional branch and does not decide the general statement.
* No hypothesis. The LIP031 header (`hr`, `hrate`, `hu`) and the positive-rate, flow, mean-field and
  interaction-gradient data are not referenced. No hypothesis is added to the specification.
* `S_*` is `minimizerSetStar_LIP03244`, the probability measures `ν` on `𝕋¹` with
  `freeEnergy A_* ν = freeEnergyMinimum A_*`. The free energy is `EReal`-valued, and
  `freeEnergyMinimum` is its infimum over all probability measures. Nonemptiness of `S_*` and the
  finiteness of the minimum are taken from LIP017 through LIP032.43; they are not re-proved here.
* "Relatively open" and "relatively closed" are `IsOpen` and `IsClosed` in the subtype
  `↥minimizerSetStar_LIP03244`, with the subspace topology of the weak topology on
  `ProbabilityMeasure (Torus 1)`. "Union is `S_*`" is read as `sPlus ∪ sMinus = Set.univ` in that
  subtype.
* The moment `M(ν)` is `momentStar_LIP03241` applied to the underlying measure of `ν`, that is
  `∫ γ dν`. The signs are strict: `0 < M` and `M < 0`. The cover of `S_*` uses `M(ν) ≠ 0` on `S_*`
  (LIP032.43).
* The homotopy `H_*` is a function on the product of the subtype and `unitInterval` (Mathlib's
  `[0,1]`), continuous for the product topology and valued in the subtype. The endpoint identities
  are equalities in the subtype, quantified over every `ν ∈ S_*`. The no-homotopy claim is the
  literal negation of the existence of such `H_*`, quantified over every `μ_* ∈ S_*`. It is not
  phrased with Mathlib's `ContractibleSpace`, and the equivalence with contractibility is not
  asserted here.
* The failure of connectedness is stated as the explicit separation into two nonempty relatively
  clopen pieces, not as `¬ IsConnected S_*` or `¬ ConnectedSpace`.
* Proof route. The statement is the composition of LIP032.43 (nonzero moment on `S_*`), LIP032.46
  (the translation `T(x) = x + 1/2` maps `S_*` to itself and reverses the moment) and LIP032.47
  (clopen separation, and the real intermediate value argument along `s ↦ M(H(T_# μ_*, s))`, which
  uses only one fixed starting minimizer). This file adds no new mathematics. It states the
  LIP032.14 claims in full and derives them from the LIP032.47 results.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

/-- The cosine moment `M(ν) = ∫ γ dν` of a point `ν` of the minimizing set `S_*` of `A_*`. -/
noncomputable def momentOnS_LIP03214 (ν : ↥minimizerSetStar_LIP03244) : ℝ :=
  momentStar_LIP03241 ((ν : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))

/-- The subset `S_{*,+} = {ν ∈ S_* | 0 < M(ν)}` of the minimizing set. -/
noncomputable def sPlus_LIP03214 : Set ↥minimizerSetStar_LIP03244 :=
  {ν | 0 < momentOnS_LIP03214 ν}

/-- The subset `S_{*,-} = {ν ∈ S_* | M(ν) < 0}` of the minimizing set. -/
noncomputable def sMinus_LIP03214 : Set ↥minimizerSetStar_LIP03244 :=
  {ν | momentOnS_LIP03214 ν < 0}

/-- **LIP032.14, separation.** The sets `S_{*,+}` and `S_{*,-}` are nonempty, disjoint, relatively
open and relatively closed in `S_*`, and their union is `S_*`. -/
theorem lip032_14_failure_connectedness_contraction_separation :
    sPlus_LIP03214.Nonempty ∧ sMinus_LIP03214.Nonempty ∧
      Disjoint sPlus_LIP03214 sMinus_LIP03214 ∧
      IsOpen sPlus_LIP03214 ∧ IsClosed sPlus_LIP03214 ∧
      IsOpen sMinus_LIP03214 ∧ IsClosed sMinus_LIP03214 ∧
      sPlus_LIP03214 ∪ sMinus_LIP03214 = Set.univ := by
  have h := lip032_47_no_contraction_real_intermediate_value_argument_separation
  exact ⟨h.1, h.2.1, h.2.2.1, isOpen_posSet_LIP03247, isClosed_posSet_LIP03247,
    isOpen_negSet_LIP03247, isClosed_negSet_LIP03247, h.2.2.2.2.2⟩

/-- **LIP032.14, no homotopy.** For every `μ_* ∈ S_*` there is no continuous `H_* : S_* × [0,1] →
S_*` with `H_*(ν, 0) = ν` and `H_*(ν, 1) = μ_*` for every `ν ∈ S_*`. -/
theorem lip032_14_failure_connectedness_contraction_no_homotopy
    (μ : ↥minimizerSetStar_LIP03244) :
    ¬ ∃ H : ↥minimizerSetStar_LIP03244 × unitInterval → ↥minimizerSetStar_LIP03244,
      Continuous H ∧ (∀ ν : ↥minimizerSetStar_LIP03244, H (ν, 0) = ν) ∧
        ∀ ν : ↥minimizerSetStar_LIP03244, H (ν, 1) = μ :=
  lip032_47_no_contraction_real_intermediate_value_argument_no_homotopy μ

/-- **LIP032.14.** Failure of connectedness and contraction for the explicit model `A_*`: the
minimizing set `S_*` splits into the nonempty, disjoint, relatively open and closed sets `S_{*,+}`
and `S_{*,-}`, whose union is `S_*`; and for every `μ_* ∈ S_*` there is no continuous
`H_* : S_* × [0,1] → S_*` with `H_*(ν, 0) = ν` and `H_*(ν, 1) = μ_*` for every `ν ∈ S_*`. -/
theorem lip032_14_failure_connectedness_contraction :
    (sPlus_LIP03214.Nonempty ∧ sMinus_LIP03214.Nonempty ∧
      Disjoint sPlus_LIP03214 sMinus_LIP03214 ∧
      IsOpen sPlus_LIP03214 ∧ IsClosed sPlus_LIP03214 ∧
      IsOpen sMinus_LIP03214 ∧ IsClosed sMinus_LIP03214 ∧
      sPlus_LIP03214 ∪ sMinus_LIP03214 = Set.univ) ∧
    ∀ μ : ↥minimizerSetStar_LIP03244,
      ¬ ∃ H : ↥minimizerSetStar_LIP03244 × unitInterval → ↥minimizerSetStar_LIP03244,
        Continuous H ∧ (∀ ν : ↥minimizerSetStar_LIP03244, H (ν, 0) = ν) ∧
          ∀ ν : ↥minimizerSetStar_LIP03244, H (ν, 1) = μ :=
  ⟨lip032_14_failure_connectedness_contraction_separation,
    lip032_14_failure_connectedness_contraction_no_homotopy⟩

end DGPS.Frontier.LIP032
