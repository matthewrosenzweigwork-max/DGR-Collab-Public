import DGPS.Frontier.LIP032.T11

/-!
# LIP032.12: Conditional contractibility

Task id and title: LIP032.12, "Conditional contractibility" (node LIP032, contractibility of the
minimizer set; leaf formalization, conditional on Task 29 and on the positive-rate flow context of
LIP031, inherited through LIP032.11).

## Provides
* `DGPS.Frontier.LIP032.lip032_12_conditional_contractibility` : MAIN. Under the exact positive-rate
  context of LIP032.11, for a fixed minimizer `μ` and bounds `|A.V| ≤ M_V`, `|A.W| ≤ M_W`, the
  minimizer set `minimizerSet_LIP03225 A` is contractible in the sense of Mathlib's
  `ContractibleSpace`.
* `DGPS.Frontier.LIP032.homotopic_id_const_LIP03212` : helper. A continuous map
  `H : X × [0,1] → X` with `H (x, 0) = x` and `H (x, 1) = c` for every `x` yields a homotopy from
  the identity of `X` to the constant map at `c`, with the interval coordinate placed first.

## R5 notes
* Inherited hypotheses. The binders `A`, `drift`, `G`, `B`, `g`, `β`, `hMF`, `hV`, `hWB`, `r`, `hr`,
  `hrate`, `μ`, `hμ`, `M_V`, `M_W`, `hVb`, `hWb` are exactly those of LIP032.11 (and hence of
  LIP032.09). Nothing is added and nothing is removed. In particular the positive-rate data `hr` and
  `hrate` are inherited, so the unit is not stated in the unconditional reading, which is false
  (FD-001). The frozen unconditional sentence "S is contractible" is neither claimed nor
  strengthened here.
* Omitted binders. The witness of `LipschitzData A` and the hypothesis `0 < d` that appear in
  Section 2.1 of the node are not binders here, because no declaration in the chain (LIP032.11 and
  its prerequisites, LIP032.30 and LIP032.32 among them) uses them. This follows the convention of
  those units.
* Conclusion. "S is contractible" is read as Mathlib's class `ContractibleSpace`
  (`hequiv_unit'` : `Nonempty (X ≃ₕ Unit)`). By `contractible_iff_id_nullhomotopic` this is the
  nullhomotopy of the identity, which is the form used in LIB12.
* Nonemptiness. The frozen clause "nonempty" is not a separate hypothesis. The fixed minimizer
  `μ` with `hμ` witnesses that `minimizerSet_LIP03225 A` is nonempty, and the constant map is the
  constant at the element `⟨μ, hμ⟩`.
* Topology. The space `S` carries the weak subspace topology of LIP032.25, through the abbreviation
  `minimizerSet_LIP03225`. No other topology is used.
* Homotopy carrier. Mathlib's `ContinuousMap.Homotopy` takes the interval coordinate first. The
  homotopy is `(s, ν) ↦ H (ν, s)` with `H` the map of LIP032.11. This factor swap is a relabelling:
  the endpoint at `s = 0` is the identity by `H (ν, 0) = ν`, and the endpoint at `s = 1` is the
  constant map at `μ` by `H (ν, 1) = μ`.
* Choice. The homotopy is not unique. It is taken from the existential of LIP032.11 (the limit map
  `R` and the map `H`), and the conclusion is existential in the same way.
* Not stated. The identity `H (μ, s) = μ` mentioned in the specification's proof is not part of
  the conclusion, since the statement does not list it.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- **LIP032.12 helper.** Homotopy from the identity to a constant map. A continuous map
`H : X × [0,1] → X` with `H (x, 0) = x` and `H (x, 1) = c` for every `x` gives a homotopy
`[0,1] × X → X`, `(s, x) ↦ H (x, s)`, from `id` to the constant map at `c`. -/
theorem homotopic_id_const_LIP03212 {X : Type*} [TopologicalSpace X] (c : X)
    (H : X × Set.Icc (0 : ℝ) 1 → X) (hH : Continuous H)
    (h0 : ∀ x : X, H (x, ⟨0, by norm_num⟩) = x)
    (h1 : ∀ x : X, H (x, ⟨1, by norm_num⟩) = c) :
    (ContinuousMap.id X).Homotopic (ContinuousMap.const X c) := by
  have hcont : Continuous (fun p : unitInterval × X =>
      (p.2, (⟨(p.1 : ℝ), p.1.2⟩ : Set.Icc (0 : ℝ) 1))) :=
    continuous_snd.prodMk
      ((continuous_subtype_val.comp continuous_fst).subtype_mk fun p => p.1.2)
  exact Nonempty.intro
    { toFun := fun p => H (p.2, ⟨(p.1 : ℝ), p.1.2⟩)
      continuous_toFun := hH.comp hcont
      map_zero_left := fun x => h0 x
      map_one_left := fun x => h1 x }

/-- **LIP032.12.** Conditional contractibility. Under the positive-rate context of LIP032.11, the
minimizer set `S` is contractible, in the sense of Mathlib's `ContractibleSpace`. The fixed
minimizer `μ` supplies the constant endpoint and the nonemptiness. -/
theorem lip032_12_conditional_contractibility (A : InteractionData d)
    (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β)
    (hV : IsWeakGradient A.V G)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ⊤ (fun x => A.W x y) (fun x => B x y))
    {r : ℝ} (hr : 0 < r) (hrate : ENNReal.ofReal r < scalarRate A drift)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (M_V M_W : ℝ) (hVb : ∀ x, |A.V x| ≤ M_V) (hWb : ∀ x y, |A.W x y| ≤ M_W) :
    ContractibleSpace (minimizerSet_LIP03225 A) := by
  obtain ⟨_, H, -, hH, h0, h1⟩ :=
    lip032_11_homotopy_minimizing_set A drift hMF hV hWB hr hrate μ hμ M_V M_W hVb hWb
  exact (contractible_iff_id_nullhomotopic (minimizerSet_LIP03225 A)).2
    ⟨⟨μ, hμ⟩, homotopic_id_const_LIP03212 ⟨μ, hμ⟩ H hH h0 h1⟩

end DGPS.Frontier.LIP032
