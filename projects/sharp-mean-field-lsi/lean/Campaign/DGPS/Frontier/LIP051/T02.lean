import DGPS.Frontier.LIP051.T03
import DGPS.Frontier.LIP051.T25
import DGPS.Frontier.LIP051.T26

/-!
# LIP051.02: Centered measurable feature representatives

Task id `LIP051.02`, title "Centered measurable feature representatives" (node LIP051,
"Joint Gaussian and quadratic fluctuation limit", verification V1, dispatch tier 4).
Source: the `LIP051.02` statement and proof in the node document for LIP051.

Let `μ` be a probability measure and `e` a real Hilbert basis of `L²(μ)` indexed by `ℕ`, with
`e 0 = 1` as an `L²` class. There are measurable representatives `f j` of the classes `e j` with
`∫ f i * f j dμ = δ_ij` for all `i j`, each `f j` in `L²(μ)`, and `∫ f j dμ = 0` for `j ≥ 1`.
Any family `g` of measurable representatives that agrees with `f` almost everywhere gives, under
each reference law `Q_N = μ^N`, equality almost everywhere of every sampled feature array. It
also gives equality almost everywhere, and equality of laws, of every joint map consisting of a
measurable function of that array together with the energy `U_N`, which does not depend on the
features and is unchanged. The energy is measurable when its kernel is measurable.

## Provides

* `DGPS.Frontier.LIP051.featureArrayLIP05102`: the sampled feature array
  `ω ↦ (f (j k) (ω l))_{k,l}` on the particle space `Fin N → α`.
* `DGPS.Frontier.LIP051.energyLIP05102`: the energy `U_N(ω) = (2N)⁻¹ ∑_{l,k} K(ω l, ω k)` of a
  kernel `K` on `α`.
* `DGPS.Frontier.LIP051.measurable_energy_LIP05102`: helper; the energy `U_N` is measurable when
  the kernel is measurable on the product.
* `DGPS.Frontier.LIP051.lip051_02_centered_measurable_feature_representatives`: the main statement
  (measurability of `U_N` under a measurable kernel, existence of centered orthonormal measurable
  representatives, and invariance of the sampled arrays, their laws and their joint laws with
  `U_N` under almost-everywhere replacement of the representatives).
* `DGPS.Frontier.LIP051.lip051_02_centered_measurable_feature_representatives_energy_torus`: for
  the centered kernel `K = centeredKernelOf_LIP05103 μ W` of a bounded continuous symmetric `W` on
  the torus, the energy `U_N` built from `K` is measurable for every `N` (the kernel measurability
  is LIP051.03).

## R5 notes

1. Ambient space. The statement is for an arbitrary probability measure `μ` on an arbitrary
   measurable space `α`, with an arbitrary Hilbert basis of `L²(μ)`. No `Spec`, `Aux`, `KData`,
   Gaussian object or mode restriction is involved. The identification of `S.mu`, `S.e` and the
   campaign `Hw d S.w` with `μ` and `e` belongs to LIP051.01, which this file does not depend on.
2. Energy kernel. The specification says "the unchanged measurable energy `U_N`" without binding
   its kernel. Here `U_N` is built from an arbitrary kernel `K : α → α → ℝ` with the hypothesis
   `Measurable (Function.uncurry K)`. That hypothesis is used only for the measurability
   conjuncts (of `U_N` and of the joint map). The almost-everywhere and law equalities do not use
   it, because `U_N` does not depend on the features. The torus corollary discharges the
   hypothesis for the centered kernel of LIP051.03.
3. Energy normalisation. `U_N(ω) = (2 * N)⁻¹ * ∑ l, ∑ k, K (ω l) (ω k)`. For `N = 0` Lean gives
   the value `0`, which the specification allows (`N = 0` may be assigned any value).
4. Representatives. "Measurable representatives" is `Measurable (f j)`, which is stronger than
   the a.e.-measurable class property. "`e_j ∈ L²`" is `MemLp (f j) 2 μ`. "`∫ e_i e_j dμ = δ_ij`"
   is the Bochner integral of the pointwise product of the chosen representatives. Products and
   integrals of the representatives are representative-independent because of the a.e. statement.
5. Basis constant. "`e_0 = 1` as an `L²` class" is the Lean equality `e 0 = Lp.const 2 μ 1`
   (class equality, read as a hypothesis as the specification lists it).
6. Replacement. The "countable family of representatives" is read as an arbitrary family
   `g : ℕ → α → ℝ` of measurable functions with `g j =ᵐ[μ] f j` for every `j`. This is the
   whole index set `ℕ`, as in the specification. It is a non-literal reading only in that the
   family of replacements is quantified over all such `g`, which is the intended strength.
7. Mode indexing (FD-002 reading). The orthonormality and product clauses quantify over all
   indices `i j : ℕ`, including `0`, because `e 0 = 1` is one element of the Hilbert basis and
   its orthonormality with the positive modes is part of the basis property. The mean-zero clause is
   restricted to `1 ≤ j`, as the specification states; the file never claims `∫ f 0 dμ = 0`
   (that integral is `1`). No Gaussian limit and no finite-coordinate convergence is asserted
   here, so the zero-mode refutation of FD-002 does not apply to this unit. The positive-mode
   restriction of the Gaussian blocks is a binder of the closing statement, not of this one.
8. Joint maps. "A measurable function of that array" is `Φ : (Fin m → Fin N → ℝ) → β` with
   `Measurable Φ`, where `β` is an arbitrary measurable space. The joint map is the pair
   `(Φ (array), U_N)` in `β × ℝ`. The array is indexed by a finite list of feature indices
   `j : Fin m → ℕ` (repetitions and the empty list are allowed) and `N` particles, for every `N`.
9. Diagonal. The kernel `K` is used pointwise as given, including on the diagonal. No
   almost-everywhere representative of the kernel is taken, in line with the node's caution about
   the original diagonal.
10. Laws. "Equality of laws" is equality of `Measure.map` pushforwards under `μ^N`
   (`Measure.pi (fun _ : Fin N => μ)`). The statement of the map equalities does not need
   measurability of the maps, because the maps are a.e. equal.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP051

/-- The sampled feature array `ω ↦ (f (j k) (ω l))_{k,l}` on the particle space `Fin N → α`. -/
def featureArrayLIP05102 {α : Type*} (f : ℕ → α → ℝ) (N m : ℕ) (j : Fin m → ℕ)
    (ω : Fin N → α) : Fin m → Fin N → ℝ :=
  fun k l => f (j k) (ω l)

/-- The energy `U_N(ω) = (2N)⁻¹ ∑_{l,k} K(ω l, ω k)` of a kernel `K` on the particle space. -/
noncomputable def energyLIP05102 {α : Type*} (K : α → α → ℝ) (N : ℕ) (ω : Fin N → α) : ℝ :=
  (2 * (N : ℝ))⁻¹ * ∑ l : Fin N, ∑ k : Fin N, K (ω l) (ω k)

/-- The energy is measurable when the kernel is measurable on the product. -/
theorem measurable_energy_LIP05102 {α : Type*} [MeasurableSpace α] (K : α → α → ℝ)
    (hK : Measurable (Function.uncurry K)) (N : ℕ) : Measurable (energyLIP05102 K N) := by
  unfold energyLIP05102
  refine Measurable.const_mul
    (Finset.measurable_sum _ fun l _ => Finset.measurable_sum _ fun k _ => ?_) _
  have hpair : Measurable (fun ω : Fin N → α => (ω l, ω k)) :=
    (measurable_pi_apply l).prodMk (measurable_pi_apply k)
  exact hK.comp hpair

/-- **LIP051.02.** Centered measurable feature representatives. The energy `U_N` is measurable
under a measurable kernel. There are measurable, `L²`, centered (for `j ≥ 1`) and orthonormal
representatives `f j` of the Hilbert basis, and under every almost-everywhere replacement of them
the sampled arrays agree almost everywhere under each `μ^N`, their laws agree, and the joint laws
of `(Φ(array), U_N)` agree almost everywhere and in law, with the joint maps measurable. -/
theorem lip051_02_centered_measurable_feature_representatives
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {β : Type*} [MeasurableSpace β]
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ))
    (K : α → α → ℝ) (hK : Measurable (Function.uncurry K)) :
    (∀ N : ℕ, Measurable (energyLIP05102 K N)) ∧
    ∃ f : ℕ → α → ℝ, (∀ j, Measurable (f j)) ∧ (∀ j, MemLp (f j) 2 μ) ∧
      (∀ i j, ∫ x, f i x * f j x ∂μ = if i = j then 1 else 0) ∧
      (∀ j, 1 ≤ j → ∫ x, f j x ∂μ = 0) ∧
      ∀ g : ℕ → α → ℝ, (∀ j, Measurable (g j)) → (∀ j, g j =ᵐ[μ] f j) →
        ∀ (N m : ℕ) (j : Fin m → ℕ),
          featureArrayLIP05102 f N m j =ᵐ[Measure.pi (fun _ : Fin N => μ)]
            featureArrayLIP05102 g N m j ∧
          (∀ Φ : (Fin m → Fin N → ℝ) → β, Measurable Φ →
            Measure.map (fun ω => Φ (featureArrayLIP05102 f N m j ω))
                (Measure.pi (fun _ : Fin N => μ))
              = Measure.map (fun ω => Φ (featureArrayLIP05102 g N m j ω))
                (Measure.pi (fun _ : Fin N => μ))) ∧
          (∀ Φ : (Fin m → Fin N → ℝ) → β, Measurable Φ →
            Measurable (fun ω => (Φ (featureArrayLIP05102 f N m j ω), energyLIP05102 K N ω)) ∧
            (fun ω => (Φ (featureArrayLIP05102 f N m j ω), energyLIP05102 K N ω))
                =ᵐ[Measure.pi (fun _ : Fin N => μ)]
              (fun ω => (Φ (featureArrayLIP05102 g N m j ω), energyLIP05102 K N ω)) ∧
            Measure.map (fun ω => (Φ (featureArrayLIP05102 f N m j ω), energyLIP05102 K N ω))
                (Measure.pi (fun _ : Fin N => μ))
              = Measure.map (fun ω => (Φ (featureArrayLIP05102 g N m j ω), energyLIP05102 K N ω))
                (Measure.pi (fun _ : Fin N => μ))) := by
  refine ⟨measurable_energy_LIP05102 K hK, ?_⟩
  obtain ⟨f, hfm, _, hmem, _, hint, hmean⟩ :=
    lip051_25_representative_moments_hilbert_basis μ e he0
  refine ⟨f, hfm, hmem, hint, fun j hj => (hmean j hj).2, ?_⟩
  intro g hgm hgf N m j
  obtain ⟨harr, hlaw, hjoint⟩ :=
    lip051_26_representative_invariance_sampled_joint_maps (β := β) (γ := ℝ) μ f g hfm hgm
      (fun j => (hgf j).symm) N m j
  have hHm : Measurable (energyLIP05102 K N) := measurable_energy_LIP05102 K hK N
  refine ⟨harr, hlaw, fun Φ hΦ => ⟨?_, (hjoint Φ hΦ _ hHm).1, (hjoint Φ hΦ _ hHm).2⟩⟩
  exact (lip051_26_representative_invariance_sampled_joint_maps_measurable f hfm N m j Φ hΦ
    (energyLIP05102 K N) hHm).2

/-- For the centered kernel `K = centeredKernelOf_LIP05103 μ W` of a bounded continuous symmetric
`W` on the torus, the energy `U_N` built from `K` is measurable for every `N`. -/
theorem lip051_02_centered_measurable_feature_representatives_energy_torus {d : ℕ}
    (μ : Measure (DGPS.Torus d)) [IsProbabilityMeasure μ]
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) {M : ℝ} (hWc : Continuous (Function.uncurry W))
    (hs : ∀ x y, W x y = W y x) (hM : 0 ≤ M) (hb : ∀ x y, |W x y| ≤ M) (N : ℕ) :
    Measurable (energyLIP05102 (DGPS.Frontier.LIP051.centeredKernelOf_LIP05103 μ W) N) :=
  measurable_energy_LIP05102 _
    (lip051_03_centering_integrability_original_kernel (μ := μ) hWc hs hM hb).1 N

end DGPS.Frontier.LIP051
