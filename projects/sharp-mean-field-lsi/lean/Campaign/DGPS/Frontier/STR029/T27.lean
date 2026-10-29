import DGPS.Frontier.STR029.T21
import DGPS.Frontier.STR029.T23

/-!
# STR029.27: Reflection and sign symmetry of the branches

Task id: STR029.27. Title: Reflection and sign symmetry of the branches. Node STR029.
Prerequisites: STR029.16 and STR029.21 (the range graph `ψ` and its equivariance under the
reflection `t ↦ -t` and the half turn `T_π`), STR029.22 (the point `(2, 0, -16/15)` solves the
slice system), STR029.23 (the three branches `Z j`, the neighbourhoods `N j` and the uniqueness
clause), STR029.49 (the entropy of a chart density).

Provides:
* `DGPS.Frontier.STR029.str029_27_reflection_sign_symmetry_branches`: the data of STR029.23
  (`U, V, ψ, O, E, η, N, Z`, every clause restated) together with a radius `0 < δ ≤ η` such that,
  for every `h` with `|h| < δ`, with `(A_j, B_j, s_j) = Z j h`, `u_j = h A_j cos t + h B_j sin t +
  ψ(h A_j, h B_j, h, h² s_j)` and `ρ_j = ρ(h, u_j)`: (a) branch zero is even in `t`, that is
  `B_0(h) = 0`, the range component `ψ(h A_0, h B_0, h, h² s_0)` is even, and so are `u_0` and
  `ρ_0`; (b) `Z j (-h) = Z j h` for every `j` (each `z_j` is even in `h`); (c) `ρ_j(-h)(t) =
  ρ_j(h)(t - π)`, that is `ρ_j(-h) = T_π ρ_j(h)`; (d) `H_{-h}(ρ_j(-h)) = H_h(ρ_j(h))`.
* `DGPS.Frontier.STR029.str029_27_reflection_sign_symmetry_branches_of_data`: the same
  conclusion for arbitrary data satisfying the clauses of STR029.23 that are used. It is a theorem
  about hypotheses, so it does not depend on how STR029.23 is proved.
* `DGPS.Frontier.STR029.chartU_STR02927`: the log-chart function `u_j` of the specification, for a
  point `z = (A, B, s)` of the reduced slice.
* `DGPS.Frontier.STR029.refl3_STR02927`: the reflection `(A, B, s) ↦ (A, -B, s)` of the slice.
* `DGPS.Frontier.STR029.Ppar_STR02927`: the parameter point `(h A, h B, h, h² s)` of the graph.
* `DGPS.Frontier.STR029.Omega_STR02927`: the open set of `(h, z)` on which all the symmetry
  identities below are available.
* `DGPS.Frontier.STR029.SymW_STR02927`: the symmetry data of the range graph on an open set `W`
  (a structure; `Fred_STR02956` and the range values are invariant under reflection and sign).
* `DGPS.Frontier.STR029.symW_STR02927`: the symmetry data on a neighbourhood of `0` for the range
  graph of STR029.23, transferred from the graph of STR029.21 by uniqueness.
* `DGPS.Frontier.STR029.mem_omega_STR02927`, `DGPS.Frontier.STR029.Ppar_zero_STR02927`,
  `DGPS.Frontier.STR029.Ppar_refl_STR02927`, `DGPS.Frontier.STR029.Ppar_neg_STR02927`,
  `DGPS.Frontier.STR029.continuous_refl3_STR02927`,
  `DGPS.Frontier.STR029.continuous_Ppar_STR02927`, `DGPS.Frontier.STR029.isOpen_omega_STR02927`,
  `DGPS.Frontier.STR029.omega_zero_STR02927`, `DGPS.Frontier.STR029.eventually_omega_STR02927`,
  `DGPS.Frontier.STR029.eventually_slice_omega_STR02927`: membership, continuity, openness and
  neighbourhood facts for the points and the set above.
* `DGPS.Frontier.STR029.E_refl_STR02927`, `DGPS.Frontier.STR029.E_sign_STR02927`: for `h ≠ 0`
  and `(h, z)` in `Omega_STR02927`, `E(h, (A, -B, s)) = E(h, (A, B, s))` and
  `E(-h, z) = E(h, z)`.
* `DGPS.Frontier.STR029.hasDerivAt_line_STR02927`, `DGPS.Frontier.STR029.fderiv_refl_STR02927`:
  the derivative of a function along a line, and the transport of the derivative of a function
  that is invariant under the reflection.
* `DGPS.Frontier.STR029.diff_slice_STR02927`, `DGPS.Frontier.STR029.Kfun_apply_STR02927`,
  `DGPS.Frontier.STR029.Kfun_refl_STR02927`, `DGPS.Frontier.STR029.Kfun_sign_STR02927`: the slice
  is differentiable; the components of `Kfun_STR02923`; `K(h, z) = 0` implies `K(h, refl z) = 0`;
  `K(-h, z) = K(h, z)` when `E(-h, ·) = E(h, ·)` near `z`.
* `DGPS.Frontier.STR029.chartU_periodic_STR02927`, `DGPS.Frontier.STR029.chart_sign_STR02927`,
  `DGPS.Frontier.STR029.psi_sign_P_STR02927`, `DGPS.Frontier.STR029.chart_even_STR02927`: the
  chart is `2π`-periodic; the chart at `-h` is the chart at `h` shifted by `π`; the range value
  at `-h`; the chart is even when `B = 0` and the range component is even.
* `DGPS.Frontier.STR029.rho_even_STR02927`, `DGPS.Frontier.STR029.rho_sign_STR02927`,
  `DGPS.Frontier.STR029.entropy_sign_STR02927`: an even chart gives an even density; the density
  and the entropy under the half turn (from STR029.21).

R5 notes:
1. Restated data. STR029.23 is an existential statement, so the objects `ψ`, `E`, `N`, `Z` have
   to be named again. The main statement restates every clause of the conclusion of
   `str029_23_three_locally_unique_solution_branches` verbatim and only then adds the new block
   about `δ`. No hypothesis is added; the new block is a conjunction of conclusions.
2. Dependence on STR029.23. The theorem of STR029.23 currently in the tree is an unproved
   placeholder, so the main statement inherits that gap. The statement
   `str029_27_reflection_sign_symmetry_branches_of_data` does not: it has exactly the clauses it
   uses as hypotheses (nothing is strengthened) and is proved completely.
3. Two graphs. STR029.21 gives its own graph `ψ₁` with the equivariance identities, STR029.23 uses
   a graph `ψ` obtained from STR029.16 with the same uniqueness property. They need not be the same
   function. `symW_STR02927` shows that they agree on an open neighbourhood `W` of `0` (a point of
   `U ∩ U₁` with `ψ₁ p ∈ V` solves `Rpar p w = 0` in `V`, hence `ψ p = ψ₁ p` by uniqueness), and the
   identities for `ψ` are only used for parameter points in `W`. This is why the conclusion holds
   for `|h| < δ` and not on all of `(-η, η)`: one needs `(h A, h B, h, h² s)` and its reflected
   and sign-changed copies in `W`, and `(h, z)` and the reflected points in `O`.
4. "Sufficiently small". The new block is `∃ δ, 0 < δ ∧ δ ≤ η ∧ ∀ h ∈ Ioo (-δ) δ, ...`; the
   radius `δ` is chosen from the continuity of `Z j` at `0`.
5. Branch zero. "Branch zero is even in `t`" is formalized as four facts: `B_0(h) = 0` (that is
   `Z 0 h 1 = 0`), the range component is even, the chart `u_0` is even and the density `ρ_0` is
   even, each for all real `t`.
6. `h = 0`. The identity `B_0(0) = 0` is not obtained from the reflection argument (the slice at
   `h = 0` is not reflection invariant in the available form) but from `Z 0 0 = (2, 0, -16/15)`,
   which is the uniqueness clause together with `Kmap_STR02922 E (2, 0, -16/15) = 0` of STR029.22.
   For `h = 0` the evenness of `z_j` is trivial.
7. The map `T_π`. It is `u ↦ u(· - π)`, that is `pb_STR02916 1 (-π)`; since all the functions
   involved are `2π`-periodic this is the same as `u(· + π)`. The density relation is stated as
   `ρ_j(-h)(t) = ρ_j(h)(t - π)` with `ρ_j(h) = rhoT_STR02901 h (chartU_STR02927 ψ h (Z j h))`.
8. The entropy. `H_h` is read as the chart formula `entropyChart_STR02949` as in STR029.24, so
   `H_{-h}(ρ_j(-h)) = H_h(ρ_j(h))` is `entropyChart_STR02949 (-h) u_j(-h) = entropyChart_STR02949 h u_j(h)`.
9. The range map. The specification refers to the equation `K = 0`; the range equation used is
   the variational `Rpar_STR02916` of STR029.16, as in STR029.21 to STR029.24, and the symmetries are
   those of `Fred_STR02956`.
10. Clauses used. `str029_27_reflection_sign_symmetry_branches_of_data` takes from the data of
   STR029.23 only: the open sets `U`, `V` around `0` with the uniqueness of the zero of
   `Rpar_STR02916` in `V`; the extension `E` (open `O`, smoothness, the formula for `h ≠ 0`, the
   slice `h = 0`); `η`; the neighbourhood `N 0` of `(2, 0, -16/15)` with its reflection
   invariance; the branches `Z j` (continuity, membership in `N j`); and the uniqueness clause.
   The openness of the `N j`, the neighbourhoods of the other two base points, disjointness, the
   rotation clauses and `Z j h 2 = Z 0 h 2` are restated in the main statement but not used.
-/

open scoped ContDiff
open Topology

namespace DGPS.Frontier.STR029

/-- The log-chart function `u(t) = h A cos t + h B sin t + ψ(h A, h B, h, h² s)(t)` of a point
`z = (A, B, s)` of the reduced slice. -/
noncomputable def chartU_STR02927 (ψ : Par_STR02916 → E_STR02969) (h : ℝ) (z : Fin 3 → ℝ) :
    ℝ → ℝ :=
  uT_STR02901 (h * z 0) (h * z 1)
    ((ψ (h * z 0, h * z 1, h, h ^ 2 * z 2) : E_STR02969) : PeriodicC2_STR02969).val

/-- The reflection `(A, B, s) ↦ (A, -B, s)` of the reduced slice. -/
noncomputable def refl3_STR02927 (z : Fin 3 → ℝ) : Fin 3 → ℝ := ![z 0, -z 1, z 2]

/-- The parameter point `(h A, h B, h, h² s)` of the range graph for `z = (A, B, s)`. -/
noncomputable def Ppar_STR02927 (h : ℝ) (z : Fin 3 → ℝ) : Par_STR02916 :=
  (h * z 0, h * z 1, h, h ^ 2 * z 2)

/-- The points `(h, z)` of `O` whose reflected and sign-changed copies are in `O`, and whose
parameter points are in `W`. -/
noncomputable def Omega_STR02927 (W : Set Par_STR02916) (O : Set (ℝ × (Fin 3 → ℝ))) :
    Set (ℝ × (Fin 3 → ℝ)) :=
  {x | x ∈ O ∧ (-x.1, x.2) ∈ O ∧ (x.1, refl3_STR02927 x.2) ∈ O ∧ Ppar_STR02927 x.1 x.2 ∈ W ∧
    Ppar_STR02927 (-x.1) x.2 ∈ W ∧ Ppar_STR02927 x.1 (refl3_STR02927 x.2) ∈ W}

/-- The symmetry data of a range graph `ψ` on an open set `W` containing `0`: `Fred_STR02956` and
the range values are invariant under the reflection `(a, b, h, γ) ↦ (a, -b, h, γ)` (with
`t ↦ -t`) and under the sign change `(a, b, h, γ) ↦ (-a, -b, -h, γ)` (with `t ↦ t - π`), whenever
both parameter points lie in `W`. -/
structure SymW_STR02927 (ψ : Par_STR02916 → E_STR02969) (W : Set Par_STR02916) : Prop where
  isOpen : IsOpen W
  zero_mem : (0 : Par_STR02916) ∈ W
  F_refl : ∀ a b h γ : ℝ, (a, b, h, γ) ∈ W → (a, -b, h, γ) ∈ W →
    Fred_STR02956 ψ (a, -b) (h, γ) = Fred_STR02956 ψ (a, b) (h, γ)
  F_sign : ∀ a b h γ : ℝ, (a, b, h, γ) ∈ W → (-a, -b, -h, γ) ∈ W →
    Fred_STR02956 ψ (-a, -b) (-h, γ) = Fred_STR02956 ψ (a, b) (h, γ)
  psi_refl : ∀ a b h γ : ℝ, (a, b, h, γ) ∈ W → (a, -b, h, γ) ∈ W → ∀ t : ℝ,
    ((ψ (a, -b, h, γ) : E_STR02969) : PeriodicC2_STR02969).val t =
      ((ψ (a, b, h, γ) : E_STR02969) : PeriodicC2_STR02969).val (-t)
  psi_sign : ∀ a b h γ : ℝ, (a, b, h, γ) ∈ W → (-a, -b, -h, γ) ∈ W → ∀ t : ℝ,
    ((ψ (-a, -b, -h, γ) : E_STR02969) : PeriodicC2_STR02969).val t =
      ((ψ (a, b, h, γ) : E_STR02969) : PeriodicC2_STR02969).val (t - Real.pi)

/-- The symmetry data on a neighbourhood of `0` for the range graph of STR029.23. The graph of
STR029.21 satisfies the identities on its domain; the two graphs agree on the open set of points
`p` of both domains with `ψ₁ p` in `V`, by uniqueness of the zero of `Rpar_STR02916` in `V`. -/
theorem symW_STR02927 {U : Set Par_STR02916} {V : Set E_STR02969}
    {ψ : Par_STR02916 → E_STR02969} (hUo : IsOpen U) (hU0 : (0 : Par_STR02916) ∈ U)
    (hVo : IsOpen V) (hV0 : (0 : E_STR02969) ∈ V)
    (hR : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) :
    ∃ W : Set Par_STR02916, SymW_STR02927 ψ W := by
  obtain ⟨U1, V1, ψ1, hU1o, h0U1, -, -, hcd1, hψ01, hψV1, hiff1, -, -, -, -, -, -, hpsiR1,
    hpsiS1, -, hFR1, hFS1, -, -, -⟩ := str029_21_equivariance_unique_range_graph
  have hWψ : ∀ p ∈ U ∩ (U1 ∩ ψ1 ⁻¹' V), ψ p = ψ1 p := by
    rintro p ⟨hpU, hpU1, hpV⟩
    exact ((hR p hpU _ hpV).mp ((hiff1 p hpU1 _ (hψV1 p hpU1)).mpr rfl)).symm
  have hF : ∀ p ∈ U ∩ (U1 ∩ ψ1 ⁻¹' V), Fgraph_STR02921 ψ p = Fgraph_STR02921 ψ1 p := by
    intro p hp
    unfold Fgraph_STR02921
    rw [hWψ p hp]
  refine ⟨U ∩ (U1 ∩ ψ1 ⁻¹' V), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hUo.inter (hcd1.continuousOn.isOpen_inter_preimage hU1o hVo)
  · refine ⟨hU0, h0U1, ?_⟩
    show ψ1 0 ∈ V
    rw [hψ01]
    exact hV0
  · intro a b h γ hp hq
    have h1 : Fgraph_STR02921 ψ ((a, -b, h, γ) : Par_STR02916) =
        Fgraph_STR02921 ψ1 ((a, -b, h, γ) : Par_STR02916) := hF ((a, -b, h, γ) : Par_STR02916) hq
    have h2 : Fgraph_STR02921 ψ ((a, b, h, γ) : Par_STR02916) =
        Fgraph_STR02921 ψ1 ((a, b, h, γ) : Par_STR02916) := hF ((a, b, h, γ) : Par_STR02916) hp
    show Fgraph_STR02921 ψ ((a, -b, h, γ) : Par_STR02916) =
      Fgraph_STR02921 ψ ((a, b, h, γ) : Par_STR02916)
    rw [h1, h2]
    exact hFR1 (a, b, h, γ) hp.2.1
  · intro a b h γ hp hq
    have h1 : Fgraph_STR02921 ψ ((-a, -b, -h, γ) : Par_STR02916) =
        Fgraph_STR02921 ψ1 ((-a, -b, -h, γ) : Par_STR02916) :=
      hF ((-a, -b, -h, γ) : Par_STR02916) hq
    have h2 : Fgraph_STR02921 ψ ((a, b, h, γ) : Par_STR02916) =
        Fgraph_STR02921 ψ1 ((a, b, h, γ) : Par_STR02916) := hF ((a, b, h, γ) : Par_STR02916) hp
    show Fgraph_STR02921 ψ ((-a, -b, -h, γ) : Par_STR02916) =
      Fgraph_STR02921 ψ ((a, b, h, γ) : Par_STR02916)
    rw [h1, h2]
    exact hFS1 (a, b, h, γ) hp.2.1
  · intro a b h γ hp hq t
    rw [hWψ _ hq, hWψ _ hp]
    exact hpsiR1 (a, b, h, γ) hp.2.1 t
  · intro a b h γ hp hq t
    rw [hWψ _ hq, hWψ _ hp]
    exact hpsiS1 (a, b, h, γ) hp.2.1 t

theorem mem_omega_STR02927 {W : Set Par_STR02916} {O : Set (ℝ × (Fin 3 → ℝ))} {h : ℝ}
    {z : Fin 3 → ℝ} :
    (h, z) ∈ Omega_STR02927 W O ↔ (h, z) ∈ O ∧ (-h, z) ∈ O ∧ (h, refl3_STR02927 z) ∈ O ∧
      Ppar_STR02927 h z ∈ W ∧ Ppar_STR02927 (-h) z ∈ W ∧
      Ppar_STR02927 h (refl3_STR02927 z) ∈ W :=
  Iff.rfl

theorem Ppar_zero_STR02927 (z : Fin 3 → ℝ) : Ppar_STR02927 0 z = 0 := by
  simp [Ppar_STR02927]

theorem Ppar_refl_STR02927 (h : ℝ) (z : Fin 3 → ℝ) :
    Ppar_STR02927 h (refl3_STR02927 z) = (h * z 0, -(h * z 1), h, h ^ 2 * z 2) := by
  have e0 : refl3_STR02927 z 0 = z 0 := rfl
  have e1 : refl3_STR02927 z 1 = -z 1 := rfl
  have e2 : refl3_STR02927 z 2 = z 2 := rfl
  unfold Ppar_STR02927
  rw [e0, e1, e2, mul_neg]

theorem Ppar_neg_STR02927 (h : ℝ) (z : Fin 3 → ℝ) :
    Ppar_STR02927 (-h) z = (-(h * z 0), -(h * z 1), -h, h ^ 2 * z 2) := by
  unfold Ppar_STR02927
  rw [neg_mul, neg_mul, neg_sq]

theorem continuous_refl3_STR02927 : Continuous refl3_STR02927 := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [refl3_STR02927] <;> fun_prop

theorem continuous_Ppar_STR02927 : Continuous (fun x : ℝ × (Fin 3 → ℝ) => Ppar_STR02927 x.1 x.2) := by
  unfold Ppar_STR02927
  fun_prop

theorem isOpen_omega_STR02927 {W : Set Par_STR02916} {O : Set (ℝ × (Fin 3 → ℝ))}
    (hW : IsOpen W) (hO : IsOpen O) : IsOpen (Omega_STR02927 W O) := by
  have c1 : Continuous (fun x : ℝ × (Fin 3 → ℝ) => ((-x.1, x.2) : ℝ × (Fin 3 → ℝ))) := by
    fun_prop
  have cr : Continuous (fun x : ℝ × (Fin 3 → ℝ) => ((x.1, refl3_STR02927 x.2) : ℝ × (Fin 3 → ℝ))) :=
    continuous_fst.prodMk (continuous_refl3_STR02927.comp continuous_snd)
  have c3 : Continuous (fun x : ℝ × (Fin 3 → ℝ) => Ppar_STR02927 x.1 x.2) :=
    continuous_Ppar_STR02927
  have c4 : Continuous (fun x : ℝ × (Fin 3 → ℝ) => Ppar_STR02927 (-x.1) x.2) :=
    continuous_Ppar_STR02927.comp c1
  have c5 : Continuous (fun x : ℝ × (Fin 3 → ℝ) => Ppar_STR02927 x.1 (refl3_STR02927 x.2)) :=
    continuous_Ppar_STR02927.comp cr
  exact hO.inter ((hO.preimage c1).inter ((hO.preimage cr).inter ((hW.preimage c3).inter
    ((hW.preimage c4).inter (hW.preimage c5)))))

theorem omega_zero_STR02927 {W : Set Par_STR02916} {O : Set (ℝ × (Fin 3 → ℝ))}
    (hW0 : (0 : Par_STR02916) ∈ W) (hOmem : ∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O)
    (z : Fin 3 → ℝ) : ((0 : ℝ), z) ∈ Omega_STR02927 W O := by
  have hP : ∀ w : Fin 3 → ℝ, Ppar_STR02927 0 w ∈ W := fun w => by
    rw [Ppar_zero_STR02927]
    exact hW0
  refine mem_omega_STR02927.mpr ⟨hOmem z, ?_, hOmem _, hP z, ?_, hP _⟩
  · rw [neg_zero]
    exact hOmem z
  · rw [neg_zero]
    exact hP z

theorem eventually_omega_STR02927 {W : Set Par_STR02916} {O : Set (ℝ × (Fin 3 → ℝ))}
    (hW : IsOpen W) (hO : IsOpen O) (hW0 : (0 : Par_STR02916) ∈ W)
    (hOmem : ∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O) {Z : ℝ → Fin 3 → ℝ} (hZ : ContinuousAt Z 0) :
    ∀ᶠ h in 𝓝 (0 : ℝ), (h, Z h) ∈ Omega_STR02927 W O := by
  have hc : ContinuousAt (fun h : ℝ => ((h, Z h) : ℝ × (Fin 3 → ℝ))) 0 :=
    continuousAt_id.prodMk hZ
  exact hc.preimage_mem_nhds ((isOpen_omega_STR02927 hW hO).mem_nhds
    (omega_zero_STR02927 hW0 hOmem (Z 0)))

theorem eventually_slice_omega_STR02927 {W : Set Par_STR02916} {O : Set (ℝ × (Fin 3 → ℝ))}
    (hΩ : IsOpen (Omega_STR02927 W O)) {h : ℝ} {z : Fin 3 → ℝ}
    (hx : (h, z) ∈ Omega_STR02927 W O) : ∀ᶠ w in 𝓝 z, (h, w) ∈ Omega_STR02927 W O := by
  have hcont : Continuous (fun w : Fin 3 → ℝ => ((h, w) : ℝ × (Fin 3 → ℝ))) :=
    continuous_const.prodMk continuous_id
  exact (hΩ.preimage hcont).mem_nhds hx

theorem E_refl_STR02927 {ψ : Par_STR02916 → E_STR02969} {W : Set Par_STR02916}
    {O : Set (ℝ × (Fin 3 → ℝ))} {E : ℝ × (Fin 3 → ℝ) → ℝ} (hW : SymW_STR02927 ψ W)
    (hval : ∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
      E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4)
    {h : ℝ} {z : Fin 3 → ℝ} (hx : (h, z) ∈ Omega_STR02927 W O) (hh : h ≠ 0) :
    E (h, refl3_STR02927 z) = E (h, z) := by
  obtain ⟨hO, -, hOr, hp, -, hq⟩ := mem_omega_STR02927.mp hx
  have hq' : ((h * z 0, -(h * z 1), h, h ^ 2 * z 2) : Par_STR02916) ∈ W := by
    rw [← Ppar_refl_STR02927]
    exact hq
  have e0 : refl3_STR02927 z 0 = z 0 := rfl
  have e1 : refl3_STR02927 z 1 = -z 1 := rfl
  have e2 : refl3_STR02927 z 2 = z 2 := rfl
  rw [hval h (refl3_STR02927 z) hOr hh, hval h z hO hh, e0, e1, e2, mul_neg,
    hW.F_refl (h * z 0) (h * z 1) h (h ^ 2 * z 2) hp hq']

theorem E_sign_STR02927 {ψ : Par_STR02916 → E_STR02969} {W : Set Par_STR02916}
    {O : Set (ℝ × (Fin 3 → ℝ))} {E : ℝ × (Fin 3 → ℝ) → ℝ} (hW : SymW_STR02927 ψ W)
    (hval : ∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
      E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4)
    {h : ℝ} {z : Fin 3 → ℝ} (hx : (h, z) ∈ Omega_STR02927 W O) (hh : h ≠ 0) :
    E (-h, z) = E (h, z) := by
  obtain ⟨hO, hO', -, hp, hq, -⟩ := mem_omega_STR02927.mp hx
  have hq' : ((-(h * z 0), -(h * z 1), -h, h ^ 2 * z 2) : Par_STR02916) ∈ W := by
    rw [← Ppar_neg_STR02927]
    exact hq
  have h4 : (-h) ^ 4 = h ^ 4 := by ring
  rw [hval (-h) z hO' (neg_ne_zero.mpr hh), hval h z hO hh, h4]
  simp only [neg_mul, neg_sq]
  rw [hW.F_sign (h * z 0) (h * z 1) h (h ^ 2 * z 2) hp hq']

theorem hasDerivAt_line_STR02927 {Φ : (Fin 3 → ℝ) → ℝ} {z : Fin 3 → ℝ}
    (hΦ : DifferentiableAt ℝ Φ z) (v : Fin 3 → ℝ) :
    HasDerivAt (fun s : ℝ => Φ (z + s • v)) (fderiv ℝ Φ z v) 0 := by
  have hl : HasDerivAt (fun s : ℝ => z + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hΦ' : HasFDerivAt Φ (fderiv ℝ Φ z) (z + (0 : ℝ) • v) := by
    simpa using hΦ.hasFDerivAt
  exact hΦ'.comp_hasDerivAt_of_eq 0 hl (by simp)

theorem fderiv_refl_STR02927 {Φ : (Fin 3 → ℝ) → ℝ} {z : Fin 3 → ℝ}
    (hΦz : DifferentiableAt ℝ Φ z) (hΦr : DifferentiableAt ℝ Φ (refl3_STR02927 z))
    (hev : ∀ᶠ w in 𝓝 z, Φ (refl3_STR02927 w) = Φ w) (v : Fin 3 → ℝ) :
    fderiv ℝ Φ z v = fderiv ℝ Φ (refl3_STR02927 z) (refl3_STR02927 v) := by
  have h1 := hasDerivAt_line_STR02927 hΦz v
  have h2 := hasDerivAt_line_STR02927 hΦr (refl3_STR02927 v)
  have hlin : ∀ s : ℝ, refl3_STR02927 (z + s • v) = refl3_STR02927 z + s • refl3_STR02927 v := by
    intro s
    funext i
    fin_cases i <;> simp [refl3_STR02927]
    ring
  have hcont : Continuous (fun s : ℝ => z + s • v) := by fun_prop
  have hev' : ∀ᶠ w in 𝓝 (z + (0 : ℝ) • v), Φ (refl3_STR02927 w) = Φ w := by simpa using hev
  have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), Φ (refl3_STR02927 (z + s • v)) = Φ (z + s • v) :=
    hcont.continuousAt.tendsto.eventually hev'
  have h3 : HasDerivAt (fun s : ℝ => Φ (z + s • v))
      (fderiv ℝ Φ (refl3_STR02927 z) (refl3_STR02927 v)) 0 := by
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [hmem] with s hs
    rw [← hlin s]
    exact hs.symm
  exact h1.unique h3

theorem diff_slice_STR02927 {O : Set (ℝ × (Fin 3 → ℝ))} {E : ℝ × (Fin 3 → ℝ) → ℝ}
    (hOo : IsOpen O) (hEC : ContDiffOn ℝ ∞ E O) {h : ℝ} {z : Fin 3 → ℝ} (hx : (h, z) ∈ O) :
    DifferentiableAt ℝ (fun w : Fin 3 → ℝ => E (h, w)) z := by
  have hE : DifferentiableAt ℝ E (h, z) :=
    (hEC.contDiffAt (hOo.mem_nhds hx)).differentiableAt (by simp)
  exact hE.comp z (by fun_prop)

theorem Kfun_apply_STR02927 (E : ℝ × (Fin 3 → ℝ) → ℝ) (h : ℝ) (z : Fin 3 → ℝ) :
    Kfun_STR02923 E (h, z) =
      ![fderiv ℝ (fun w : Fin 3 → ℝ => E (h, w)) z (Pi.single 0 1),
        fderiv ℝ (fun w : Fin 3 → ℝ => E (h, w)) z (Pi.single 1 1), E (h, z)] :=
  rfl

theorem Kfun_refl_STR02927 (E : ℝ × (Fin 3 → ℝ) → ℝ) {h : ℝ} {z : Fin 3 → ℝ}
    (hΦz : DifferentiableAt ℝ (fun w : Fin 3 → ℝ => E (h, w)) z)
    (hΦr : DifferentiableAt ℝ (fun w : Fin 3 → ℝ => E (h, w)) (refl3_STR02927 z))
    (hev : ∀ᶠ w in 𝓝 z, E (h, refl3_STR02927 w) = E (h, w))
    (hK : Kfun_STR02923 E (h, z) = 0) : Kfun_STR02923 E (h, refl3_STR02927 z) = 0 := by
  have hA : fderiv ℝ (fun w : Fin 3 → ℝ => E (h, w)) z (Pi.single 0 1) = 0 := congrFun hK 0
  have hB : fderiv ℝ (fun w : Fin 3 → ℝ => E (h, w)) z (Pi.single 1 1) = 0 := congrFun hK 1
  have hC : E (h, z) = 0 := congrFun hK 2
  have hr0 : refl3_STR02927 (Pi.single 0 1 : Fin 3 → ℝ) = Pi.single 0 1 := by
    funext i
    fin_cases i <;> simp [refl3_STR02927]
  have hr1 : refl3_STR02927 (Pi.single 1 1 : Fin 3 → ℝ) = -Pi.single 1 1 := by
    funext i
    fin_cases i <;> simp [refl3_STR02927]
  have hA' : fderiv ℝ (fun w : Fin 3 → ℝ => E (h, w)) (refl3_STR02927 z) (Pi.single 0 1) = 0 := by
    have := fderiv_refl_STR02927 hΦz hΦr hev (Pi.single 0 1)
    rw [hr0] at this
    rw [← this]
    exact hA
  have hB' : fderiv ℝ (fun w : Fin 3 → ℝ => E (h, w)) (refl3_STR02927 z) (Pi.single 1 1) = 0 := by
    have := fderiv_refl_STR02927 hΦz hΦr hev (Pi.single 1 1)
    rw [hr1, map_neg, hB] at this
    linarith
  have hC' : E (h, refl3_STR02927 z) = 0 := by
    rw [hev.self_of_nhds]
    exact hC
  rw [Kfun_apply_STR02927, hA', hB', hC']
  funext i
  fin_cases i <;> rfl

theorem Kfun_sign_STR02927 (E : ℝ × (Fin 3 → ℝ) → ℝ) {h : ℝ} {z : Fin 3 → ℝ}
    (hev : ∀ᶠ w in 𝓝 z, E (-h, w) = E (h, w)) :
    Kfun_STR02923 E (-h, z) = Kfun_STR02923 E (h, z) := by
  have heq : (fun w : Fin 3 → ℝ => E (-h, w)) =ᶠ[𝓝 z] (fun w : Fin 3 → ℝ => E (h, w)) := hev
  rw [Kfun_apply_STR02927, Kfun_apply_STR02927, heq.fderiv_eq, hev.self_of_nhds]

theorem chartU_periodic_STR02927 (ψ : Par_STR02916 → E_STR02969) (h : ℝ) (z : Fin 3 → ℝ) :
    Function.Periodic (chartU_STR02927 ψ h z) (2 * Real.pi) := by
  obtain ⟨hper, -, -, -, -⟩ := uT_isC2_STR02921 (h * z 0) (h * z 1)
    (ψ (h * z 0, h * z 1, h, h ^ 2 * z 2))
  exact hper

theorem chart_sign_STR02927 {ψ : Par_STR02916 → E_STR02969} {h : ℝ} {z : Fin 3 → ℝ}
    (hs : ∀ t : ℝ,
      ((ψ ((-h) * z 0, (-h) * z 1, -h, (-h) ^ 2 * z 2) : E_STR02969) :
          PeriodicC2_STR02969).val t =
        ((ψ (h * z 0, h * z 1, h, h ^ 2 * z 2) : E_STR02969) :
          PeriodicC2_STR02969).val (t - Real.pi)) :
    chartU_STR02927 ψ (-h) z = pb_STR02916 1 (-Real.pi) (chartU_STR02927 ψ h z) := by
  funext t
  simp only [chartU_STR02927, uT_STR02901, pb_STR02916]
  rw [hs t, show (1 : ℝ) * t + -Real.pi = t - Real.pi by ring, Real.cos_sub_pi, Real.sin_sub_pi]
  ring

theorem psi_sign_P_STR02927 {ψ : Par_STR02916 → E_STR02969} {W : Set Par_STR02916}
    (hW : SymW_STR02927 ψ W) {h : ℝ} {z : Fin 3 → ℝ} (hp : Ppar_STR02927 h z ∈ W)
    (hq : Ppar_STR02927 (-h) z ∈ W) (t : ℝ) :
    ((ψ ((-h) * z 0, (-h) * z 1, -h, (-h) ^ 2 * z 2) : E_STR02969) :
        PeriodicC2_STR02969).val t =
      ((ψ (h * z 0, h * z 1, h, h ^ 2 * z 2) : E_STR02969) :
        PeriodicC2_STR02969).val (t - Real.pi) := by
  have e : ((-h) * z 0, (-h) * z 1, -h, (-h) ^ 2 * z 2) =
      (-(h * z 0), -(h * z 1), -h, h ^ 2 * z 2) := Ppar_neg_STR02927 h z
  have hq' : ((-(h * z 0), -(h * z 1), -h, h ^ 2 * z 2) : Par_STR02916) ∈ W := by
    rw [← Ppar_neg_STR02927]
    exact hq
  rw [e]
  exact hW.psi_sign (h * z 0) (h * z 1) h (h ^ 2 * z 2) hp hq' t

theorem chart_even_STR02927 {ψ : Par_STR02916 → E_STR02969} {h : ℝ} {z : Fin 3 → ℝ}
    (hz1 : z 1 = 0)
    (hw : ∀ t : ℝ,
      ((ψ (h * z 0, h * z 1, h, h ^ 2 * z 2) : E_STR02969) : PeriodicC2_STR02969).val (-t) =
        ((ψ (h * z 0, h * z 1, h, h ^ 2 * z 2) : E_STR02969) : PeriodicC2_STR02969).val t)
    (t : ℝ) : chartU_STR02927 ψ h z (-t) = chartU_STR02927 ψ h z t := by
  simp only [chartU_STR02927, uT_STR02901]
  rw [hw t, Real.cos_neg, Real.sin_neg, hz1]
  ring

theorem rho_even_STR02927 (h : ℝ) {u : ℝ → ℝ} (hu : ∀ t : ℝ, u (-t) = u t) (t : ℝ) :
    rhoT_STR02901 h u (-t) = rhoT_STR02901 h u t := by
  unfold rhoT_STR02901
  rw [mul_neg, Real.cos_neg, hu t]

theorem rho_sign_STR02927 (h : ℝ) {u : ℝ → ℝ} (hu : Function.Periodic u (2 * Real.pi))
    (t : ℝ) :
    rhoT_STR02901 (-h) (pb_STR02916 1 (-Real.pi) u) t = rhoT_STR02901 h u (t - Real.pi) := by
  have key := rho_pb_STR02921 symOK_half_STR02921 h hu
  rw [show (-1 : ℝ) * h = -h by ring] at key
  rw [key]
  simp only [pb_STR02916]
  congr 1
  ring

theorem entropy_sign_STR02927 (h : ℝ) {u : ℝ → ℝ} (hu : Function.Periodic u (2 * Real.pi)) :
    entropyChart_STR02949 (-h) (pb_STR02916 1 (-Real.pi) u) = entropyChart_STR02949 h u := by
  have key := entropy_pb_STR02921 symOK_half_STR02921 h hu
  rwa [show (-1 : ℝ) * h = -h by ring] at key

/-- STR029.27 for arbitrary data with the clauses of STR029.23 that the argument uses: the
`δ`-block of the conclusion. -/
theorem str029_27_reflection_sign_symmetry_branches_of_data
    {U : Set Par_STR02916} {V : Set E_STR02969} {ψ : Par_STR02916 → E_STR02969}
    {O : Set (ℝ × (Fin 3 → ℝ))} {E : ℝ × (Fin 3 → ℝ) → ℝ} {η : ℝ}
    {N : Fin 3 → Set (Fin 3 → ℝ)} {Z : Fin 3 → ℝ → (Fin 3 → ℝ)}
    (hUo : IsOpen U) (hU0 : (0 : Par_STR02916) ∈ U) (hVo : IsOpen V)
    (hV0 : (0 : E_STR02969) ∈ V) (hR : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p)
    (hOo : IsOpen O) (hOmem : ∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O) (hEC : ContDiffOn ℝ ∞ E O)
    (hval : ∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
      E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4)
    (hzero : ∀ z : Fin 3 → ℝ, E ((0 : ℝ), z) =
      Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2))
    (hη : 0 < η) (hn0 : N 0 ∈ 𝓝 (![2, 0, -16 / 15] : Fin 3 → ℝ))
    (hsym : ∀ z : Fin 3 → ℝ, z ∈ N 0 ↔ (![z 0, -z 1, z 2] : Fin 3 → ℝ) ∈ N 0)
    (hZC : ∀ j : Fin 3, ContDiffOn ℝ ∞ (Z j) (Set.Ioo (-η) η))
    (hZN : ∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, Z j h ∈ N j)
    (hKuniq : ∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, ∀ z ∈ N j,
      Kfun_STR02923 E (h, z) = 0 ↔ z = Z j h) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ η ∧ ∀ h ∈ Set.Ioo (-δ) δ,
      (Z 0 h 1 = 0 ∧
        (∀ t : ℝ,
          ((ψ (h * Z 0 h 0, h * Z 0 h 1, h, h ^ 2 * Z 0 h 2) : E_STR02969) :
              PeriodicC2_STR02969).val (-t) =
            ((ψ (h * Z 0 h 0, h * Z 0 h 1, h, h ^ 2 * Z 0 h 2) : E_STR02969) :
              PeriodicC2_STR02969).val t) ∧
        (∀ t : ℝ, chartU_STR02927 ψ h (Z 0 h) (-t) = chartU_STR02927 ψ h (Z 0 h) t) ∧
        (∀ t : ℝ, rhoT_STR02901 h (chartU_STR02927 ψ h (Z 0 h)) (-t) =
          rhoT_STR02901 h (chartU_STR02927 ψ h (Z 0 h)) t)) ∧
      (∀ j : Fin 3, Z j (-h) = Z j h) ∧
      (∀ j : Fin 3, ∀ t : ℝ, rhoT_STR02901 (-h) (chartU_STR02927 ψ (-h) (Z j (-h))) t =
        rhoT_STR02901 h (chartU_STR02927 ψ h (Z j h)) (t - Real.pi)) ∧
      (∀ j : Fin 3, entropyChart_STR02949 (-h) (chartU_STR02927 ψ (-h) (Z j (-h))) =
        entropyChart_STR02949 h (chartU_STR02927 ψ h (Z j h))) := by
  obtain ⟨W, hW⟩ := symW_STR02927 hUo hU0 hVo hV0 hR
  have hΩo : IsOpen (Omega_STR02927 W O) := isOpen_omega_STR02927 hW.isOpen hOo
  have hηmem : (0 : ℝ) ∈ Set.Ioo (-η) η := ⟨by linarith, hη⟩
  have hIoo' : Set.Ioo (-η) η ∈ 𝓝 (0 : ℝ) := isOpen_Ioo.mem_nhds hηmem
  have hZcont : ∀ j, ContinuousAt (Z j) 0 := fun j => ((hZC j).continuousOn).continuousAt hIoo'
  have hZ00 : Z 0 0 = ![2, 0, -16 / 15] := by
    have hK := (str029_22_invertible_finite_dimensional_jacobian_of_slice E hzero).1
    have hmem : (![2, 0, -16 / 15] : Fin 3 → ℝ) ∈ N 0 := mem_of_mem_nhds hn0
    exact ((hKuniq 0 0 hηmem _ hmem).mp hK).symm
  have hev : ∀ᶠ h in 𝓝 (0 : ℝ), ∀ j : Fin 3, (h, Z j h) ∈ Omega_STR02927 W O :=
    Filter.eventually_all.mpr fun j =>
      eventually_omega_STR02927 hW.isOpen hOo hW.zero_mem hOmem (hZcont j)
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min ε η, lt_min hε hη, min_le_right _ _, ?_⟩
  intro h hh
  have h1 := min_le_left ε η
  have h2 := min_le_right ε η
  have hhη : h ∈ Set.Ioo (-η) η := ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hnhη : -h ∈ Set.Ioo (-η) η := ⟨by linarith [hhη.2], by linarith [hhη.1]⟩
  have hd : dist h 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hhΩ : ∀ j : Fin 3, (h, Z j h) ∈ Omega_STR02927 W O := hεP hd
  have hZeven : ∀ j : Fin 3, Z j (-h) = Z j h := by
    intro j
    by_cases h0 : h = 0
    · rw [h0, neg_zero]
    · have hx := hhΩ j
      have hev2 : ∀ᶠ w in 𝓝 (Z j h), E (-h, w) = E (h, w) := by
        filter_upwards [eventually_slice_omega_STR02927 hΩo hx] with w hw
        exact E_sign_STR02927 hW hval hw h0
      have hK : Kfun_STR02923 E (-h, Z j h) = 0 := by
        rw [Kfun_sign_STR02927 E hev2]
        exact (hKuniq j h hhη _ (hZN j h hhη)).mpr rfl
      exact ((hKuniq j (-h) hnhη _ (hZN j h hhη)).mp hK).symm
  have hB0 : Z 0 h 1 = 0 := by
    by_cases h0 : h = 0
    · simp [h0, hZ00]
    · have hx := hhΩ 0
      obtain ⟨hO, -, hOr, -, -, -⟩ := mem_omega_STR02927.mp hx
      have hev1 : ∀ᶠ w in 𝓝 (Z 0 h), E (h, refl3_STR02927 w) = E (h, w) := by
        filter_upwards [eventually_slice_omega_STR02927 hΩo hx] with w hw
        exact E_refl_STR02927 hW hval hw h0
      have hK0 : Kfun_STR02923 E (h, Z 0 h) = 0 :=
        (hKuniq 0 h hhη _ (hZN 0 h hhη)).mpr rfl
      have hKr : Kfun_STR02923 E (h, refl3_STR02927 (Z 0 h)) = 0 :=
        Kfun_refl_STR02927 E (diff_slice_STR02927 hOo hEC hO) (diff_slice_STR02927 hOo hEC hOr)
          hev1 hK0
      have hmemr : refl3_STR02927 (Z 0 h) ∈ N 0 := (hsym (Z 0 h)).mp (hZN 0 h hhη)
      have hfix : refl3_STR02927 (Z 0 h) = Z 0 h := (hKuniq 0 h hhη _ hmemr).mp hKr
      have h3 : -(Z 0 h 1) = Z 0 h 1 := congrFun hfix 1
      linarith
  have hrange : ∀ t : ℝ,
      ((ψ (h * Z 0 h 0, h * Z 0 h 1, h, h ^ 2 * Z 0 h 2) : E_STR02969) :
          PeriodicC2_STR02969).val (-t) =
        ((ψ (h * Z 0 h 0, h * Z 0 h 1, h, h ^ 2 * Z 0 h 2) : E_STR02969) :
          PeriodicC2_STR02969).val t := by
    obtain ⟨-, -, -, hp, -, hq⟩ := mem_omega_STR02927.mp (hhΩ 0)
    have hq' : ((h * Z 0 h 0, -(h * Z 0 h 1), h, h ^ 2 * Z 0 h 2) : Par_STR02916) ∈ W := by
      rw [← Ppar_refl_STR02927]
      exact hq
    have hb : -(h * Z 0 h 1) = h * Z 0 h 1 := by
      rw [hB0]
      ring
    have key := hW.psi_refl (h * Z 0 h 0) (h * Z 0 h 1) h (h ^ 2 * Z 0 h 2) hp hq'
    rw [hb] at key
    intro t
    exact (key t).symm
  have hchart0 : ∀ t : ℝ, chartU_STR02927 ψ h (Z 0 h) (-t) = chartU_STR02927 ψ h (Z 0 h) t :=
    chart_even_STR02927 hB0 hrange
  have hsignP : ∀ j : Fin 3, chartU_STR02927 ψ (-h) (Z j (-h)) =
      pb_STR02916 1 (-Real.pi) (chartU_STR02927 ψ h (Z j h)) := by
    intro j
    obtain ⟨-, -, -, hp, hq, -⟩ := mem_omega_STR02927.mp (hhΩ j)
    rw [hZeven j]
    exact chart_sign_STR02927 (psi_sign_P_STR02927 hW hp hq)
  refine ⟨⟨hB0, hrange, hchart0, rho_even_STR02927 h hchart0⟩, hZeven, ?_, ?_⟩
  · intro j t
    rw [hsignP j]
    exact rho_sign_STR02927 h (chartU_periodic_STR02927 ψ h (Z j h)) t
  · intro j
    rw [hsignP j]
    exact entropy_sign_STR02927 h (chartU_periodic_STR02927 ψ h (Z j h))

/-- STR029.27: reflection and sign symmetry of the branches. The data of STR029.23 (the range
graph `ψ`, the extension `E`, the three branches `Z j` with their neighbourhoods and uniqueness
clause) are restated, and then there is a radius `0 < δ ≤ η` such that for `|h| < δ`: branch zero
is even in `t` (`B_0(h) = 0` and the range component, `u_0`, `ρ_0` are even); each `z_j` is even in
`h`; `ρ_j(-h)(t) = ρ_j(h)(t - π)`; and `H_{-h}(ρ_j(-h)) = H_h(ρ_j(h))`. -/
theorem str029_27_reflection_sign_symmetry_branches :
    ∃ (U : Set Par_STR02916) (V : Set E_STR02969) (ψ : Par_STR02916 → E_STR02969),
      IsOpen U ∧ (0 : Par_STR02916) ∈ U ∧ IsOpen V ∧ (0 : E_STR02969) ∈ V ∧
      ContDiffOn ℝ ∞ ψ U ∧ ψ 0 = 0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
      (∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) ∧
      ∃ (O : Set (ℝ × (Fin 3 → ℝ))) (E : ℝ × (Fin 3 → ℝ) → ℝ),
        IsOpen O ∧ (∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O) ∧ ContDiffOn ℝ ∞ E O ∧
        (∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
          E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4) ∧
        (∀ z : Fin 3 → ℝ, E ((0 : ℝ), z) =
          Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2)) ∧
        ∃ η : ℝ, 0 < η ∧
          ∃ (N : Fin 3 → Set (Fin 3 → ℝ)) (Z : Fin 3 → ℝ → (Fin 3 → ℝ)),
            IsOpen (N 0) ∧ IsOpen (N 1) ∧ IsOpen (N 2) ∧
            N 0 ∈ 𝓝 (![2, 0, -16 / 15] : Fin 3 → ℝ) ∧
            N 1 ∈ 𝓝 (![-1, Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) ∧
            N 2 ∈ 𝓝 (![-1, -Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) ∧
            (∀ i j : Fin 3, i ≠ j → Disjoint (N i) (N j)) ∧
            (∀ z : Fin 3 → ℝ, z ∈ N 0 ↔ (![z 0, -z 1, z 2] : Fin 3 → ℝ) ∈ N 0) ∧
            N 1 = rot_STR02923 '' N 0 ∧ N 2 = rot_STR02923 '' N 1 ∧
            (∀ j : Fin 3, ContDiffOn ℝ ∞ (Z j) (Set.Ioo (-η) η)) ∧
            (∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, Z j h ∈ N j) ∧
            (∀ h ∈ Set.Ioo (-η) η, Z 1 h = rot_STR02923 (Z 0 h) ∧ Z 2 h = rot_STR02923 (Z 1 h)) ∧
            (∀ h ∈ Set.Ioo (-η) η, ∀ j : Fin 3, Z j h 2 = Z 0 h 2) ∧
            (∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, ∀ z ∈ N j,
              Kfun_STR02923 E (h, z) = 0 ↔ z = Z j h) ∧
            ∃ δ : ℝ, 0 < δ ∧ δ ≤ η ∧ ∀ h ∈ Set.Ioo (-δ) δ,
              (Z 0 h 1 = 0 ∧
                (∀ t : ℝ,
                  ((ψ (h * Z 0 h 0, h * Z 0 h 1, h, h ^ 2 * Z 0 h 2) : E_STR02969) :
                      PeriodicC2_STR02969).val (-t) =
                    ((ψ (h * Z 0 h 0, h * Z 0 h 1, h, h ^ 2 * Z 0 h 2) : E_STR02969) :
                      PeriodicC2_STR02969).val t) ∧
                (∀ t : ℝ, chartU_STR02927 ψ h (Z 0 h) (-t) = chartU_STR02927 ψ h (Z 0 h) t) ∧
                (∀ t : ℝ, rhoT_STR02901 h (chartU_STR02927 ψ h (Z 0 h)) (-t) =
                  rhoT_STR02901 h (chartU_STR02927 ψ h (Z 0 h)) t)) ∧
              (∀ j : Fin 3, Z j (-h) = Z j h) ∧
              (∀ j : Fin 3, ∀ t : ℝ,
                rhoT_STR02901 (-h) (chartU_STR02927 ψ (-h) (Z j (-h))) t =
                  rhoT_STR02901 h (chartU_STR02927 ψ h (Z j h)) (t - Real.pi)) ∧
              (∀ j : Fin 3, entropyChart_STR02949 (-h) (chartU_STR02927 ψ (-h) (Z j (-h))) =
                entropyChart_STR02949 h (chartU_STR02927 ψ h (Z j h))) := by
  obtain ⟨U, V, ψ, hUo, hU0, hVo, hV0, hψC, hψ0, hψV, hR, O, E, hOo, hOmem, hEC, hval, hzero, η,
    hη, N, Z, hN0, hN1, hN2, hn0, hn1, hn2, hdisj, hsym, hrot1, hrot2, hZC, hZN, hZrot, hZs,
    hKuniq⟩ := str029_23_three_locally_unique_solution_branches
  exact ⟨U, V, ψ, hUo, hU0, hVo, hV0, hψC, hψ0, hψV, hR, O, E, hOo, hOmem, hEC, hval, hzero, η,
    hη, N, Z, hN0, hN1, hN2, hn0, hn1, hn2, hdisj, hsym, hrot1, hrot2, hZC, hZN, hZrot, hZs,
    hKuniq, str029_27_reflection_sign_symmetry_branches_of_data hUo hU0 hVo hV0 hR hOo hOmem hEC
      hval hzero hη hn0 hsym hZC hZN hKuniq⟩

end DGPS.Frontier.STR029
