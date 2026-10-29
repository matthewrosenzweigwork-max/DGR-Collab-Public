import Mathlib

/-!
# LIP051.26: Representative invariance of sampled joint maps

Task id: LIP051.26 (node LIP051, joint Gaussian and quadratic fluctuation limit).
Title: Representative invariance of sampled joint maps.

Provides:
* `DGPS.Frontier.LIP051.lip051_26_representative_invariance_sampled_joint_maps`: for a probability
  measure `μ` on a measurable space `E`, measurable real functions `f i`, `g i` (`i : ℕ`) with
  `f i =ᵐ[μ] g i` for every `i`, a particle number `N`, and a finite list `j : Fin m → ℕ`, the sampled
  arrays `(f (j k) (ω l))_{k,l}` and `(g (j k) (ω l))_{k,l}` on the product `μ^N` are equal almost
  everywhere; for every measurable `Φ` on the array space and every measurable `H` on the particle
  space, the joint maps `(Φ(f-array), H)` and `(Φ(g-array), H)` are equal almost everywhere and have
  equal laws (`Measure.map`); and `Φ(f-array)`, `Φ(g-array)` have equal laws.
* `DGPS.Frontier.LIP051.lip051_26_representative_invariance_sampled_joint_maps_measurable`: the sampled
  array and the joint maps built from it are measurable under the stated hypotheses, so the
  `Measure.map` in the main statement is the genuine pushforward law.
* Helpers (all suffixed `_LIP05126`): `ae_eval_eq_LIP05126` (almost-everywhere agreement of one
  coordinate entry, obtained from the coordinate marginal of `μ^N`) and `measurable_array_LIP05126`
  (measurability of the sampled array).

R5 notes:
* Ambient space. `E` is an arbitrary measurable space with `[IsProbabilityMeasure μ]`, `μ^N` is
  `Measure.pi (fun _ : Fin N => μ)` on `Fin N → E`. The campaign's `Torus d` is an instance; no
  property of the torus is used, so the statement is at least as general as the specification.
* Features. `f`, `g` are `ℕ`-indexed families of measurable real-valued functions on `E`, as the
  specification states. The specification's indices `j_1,…,j_m` are a finite list `j : Fin m → ℕ`;
  repetitions and the empty list are allowed, and `N = 0` is allowed.
* Hypotheses. Exactly those of the specification: measurability of every `f i` and `g i`, and
  `f i =ᵐ[μ] g i` for every `i`. Nothing else is assumed. No injectivity or distinctness of `j`.
* Arrays and maps. The array space is `Fin m → Fin N → ℝ` with the Pi σ-algebra; the particle space is
  `Fin N → E` with the Pi σ-algebra. `Φ` and `H` range over arbitrary measurable spaces `β` and `γ`
  (fixed by the theorem's binders, with `Φ` and `H` universally quantified in the conclusion).
* "Equal laws" is read as equality of `Measure.map` pushforwards on `μ^N`. Measurability of the maps is
  not part of the frozen conclusion; it is proved as a separate public lemma, under the same hypotheses
  plus measurability of `Φ` and `H`. The almost-everywhere equality argument itself does not use
  measurability of `Φ` or `H`, nor of the features `f i`, `g i`: those measurability hypotheses are
  carried as specified (and so are named `_hf`, `_hg`), but the argument does not consume them.
* Proved inputs. The specification cites `LIP051.35` and `LIP051.36`. This module does not depend on them.
  It uses only the one-coordinate content of the restriction law, namely that `Function.eval l` pushes
  `μ^N` forward to `μ` (Mathlib's `measurePreserving_eval`), which is the singleton case of `.35`.
* Mode indexing (FD-002). This unit has no Gaussian object, no Fourier mode, and no positive-mode
  convention. The statement holds for every index `j k : ℕ`, including index `0`, and no mode-zero
  restriction is added or dropped.
-/

namespace DGPS.Frontier.LIP051

open MeasureTheory

/-- Almost-everywhere agreement of `φ` and `ψ` under `μ` transfers to the `l`-th coordinate of `μ^N`. -/
lemma ae_eval_eq_LIP05126 {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    {N : ℕ} (φ ψ : E → ℝ) (h : φ =ᵐ[μ] ψ) (l : Fin N) :
    ∀ᵐ ω ∂(Measure.pi (fun _ : Fin N => μ)), φ (ω l) = ψ (ω l) :=
  (measurePreserving_eval (fun _ : Fin N => μ) l).quasiMeasurePreserving.ae_eq_comp h

/-- The sampled array `ω ↦ (φ (ω l))` indexed by `k` and `l` is measurable. -/
lemma measurable_array_LIP05126 {E : Type*} [MeasurableSpace E] {N m : ℕ} (f : ℕ → E → ℝ)
    (hf : ∀ i, Measurable (f i)) (j : Fin m → ℕ) :
    Measurable (fun ω : Fin N → E => fun (k : Fin m) (l : Fin N) => f (j k) (ω l)) :=
  Measurable.of_eval fun k => Measurable.of_eval fun l =>
    (hf (j k)).comp (measurable_pi_apply l)

/-- **LIP051.26.** Representative invariance of the sampled joint maps. Replacing each feature by an
almost-everywhere equal representative changes neither the sampled arrays (almost everywhere on
`μ^N`), nor the joint laws of `Φ(array)` together with any auxiliary `H`, nor the laws of `Φ(array)`. -/
theorem lip051_26_representative_invariance_sampled_joint_maps
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (f g : ℕ → E → ℝ) (_hf : ∀ i, Measurable (f i)) (_hg : ∀ i, Measurable (g i))
    (hfg : ∀ i, f i =ᵐ[μ] g i) (N m : ℕ) (j : Fin m → ℕ) :
    (fun ω : Fin N → E => fun (k : Fin m) (l : Fin N) => f (j k) (ω l))
        =ᵐ[Measure.pi (fun _ : Fin N => μ)]
      (fun ω : Fin N → E => fun (k : Fin m) (l : Fin N) => g (j k) (ω l)) ∧
    (∀ Φ : (Fin m → Fin N → ℝ) → β, Measurable Φ →
      Measure.map (fun ω : Fin N → E => Φ (fun (k : Fin m) (l : Fin N) => f (j k) (ω l)))
          (Measure.pi (fun _ : Fin N => μ))
        = Measure.map (fun ω : Fin N → E => Φ (fun (k : Fin m) (l : Fin N) => g (j k) (ω l)))
          (Measure.pi (fun _ : Fin N => μ))) ∧
    (∀ Φ : (Fin m → Fin N → ℝ) → β, Measurable Φ → ∀ H : (Fin N → E) → γ, Measurable H →
      (fun ω : Fin N → E =>
          (Φ (fun (k : Fin m) (l : Fin N) => f (j k) (ω l)), H ω))
        =ᵐ[Measure.pi (fun _ : Fin N => μ)]
      (fun ω : Fin N → E =>
          (Φ (fun (k : Fin m) (l : Fin N) => g (j k) (ω l)), H ω)) ∧
      Measure.map
          (fun ω : Fin N → E =>
            (Φ (fun (k : Fin m) (l : Fin N) => f (j k) (ω l)), H ω))
          (Measure.pi (fun _ : Fin N => μ))
        = Measure.map
          (fun ω : Fin N → E =>
            (Φ (fun (k : Fin m) (l : Fin N) => g (j k) (ω l)), H ω))
          (Measure.pi (fun _ : Fin N => μ))) := by
  have harr : (fun ω : Fin N → E => fun (k : Fin m) (l : Fin N) => f (j k) (ω l))
      =ᵐ[Measure.pi (fun _ : Fin N => μ)]
      (fun ω : Fin N → E => fun (k : Fin m) (l : Fin N) => g (j k) (ω l)) := by
    have hall : ∀ᵐ ω ∂(Measure.pi (fun _ : Fin N => μ)),
        ∀ (k : Fin m) (l : Fin N), f (j k) (ω l) = g (j k) (ω l) :=
      ae_all_iff.2 fun k => ae_all_iff.2 fun l =>
        ae_eval_eq_LIP05126 μ (f (j k)) (g (j k)) (hfg (j k)) l
    filter_upwards [hall] with ω hω
    funext k l
    exact hω k l
  refine ⟨harr, ?_, ?_⟩
  · intro Φ _
    have hΦ : (fun ω : Fin N → E => Φ (fun (k : Fin m) (l : Fin N) => f (j k) (ω l)))
        =ᵐ[Measure.pi (fun _ : Fin N => μ)]
        (fun ω : Fin N → E => Φ (fun (k : Fin m) (l : Fin N) => g (j k) (ω l))) := by
      filter_upwards [harr] with ω hω
      rw [hω]
    exact Measure.map_congr hΦ
  · intro Φ _ H _
    have hJ : (fun ω : Fin N → E =>
          (Φ (fun (k : Fin m) (l : Fin N) => f (j k) (ω l)), H ω))
        =ᵐ[Measure.pi (fun _ : Fin N => μ)]
        (fun ω : Fin N → E =>
          (Φ (fun (k : Fin m) (l : Fin N) => g (j k) (ω l)), H ω)) := by
      filter_upwards [harr] with ω hω
      rw [hω]
    exact ⟨hJ, Measure.map_congr hJ⟩

/-- **LIP051.26 (measurability).** Under the same hypotheses, with `Φ` and `H` measurable, the sampled
array and the joint maps `(Φ(array), H)` are measurable, so their `Measure.map` is the genuine
pushforward law. -/
theorem lip051_26_representative_invariance_sampled_joint_maps_measurable
    {E : Type*} [MeasurableSpace E]
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (f : ℕ → E → ℝ) (hf : ∀ i, Measurable (f i)) (N m : ℕ) (j : Fin m → ℕ)
    (Φ : (Fin m → Fin N → ℝ) → β) (hΦ : Measurable Φ) (H : (Fin N → E) → γ) (hH : Measurable H) :
    Measurable (fun ω : Fin N → E => Φ (fun (k : Fin m) (l : Fin N) => f (j k) (ω l))) ∧
    Measurable (fun ω : Fin N → E =>
      (Φ (fun (k : Fin m) (l : Fin N) => f (j k) (ω l)), H ω)) :=
  ⟨hΦ.comp (measurable_array_LIP05126 f hf j),
    (hΦ.comp (measurable_array_LIP05126 f hf j)).prodMk hH⟩

end DGPS.Frontier.LIP051
