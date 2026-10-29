import DGRHS.Commutator.SourceRieszLocalNumerator
import DGRHS.Commutator.SourceRieszLocalPartition

/-! Source Lemma 7.2 (local numerator estimate, TeX 3307-3318) for the Riesz kernel
`0<s<d/2`, as a standalone export with the shape of
`exists_sourceLogTransport_local_numerator`.

Constants. `Csr` is `sourceRieszLocalProfileConstant s n` (the printed `C_{sr,n}`, which
depends only on `d`, `s`, `n`; so `s` is fixed before `Csr`).  `βloc` is the checked
`sourceRieszLocalBeta s M` (it depends only on `s`, `M`, `d`).  The coefficient is the
printed `γ/(4 C_{sr,n} ‖∇v‖^n)` with `K` the Lipschitz constant in place of `‖∇v‖_{L^∞}`.
The upper bound is exactly the printed `e + L`, with `L = glzUniversalTailConstant`
(no sharper constant is claimed, unlike the LOG export which obtains `e`).
The exponent is `σ ε N A_n - γ N F_N`, written as `σ ε (N A_n) + sourceRieszLocalParticleExponent`
because `sourceRieszLocalParticleExponent ρ s γ N = -γ N F_N` by definition; `A_n` is
`sourceRieszLocalTransportEnergy` (the active Riesz transport energy). -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration

/-- Source Lemma 7.2 for the Riesz kernel: local numerator estimate with the printed
`e + L`.  The coefficient constant `Csr` is chosen before the Lipschitz field, the density,
`γ`, `σ`, `N`; `βloc` is chosen after the density. -/
theorem exists_sourceRieszTransport_local_numerator {ι : Type*} [Fintype ι]
    (n : ℕ) (hn : 0 < n) (s : ℝ) (hs : 0 < s) (hd : 2 * s < (Fintype.card ι : ℝ)) :
    ∃ Csr : ℝ, 0 < Csr ∧ ∀ {K : ℝ≥0}
      {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}, LipschitzWith K v →
      0 < (K : ℝ) →
      ∀ (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ), 0 ≤ M →
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume, ρ x ≤ M) →
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ γ : ℝ, 0 ≤ γ → γ ≤ βloc →
      ∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 0 < N →
      Integrable (fun x : Fin N → EuclideanSpace ℝ ι =>
        Real.exp (σ * (γ / (4 * Csr * (K : ℝ) ^ n)) *
            ((N : ℝ) * sourceRieszLocalTransportEnergy ρ s n v N x) +
          sourceRieszLocalParticleExponent ρ s γ N x))
        (Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ)) ∧
      (∫ x : Fin N → EuclideanSpace ℝ ι,
        Real.exp (σ * (γ / (4 * Csr * (K : ℝ) ^ n)) *
            ((N : ℝ) * sourceRieszLocalTransportEnergy ρ s n v N x) +
          sourceRieszLocalParticleExponent ρ s γ N x)
        ∂Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ)) ≤
          Real.exp 1 + glzUniversalTailConstant := by
  have hs' : s < (Fintype.card ι : ℝ) := by linarith
  refine ⟨sourceRieszLocalProfileConstant (ι := ι) s n,
    (sourceRieszLocalProfileConstant_properties (ι := ι) s n).1, ?_⟩
  intro K v hv hK ρ M hM hprob hρ
  have hloc := (sourceRieszLocalBeta_properties (ι := ι) s M hs hs' hM).1
  refine ⟨sourceRieszLocalBeta (ι := ι) s M, hloc, ?_⟩
  intro γ hγ hγb σ hσ N hN
  have hL := glzUniversalTailConstant_pos
  have hexp : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  rcases hγ.eq_or_lt with h0 | hpos
  · subst h0
    have hz : (fun x : Fin N → EuclideanSpace ℝ ι =>
        Real.exp (σ * ((0 : ℝ) / (4 * sourceRieszLocalProfileConstant (ι := ι) s n *
            (K : ℝ) ^ n)) *
            ((N : ℝ) * sourceRieszLocalTransportEnergy ρ s n v N x) +
          sourceRieszLocalParticleExponent ρ s 0 N x)) = fun _ => 1 := by
      funext x
      simp [sourceRieszLocalParticleExponent]
    rw [hz]
    refine ⟨integrable_const 1, ?_⟩
    have h1 : (∫ _x : Fin N → EuclideanSpace ℝ ι, (1 : ℝ)
        ∂Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ)) = 1 := by simp
    rw [h1]
    linarith
  · have hN1 : 1 ≤ N := hN
    obtain ⟨hi, hb⟩ := sourceRieszLocal_numerator s n hs hd γ σ hpos hσ.le hv ρ M hM hρ N hN1 hγb
    have he : (fun x : Fin N → EuclideanSpace ℝ ι =>
        Real.exp (σ * (γ / (4 * sourceRieszLocalProfileConstant (ι := ι) s n *
            (K : ℝ) ^ n)) *
            ((N : ℝ) * sourceRieszLocalTransportEnergy ρ s n v N x) +
          sourceRieszLocalParticleExponent ρ s γ N x)) =
        fun x => Real.exp (sourceRieszLocalNumeratorExponent ρ s n γ σ K v N x) := by
      funext x
      congr 1
      unfold sourceRieszLocalNumeratorExponent sourceRieszLocalParticleExponent
        sourceRieszLocalCoefficient
      ring
    rw [he]
    exact ⟨hi, hb⟩

end DGRHS.Commutator
#check @DGRHS.Commutator.exists_sourceRieszTransport_local_numerator
#print axioms DGRHS.Commutator.exists_sourceRieszTransport_local_numerator
