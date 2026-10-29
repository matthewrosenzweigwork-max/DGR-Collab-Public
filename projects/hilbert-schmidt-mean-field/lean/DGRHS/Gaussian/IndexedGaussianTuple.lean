import DGRHS.Gaussian.IndexedGaussianLaw

/-!
Adapted under Apache-2.0 from StatLean/Stat-Lean IsonormalProcess.lean,
revision 86b3823f77fc2b0f5a9923f85b588a4f8a65f94c,
upstream path StatLean/AsymptoticStatistics/ForMathlib/Probability/IsonormalProcess.lean,
SHA-256 eab89af1820ec44fc960b1a702a99f4267ba6f182759504d4b585dcc0bc6c5fa.
See Imported/LICENSE. The finite-tuple proof is generalized from the Nat-basis
map to the constructed map for any countable genuine Hilbert-basis index.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators InnerProductSpace

namespace DGRHS.Gaussian
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem indexedGaussianIsometry_hasGaussianLaw_tuple [Countable ι] {m : ℕ}
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f) (h : Fin m → H) :
    HasGaussianLaw
      (fun ω => (fun k => indexedGaussianIsometry b f hf (h k) ω) : (ℕ → ℝ) → (Fin m → ℝ)) IsonormalProcess.iidStdGaussian := by
  classical
  set P := IsonormalProcess.iidStdGaussian
  set X : (ℕ → ℝ) → (Fin m → ℝ) := fun ω k => indexedGaussianIsometry b f hf (h k) ω with hX
  -- `X` is a.e.-measurable (each coordinate is, and the codomain is a finite product).
  have hXmeas : AEMeasurable X P := by
    apply aemeasurable_pi_iff.mpr
    intro k
    exact (Lp.aestronglyMeasurable (indexedGaussianIsometry b f hf (h k))).aemeasurable
  rw [hasGaussianLaw_iff_charFunDual_map_eq hXmeas]
  intro L
  -- `combo L = ∑ k, L(Pi.single k 1) • h k`, and `L ∘ X =ᵐ indexedGaussianIsometry b f hf (combo L)`.
  set combo : H := ∑ k, L (Pi.single k 1) • h k with hcombo
  have hLX_ae : (fun ω => L (X ω)) =ᵐ[P] (indexedGaussianIsometry b f hf combo : (ℕ → ℝ) → ℝ) := by
    -- coeFn of the `Lp` linear combination equals the pointwise sum, a.e.
    have hiso_sum : (indexedGaussianIsometry b f hf combo : Lp ℝ 2 P)
        = ∑ k, (L (Pi.single k 1)) • indexedGaussianIsometry b f hf (h k) := by
      rw [hcombo, map_sum]
      simp_rw [map_smul]
    have hcoe : (indexedGaussianIsometry b f hf combo : (ℕ → ℝ) → ℝ)
        =ᵐ[P] fun ω => ∑ k, (L (Pi.single k 1)) * (indexedGaussianIsometry b f hf (h k) ω) := by
      rw [hiso_sum]
      refine (IsonormalProcess.coeFn_lp_finset_sum (fun k => (L (Pi.single k 1)) • indexedGaussianIsometry b f hf (h k))
        Finset.univ).trans ?_
      have hsmul : ∀ k : Fin m, (⇑((L (Pi.single k 1)) • indexedGaussianIsometry b f hf (h k)) : (ℕ → ℝ) → ℝ)
          =ᵐ[P] fun ω => (L (Pi.single k 1)) * (indexedGaussianIsometry b f hf (h k) ω) := by
        intro k
        filter_upwards [Lp.coeFn_smul (L (Pi.single k 1)) (indexedGaussianIsometry b f hf (h k))] with ω hω
        rw [hω]; rfl
      filter_upwards [(ae_all_iff.mpr hsmul)] with ω hω
      exact Finset.sum_congr rfl (fun k _ => hω k)
    filter_upwards [hcoe] with ω hω
    -- `L (X ω) = ∑ k, (X ω k) • L(Pi.single k 1) = ∑ k, L(Pi.single k 1) * indexedGaussianIsometry b f hf (h k) ω`.
    rw [hω]
    have hdecomp : L (X ω) = ∑ k, (X ω k) • L (Pi.single k 1) := by
      conv_lhs => rw [show (X ω : Fin m → ℝ) = ∑ k, (X ω k) • (Pi.single k 1 : Fin m → ℝ) from
        pi_eq_sum_univ' (X ω)]
      rw [map_sum]
      simp only [map_smul]
    rw [hdecomp]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [hX, smul_eq_mul]
    ring
  -- `L ∘ X` is Gaussian (a.e.-equal to the 1-D isonormal image).
  have hLX_gauss : HasGaussianLaw (fun ω => L (X ω)) P :=
    (hasGaussianLaw_indexedGaussianIsometry b f hf combo).congr hLX_ae.symm
  -- Transport the scalar `charFunDual_map_eq` to the vector `charFunDual (P.map X) L`.
  have hidR : (ContinuousLinearMap.id ℝ ℝ : StrongDual ℝ ℝ) ∘L L = L :=
    ContinuousLinearMap.id_comp L
  have hmapmap : P.map (fun ω => L (X ω)) = (P.map X).map L := by
    rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hXmeas]
    rfl
  calc charFunDual (P.map X) L
      = charFunDual (P.map X) ((ContinuousLinearMap.id ℝ ℝ) ∘L L) := by rw [hidR]
    _ = charFunDual ((P.map X).map L) (ContinuousLinearMap.id ℝ ℝ) :=
        (charFunDual_map L (ContinuousLinearMap.id ℝ ℝ)).symm
    _ = charFunDual (P.map (fun ω => L (X ω))) (ContinuousLinearMap.id ℝ ℝ) := by rw [hmapmap]
    _ = Complex.exp ((∫ ω, (ContinuousLinearMap.id ℝ ℝ) (L (X ω)) ∂P : ℝ) * Complex.I
          - Var[fun ω => (ContinuousLinearMap.id ℝ ℝ) (L (X ω)) ; P] / 2) :=
        hLX_gauss.charFunDual_map_eq_fun (ContinuousLinearMap.id ℝ ℝ)
    _ = Complex.exp ((∫ ω, L (X ω) ∂P : ℝ) * Complex.I
          - Var[fun ω => L (X ω) ; P] / 2) := by simp only [ContinuousLinearMap.id_apply]
    _ = Complex.exp ((P[(L : (Fin m → ℝ) →L[ℝ] ℝ) ∘ X] : ℝ) * Complex.I
          - Var[(L : (Fin m → ℝ) →L[ℝ] ℝ) ∘ X ; P] / 2) := by
        simp only [Function.comp_def]


end DGRHS.Gaussian

#print axioms DGRHS.Gaussian.indexedGaussianIsometry_hasGaussianLaw_tuple
#check DGRHS.Gaussian.indexedGaussianIsometry_hasGaussianLaw_tuple
