import DGPS.Lipschitz.T01HybridComparison
import DGPS.Lipschitz.T01DependencyBridge
import FullLabeledLSI.Paper.Hybrid63AltI

/-!
# Finite-rank comparison on the actual campaign reference

For a genuine finite-rank approximation, the hybrid ground-state calculation controls the
reference comparison form by the seven explicit labeled-replacement errors. All basis,
Sobolev, and one-body LSI data are discharged on the same campaign spectral witness.
The finite matrix positivity and inverse remain explicit inputs to this finite-rank step.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace DGPS.Lipschitz

open KernelApproximation SharpLSI SharpLSI.FL

theorem finite_rank_reference_comparison {d : ℕ}
    (S : Spec d) (aux : Aux S)
    (he : SharpLSI.IsRefEigenbasis S.mu S.v S.lam)
    (hC1 : ∀ j, Gross.C1T (S.v j)) (hlam0 : S.lam 0 = 0) (hlam1 : 0 < S.lam 1)
    {W : Torus d → Torus d → ℝ}
    (A : FiniteRankApprox W S.mu S.v) (CR : ℕ → ℕ → ℕ → ℝ) (R : ℕ)
    {σ : ℝ} (hσ : 0 < σ) (hpos : PosIPlus A R σ) (hC : IsInverseOfIPlus (A.a R) (CR R))
    (J : ℕ) (hJ : ∀ i ∈ A.s R, i < J) (L : ℝ) {N : ℕ} (T : Finset (Fin N → ℕ))
    (cc : (Fin N → ℕ) → ℝ) (hT : ∀ k ∈ T, ∑ i, S.lam (k i) ≤ L) (hTJ : ∀ k ∈ T, ∀ i, k i ≤ J)
    (F : Config N d → ℝ) (hF : ∀ X, F X = ∑ k ∈ T, cc k * ∏ i, S.v (k i) (X i))
    (δ : ℝ) (hn : 0 < lowCount (coefArr (J := J) T cc) δ) :
    -(errT1 S.mu A S.lam R S.v (coefArr (J := J) T cc) δ +
      errT2 S.mu A S.lam R S.v (coefArr (J := J) T cc) δ +
      (bRate S.mu S.lam (CR R)).toReal / 2 *
        (errT3 S.mu S.v (coefArr (J := J) T cc) δ +
          errT4 S.mu S.v (coefArr (J := J) T cc) δ +
          errT5 S.mu A R S.v (coefArr (J := J) T cc) δ +
          errT6 S.mu A R S.v (coefArr (J := J) T cc) δ +
          |Real.log (kappaR A R)| * errT7 S.mu S.v (coefArr (J := J) T cc) δ))
      ≤ Jexpr A S.lam (CR R) R F := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  let P : BoundedPositiveReference d :=
    { density := S.w, measurable_density := S.meas, lower := S.c, upper := S.C,
      lower_pos := S.pos, lower_le := S.bound.mono fun _ hx => hx.1,
      le_upper := S.bound.mono fun _ hx => hx.2, mass_one := S.prob }
  have hG := goodBasis_of_spec_aux S aux
  have hae : ∀ j, S.v j =ᵐ[S.mu] S.v j := fun _ => Filter.EventuallyEq.refl _ _
  set c : (Fin N → Fin (J + 1)) → ℝ := coefArr (J := J) T cc with hc
  have hcspec : SpectralCoeff S.lam L c := spectralCoeff_coefArr S.lam L T hT cc
  have hFe : F = polyEval S.v c := funext fun X => by
    rw [hF X, hc, polyEval_coefArr S.v T hTJ cc X]
  have hac : S.mu ≪ volume := Analysis.CompactResolvent.wMeasure_ac_haar
  have hca : volume ≪ S.mu := Analysis.CompactResolvent.haar_ac_wMeasure S.pos S.bound
  have hlamnn := S.lam_nonneg
  -- the energy
  have hnn : 0 ≤ ∑ k ∈ T, (∑ i, S.lam (k i)) * cc k ^ 2 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (Finset.sum_nonneg fun i _ => hlamnn _) (sq_nonneg _)
  have hE : (refEnergy S.mu (polyEval S.v c)).toReal =
      ∑ j, (∑ i, S.lam (j i)) * c j ^ 2 := by
    have := (Gross.torus_energy_formula hac hca he hC1 hae T cc
      (F := polyEval S.v c) (fun X => by rw [hc, polyEval_coefArr S.v T hTJ cc X])).2
    rw [this, ENNReal.toReal_ofReal hnn, hc, energy_coefArr S.lam T hTJ cc]
  -- the hybrid inequality
  have hBs : (retained c δ).card < N := by
    have : (retained c δ).card ≤ N := by simpa using Finset.card_le_univ (retained c δ)
    unfold lowCount at hn; omega
  have hH := hybrid_comparison_of_campaign_reference (P := P) he hC1 hlam0 A hJ
    (lt_min hσ one_pos) (HLA.posTm_of_posIPlus A hJ hσ hpos) hC
    (retained c δ) hBs c
  -- the entropies
  have hmomE : HybridPolyMoment S.mu S.v S.lam J :=
    hybrid_moments_of_campaign_reference P he hC1 hlam0 hlam1 J
  obtain ⟨K4, -, hK4⟩ := hyb_integrable_pow hG hmomE L 4
  have hentH := ent_toReal_formula (hybMeasure S.mu N J)
    (measurable_polyB hG c (retained c δ)) (hK4 N (retained c δ) c hcspec).1
  obtain ⟨Kb, hKb⟩ := polyEval_bounded hG c
  have hentQ := ent_toReal_formula (Measure.pi fun _ : Fin N => S.mu)
    (measurable_polyEval hG c)
    (Integrable.of_bound ((measurable_polyEval hG c).abs.pow_const 4).aestronglyMeasurable
      (|Kb| ^ 4) (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_pow, abs_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) ((hKb X).trans (le_abs_self _)) 4))
  -- assemble
  have hJe := Jexpr_eq_e' A S.lam (CR R) R hae c hE
  rw [hFe, hJe]
  have key := master_alg (E := ∑ j, (∑ i, S.lam (j i)) * c j ^ 2)
    (Vq := ∫ X, polyEval S.v c X ^ 2 * vR A S.lam R (fun n => fluct S.v N n X)
      ∂Measure.pi (fun _ : Fin N => S.mu))
    (Vl := ∫ X, polyEval S.v c X ^ 2 * vR A S.lam R (zext (fun m : Fin J => Zlow S.v c δ X m))
      ∂Measure.pi (fun _ : Fin N => S.mu))
    (Uq := ∫ X, polyEval S.v c X ^ 2 * uR A R (fun n => fluct S.v N n X)
      ∂Measure.pi (fun _ : Fin N => S.mu))
    (Ul := ∫ X, polyEval S.v c X ^ 2 * uR A R (zext (fun m : Fin J => Zlow S.v c δ X m))
      ∂Measure.pi (fun _ : Fin N => S.mu))
    (ρ := (bRate S.mu S.lam (CR R)).toReal) (K := Real.log (kappaR A R))
    ENNReal.toReal_nonneg hentQ hentH hH
  unfold errT1 errT2 errT3 errT4 errT5 errT6 errT7
  exact key


end DGPS.Lipschitz
