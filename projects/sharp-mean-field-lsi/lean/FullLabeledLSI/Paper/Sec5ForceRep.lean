import FullLabeledLSI.Paper.Sec5ForceDefs
import SharpSymmetricLSI.Statements.R20_Lemma_5_3

/-!
# Lemma 5.5: bounded measurable representatives of `b` and `b_Δ`
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- Bounded measurable representatives `bF` of `b = ∇₁K` and `bΔ` of `b_Δ`, with the a.e.
identities `b = bF` (`m ⊗ m`-a.e.) and `∇_iU_N = G_i` (`m^{⊗N}`-a.e.). -/
theorem exists_force_rep {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : SharpLSI.Hyp V W KV KW) (μ : ProbabilityMeasure (Torus d))
    (hμ : SharpLSI.IsMinimizer V W μ) :
    ∃ (bF : Torus d → Torus d → Fin d → ℝ) (bΔ : Torus d → Fin d → ℝ) (Bb : ℝ),
      ForceRep bF bΔ Bb ∧
      (∀ᵐ p ∂(SharpLSI.haar d).prod (SharpLSI.haar d), ∀ k,
        SharpLSI.bForce W (μ : Measure (Torus d)) p.1 p.2 k = bF p.1 p.2 k) ∧
      ∀ N : ℕ, 1 ≤ N → ∀ᵐ X ∂(volume : Measure (Config N d)), ∀ i k,
        SharpLSI.weakGradC (SharpLSI.Ucentered W (μ : Measure (Torus d)) N) X i k =
          Gpart bF bΔ N X i k := by
  have hac := SharpLSI.minimizer_ac hyp hμ
  set β := SharpLSI.bForceL W (SharpLSI.densOf (μ : Measure (Torus d))) with hβ
  obtain ⟨hw, hβm, ⟨Cβ, hCβ⟩, -⟩ := SharpLSI.forceMean_props hyp hac
  obtain ⟨Cb, hCb⟩ := SharpLSI.bGrad_bdd hyp (W := W)
  have hdiag : ∀ᵐ x ∂SharpLSI.haar d, ∀ k, SharpLSI.bDiag W μ x k = -β x k := by
    filter_upwards [SharpLSI.weakGrad_ae_eq (SharpLSI.isWeakGrad_diagK hyp hac)] with x hx k
    simp only [SharpLSI.bDiag]; rw [congrFun hx k]
  refine ⟨fun x y k => SharpLSI.bGrad W x y k - β x k, fun x k => -β x k, |Cb| + |Cβ|,
    ⟨fun k => ?_, fun k => ?_, fun x y k => ?_, fun x k => ?_⟩, ?_, fun N hN => ?_⟩
  · exact (SharpLSI.measurable_bGrad hyp (W := W) k).sub ((hβm k).comp measurable_fst)
  · exact (hβm k).neg
  · refine (abs_sub _ _).trans ?_
    exact add_le_add ((hCb x y k).trans (le_abs_self _)) ((hCβ x k).trans (le_abs_self _))
  · rw [abs_neg]; exact ((hCβ x k).trans (le_abs_self _)).trans (le_add_of_nonneg_left (abs_nonneg _))
  · filter_upwards [SharpLSI.bForce_ae_prod hyp hac] with p hp k
    exact hp k
  · have hflat : MeasurePreserving (SharpLSI.flat : Config N d → UnitAddTorus (Fin N × Fin d))
        volume volume := ⟨SharpLSI.measurable_flat, SharpLSI.map_flat_volume N⟩
    have hK := SharpLSI.weakGrad_ae_eq (SharpLSI.isWeakGrad_K2 hyp hac)
    have hb : ∀ᵐ X ∂(volume : Measure (Config N d)), ∀ i l : Fin N, i ≠ l → ∀ k,
        SharpLSI.bForce W μ (X i) (X l) k = SharpLSI.bGrad W (X i) (X l) k - β (X i) k := by
      refine ae_all_iff.mpr fun i => ae_all_iff.mpr fun l => ?_
      by_cases hil : i = l
      · exact Filter.Eventually.of_forall fun X h => absurd hil h
      have := (((SharpLSI.measurePreserving_projPair (d := d) hil).comp
        hflat).quasiMeasurePreserving.ae hK)
      filter_upwards [this] with X hX _ k
      simp only [Function.comp, SharpLSI.projPair_flat] at hX
      rw [SharpLSI.bForce_eq_weakGrad_K2,
        show SharpLSI.pairFlat (X i, X l) = SharpLSI.flat ![X i, X l] from rfl, hX,
        ← SharpLSI.gK_pairFlat]
      rfl
    have hdd : ∀ᵐ X ∂(volume : Measure (Config N d)), ∀ i k,
        SharpLSI.bDiag W μ (X i) k = -β (X i) k := by
      refine ae_all_iff.mpr fun i => ?_
      have := ((SharpLSI.measurePreserving_projBlock (d := d) i).comp
        hflat).quasiMeasurePreserving.ae
        (show ∀ᵐ x ∂(volume : Measure (Torus d)), ∀ k, SharpLSI.bDiag W μ x k = -β x k from hdiag)
      filter_upwards [this] with X hX
      exact hX
    filter_upwards [(SharpLSI.particle_force hd hyp hμ).2.2 N hN, hb, hdd] with X hX hbX hdX i k
    have hsum : (∑ l, if l ≠ i then SharpLSI.bForce W (μ : Measure (Torus d)) (X i) (X l) k
        else 0) = ∑ l, if l ≠ i then (SharpLSI.bGrad W (X i) (X l) k - β (X i) k) else 0 := by
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : l ≠ i
      · simp only [hl, ne_eq, not_false_eq_true, ite_true]; exact hbX i l (Ne.symm hl) k
      · simp [hl]
    rw [hX i k, hdX i k, hsum]
    rfl

end SharpLSI.FL
