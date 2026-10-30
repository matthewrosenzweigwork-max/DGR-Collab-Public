import DGPS.Examples.ThreeSpeciesCircle.InteractingMinimizerLocalization

/-! A genuine pointwise control of continuous representatives by the accepted
original Haar-H1 metric. This supplies the first topology upgrade for capture;
it does not assert higher-derivative convergence or branch classification. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- No positivity is needed for this original-H1 embedding estimate. Both
stored roots may have arbitrary null-set values. -/
theorem ordinaryRoot_continuous_deviation_bound (σ ρ : AbsoluteDensity 1)
    {u v : Torus 1 → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hσu : σ.sqrt =ᵐ[haar 1] u) (hρv : ρ.sqrt =ᵐ[haar 1] v) :
    ∀ x, |v x - u x| ≤ ordinaryRootH1Deviation σ ρ u := by
  have hσ := (isWeakGradient_weakGradient σ.sqrt_mem).congr_ae hσu (ae_eq_refl _)
  have hρ := (isWeakGradient_weakGradient ρ.sqrt_mem).congr_ae hρv (ae_eq_refl _)
  have hd : IsWeakGradient (fun x => v x - u x)
      (fun x => weakGradient ρ.sqrt ρ.sqrt_mem x - weakGradient σ.sqrt σ.sqrt_mem x) :=
    by
      have hh := hρ.add (hσ.smul (-1))
      exact hh.congr_ae (Eventually.of_forall fun x => by ring)
        (Eventually.of_forall fun x => by simp [sub_eq_add_neg])
  obtain ⟨w, hw, hwe, _, hwb⟩ := exists_continuous_rep_one hd
  have he : w = fun x => v x - u x :=
    MeasureTheory.Measure.eq_of_ae_eq hwe hw (hv.sub hu)
  have hnorm : eLpNorm (fun x => v x - u x) 2 (haar 1) =
      eLpNorm (fun x => ρ.sqrt x - u x) 2 (haar 1) := by
    apply eLpNorm_congr_ae
    filter_upwards [hρv] with x hx
    change v x - u x = ρ.sqrt x - u x
    rw [hx]
  intro x
  have hb := hwb x
  rw [he, hnorm] at hb
  exact hb

/-- The actual original-H1 metric convergence implies uniform convergence of
the genuine continuous representatives on the entire torus. -/
theorem ordinaryRoot_continuous_tendstoUniformly (σ : AbsoluteDensity 1)
    (ρ : ℕ → AbsoluteDensity 1) {u : Torus 1 → ℝ} {v : ℕ → Torus 1 → ℝ}
    (hu : Continuous u) (hv : ∀ n, Continuous (v n))
    (hσu : σ.sqrt =ᵐ[haar 1] u) (hρv : ∀ n, (ρ n).sqrt =ᵐ[haar 1] v n)
    (hd : Tendsto (fun n => ordinaryRootH1Deviation σ (ρ n) u) atTop (𝓝 0)) :
    TendstoUniformly v u atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have he : ∀ᶠ n in atTop, ordinaryRootH1Deviation σ (ρ n) u < ε :=
    hd.eventually (gt_mem_nhds hε)
  filter_upwards [he] with n hn x
  rw [Real.dist_eq, abs_sub_comm]
  exact (ordinaryRoot_continuous_deviation_bound σ (ρ n) hu (hv n) hσu (hρv n) x).trans_lt hn

end DGPS.Examples.ThreeSpeciesCircle
