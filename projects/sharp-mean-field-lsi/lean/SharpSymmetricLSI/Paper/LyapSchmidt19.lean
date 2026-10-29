import SharpSymmetricLSI.Paper.LyapSchmidt18

/-!
# Section 4.2 (lane s42; R14): the gradient of `y(a)` as a smooth `L^∞`-valued map

`gradL a h b k = ∂ₖ(W * (p kC a)) - (1 + h) ∂ₖ(W * (p (h + kC b)))` in `L^∞`; on the graph
(`h = kC a + ψ a`, `b = b(a)`) it is the weak gradient of `ψ(a)`. As a function of `a` it is
`C^∞` on the ball, vanishes at `0`, and has zero derivative at `0` (`Dψ(0) = 0`, `Db(0) = 0`).
-/

noncomputable section
open MeasureTheory Filter Real Topology Metric
open scoped ENNReal ContDiff

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section ygrad
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis' W μ φ)

/-- The `L^∞` gradient expression. -/
def gradL (a : EuclideanSpace ℝ (Fin n)) (h : CT d) (bv : EuclideanSpace ℝ (Fin n))
    (k : Fin d) : Linf d :=
  forceL hyp hμ k (kC hyp hφ a) - mulLinf (toLinf (1 + h)) (forceL hyp hμ k (h + kC hyp hφ bv))

include hyp hμ hφ

theorem haar_ae_of_ae {P : Torus d → Prop} (h : ∀ᵐ x ∂(μ : Measure (Torus d)), P x) :
    ∀ᵐ x ∂haar d, P x := by
  obtain ⟨hpm, hppos, -⟩ := elDensity_props hyp (μ : Measure (Torus d))
  have hac : haar d ≪ (μ : Measure (Torus d)) := by
    rw [minimizer_eq_elDensity hyp hμ]
    exact withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp hpm).aemeasurable
      (Eventually.of_forall fun x => by simp [hppos x])
  exact hac.ae_le h

theorem bForceL_kC (a : EuclideanSpace ℝ (Fin n)) (x : Torus d) (k : Fin d) :
    bForceL W (fun y => elDens V W (μ : Measure (Torus d)) y * kC hyp hφ a y) x k =
      ∑ i, a i * bForceL W (fun y => elDens V W (μ : Measure (Torus d)) y * φ i y) x k := by
  have hpφ : ∀ i, Integrable (fun y => elDens V W (μ : Measure (Torus d)) y * phiC hyp hφ i y)
      (haar d) := fun i =>
    integrable_elDens_mul hyp hμ (integrable_of_continuous (phiC hyp hφ i).continuous)
  have e : (fun y => elDens V W (μ : Measure (Torus d)) y * kC hyp hφ a y) =
      fun y => ∑ i, a i * (fun i y => elDens V W (μ : Measure (Torus d)) y * phiC hyp hφ i y) i y :=
    by funext y; rw [kC_apply, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, bForceL_finsetSum hyp hpφ a x k]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hae : (fun y => elDens V W (μ : Measure (Torus d)) y * phiC hyp hφ i y) =ᵐ[haar d]
      fun y => elDens V W (μ : Measure (Torus d)) y * φ i y := by
    filter_upwards [haar_ae_of_ae hyp hμ hφ (phiC_ae hyp hφ i)] with y hy
    rw [hy]
  exact congrFun (congrFun (bForceL_congr_ae hae) x) k

/-- The pointwise form of `gradL`. -/
theorem gradL_ae (a bv : EuclideanSpace ℝ (Fin n)) (h : CT d) (k : Fin d) :
    (gradL hyp hμ hφ a h bv k : Torus d → ℝ) =ᵐ[haar d] fun x =>
      ∑ i, a i * bForceL W (fun y => elDens V W (μ : Measure (Torus d)) y * φ i y) x k -
        (1 + h x) * (bForceL W (fun y => elDens V W (μ : Measure (Torus d)) y * h y) x k +
          ∑ i, bv i * bForceL W (fun y => elDens V W (μ : Measure (Torus d)) y * φ i y) x k) := by
  have hph : Integrable (fun y => elDens V W (μ : Measure (Torus d)) y * h y) (haar d) :=
    integrable_elDens_mul hyp hμ (integrable_of_continuous h.continuous)
  have hpk : Integrable (fun y => elDens V W (μ : Measure (Torus d)) y * kC hyp hφ bv y)
      (haar d) := integrable_elDens_mul hyp hμ (integrable_of_continuous (kC hyp hφ bv).continuous)
  unfold gradL
  filter_upwards [Lp.coeFn_sub (forceL hyp hμ k (kC hyp hφ a))
      (mulLinf (toLinf (1 + h)) (forceL hyp hμ k (h + kC hyp hφ bv))),
    forceL_ae hyp hμ k (kC hyp hφ a),
    mulLinf_ae (toLinf (1 + h)) (forceL hyp hμ k (h + kC hyp hφ bv)),
    toLinf_ae (1 + h), forceL_ae hyp hμ k (h + kC hyp hφ bv)] with x h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2, h3, h4, h5, bForceL_kC hyp hμ hφ a x k]
  have e : (fun y => elDens V W (μ : Measure (Torus d)) y * (h + kC hyp hφ bv) y) =
      fun y => 1 * (elDens V W (μ : Measure (Torus d)) y * h y) +
        1 * (elDens V W (μ : Measure (Torus d)) y * kC hyp hφ bv y) := by
    funext y; simp only [ContinuousMap.add_apply]; ring
  rw [e, bForceL_add hyp hph hpk 1 1 x k, bForceL_kC hyp hμ hφ bv x k]
  simp only [ContinuousMap.add_apply, ContinuousMap.one_apply]
  ring

end ygrad

end SharpLSI
