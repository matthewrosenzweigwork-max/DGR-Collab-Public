import SharpSymmetricLSI.Paper.AppAPicard1

/-!
# Lemma A.1, existence (2): joint measurability

`(t,x) ↦ e^{tΔ}f(x)`, the Duhamel term `(t,x) ↦ ∫_{(0,t]} ∇·e^{(t-u)Δ}N_u(x) du` and the modified
flux `(u,y) ↦ N(η_u)(y)` are jointly measurable when the data are.
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem measurable_heatKernel_joint :
    Measurable fun p : ℝ × (ι → ℝ) => heatKernel p.1 p.2 := by
  unfold heatKernel; fun_prop

theorem measurable_heatT_joint {f : UnitAddTorus ι → ℝ} (hf : Measurable f) :
    Measurable fun p : ℝ × UnitAddTorus ι => heatT p.1 f p.2 := by
  unfold heatT
  have hm : StronglyMeasurable (fun q : (ℝ × UnitAddTorus ι) × (ι → ℝ) =>
      f (q.1.2 - liftT q.2) * heatKernel q.1.1 q.2) :=
    ((hf.comp ((measurable_snd.comp measurable_fst).sub (measurable_liftT.comp measurable_snd))).mul
      (measurable_heatKernel_joint.comp ((measurable_fst.comp measurable_fst).prodMk
        measurable_snd))).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

/-- The explicit kernel `∂ₖ G_s(y) = -G_s(y) yₖ / (2s)`. -/
noncomputable def duhKer (s : ℝ) (y : ι → ℝ) (k : ι) : ℝ := -(heatKernel s y * y k / (2 * s))

theorem measurable_duhKer (k : ι) : Measurable fun p : ℝ × (ι → ℝ) => duhKer p.1 p.2 k := by
  unfold duhKer
  exact ((measurable_heatKernel_joint.mul ((measurable_pi_apply k).comp measurable_snd)).div
    (measurable_const.mul measurable_fst)).neg

theorem divHeatT_eq_duhKer {s : ℝ} (hs : 0 < s) (F : UnitAddTorus ι → ι → ℝ)
    (x : UnitAddTorus ι) :
    divHeatT s F x = ∑ k, ∫ y : ι → ℝ, duhKer s y k * F (x - liftT y) k := by
  unfold divHeatT duhKer
  simp_rw [fderiv_heatKernel_single hs]

/-- The Duhamel term `∫_{(0,t]} ∇·e^{(t-u)Δ} N_u(x) du`. -/
noncomputable def duhamel (N : ℝ → UnitAddTorus ι → ι → ℝ) (t : ℝ) (x : UnitAddTorus ι) : ℝ :=
  ∫ u in Ioc 0 t, divHeatT (t - u) (N u) x

theorem duhamel_eq_ker (N : ℝ → UnitAddTorus ι → ι → ℝ) (t : ℝ) (x : UnitAddTorus ι) :
    duhamel N t x = ∫ u, (if 0 < u ∧ u < t then
      ∑ k, ∫ y : ι → ℝ, duhKer (t - u) y k * N u (x - liftT y) k else 0) := by
  unfold duhamel
  have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ t := by rw [ae_iff]; simp
  rw [← integral_indicator measurableSet_Ioc]
  refine integral_congr_ae ?_
  filter_upwards [hne] with u hu
  by_cases h : 0 < u ∧ u < t
  · rw [indicator_of_mem (show u ∈ Ioc 0 t from ⟨h.1, h.2.le⟩), if_pos h,
      divHeatT_eq_duhKer (sub_pos.2 h.2)]
  · rw [if_neg h, indicator_of_notMem]
    rintro ⟨h1, h2⟩
    exact h ⟨h1, lt_of_le_of_ne h2 hu⟩

theorem measurable_duhamel {N : ℝ → UnitAddTorus ι → ι → ℝ}
    (hN : ∀ k, Measurable fun p : ℝ × UnitAddTorus ι => N p.1 p.2 k) :
    Measurable fun p : ℝ × UnitAddTorus ι => duhamel N p.1 p.2 := by
  simp_rw [duhamel_eq_ker]
  have hin : ∀ k, Measurable fun q : ((ℝ × UnitAddTorus ι) × ℝ) =>
      ∫ y : ι → ℝ, duhKer (q.1.1 - q.2) y k * N q.2 (q.1.2 - liftT y) k := fun k => by
    have hm : StronglyMeasurable (fun r : ((ℝ × UnitAddTorus ι) × ℝ) × (ι → ℝ) =>
        duhKer (r.1.1.1 - r.1.2) r.2 k * N r.1.2 (r.1.1.2 - liftT r.2) k) := by
      refine Measurable.stronglyMeasurable ?_
      refine ((measurable_duhKer k).comp ((((measurable_fst.comp measurable_fst).comp
        measurable_fst).sub (measurable_snd.comp measurable_fst)).prodMk measurable_snd)).mul ?_
      exact (hN k).comp ((measurable_snd.comp measurable_fst).prodMk
        (((measurable_snd.comp measurable_fst).comp measurable_fst).sub
          (measurable_liftT.comp measurable_snd)))
    exact hm.integral_prod_right'.measurable
  have hQ : Measurable fun q : ((ℝ × UnitAddTorus ι) × ℝ) => (if 0 < q.2 ∧ q.2 < q.1.1 then
      ∑ k, ∫ y : ι → ℝ, duhKer (q.1.1 - q.2) y k * N q.2 (q.1.2 - liftT y) k else 0) := by
    refine Measurable.ite ?_ (Finset.measurable_sum _ fun k _ => hin k) measurable_const
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_fst.comp measurable_fst))
  exact hQ.stronglyMeasurable.integral_prod_right'.measurable

end General

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem measurable_mass {η : ℝ → Torus d → ℝ} (hη : Measurable (Function.uncurry η)) :
    Measurable fun u => ∫ z, max (η u z) 0 ∂haar d :=
  (hη.max measurable_const).stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_posNorm {η : ℝ → Torus d → ℝ} (hη : Measurable (Function.uncurry η)) :
    Measurable fun p : ℝ × Torus d => posNorm (η p.1) p.2 := by
  unfold posNorm
  exact (hη.max measurable_const).div (measurable_const.max ((measurable_mass hη).comp measurable_fst))

theorem measurable_modFlux (hyp : Hyp V W KV KW) {η : ℝ → Torus d → ℝ}
    (hη : Measurable (Function.uncurry η)) (k : Fin d) :
    Measurable fun p : ℝ × Torus d => modFlux V W (η p.1) p.2 k := by
  unfold modFlux bForceL
  have hb : Measurable fun p : ℝ × Torus d =>
      ∫ z, bGrad W p.2 z k * posNorm (η p.1) z ∂haar d := by
    have hm : StronglyMeasurable (fun q : (ℝ × Torus d) × Torus d =>
        bGrad W q.1.2 q.2 k * posNorm (η q.1.1) q.2) :=
      (((measurable_bGrad hyp k).comp ((measurable_snd.comp measurable_fst).prodMk
        measurable_snd)).mul ((measurable_posNorm hη).comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd))).stronglyMeasurable
    exact hm.integral_prod_right'.measurable
  exact hη.mul (((measurable_lipGrad hyp.continuous_V k).comp measurable_snd).add hb)

end SharpLSI
