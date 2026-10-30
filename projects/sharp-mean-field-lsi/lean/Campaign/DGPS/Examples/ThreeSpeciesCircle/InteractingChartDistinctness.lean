import DGPS.Examples.ThreeSpeciesCircle.InteractingChartProbability
import DGPS.Examples.ThreeSpeciesCircle.InteractingChartLogProfile
import DGPS.Examples.ThreeSpeciesCircle.InteractingMinimizerHolderCapture

/-! Actual mean-zero chart-law injectivity and persistence of the distinct
SAME-D ordinary seeds. These are probability-law assertions, not assertions
about arbitrary original stored roots. -/

noncomputable section
open MeasureTheory Filter Topology Set
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Equal canonical laws determine the full normalized mean-zero chart. -/
theorem interactingChartAbsolute_injective_meanZero (h : ℝ) (u v : PeriodicC2_STR02969)
    (hu : meanT_STR02901 u.val=0) (hv : meanT_STR02901 v.val=0)
    (hμ : (densityMeasure (interactingChartAbsolute h u) : Measure (Torus 1))=
      densityMeasure (interactingChartAbsolute h v)) : u=v := by
  let ρ := interactingChartAbsolute h u
  have hc := (interactingChartAbsolute_positive_continuous h u).1
  have hpu : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ)=rhoT_STR02901 h u.val (angSec θ) :=
    Eventually.of_forall (interactingChartAbsolute_density h u)
  have hden := (densityMeasure_eq_iff_STR02901 (interactingChartAbsolute h u)
    (interactingChartAbsolute h v)).1 hμ
  have heang : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ)=
      (interactingChartAbsolute h v).density (angEquiv.symm θ) := by
    apply (ae_comp_angEquiv_iff (p:=fun θ => ρ.density (angEquiv.symm θ)=
      (interactingChartAbsolute h v).density (angEquiv.symm θ))).1
    filter_upwards [hden] with x hx
    simpa only [MeasurableEquiv.symm_apply_apply, ρ] using hx
  have hpv : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ)=rhoT_STR02901 h v.val (angSec θ) := by
    filter_upwards [heang] with θ hθ
    exact hθ.trans (interactingChartAbsolute_density h v θ)
  have h1 := interactingChart_continuous_logProfile h u ρ hc (ae_eq_refl _) hpu
  have h2 := interactingChart_continuous_logProfile h v ρ hc (ae_eq_refl _) hpv
  have he : (fun t => u.val t+elementaryChartLogConstant h u)=
      fun t => v.val t+elementaryChartLogConstant h v := h1.symm.trans h2
  have hmeans := congrArg meanT_STR02901 he
  change meanT_STR02901 (u.val + fun _ => elementaryChartLogConstant h u) = meanT_STR02901 (v.val + fun _ => elementaryChartLogConstant h v) at hmeans
  have hconst : elementaryChartLogConstant h u=elementaryChartLogConstant h v := by
    rw [meanT_add_STR02953 (continuous_val_STR02924 u) continuous_const,
      meanT_add_STR02953 (continuous_val_STR02924 v) continuous_const,hu,hv] at hmeans
    simpa [meanT_STR02901] using hmeans
  apply Subtype.ext
  funext t
  have ht := congrFun he t
  rw [hconst] at ht
  change u.val t = v.val t
  linarith

/-- The exact retained ordinary seeds are distinct at every actual admissible
fixed field. The proof uses actual ordinary density distinction from D.roots. -/
theorem ordinaryHolderCaptureSeed_distinct (D : OrdinaryRootGraphData) (h : ℝ)
    (hh : 0<h) (hsmall : h<D.radius) : Pairwise (fun i j =>
      ordinaryHolderCaptureSeed D h i≠ordinaryHolderCaptureSeed D h j) := by
  obtain ⟨σ,hσ,_,_,_,hne,_⟩ := D.roots h hh hsmall
  intro i j hij he
  apply hne i j hij
  exact Eventually.of_forall fun x => by
    have hi := hσ i (angEquiv x)
    have hj := hσ j (angEquiv x)
    have hv : chartU_STR02924 D.ψ h (D.Z i h)=chartU_STR02924 D.ψ h (D.Z j h) := by
      have ht := congrArg PeriodicC2_STR02969.val he
      have hi : (ordinaryHolderCaptureSeed D h i).val=chartU_STR02924 D.ψ h (D.Z i h) := by
        unfold ordinaryHolderCaptureSeed Lamp_STR02956 iota_STR02956
        rw [paramMap_val_STR02915]
        rfl
      have hj : (ordinaryHolderCaptureSeed D h j).val=chartU_STR02924 D.ψ h (D.Z j h) := by
        unfold ordinaryHolderCaptureSeed Lamp_STR02956 iota_STR02956
        rw [paramMap_val_STR02915]
        rfl
      simpa only [hi,hj] using ht
    rw [hv] at hi
    simpa only [MeasurableEquiv.symm_apply_apply] using hi.trans hj.symm

/-- Distinct mean-zero seeds remain distinct as probability laws on one
interval for all three continuous chart curves. No desired law distinction or
optimizer premise is added at positive coupling. -/
theorem interactingChart_curves_distinct (u : Fin 3 → ℝ → PeriodicC2_STR02969)
    (h : ℝ) (hc : ∀ j, ContinuousAt (u j) 0)
    (hseed : Pairwise (fun i j => u i 0≠u j 0))
    (hm : ∀ j ε, meanT_STR02901 (u j ε).val=0) :
    ∃ d : ℝ, 0<d ∧ ∀ ε : ℝ, |ε|<d → Pairwise (fun i j =>
      densityMeasure (interactingChartAbsolute h (u i ε))≠
        densityMeasure (interactingChartAbsolute h (u j ε))) := by
  have hev : ∀ᶠ ε in 𝓝 (0:ℝ), ∀ i j : Fin 3, i≠j →
      densityMeasure (interactingChartAbsolute h (u i ε))≠
        densityMeasure (interactingChartAbsolute h (u j ε)) := by
    apply Filter.eventually_all.2
    intro i
    apply Filter.eventually_all.2
    intro j
    by_cases hij : i=j
    · exact Eventually.of_forall fun _ hn => (hn hij).elim
    · have hd : 0<dist (u i 0) (u j 0) := dist_pos.mpr (hseed hij)
      have ht := ((hc i).dist (hc j)).eventually (lt_mem_nhds hd)
      filter_upwards [ht] with ε hε _ heq
      have hμ := congrArg (fun μ : ProbabilityMeasure (Torus 1) => (μ : Measure (Torus 1))) heq
      have he := interactingChartAbsolute_injective_meanZero h (u i ε) (u j ε)
        (hm i ε) (hm j ε) hμ
      rw [he,dist_self] at hε
      exact (lt_irrefl (0:ℝ)) hε
  obtain ⟨d,hd,htail⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨d,hd,fun ε hε i j hij => ?_⟩
  exact htail (by simpa only [Real.dist_eq,sub_zero] using hε) i j hij

end DGPS.Examples.ThreeSpeciesCircle
