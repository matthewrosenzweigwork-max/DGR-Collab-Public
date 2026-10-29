import DGRHS.Commutator.SourceRieszBrownianApproximationAE
import DGRHS.Commutator.SourceRieszBrownianContinuousPaths
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the preserved MathFin LICENSE.
Fast uniform-limit strategy adapted from MathFin/Foundations/
ItoIntegralProcessContinuousModification.lean at f085fd572075c934827f1eb92c4a085941cd21e5.
This version uses measurable real limsup instead of limUnder in the definition,
so it is strongly adapted to the supplied full filtration even off convergence
sets. Continuity is proved almost surely; no completeness of the filtration or
all-path continuous version is assumed or inferred.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
variable (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBa : StronglyAdapted F B)
variable (hind : ∀ s t,s≤t →
  Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)
variable (hBc : ∀ᵐ ω ∂P,Continuous (fun r=>B r ω))

include hB hBa hind hBc in
lemma sourceRieszBrownianApprox_eventually_all_of_ae_continuous
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (c : ℕ→(SourceRieszBrownianAtom F T →₀ ℝ))
    (hc : ∀ n,‖sourceRieszBrownianAtomAssembly P F T (c n)-g‖≤(2⁻¹:ℝ)^n) :
    ∀ᵐ ω ∂P,∀ᶠ n in atTop,∀ t,
      ‖sourceRieszBrownianElementaryProcess F T B (c n) t ω-
        sourceRieszBrownianElementaryProcess F T B (c (n+1)) t ω‖≤(3/4:ℝ)^n := by
  filter_upwards [sourceRieszBrownianApprox_eventually_of_ae_continuous P F T B hB hBa hind hBc g c hc] with ω hω
  filter_upwards [hω] with n hn
  intro t
  rw [congrFun (sourceRieszBrownianElementaryProcess_stopped F T B (c n) t) ω,
    congrFun (sourceRieszBrownianElementaryProcess_stopped F T B (c (n+1)) t) ω]
  exact hn _ (min_le_right _ _)

include hB hBa hind in
lemma sourceRieszBrownianContinuousProcess_adapted_no_continuity
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    StronglyAdapted F (sourceRieszBrownianContinuousProcess P F T B g) := by
  intro t
  exact (Measurable.limsup (fun n=>(sourceRieszBrownianElementaryProcess_martingale_no_continuity
    P F T B hB hBa hind ((sourceRieszBrownianApproxSeq P F T g).choose n)).1.stronglyAdapted t
      |>.measurable)).stronglyMeasurable

include hB hBa hind hBc in
lemma sourceRieszBrownianContinuousProcess_tendsto_of_ae_continuous
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    ∀ᵐ ω ∂P,∀ t,Tendsto (fun n=>sourceRieszBrownianElementaryProcess F T B
      ((sourceRieszBrownianApproxSeq P F T g).choose n) t ω) atTop
        (𝓝 (sourceRieszBrownianContinuousProcess P F T B g t ω)) := by
  let c := (sourceRieszBrownianApproxSeq P F T g).choose
  have hc := (sourceRieszBrownianApproxSeq P F T g).choose_spec
  filter_upwards [sourceRieszBrownianApprox_eventually_all_of_ae_continuous P F T B hB hBa hind hBc g c hc] with ω hω
  intro t
  have hC : CauchySeq (fun n=>sourceRieszBrownianElementaryProcess F T B (c n) t ω) := by
    apply cauchySeq_of_summable_dist
    obtain ⟨N,hN⟩ := eventually_atTop.mp hω
    rw [←summable_nat_add_iff N]
    refine Summable.of_nonneg_of_le (fun _=>dist_nonneg) (fun n=>?_) (f:=fun n=>(3/4:ℝ)^(n+N)) ?_
    · rw [dist_eq_norm]
      exact hN (n+N) (Nat.le_add_left N n) t
    · simp_rw [pow_add]
      exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have ht := hC.tendsto_limUnder
  have he := ht.limsup_eq
  change Tendsto _ _ (𝓝 (limsup _ atTop))
  rw [he]
  exact ht

include hB hBa hind hBc in
theorem sourceRieszBrownianContinuousProcess_continuous_of_ae_continuous
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    ∀ᵐ ω ∂P,Continuous (fun t=>sourceRieszBrownianContinuousProcess P F T B g t ω) := by
  let c := (sourceRieszBrownianApproxSeq P F T g).choose
  have hc := (sourceRieszBrownianApproxSeq P F T g).choose_spec
  filter_upwards [sourceRieszBrownianApprox_eventually_all_of_ae_continuous P F T B hB hBa hind hBc g c hc,
    sourceRieszBrownianContinuousProcess_tendsto_of_ae_continuous P F T B hB hBa hind hBc g,
    ae_all_iff.2 (fun n=>sourceRieszBrownianElementaryProcess_ae_continuous P F T B hBc (c n))] with ω hω htends hcont
  obtain ⟨N,hN⟩ := eventually_atTop.mp hω
  have hu : TendstoUniformlyOn (fun n t=>sourceRieszBrownianElementaryProcess F T B (c n) t ω)
      (fun t=>sourceRieszBrownianContinuousProcess P F T B g t ω) atTop univ := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h0 : Tendsto (fun n=>4*(3/4:ℝ)^n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤3/4)
        (by norm_num : (3/4:ℝ)<1)).const_mul 4
    filter_upwards [eventually_ge_atTop N,h0.eventually_lt_const hε] with n hn hnε
    intro t _
    rw [dist_comm]
    have ht : Tendsto (fun k=>sourceRieszBrownianElementaryProcess F T B (c (k+n)) t ω) atTop
        (𝓝 (sourceRieszBrownianContinuousProcess P F T B g t ω)) :=
      (htends t).comp (tendsto_add_atTop_nat n)
    have hs : ∀ k,dist (sourceRieszBrownianElementaryProcess F T B (c (k+n)) t ω)
        (sourceRieszBrownianElementaryProcess F T B (c (k+1+n)) t ω)≤(3/4:ℝ)^n*(3/4:ℝ)^k := by
      intro k
      rw [show k+1+n=(k+n)+1 by omega,dist_eq_norm]
      exact (hN (k+n) (hn.trans (Nat.le_add_left n k)) t).trans_eq (by rw [pow_add];ring)
    have hdist := dist_le_of_le_geometric_of_tendsto₀ (3/4) ((3/4:ℝ)^n) (by norm_num) hs ht
    simp only [zero_add] at hdist
    refine lt_of_le_of_lt (hdist.trans_eq ?_) hnε
    rw [show (1:ℝ)-3/4=1/4 by norm_num]
    ring
  simpa only [continuousOn_univ] using (hu.continuousOn
    (Eventually.of_forall (fun n=>(hcont n).continuousOn)).frequently)

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszBrownianApprox_eventually_all_of_ae_continuous
#print axioms DGRHS.Commutator.sourceRieszBrownianApprox_eventually_all_of_ae_continuous
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_adapted_no_continuity
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_adapted_no_continuity
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_tendsto_of_ae_continuous
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_tendsto_of_ae_continuous
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_continuous_of_ae_continuous
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_continuous_of_ae_continuous
