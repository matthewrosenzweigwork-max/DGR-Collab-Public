import DGRHS.Commutator.SourceRieszBrownianElementaryProcess
import Mathlib.Probability.BorelCantelli

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the preserved MathFin LICENSE.
Selected fast approximation / Borel-Cantelli argument from
MathFin/Foundations/ItoIntegralProcessContinuousModification.lean,
f085fd572075c934827f1eb92c4a085941cd21e5. Adapted to the proved full-filtration
Finsupp atom density and strict-tail maximal inequality, using actual common
Brownian sums and no independent-integrals assumption.
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
variable (hBc : ∀ ω,Continuous (fun r=>B r ω))

lemma sourceRieszBrownianApproxSeq
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    ∃ c : ℕ→(SourceRieszBrownianAtom F T →₀ ℝ),
      ∀ n,‖sourceRieszBrownianAtomAssembly P F T (c n)-g‖≤(2⁻¹:ℝ)^n := by
  have hd := sourceRieszBrownianAtomAssembly_dense P F T
  have he : ∀ n:ℕ,∃ c,‖sourceRieszBrownianAtomAssembly P F T c-g‖≤(2⁻¹:ℝ)^n := by
    intro n
    obtain ⟨c,hc⟩ := hd.exists_dist_lt g (by positivity : (0:ℝ)<(2⁻¹:ℝ)^n)
    exact ⟨c,by rw [←dist_eq_norm,dist_comm]; exact hc.le⟩
  exact Classical.axiomOfChoice he

include hB hBa hind hBc in
theorem sourceRieszBrownianApprox_ae_eventually
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (c : ℕ→(SourceRieszBrownianAtom F T →₀ ℝ))
    (hc : ∀ n,‖sourceRieszBrownianAtomAssembly P F T (c n)-g‖≤(2⁻¹:ℝ)^n) :
    ∀ᵐ ω ∂P,∀ᶠ n in atTop,∀ t,t≤T →
      ‖sourceRieszBrownianElementaryProcess F T B (c n) t ω-
        sourceRieszBrownianElementaryProcess F T B (c (n+1)) t ω‖≤(3/4:ℝ)^n := by
  let A n : Set Ω := {ω | ∃ t,t≤T ∧ (3/4:ℝ)^n<
    ‖sourceRieszBrownianElementaryProcess F T B (c n-c (n+1)) t ω‖}
  have hb n : P (A n)≤ENNReal.ofReal (2*(2/3:ℝ)^n) := by
    refine (sourceRieszBrownianElementaryProcess_maximal P F T B hB hBa hind hBc
      (c n-c (n+1)) (by positivity : (0:ℝ)<(3/4:ℝ)^n)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hn : ‖sourceRieszBrownianAtomAssembly P F T (c n-c (n+1))‖≤2*(2⁻¹:ℝ)^n := by
      rw [map_sub]
      calc
        _ ≤ ‖sourceRieszBrownianAtomAssembly P F T (c n)-g‖+
          ‖g-sourceRieszBrownianAtomAssembly P F T (c (n+1))‖ := by
          simpa using norm_add_le (sourceRieszBrownianAtomAssembly P F T (c n)-g)
            (g-sourceRieszBrownianAtomAssembly P F T (c (n+1)))
        _ ≤ (2⁻¹:ℝ)^n+(2⁻¹:ℝ)^(n+1) := add_le_add (hc n) (by rw [norm_sub_rev];exact hc (n+1))
        _ ≤ 2*(2⁻¹:ℝ)^n := by rw [pow_succ];nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2⁻¹) n]
    calc
      _ ≤ ((3/4:ℝ)^n)⁻¹*(2*(2⁻¹:ℝ)^n) := mul_le_mul_of_nonneg_left hn (by positivity)
      _ = 2*(2/3:ℝ)^n := by rw [←inv_pow];ring_nf;norm_num;rw [←mul_pow];norm_num
  have hs : Summable (fun n=>P.real (A n)) :=
    Summable.of_nonneg_of_le (fun _=>measureReal_nonneg)
      (fun n=>ENNReal.toReal_le_of_le_ofReal (by positivity) (hb n))
      ((summable_geometric_of_lt_one (r:=(2/3:ℝ)) (by norm_num) (by norm_num)).mul_left 2)
  have hsum : (∑' n,P (A n))≠∞ := by
    have he : ∀ n,P (A n)=ENNReal.ofReal (P.real (A n)) :=
      fun n=>(ENNReal.ofReal_toReal (measure_ne_top P _)).symm
    simp_rw [he]
    rw [←ENNReal.ofReal_tsum_of_nonneg (fun n=>measureReal_nonneg) hs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  intro t ht
  have h : ‖sourceRieszBrownianElementaryProcess F T B (c n-c (n+1)) t ω‖≤(3/4:ℝ)^n :=
    le_of_not_gt (fun h=>hn ⟨t,ht,h⟩)
  simpa only [sourceRieszBrownianElementaryProcess_sub,Pi.sub_apply] using h

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszBrownianApproxSeq
#print axioms DGRHS.Commutator.sourceRieszBrownianApproxSeq
#check @DGRHS.Commutator.sourceRieszBrownianApprox_ae_eventually
#print axioms DGRHS.Commutator.sourceRieszBrownianApprox_ae_eventually
