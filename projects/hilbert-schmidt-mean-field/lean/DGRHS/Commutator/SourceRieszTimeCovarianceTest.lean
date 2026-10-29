import DGRHS.Commutator.SourceRieszTimeMeasurable
import DGRHS.Commutator.SourceRieszDynamicOscillation

/-! Actual cross-gradient test. Joint continuity and gradient norm bounds on
the finite horizon derive measurable totalization and true bounded oscillation.
No supplied test moment/range assumption. The zero extension is only outside
the horizon and agrees with actual gradients at both endpoints. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal RealInnerProductSpace
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Dynamics
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

 def sourceRieszCrossGradientCut (T : ℝ) (f g : ℝ→E→ℝ) : ℝ×E→ℝ :=
  (Icc 0 T ×ˢ (univ : Set E)).piecewise
    (fun p=>⟪gradient (f p.1) p.2,gradient (g p.1) p.2⟫) (fun _=>0)

 theorem sourceRieszCrossGradientCut_eq (T : ℝ) (f g : ℝ→E→ℝ)
    (r : ℝ) (hr : r∈Icc 0 T) (z : E) :
    sourceRieszCrossGradientCut T f g (r,z)=⟪gradient (f r) z,gradient (g r) z⟫ := by
  simp [sourceRieszCrossGradientCut,Set.piecewise,hr]

 theorem measurable_sourceRieszCrossGradientCut (T : ℝ) (f g : ℝ→E→ℝ)
    (hf : ContinuousOn (fun p : ℝ×E=>gradient (f p.1) p.2) (Icc 0 T ×ˢ univ))
    (hg : ContinuousOn (fun p : ℝ×E=>gradient (g p.1) p.2) (Icc 0 T ×ˢ univ)) :
    Measurable (sourceRieszCrossGradientCut T f g) := by
  exact (hf.inner hg).measurable_piecewise continuousOn_const (measurableSet_Icc.prod MeasurableSet.univ)

 theorem sourceRieszCrossGradient_range (T : ℝ) (f g : ℝ→E→ℝ) (Gf Gg : ℝ≥0)
    (hf : ∀ r∈Icc 0 T,∀ z,‖gradient (f r) z‖≤(Gf:ℝ))
    (hg : ∀ r∈Icc 0 T,∀ z,‖gradient (g r) z‖≤(Gg:ℝ))
    (r : ℝ) (hr : r∈Icc 0 T) :
    BddBelow (range (fun z=>sourceRieszCrossGradientCut T f g (r,z))) ∧
    BddAbove (range (fun z=>sourceRieszCrossGradientCut T f g (r,z))) ∧
    sSup (range (fun z=>sourceRieszCrossGradientCut T f g (r,z)))-
      sInf (range (fun z=>sourceRieszCrossGradientCut T f g (r,z)))≤2*(Gf:ℝ)*(Gg:ℝ) := by
  let q := fun z=>sourceRieszCrossGradientCut T f g (r,z)
  have hb (z : E) : |q z|≤(Gf:ℝ)*(Gg:ℝ) := by
    dsimp only [q]
    rw [sourceRieszCrossGradientCut_eq T f g r hr z]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hf r hr z) (hg r hr z) (norm_nonneg _) Gf.coe_nonneg)
  have hlo : BddBelow (range q) := ⟨-((Gf:ℝ)*(Gg:ℝ)),by rintro y ⟨z,rfl⟩;exact (abs_le.mp (hb z)).1⟩
  have hup : BddAbove (range q) := ⟨(Gf:ℝ)*(Gg:ℝ),by rintro y ⟨z,rfl⟩;exact (abs_le.mp (hb z)).2⟩
  have hsup := csSup_le (range_nonempty q) (fun y hy=>by rcases hy with ⟨z,rfl⟩;exact (abs_le.mp (hb z)).2)
  have hinf := le_csInf (range_nonempty q) (fun y hy=>by rcases hy with ⟨z,rfl⟩;exact (abs_le.mp (hb z)).1)
  exact ⟨hlo,hup,by linarith⟩

 theorem measurable_sourceRieszEmpiricalDifference_time {Ω : Type*} [MeasurableSpace Ω]
    (ρ : ℝ→E→ℝ) (hρ : Measurable (Function.uncurry ρ))
    (q : ℝ×E→ℝ) (hq : Measurable q) (N : ℕ)
    (X : ℝ×Ω→Fin N→E) (hX : Measurable X) :
    Measurable (fun p : ℝ×Ω=>sourceRieszDynamicEmpiricalDifference (ρ p.1)
      (fun z=>q (p.1,z)) N (X p)) := by
  let κ := sourceDensityKernel volume ρ
  letI := sourceDensityKernel_sfinite volume ρ
  have hκ (r : ℝ) : κ r=gaussianRieszDensityMeasure (ρ r) := sourceDensityKernel_apply volume ρ hρ r
  have hI : Measurable (fun r=>∫ z,q (r,z) ∂κ r) := hq.stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hsum : Measurable (fun p : ℝ×Ω=>∑ i : Fin N,q (p.1,X p i)) :=
    Finset.measurable_sum _ (fun i _=>hq.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp hX)))
  simp_rw [sourceRieszDynamicEmpiricalDifference,integral_sourceRieszLocalEmpiricalLaw]
  have hh := (hsum.const_mul (N:ℝ)⁻¹).sub (hI.comp measurable_fst)
  change Measurable (fun p : ℝ×Ω=>(N:ℝ)⁻¹*(∑ i : Fin N,q (p.1,X p i))-(∫ z,q (p.1,z) ∂κ p.1)) at hh
  simpa only [hκ] using hh

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszCrossGradientCut
#print axioms DGRHS.Commutator.sourceRieszCrossGradientCut
#check @DGRHS.Commutator.sourceRieszCrossGradientCut_eq
#print axioms DGRHS.Commutator.sourceRieszCrossGradientCut_eq
#check @DGRHS.Commutator.measurable_sourceRieszCrossGradientCut
#print axioms DGRHS.Commutator.measurable_sourceRieszCrossGradientCut
#check @DGRHS.Commutator.sourceRieszCrossGradient_range
#print axioms DGRHS.Commutator.sourceRieszCrossGradient_range
#check @DGRHS.Commutator.measurable_sourceRieszEmpiricalDifference_time
#print axioms DGRHS.Commutator.measurable_sourceRieszEmpiricalDifference_time
