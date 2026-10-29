import DGRHS.Gaussian.PeriodicDynamicTerminal
import DGRHS.Gaussian.PeriodicForceData

/-!
Packet P11c, unit 4 (part 4): the backward-adjoint interface of Theorem 2.13(iii) (TeX 883-899) on the
torus, for an abstract periodic force.  Torus form of `SourceRieszClassicalBackwardSolution` /
`SourceRieszBackwardClassicalWellPosed` / `sourceRieszUprop`: a classical solution of
`-∂_r f = L_{β,μ^r} f`, `f^t = φ`, with `f`, `∇f`, `∇^{⊗2} f` (of the lift) jointly continuous, uniformly
bounded value, gradient, Hessian, and a bounded jointly continuous extension of `∂_r f` to the closed
interval.  Tests are functions on the torus, differentiated through their lifts.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology Classical
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

structure PeriodicClassicalBackwardSolution (F : PeriodicTorus ι → E) (β : ℝ)
    (ρ : ℝ → PeriodicTorus ι → ℝ) (t : ℝ≥0) (φ : PeriodicTorus ι → ℝ)
    (f : ℝ → PeriodicTorus ι → ℝ) : Prop where
  terminal : f (t : ℝ) = φ
  spatial_contdiff : ∀ r ∈ Icc 0 (t : ℝ), ContDiff ℝ 2 (periodicLiftFn (f r))
  value_continuous : ContinuousOn (fun p : ℝ × E => periodicLiftFn (f p.1) p.2) (Icc 0 (t : ℝ) ×ˢ univ)
  gradient_continuous : ContinuousOn (fun p : ℝ × E => gradient (periodicLiftFn (f p.1)) p.2)
    (Icc 0 (t : ℝ) ×ˢ univ)
  hessian_continuous : ContinuousOn (fun p : ℝ × E => iteratedFDeriv ℝ 2 (periodicLiftFn (f p.1)) p.2)
    (Icc 0 (t : ℝ) ×ˢ univ)
  bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc 0 (t : ℝ), ∀ z : E,
    |periodicLiftFn (f r) z| ≤ C ∧ ‖gradient (periodicLiftFn (f r)) z‖ ≤ C ∧
      ‖iteratedFDeriv ℝ 2 (periodicLiftFn (f r)) z‖ ≤ C
  time_equation : ∃ δ : ℝ → PeriodicTorus ι → ℝ,
    ContinuousOn (fun p : ℝ × E => δ p.1 (periodicLift p.2)) (Icc 0 (t : ℝ) ×ˢ univ) ∧
    (∃ C : ℝ, ∀ r ∈ Icc 0 (t : ℝ), ∀ z, |δ r z| ≤ C) ∧
    (∀ r ∈ Ioo 0 (t : ℝ), ∀ z, HasDerivAt (fun u => f u z) (δ r z) r) ∧
    ∀ r ∈ Icc 0 (t : ℝ), ∀ z, δ r z + β⁻¹ * periodicLap (f r) z =
      ∫ y, ⟪F (z - y), periodicGrad (f r) z - periodicGrad (f r) y⟫ ∂periodicCappedDensityMeasure (ρ r)

/-- Literal existence and uniqueness assumption for the real linear test space `𝒟_T`. -/
def PeriodicBackwardClassicalWellPosed (T : ℝ≥0) (F : PeriodicTorus ι → E) (β : ℝ)
    (ρ : ℝ → PeriodicTorus ι → ℝ) (D : Submodule ℝ (PeriodicTorus ι → ℝ)) : Prop :=
  ∀ t : ℝ≥0, t ≤ T → ∀ φ : PeriodicTorus ι → ℝ, φ ∈ D → ∃ f : ℝ → PeriodicTorus ι → ℝ,
    PeriodicClassicalBackwardSolution F β ρ t φ f ∧
    ∀ g : ℝ → PeriodicTorus ι → ℝ, PeriodicClassicalBackwardSolution F β ρ t φ g →
      ∀ r ∈ Icc 0 (t : ℝ), f r = g r

/-- The propagator `U^{r,t} φ`, selected once from the assumed unique classical solution. -/
def periodicUprop (T : ℝ≥0) (F : PeriodicTorus ι → E) (β : ℝ) (ρ : ℝ → PeriodicTorus ι → ℝ)
    (D : Submodule ℝ (PeriodicTorus ι → ℝ)) (h : PeriodicBackwardClassicalWellPosed T F β ρ D)
    (t : ℝ≥0) (ht : t ≤ T) (φ : PeriodicTorus ι → ℝ) (hφ : φ ∈ D) : ℝ → PeriodicTorus ι → ℝ :=
  Classical.choose (h t ht φ hφ)

lemma periodicUprop_spec (T : ℝ≥0) (F : PeriodicTorus ι → E) (β : ℝ) (ρ : ℝ → PeriodicTorus ι → ℝ)
    (D : Submodule ℝ (PeriodicTorus ι → ℝ)) (h : PeriodicBackwardClassicalWellPosed T F β ρ D)
    (t : ℝ≥0) (ht : t ≤ T) (φ : PeriodicTorus ι → ℝ) (hφ : φ ∈ D) :
    PeriodicClassicalBackwardSolution F β ρ t φ (periodicUprop T F β ρ D h t ht φ hφ) ∧
    ∀ g : ℝ → PeriodicTorus ι → ℝ, PeriodicClassicalBackwardSolution F β ρ t φ g →
      ∀ r ∈ Icc 0 (t : ℝ), periodicUprop T F β ρ D h t ht φ hφ r = g r :=
  Classical.choose_spec (h t ht φ hφ)

lemma PeriodicClassicalBackwardSolution.backward_ae (F : PeriodicTorus ι → E) (β : ℝ)
    (ρ : ℝ → PeriodicTorus ι → ℝ) (t : ℝ≥0) (φ : PeriodicTorus ι → ℝ) (f : ℝ → PeriodicTorus ι → ℝ)
    (h : PeriodicClassicalBackwardSolution F β ρ t φ f) :
    ∀ᵐ r ∂volume.restrict (Ioc 0 (t : ℝ)), PeriodicBackwardEq F β (ρ r) f r := by
  obtain ⟨δ, hδc, hδb, hδ, hEq⟩ := h.time_equation
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne (t : ℝ))] with r hr hrt
  intro z
  rw [(hδ r ⟨hr.1, lt_of_le_of_ne hr.2 hrt⟩ z).deriv]
  exact hEq r ⟨hr.1.le, hr.2⟩ z

/-- Finite-family uniform bounds by a sum of the individual bounds. -/
lemma periodicClassicalBackwardSolution_finite_bounds (F : PeriodicTorus ι → E) (β : ℝ)
    (ρ : ℝ → PeriodicTorus ι → ℝ) (k : ℕ) (t : Fin k → ℝ≥0)
    (φ : Fin k → PeriodicTorus ι → ℝ) (f : Fin k → ℝ → PeriodicTorus ι → ℝ)
    (h : ∀ a, PeriodicClassicalBackwardSolution F β ρ (t a) (φ a) (f a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ∀ r ∈ Icc 0 (t a : ℝ), ∀ z : E,
      |periodicLiftFn (f a r) z| ≤ C ∧ ‖gradient (periodicLiftFn (f a r)) z‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 2 (periodicLiftFn (f a r)) z‖ ≤ C := by
  choose C hC hb using fun a => (h a).bounded
  refine ⟨∑ a, C a, Finset.sum_nonneg (fun a _ => hC a), ?_⟩
  intro a r hr z
  have hle : C a ≤ ∑ b, C b := Finset.single_le_sum (fun b _ => hC b) (Finset.mem_univ a)
  exact ⟨((hb a r hr z).1).trans hle, ((hb a r hr z).2.1).trans hle, ((hb a r hr z).2.2).trans hle⟩

/-- All spatial quantities in the tested mean-field equation are proper. -/
theorem PeriodicClassicalBackwardSolution.spatial_properness (D : PeriodicForceData ι) (β : ℝ)
    (t : ℝ≥0) (ρ : ℝ → PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hprob : ∀ r ∈ Icc 0 (t : ℝ), IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r)))
    (hρ : ∀ r ∈ Icc 0 (t : ℝ), ∀ᵐ z ∂periodicHaar ι, ρ r z ≤ M)
    (φ : PeriodicTorus ι → ℝ) (f : ℝ → PeriodicTorus ι → ℝ)
    (h : PeriodicClassicalBackwardSolution D.F β ρ t φ f) :
    (∀ r ∈ Icc 0 (t : ℝ),
      Integrable (f r) (periodicCappedDensityMeasure (ρ r)) ∧
      (∀ z, Integrable (fun y => ⟪D.F (z - y), periodicGrad (f r) z - periodicGrad (f r) y⟫)
        (periodicCappedDensityMeasure (ρ r))) ∧
      Integrable (periodicForcePair D.F (periodicGrad (f r)))
        ((periodicCappedDensityMeasure (ρ r)).prod (periodicCappedDensityMeasure (ρ r)))) ∧
    ∀ᵐ r ∂volume.restrict (Ioc 0 (t : ℝ)),
      Integrable (fun z => deriv (fun u => f u z) r + β⁻¹ * periodicLap (f r) z)
        (periodicCappedDensityMeasure (ρ r)) := by
  obtain ⟨C, hC, hb⟩ := h.bounded
  let K : ℝ≥0 := ⟨C, hC⟩
  obtain ⟨Cs, -, hsec⟩ := D.section_density (K * (Fintype.card ι : ℝ≥0))
  obtain ⟨Cp, -, hpair⟩ := D.pair_density_integrable (K * (Fintype.card ι : ℝ≥0))
  have hspace : ∀ r ∈ Icc 0 (t : ℝ),
      Integrable (f r) (periodicCappedDensityMeasure (ρ r)) ∧
      (∀ z, Integrable (fun y => ⟪D.F (z - y), periodicGrad (f r) z - periodicGrad (f r) y⟫)
        (periodicCappedDensityMeasure (ρ r))) ∧
      Integrable (periodicForcePair D.F (periodicGrad (f r)))
        ((periodicCappedDensityMeasure (ρ r)).prod (periodicCappedDensityMeasure (ρ r))) := by
    intro r hr
    haveI := hprob r hr
    have hg := periodicGrad_lipschitz (h.spatial_contdiff r hr) K (fun z => (hb r hr z).2.2)
    refine ⟨?_, fun z => (hsec hg (ρ r) M hM (hρ r hr) z).1, (hpair hg (ρ r) M hM (hρ r hr)).1⟩
    apply (integrable_const C).mono'
      (measurable_of_contDiff_lift ((h.spatial_contdiff r hr).of_le (by norm_num))).aestronglyMeasurable
    refine ae_of_all _ (fun z => ?_)
    have := (hb r hr (periodicCenteredLift z)).1
    simpa only [Real.norm_eq_abs, periodicLiftFn, periodicLift_centeredLift] using this
  refine ⟨hspace, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    PeriodicClassicalBackwardSolution.backward_ae D.F β ρ t φ f h] with r hr hback
  haveI := hprob r ⟨hr.1.le, hr.2⟩
  have hp := (hspace r ⟨hr.1.le, hr.2⟩).2.2
  have he : (fun z => deriv (fun u => f u z) r + β⁻¹ * periodicLap (f r) z) =
      (fun z => ∫ y, periodicForcePair D.F (periodicGrad (f r)) (z, y)
        ∂periodicCappedDensityMeasure (ρ r)) := funext fun z => hback z
  rw [he]
  exact hp.integral_prod_left

end DGRHS.Periodic
