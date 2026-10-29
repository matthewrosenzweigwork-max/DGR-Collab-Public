import DGRHS.Dynamics.SourceDynamicGaussian

/-! Horizon-only measurability for the actual source covariance. The auxiliary
density extension equals the original density at every time of the horizon;
the backward tests and their gradients are never clamped or differentiated. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace
namespace DGRHS.Dynamics
open DGRHS.Gaussian DGRHS.Commutator
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem sourceDynamic_interval_covariance (T β : ℝ) (hT : 0≤T) (hβ : 0≤β)
    (ρ : ℝ→E→ℝ)
    (hρ : Measurable (fun p : Icc (0:ℝ) T×E=>ρ p.1 p.2))
    (hp : ∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (k : ℕ) (t : Fin k→ℝ) (ht : ∀ a,t a≤T) (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0)
    (hf : ∀ a,ContinuousOn (fun p : ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a) ×ˢ univ))
    (hb : ∀ a,∀ r∈Icc 0 (t a),∀ z,‖gradient (f a r) z‖≤(G:ℝ)) :
    Matrix.PosSemidef (sourceDynamicTimeCovariance β ρ k t f) ∧
    ∀ θ : Fin k→ℝ,
      (∑ a,∑ b,(θ a*θ b)*sourceDynamicTimeCovariance β ρ k t f a b)=
      (2/β)*∫ r in Ioc 0 T,∫ z,
        ‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
          ∂gaussianRieszDensityMeasure (ρ r) := by
  let ρe := fun r=>ρ (projIcc 0 T hT r)
  have hρe : Measurable (Function.uncurry ρe) :=
    hρ.comp (((continuous_projIcc : Continuous (projIcc 0 T hT)).measurable.comp
      measurable_fst).prodMk measurable_snd)
  have heq (r : ℝ) (hr : r∈Icc 0 T) : ρe r=ρ r := by
    dsimp only [ρe];rw [projIcc_of_mem hT hr]
  have hpe : ∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρe r)) := by
    intro r hr;rw [heq r hr];exact hp r hr
  have hcov : sourceDynamicTimeCovariance β ρe k t f=sourceDynamicTimeCovariance β ρ k t f := by
    funext a b
    unfold sourceDynamicTimeCovariance
    apply congrArg (fun v : ℝ=>(2/β)*v)
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [heq r ⟨hr.1.le,hr.2.trans ((min_le_left _ _).trans (ht a))⟩]
  refine ⟨hcov ▸ sourceDynamic_time_covariance_posSemidef T β hβ ρe hρe hpe k t ht f G hf hb,?_⟩
  intro θ
  have hh := sourceDynamic_time_covariance_quadratic T β ρe hρe hpe k t θ ht f G hf hb
  rw [hcov] at hh
  refine hh.trans ?_
  apply congrArg (fun v : ℝ=>(2/β)*v)
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [heq r ⟨hr.1.le,hr.2⟩]

theorem sourceDynamic_total_interval_covariance_posSemidef {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (k : ℕ) (Z : Ω→Fin k→ℝ) (hZ : ∀ a,MemLp (fun ω=>Z ω a) 2 ν)
    (T β : ℝ) (hT : 0≤T) (hβ : 0≤β) (ρ : ℝ→E→ℝ)
    (hρ : Measurable (fun p : Icc (0:ℝ) T×E=>ρ p.1 p.2))
    (hp : ∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (t : Fin k→ℝ) (ht : ∀ a,t a≤T) (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0)
    (hf : ∀ a,ContinuousOn (fun p : ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a) ×ˢ univ))
    (hb : ∀ a,∀ r∈Icc 0 (t a),∀ z,‖gradient (f a r) z‖≤(G:ℝ)) :
    Matrix.PosSemidef (fun a b=>(∫ ω,Z ω a*Z ω b ∂ν)+sourceDynamicTimeCovariance β ρ k t f a b) :=
  (sourceDynamic_initial_secondMoment_posSemidef ν k Z hZ).add
    (sourceDynamic_interval_covariance T β hT hβ ρ hρ hp k t ht f G hf hb).1

end DGRHS.Dynamics
set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_interval_covariance
#print axioms DGRHS.Dynamics.sourceDynamic_interval_covariance
set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_total_interval_covariance_posSemidef
#print axioms DGRHS.Dynamics.sourceDynamic_total_interval_covariance_posSemidef
