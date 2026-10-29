import DGRHS.Gaussian.PeriodicD1VandermondePairing
import DGRHS.Gaussian.PeriodicD1BetaGammaValue
import DGRHS.Gaussian.PeriodicD1BoundedMomentLaw

/-! RECORDS-ONLY UNCOMPILED DRAFT. A concrete all-N circular Mellin proof via
Good's natural moments and a bounded Beta-product comparison law. Every moment
equality and bound used by the law theorem is derived below for the actual
variables. The imported Beta/Gamma/moment-law successors remain uncompiled.
The original Green-kernel/physical-partition bridge is separate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical
namespace DGRHS.Periodic

def periodicD1CircleVandermonde (N : ℕ) (x : Fin N → UnitAddCircle) : ℝ :=
  periodicD1VandermondeSquared Finset.univ (periodicD1GoodNodes x)

def periodicD1CircleVandermondeBound (N : ℕ) : ℝ :=
  4^(((Finset.univ : Finset (Fin N))×ˢFinset.univ).filter (fun p => p.1<p.2)).card

lemma periodicD1CircleVandermonde_continuous (N : ℕ) :
    Continuous (periodicD1CircleVandermonde N) := by
  unfold periodicD1CircleVandermonde periodicD1VandermondeSquared
  apply continuous_finsetProd
  intro p hp
  exact ((((fourier 1).continuous.comp (continuous_apply p.1)).sub
    ((fourier 1).continuous.comp (continuous_apply p.2))).norm).pow 2

set_option diagnostics true in
lemma periodicD1CircleVandermonde_bounds (N : ℕ) (x : Fin N → UnitAddCircle) :
    0≤periodicD1CircleVandermonde N x ∧
      periodicD1CircleVandermonde N x≤periodicD1CircleVandermondeBound N := by
  have hprod (t : Finset (Fin N × Fin N)) (w : Fin N × Fin N → ℝ)
      (hw0 : ∀ p ∈ t, (0:ℝ) ≤ w p) (hw4 : ∀ p ∈ t, w p ≤ (4:ℝ)) :
      0 ≤ t.prod w ∧ t.prod w ≤ (4:ℝ)^t.card := by
    refine ⟨Finset.prod_nonneg (R := ℝ) (s := t) (f := w) hw0, ?_⟩
    have hp : t.prod w ≤ t.prod (fun _ : Fin N × Fin N => (4:ℝ)) :=
      Finset.prod_le_prod₀ (R := ℝ) (s := t)
        (f := w) (g := fun _ : Fin N × Fin N => (4:ℝ)) hw0 hw4
    simpa only [Finset.prod_const] using hp
  have hbound (t : Finset (Fin N × Fin N)) (z : Fin N → ℂ)
      (hz : ∀ i, ‖z i‖ = 1) :
      0 ≤ (∏ p ∈ t, ‖z p.1-z p.2‖^2) ∧
        (∏ p ∈ t, ‖z p.1-z p.2‖^2) ≤ (4:ℝ)^t.card := by
    have hsq (p : Fin N × Fin N) : ‖z p.1-z p.2‖^2 ≤ (4:ℝ) := by
      have h : ‖z p.1-z p.2‖ ≤ (1:ℝ)+1 :=
        norm_sub_le_of_le (hz p.1).le (hz p.2).le
      calc
        _ ≤ ((1:ℝ)+1)^2 := pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = 4 := by norm_num
    exact hprod t (fun p : Fin N × Fin N => ‖z p.1-z p.2‖^2)
      (fun p _ => sq_nonneg (‖z p.1-z p.2‖))
      (fun p _ => hsq p)
  unfold periodicD1CircleVandermonde periodicD1CircleVandermondeBound
    periodicD1VandermondeSquared
  exact hbound
    (((Finset.univ : Finset (Fin N)) ×ˢ Finset.univ).filter (fun p => p.1 < p.2))
    (periodicD1GoodNodes x)
    (fun i => by
      rw [periodicD1GoodNodes, fourier_apply]
      exact Circle.norm_coe _)

lemma periodicD1CircleVandermonde_natural_integrable (N m : ℕ) :
    Integrable (fun x => (periodicD1CircleVandermonde N x)^m) (periodicHaar (Fin N)) :=
  ((periodicD1CircleVandermonde_continuous N).pow m).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma periodicD1CircleVandermonde_natural_moment (N m : ℕ) :
    (∫x,(periodicD1CircleVandermonde N x)^m ∂periodicHaar (Fin N))=
      ((N*m).factorial:ℝ)/(m.factorial:ℝ)^N := by
  have he (x : Fin N → UnitAddCircle) :
      periodicD1GoodWeight Finset.univ (fun _ => m) (periodicD1GoodNodes x)=
        (periodicD1CircleVandermonde N x:ℂ)^m :=
    periodicD1GoodWeight_eq_vandermonde _ _
      (fun i _ => by simp [periodicD1GoodNodes,fourier_apply]) m
  calc
    _ = (periodicD1GoodIntegral (Finset.univ : Finset (Fin N)) (fun _ => m)).re := by
      unfold periodicD1GoodIntegral
      have hire : (∫ x : Fin N → UnitAddCircle,
          (periodicD1GoodWeight Finset.univ (fun _ => m) (periodicD1GoodNodes x)).re
          ∂periodicHaar (Fin N)) =
          (∫ x : Fin N → UnitAddCircle,
            periodicD1GoodWeight Finset.univ (fun _ => m) (periodicD1GoodNodes x)
            ∂periodicHaar (Fin N)).re := by
        simpa only [RCLike.re_eq_complex_re] using
          (integral_re (periodicD1GoodWeight_integrable (N := N) Finset.univ (fun _ => m)))
      rw [←hire]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [he x,←Complex.ofReal_pow,Complex.ofReal_re]
    _ = _ := by
      rw [periodicD1GoodIntegral_constant]
      have hc : ((N*m).factorial:ℂ)/(m.factorial:ℂ)^N =
          Complex.ofReal (((N*m).factorial:ℝ)/(m.factorial:ℝ)^N) := by
        simp only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
      have hr := congrArg Complex.re hc
      simpa only [Complex.ofReal_re] using hr

lemma periodicD1BetaProductVariable_natural_moment (N : ℕ) (hN : 0<N) (m : ℕ) :
    (∫x,(periodicD1BetaProductVariable N x)^m ∂periodicD1BetaProductLaw N)=
      ((N*m).factorial:ℝ)/(m.factorial:ℝ)^N := by
  have h := (periodicD1BetaProductVariable_gamma_moment N hN (m:ℝ) (by positivity)).2
  rw [show 1+(N:ℝ)*(m:ℝ)=((N*m:ℕ):ℝ)+1 by push_cast;ring,
    show 1+(m:ℝ)=(m:ℝ)+1 by ring,
    Real.Gamma_nat_eq_factorial,Real.Gamma_nat_eq_factorial] at h
  simpa only [Real.rpow_natCast] using h

/-- The actual squared circle Vandermonde has the explicit bounded Beta-product law. -/
theorem periodicD1CircleVandermonde_law (N : ℕ) (hN : 0<N) :
    Measure.map (periodicD1CircleVandermonde N) (periodicHaar (Fin N))=
      Measure.map (periodicD1BetaProductVariable N) (periodicD1BetaProductLaw N) := by
  letI := periodicD1BetaProductLaw_probability N hN
  apply periodicD1_bounded_moments_law
    (periodicD1CircleVandermonde_continuous N).measurable.aemeasurable
    (periodicD1BetaProductVariable_continuous N).measurable.aemeasurable
    (Eventually.of_forall (periodicD1CircleVandermonde_bounds N))
    ((periodicD1BetaProductVariable_bounds N hN).mono (fun _ h => ⟨h.1.le,h.2⟩))
  intro m
  rw [periodicD1CircleVandermonde_natural_moment,
    periodicD1BetaProductVariable_natural_moment N hN m]

/-- Genuine proper real circular Mellin integral on the source attractive domain.
This is an actual integral formula, without a supplied circle-identity premise. -/
theorem periodicD1CircleVandermonde_real_moment (N : ℕ) (hN : 0<N) (s : ℝ)
    (hs : 0<1+(N:ℝ)*s) :
    Integrable (fun x => (periodicD1CircleVandermonde N x)^s) (periodicHaar (Fin N)) ∧
      (∫x,(periodicD1CircleVandermonde N x)^s ∂periodicHaar (Fin N))=
        Real.Gamma (1+(N:ℝ)*s)/(Real.Gamma (1+s))^N := by
  letI := periodicD1BetaProductLaw_probability N hN
  have hm := periodicD1BetaProductVariable_gamma_moment N hN s hs
  have h := periodicD1_bounded_moments_proper_transfer
    (periodicD1CircleVandermonde_continuous N).measurable.aemeasurable
    (periodicD1BetaProductVariable_continuous N).measurable.aemeasurable
    (Eventually.of_forall (periodicD1CircleVandermonde_bounds N))
    ((periodicD1BetaProductVariable_bounds N hN).mono (fun _ h => ⟨h.1.le,h.2⟩))
    (fun m => (periodicD1CircleVandermonde_natural_moment N m).trans
      (periodicD1BetaProductVariable_natural_moment N hN m).symm)
    (fun y : ℝ => y^s) (by fun_prop) hm.1
  exact ⟨h.1,h.2.trans hm.2⟩

end DGRHS.Periodic
