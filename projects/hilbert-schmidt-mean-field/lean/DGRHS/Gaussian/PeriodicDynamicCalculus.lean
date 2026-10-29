import DGRHS.Gaussian.PeriodicRieszTransportKernel
import DGRHS.Gaussian.PeriodicLogTransportKernel
import DGRHS.Gaussian.PeriodicRieszPairProperties
import DGRHS.Gaussian.PeriodicRieszSmoothSymmetry
import DGRHS.Dynamics.SourceAdjointHessianLipschitz
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
Packet P11c, units 3-4 (part 1): calculus on the flat torus `𝕋^d = ι → UnitAddCircle` for the dynamical
statements (Remark 2.1: the proofs are unchanged after the notational substitutions).

A test function `f : 𝕋^d → ℝ` is differentiated through its lift `periodicLiftFn f = f ∘ periodicLift`
to `ℝ^d`; the lift is lattice periodic, so its gradient, Hessian and Laplacian are lattice periodic and
`periodicGrad f`, `periodicLap f` are well defined torus functions (evaluated at the centered lift).
The interaction force `∇g` is the gradient of the smooth lift of the periodic kernel (the same smooth
representative as in the torus transport kernel of Theorem 2.8); `periodicForcePair F v (x,y) =
⟪F(x - y), v x - v y⟫` is the `n = 1` transport kernel.
-/

noncomputable section
open MeasureTheory Laplacian Set
open scoped NNReal RealInnerProductSpace ENNReal Classical
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-! ### Lifts -/

lemma periodicLift_eq_iff_lattice (a b : E) (h : periodicLift a = periodicLift b) :
    ∃ m : PeriodicFrequency ι, a = b + periodicFrequencyVector m := by
  have hi : ∀ i, ∃ n : ℤ, a i = b i + (n : ℝ) := by
    intro i
    have h1 : (((a i - b i : ℝ)) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub]
      have := congrFun h i
      simp only [periodicLift] at this
      rw [this]; abel
    rw [AddCircle.coe_eq_zero_iff] at h1
    obtain ⟨n, hn⟩ := h1
    exact ⟨n, by simp at hn; linarith⟩
  choose m hm using hi
  refine ⟨m, ?_⟩
  ext i
  simp [hm i]

/-- A function on `ℝ^d` that is invariant under lattice translations. -/
def IsLatticePeriodic (F : E → ℝ) : Prop :=
  ∀ z (m : PeriodicFrequency ι), F (z + periodicFrequencyVector m) = F z

/-- The lift `f ∘ periodicLift` of a torus function to `ℝ^d`. -/
def periodicLiftFn (f : PeriodicTorus ι → ℝ) : E → ℝ := fun x => f (periodicLift x)

lemma isLatticePeriodic_periodicLiftFn (f : PeriodicTorus ι → ℝ) :
    IsLatticePeriodic (periodicLiftFn f) := by
  intro z m
  simp [periodicLiftFn, periodicLift_add_lattice]

lemma IsLatticePeriodic.gradient_add {F : E → ℝ} (hF : IsLatticePeriodic F) (z : E)
    (m : PeriodicFrequency ι) : gradient F (z + periodicFrequencyVector m) = gradient F z := by
  have h : (fun y => F (y + periodicFrequencyVector m)) = F := funext fun y => hF y m
  have := fderiv_comp_add_right (f := F) (𝕜 := ℝ) (periodicFrequencyVector m) (x := z)
  rw [h] at this
  simp only [gradient, ← this]

lemma IsLatticePeriodic.laplacian_add {F : E → ℝ} (hF : IsLatticePeriodic F) (z : E)
    (m : PeriodicFrequency ι) : laplacian F (z + periodicFrequencyVector m) = laplacian F z := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_add_lattice hF 2 z m]

lemma IsLatticePeriodic.iteratedFDeriv_add {F : E → ℝ} (hF : IsLatticePeriodic F) (n : ℕ) (z : E)
    (m : PeriodicFrequency ι) :
    iteratedFDeriv ℝ n F (z + periodicFrequencyVector m) = iteratedFDeriv ℝ n F z :=
  iteratedFDeriv_add_lattice hF n z m

/-- Gradient of a torus function (through its lift), a torus function with values in `ℝ^d`. -/
def periodicGrad (f : PeriodicTorus ι → ℝ) (z : PeriodicTorus ι) : E :=
  gradient (periodicLiftFn f) (periodicCenteredLift z)

/-- Laplacian of a torus function (through its lift). -/
def periodicLap (f : PeriodicTorus ι → ℝ) (z : PeriodicTorus ι) : ℝ :=
  laplacian (periodicLiftFn f) (periodicCenteredLift z)

lemma periodicCenteredLift_periodicLift (x : E) :
    ∃ m : PeriodicFrequency ι, periodicCenteredLift (periodicLift x) = x + periodicFrequencyVector m :=
  periodicLift_eq_iff_lattice _ _ (periodicLift_centeredLift _)

lemma periodicGrad_lift (f : PeriodicTorus ι → ℝ) (x : E) :
    periodicGrad f (periodicLift x) = gradient (periodicLiftFn f) x := by
  obtain ⟨m, hm⟩ := periodicCenteredLift_periodicLift (ι := ι) x
  unfold periodicGrad
  rw [hm]
  exact (isLatticePeriodic_periodicLiftFn f).gradient_add x m

lemma periodicLap_lift (f : PeriodicTorus ι → ℝ) (x : E) :
    periodicLap f (periodicLift x) = laplacian (periodicLiftFn f) x := by
  obtain ⟨m, hm⟩ := periodicCenteredLift_periodicLift (ι := ι) x
  unfold periodicLap
  rw [hm]
  exact (isLatticePeriodic_periodicLiftFn f).laplacian_add x m

lemma measurable_periodicGrad {f : PeriodicTorus ι → ℝ} (hf : ContDiff ℝ 1 (periodicLiftFn f)) :
    Measurable (periodicGrad f) := by
  have h1 : Continuous (gradient (periodicLiftFn f)) := by
    have : Continuous (fderiv ℝ (periodicLiftFn f)) := hf.continuous_fderiv (by norm_num)
    exact ((InnerProductSpace.toDual ℝ E).symm.continuous).comp this
  exact h1.measurable.comp measurable_periodicCenteredLift

lemma measurable_periodicLap {f : PeriodicTorus ι → ℝ} (hf : ContDiff ℝ 2 (periodicLiftFn f)) :
    Measurable (periodicLap f) := by
  have h1 : Continuous (laplacian (periodicLiftFn f)) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    refine continuous_finsetSum _ (fun i _ => ?_)
    have h := hf.continuous_iteratedFDeriv (m := 2) le_rfl
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ
      ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]).continuous.comp h
  exact h1.measurable.comp measurable_periodicCenteredLift

/-- The Euclidean norm of the centered lift is at most `d` times the torus norm. -/
lemma norm_periodicCenteredLift_le_card_mul (z : PeriodicTorus ι) :
    ‖periodicCenteredLift z‖ ≤ (Fintype.card ι : ℝ) * ‖z‖ := by
  have hd : 1 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hm : ∀ i, |periodicCenteredLift z i| ≤ ‖z‖ := by
    intro i
    rw [periodicCenteredLift_apply, ← norm_circleCentered]
    exact norm_le_pi_norm z i
  have h0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hsq : ‖periodicCenteredLift z‖ ^ 2 ≤ ((Fintype.card ι : ℝ) * ‖z‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖periodicCenteredLift z i‖ ^ 2 ≤ ∑ _i : ι, ‖z‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hm i) 2
      _ = (Fintype.card ι : ℝ) * ‖z‖ ^ 2 := by simp
      _ ≤ (Fintype.card ι : ℝ) ^ 2 * ‖z‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          nlinarith
      _ = _ := by ring
  exact le_of_sq_le_sq hsq (by positivity)

/-- The gradient of a torus function with bounded Hessian is Lipschitz for the torus sup metric. -/
lemma periodicGrad_lipschitz {f : PeriodicTorus ι → ℝ} (hf : ContDiff ℝ 2 (periodicLiftFn f))
    (K : ℝ≥0) (hK : ∀ z, ‖iteratedFDeriv ℝ 2 (periodicLiftFn f) z‖ ≤ (K : ℝ)) :
    LipschitzWith (K * (Fintype.card ι : ℝ≥0)) (periodicGrad f) := by
  have hL := DGRHS.Dynamics.sourceAdjoint_gradient_lipschitz_of_hessian_bound
    (periodicLiftFn f) hf K hK
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  set a := periodicCenteredLift x with ha
  set b := a - periodicCenteredLift (x - y) with hb
  have hlx : periodicLift a = x := periodicLift_centeredLift x
  have hly : periodicLift b = y := by
    rw [hb, periodicLift_sub, hlx, periodicLift_centeredLift]; abel
  have e1 : periodicGrad f x = gradient (periodicLiftFn f) a := by
    rw [← hlx]; exact periodicGrad_lift f a
  have e2 : periodicGrad f y = gradient (periodicLiftFn f) b := by
    rw [← hly]; exact periodicGrad_lift f b
  rw [e1, e2]
  refine (hL.dist_le_mul a b).trans ?_
  rw [dist_eq_norm a b, hb, sub_sub_cancel]
  have := norm_periodicCenteredLift_le_card_mul (ι := ι) (x - y)
  rw [dist_eq_norm x y]
  push_cast
  calc (K : ℝ) * ‖periodicCenteredLift (x - y)‖ ≤ (K : ℝ) * ((Fintype.card ι : ℝ) * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left this K.coe_nonneg
    _ = _ := by ring

end DGRHS.Periodic

namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-! ### The interaction force and the `n = 1` transport kernel -/

/-- The torus interaction force: the gradient of the smooth lift `g` of the periodic kernel at the
centered lift of `z`, and `0` at the collision `z = 0`. -/
def periodicForceOfSmooth (g : E → ℝ) (z : PeriodicTorus ι) : E :=
  if z = 0 then 0 else gradient g (periodicCenteredLift z)

/-- The `n = 1` pair kernel `⟪F(x - y), v x - v y⟫` of a force `F` and a velocity field `v`. -/
def periodicForcePair (F : PeriodicTorus ι → E) (v : PeriodicTorus ι → E)
    (p : PeriodicTorus ι × PeriodicTorus ι) : ℝ :=
  ⟪F (p.1 - p.2), v p.1 - v p.2⟫

lemma periodicForceOfSmooth_zero (g : E → ℝ) : periodicForceOfSmooth g (0 : PeriodicTorus ι) = 0 := by
  simp [periodicForceOfSmooth]

lemma periodicTransportKernel_one_eq_forcePair (g : E → ℝ) (v : PeriodicTorus ι → E)
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    (if p.1 = p.2 then 0 else
      iteratedFDeriv ℝ 1 g (periodicCenteredLift (p.1 - p.2)) (fun _ => v p.1 - v p.2)) =
    periodicForcePair (periodicForceOfSmooth g) v p := by
  by_cases hp : p.1 = p.2
  · simp [periodicForcePair, hp, periodicForceOfSmooth_zero]
  · have hz : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hp
    simp only [ite_eq_right hp, periodicForcePair, periodicForceOfSmooth, ite_eq_right hz]
    rw [iteratedFDeriv_one_apply, inner_gradient_left]

lemma periodicRieszTransportKernel_one (s : ℝ) (v : PeriodicTorus ι → E) :
    periodicRieszTransportKernel 1 s v =
      periodicForcePair (periodicForceOfSmooth (periodicRieszSmooth (ι := ι) s)) v := by
  funext p
  exact periodicTransportKernel_one_eq_forcePair _ v p

lemma periodicLogTransportKernel_one (v : PeriodicTorus ι → E) :
    periodicLogTransportKernel 1 v =
      periodicForcePair (periodicForceOfSmooth (periodicLogSmooth (ι := ι))) v := by
  funext p
  exact periodicTransportKernel_one_eq_forcePair _ v p

lemma gradient_neg_of_even {g : E → ℝ} (heven : ∀ u, g (-u) = g u) (u : E) :
    gradient g (-u) = -gradient g u := by
  refine ext_inner_right ℝ (fun w => ?_)
  rw [inner_gradient_left, inner_neg_left, inner_gradient_left]
  have h := iteratedFDeriv_neg_apply_neg heven 1 u (fun _ => w)
  have h2 := iteratedFDeriv_neg_apply_neg heven 1 u (fun _ => -w)
  simp only [iteratedFDeriv_one_apply, neg_neg] at h h2
  have h3 : fderiv ℝ g (-u) (-w) = -fderiv ℝ g (-u) w := map_neg _ _
  rw [h3] at h
  linarith

lemma periodicForceOfSmooth_odd {g : E → ℝ} (heven : ∀ u, g (-u) = g u)
    (hper : IsLatticePeriodic g) (z : PeriodicTorus ι) :
    periodicForceOfSmooth g (-z) = -periodicForceOfSmooth g z := by
  by_cases hz : z = 0
  · simp [hz, periodicForceOfSmooth_zero]
  · have hz' : -z ≠ 0 := neg_ne_zero.mpr hz
    simp only [periodicForceOfSmooth, ite_eq_right hz, ite_eq_right hz']
    obtain ⟨m, hm⟩ := exists_centeredLift_neg z
    rw [hm, hper.gradient_add, gradient_neg_of_even heven]

lemma measurable_periodicForceOfSmooth {g : E → ℝ}
    (hco : ContDiffOn ℝ 1 g (periodicOffLattice : Set E)) :
    Measurable (periodicForceOfSmooth g : PeriodicTorus ι → E) := by
  let U : Set E := (periodicOffLattice : Set E)
  have hU : IsOpen U := isOpen_periodicOffLattice
  have hcf : ContinuousOn (fderiv ℝ g) U := hco.continuousOn_fderiv_of_isOpen hU le_rfl
  have hcg : ContinuousOn (gradient g) U :=
    ((InnerProductSpace.toDual ℝ E).symm.continuous).comp_continuousOn hcf
  have hmeas : Measurable (U.piecewise (gradient g) (fun _ => (0 : E))) :=
    hcg.measurable_piecewise continuousOn_const hU.measurableSet
  have heq : (periodicForceOfSmooth g : PeriodicTorus ι → E) =
      fun z => U.piecewise (gradient g) (fun _ => (0 : E)) (periodicCenteredLift z) := by
    funext z
    by_cases hz : z = 0
    · have h0 : periodicCenteredLift z ∉ U := by
        intro h
        have := h 0
        simp [hz, periodicCenteredLift_zero] at this
      rw [Set.piecewise_eq_of_notMem _ _ _ h0]
      simp [periodicForceOfSmooth, hz]
    · have h1 : periodicCenteredLift z ∈ U := periodicCenteredLift_mem_offLattice hz
      rw [Set.piecewise_eq_of_mem _ _ _ h1]
      simp [periodicForceOfSmooth, hz]
  rw [heq]
  exact hmeas.comp measurable_periodicCenteredLift

end DGRHS.Periodic
