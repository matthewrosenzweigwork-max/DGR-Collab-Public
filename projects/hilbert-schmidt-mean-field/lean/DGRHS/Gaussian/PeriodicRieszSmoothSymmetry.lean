import DGRHS.Gaussian.PeriodicRieszSmoothKernel

/-!
Packet P9h, unit 2 (part 10): periodicity and evenness of the smooth periodic Riesz kernel on `ℝ^d`
and of its derivatives.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

lemma periodicProfileSum_add_lattice (c s : ℝ) (S : Set ℝ) (z : E) (m : PeriodicFrequency ι) :
    periodicProfileSum c s S (z + periodicFrequencyVector m) = periodicProfileSum c s S z := by
  unfold periodicProfileSum
  have h := (Equiv.addRight m).tsum_eq
    (fun k : PeriodicFrequency ι => periodicProfile c s S (z + periodicFrequencyVector k))
  rw [← h]
  refine tsum_congr fun k => ?_
  simp only [Equiv.coe_addRight]
  congr 1
  have : periodicFrequencyVector (k + m) = periodicFrequencyVector k + periodicFrequencyVector m := by
    ext i; simp
  rw [this]; abel

lemma periodicProfile_neg (c s : ℝ) (S : Set ℝ) (y : E) :
    periodicProfile c s S (-y) = periodicProfile c s S y := by
  unfold periodicProfile sourceRieszGaussianScale
  simp [norm_neg]

lemma periodicProfileSum_neg (c s : ℝ) (S : Set ℝ) (z : E) :
    periodicProfileSum c s S (-z) = periodicProfileSum c s S z := by
  unfold periodicProfileSum
  have h := (Equiv.neg (PeriodicFrequency ι)).tsum_eq
    (fun k : PeriodicFrequency ι => periodicProfile c s S (z + periodicFrequencyVector k))
  rw [← h]
  refine tsum_congr fun k => ?_
  simp only [Equiv.neg_apply]
  rw [← periodicProfile_neg c s S (z + periodicFrequencyVector (-k))]
  congr 1
  have : periodicFrequencyVector (-k) = -periodicFrequencyVector k := by ext i; simp
  rw [this]; abel

lemma periodicPhase_add_lattice (k m : PeriodicFrequency ι) (z : E) :
    periodicPhase k (z + periodicFrequencyVector m) = periodicPhase k z + (∑ i, (k i : ℝ) * (m i : ℝ)) := by
  rw [periodicPhase_eq, periodicPhase_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_add]

lemma cos_two_pi_add_int (x : ℝ) (n : ℤ) : Real.cos (2 * Real.pi * (x + (n : ℝ))) = Real.cos (2 * Real.pi * x) := by
  have h : 2 * Real.pi * (x + (n : ℝ)) = 2 * Real.pi * x + (n : ℝ) * (2 * Real.pi) := by ring
  rw [h]
  exact Real.cos_add_int_mul_two_pi _ _

lemma periodicRieszLongKernel_add_lattice (s ε : ℝ) (z : E) (m : PeriodicFrequency ι) :
    periodicRieszLongKernel s ε (z + periodicFrequencyVector m) = periodicRieszLongKernel s ε z := by
  unfold periodicRieszLongKernel
  refine tsum_congr fun k => ?_
  rw [periodicPhase_add_lattice]
  have h : (∑ i, (k i : ℝ) * (m i : ℝ)) = (((∑ i, k i * m i : ℤ)) : ℝ) := by push_cast; rfl
  rw [h, cos_two_pi_add_int]

lemma periodicRieszLongKernel_neg (s ε : ℝ) (z : E) :
    periodicRieszLongKernel s ε (-z) = periodicRieszLongKernel s ε z := by
  unfold periodicRieszLongKernel
  have h := (Equiv.neg (PeriodicFrequency ι)).tsum_eq
    (fun k : PeriodicFrequency ι => periodicRieszLCCoeff s ε k * Real.cos (2 * Real.pi * periodicPhase k z))
  rw [← h]
  refine tsum_congr fun k => ?_
  simp only [Equiv.neg_apply]
  rw [periodicRieszLCCoeff_neg]
  congr 1
  have h1 : periodicPhase k (-z) = periodicPhase (-k) z := by
    rw [periodicPhase_eq, periodicPhase_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [h1]

lemma periodicRieszSmoothLift_add_lattice (s τ : ℝ) (z : E) (m : PeriodicFrequency ι) :
    periodicRieszSmoothLift s τ (z + periodicFrequencyVector m) = periodicRieszSmoothLift s τ z := by
  simp only [periodicRieszSmoothLift_eq, periodicProfileSum_add_lattice,
    periodicRieszLongKernel_add_lattice]

lemma periodicRieszSmoothLift_neg (s τ : ℝ) (z : E) :
    periodicRieszSmoothLift s τ (-z) = periodicRieszSmoothLift s τ z := by
  simp only [periodicRieszSmoothLift_eq, periodicProfileSum_neg, periodicRieszLongKernel_neg]

/-- The iterated derivative of a lattice-periodic function is lattice-periodic. -/
lemma iteratedFDeriv_add_lattice {f : E → ℝ} (hf : ∀ z (m : PeriodicFrequency ι), f (z + periodicFrequencyVector m) = f z)
    (n : ℕ) (z : E) (m : PeriodicFrequency ι) :
    iteratedFDeriv ℝ n f (z + periodicFrequencyVector m) = iteratedFDeriv ℝ n f z := by
  have h : (fun y => f (y + periodicFrequencyVector m)) = f := funext fun y => hf y m
  have := iteratedFDeriv_comp_add_right (f := f) (𝕜 := ℝ) n (periodicFrequencyVector m) z
  rw [h] at this
  exact this.symm

/-- Derivatives of an even function: `D^n f(-z)(-w, ..., -w) = D^n f(z)(w, ..., w)`. -/
lemma iteratedFDeriv_neg_apply_neg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {f : F → ℝ}
    (hf : ∀ u, f (-u) = f u) (n : ℕ) (z : F) (w : Fin n → F) :
    iteratedFDeriv ℝ n f (-z) (fun i => -w i) = iteratedFDeriv ℝ n f z w := by
  let g : F ≃L[ℝ] F := (LinearEquiv.smulOfNeZero ℝ F (-1 : ℝ) (by norm_num)).toContinuousLinearEquiv
  have hg : ∀ u, g u = -u := by intro u; change (-1 : ℝ) • u = -u; simp
  have he : (f ∘ g) = f := by
    funext u
    simp [Function.comp_apply, hg, hf]
  have hc : iteratedFDeriv ℝ n (f ∘ g) z =
      (iteratedFDeriv ℝ n f (g z)).compContinuousLinearMap (fun _ => g.toContinuousLinearMap) := by
    simpa only [preimage_univ, iteratedFDerivWithin_univ] using
      g.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ z) n
  rw [he] at hc
  have hm := congrArg (fun F' => F' w) hc
  simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply, hg] using hm.symm

end DGRHS.Periodic
