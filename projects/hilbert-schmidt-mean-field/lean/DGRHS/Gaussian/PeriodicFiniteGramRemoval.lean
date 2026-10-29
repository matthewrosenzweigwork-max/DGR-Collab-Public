import DGRHS.Gaussian.PeriodicFiniteGaussianRemoval

/-! Exact ordered off-diagonal finite Gram partition. Pointwise Wick
normalization cancels each selected atom's diagonal before residual Jensen;
there is no external trace prefactor or trace convergence assumption. -/
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian
variable {α γ δ : Type*} [Fintype α] [Fintype γ] [Fintype δ]

lemma periodic_sum_offDiagonal {η : Type*} [Fintype η] (f : η → η → ℝ) :
    (∑ i,∑ j,if i=j then 0 else f i j) = (∑ i,∑ j,f i j)-∑ i,f i i := by
  have he (i : η) : (∑ j,if i=j then 0 else f i j)+f i i=∑ j,f i j := by
    calc
      _ = (∑ j,if i=j then 0 else f i j)+(∑ j,if i=j then f i j else 0) := by simp
      _ = ∑ j,((if i=j then 0 else f i j)+(if i=j then f i j else 0)) :=
        (Finset.sum_add_distrib).symm
      _ = _ := by apply Finset.sum_congr rfl;intro j _;split_ifs <;> simp_all
  have hh := congrArg (fun g : η → ℝ => ∑ i,g i) (funext he)
  simp only [Finset.sum_add_distrib] at hh
  linarith

lemma periodic_Gram_square_offDiagonal {η : Type*} [Fintype η] (q : η → γ → ℝ) :
    (∑ a,(∑ i,q i a)^2)-(∑ i,∑ a,q i a^2) =
      ∑ i,∑ j,if i=j then 0 else ∑ a,q i a*q j a := by
  rw [periodic_sum_offDiagonal]
  congr 1
  · simp_rw [pow_two,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  · simp only [pow_two]

def periodicFiniteGramPartition (p : α → ℝ) (q : α → γ → ℝ)
    (r : α → δ → ℝ) (t : ℝ) (N : ℕ) : ℝ :=
  ∑ l : Fin N → α,(∏ i,p (l i))*Real.exp (t^2/2*
    (∑ i : Fin N,∑ j : Fin N,if i=j then 0 else
      (∑ a,q (l i) a*q (l j) a)+(∑ b,r (l i) b*r (l j) b)))

/-- Actual Gaussian word expansion equals the ordered-pair Gram partition,
including N=0,1. Every product integral is proper independently of p. -/
theorem periodicFiniteGramPartition_gaussian_identity (p : α → ℝ)
    (q : α → γ → ℝ) (r : α → δ → ℝ) (t : ℝ) (N : ℕ) :
    (∫ zw,periodicFiniteJoinedFactor p q r t zw^N
      ∂(finiteStandardGaussian γ).prod (finiteStandardGaussian δ)) =
      periodicFiniteGramPartition p q r t N := by
  simp_rw [periodicFiniteJoinedFactor_pow_eq]
  rw [integral_finsetSum _ (fun l _ =>
    ((periodicFiniteGaussianWick_particle_integral t (fun i : Fin N => q (l i))).1.mul_prod
      (periodicFiniteGaussianWick_particle_integral t (fun i : Fin N => r (l i))).1).const_mul _)]
  unfold periodicFiniteGramPartition
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_const_mul,integral_prod_mul
    (fun z : γ → ℝ => ∏ i : Fin N,periodicFiniteGaussianWick t (q (l i)) z)
    (fun w : δ → ℝ => ∏ i : Fin N,periodicFiniteGaussianWick t (r (l i)) w),
    (periodicFiniteGaussianWick_particle_integral t (fun i : Fin N => q (l i))).2,
    (periodicFiniteGaussianWick_particle_integral t (fun i : Fin N => r (l i))).2,
    ←Real.exp_add,periodic_Gram_square_offDiagonal,periodic_Gram_square_offDiagonal]
  congr 2
  rw [←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

/-- No diagonal/trace bound on the actual residual is needed. -/
theorem periodicFiniteGramPartition_firstShell_lower (p : α → ℝ) (hp : ∀ a,0≤p a)
    (q : α → γ → ℝ) (r : α → δ → ℝ) (t : ℝ) (N : ℕ) :
    (∫ z,periodicFiniteWickFactor p q t z^N ∂finiteStandardGaussian γ) ≤
      periodicFiniteGramPartition p q r t N := by
  rw [←periodicFiniteGramPartition_gaussian_identity]
  exact periodicFiniteGaussian_residual_removal p hp q r t N

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_sum_offDiagonal
#print axioms DGRHS.Periodic.periodic_Gram_square_offDiagonal
#print axioms DGRHS.Periodic.periodicFiniteGramPartition_gaussian_identity
#print axioms DGRHS.Periodic.periodicFiniteGramPartition_firstShell_lower
#check @DGRHS.Periodic.periodicFiniteGramPartition_gaussian_identity
#check @DGRHS.Periodic.periodicFiniteGramPartition_firstShell_lower
