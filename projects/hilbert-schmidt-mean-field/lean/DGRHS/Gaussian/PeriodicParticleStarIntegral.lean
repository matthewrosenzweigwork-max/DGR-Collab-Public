import DGRHS.Gaussian.PeriodicGreenExponentialIntegrability

/-! Proper factorization of particle stars under the actual product Haar law.
The distinguished particle is separated by the native measure-preserving
finite-coordinate equivalence; each remaining difference has exact Haar law. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicGreenExponentialMass (γ : ℝ) : ℝ :=
  ∫ x : PeriodicTorus ι,Real.exp (γ*periodicLogKernel x) ∂periodicHaar ι

def periodicParticleStar (γ : ℝ) (N : ℕ) (i : Fin N) (x : Fin N → PeriodicTorus ι) : ℝ :=
  ∏ j : Fin N,if i=j then 1 else Real.exp (γ*periodicLogKernel (x i-x j))

lemma periodicParticleStar_nonneg (γ : ℝ) (N : ℕ) (i : Fin N) (x : Fin N → PeriodicTorus ι) :
    0≤periodicParticleStar γ N i x := by
  apply Finset.prod_nonneg
  intro j _
  split_ifs <;> positivity

lemma periodicParticleStar_measurable (γ : ℝ) (N : ℕ) (i : Fin N) :
    Measurable (periodicParticleStar (ι := ι) γ N i) := by
  apply Finset.measurable_prod
  intro j _
  by_cases hij : i=j
  · simp only [hij,if_true]; exact measurable_const
  · simp only [if_neg hij]
    exact Real.continuous_exp.measurable.comp (measurable_const.mul (periodicLogKernel_measurable.comp
      ((measurable_pi_apply i).sub (measurable_pi_apply j))))

lemma periodicGreenExponential_row_integral (γ : ℝ) (hγ0 : 0≤γ) (hγd : γ<(Fintype.card ι:ℝ))
    (x : PeriodicTorus ι) :
    (∫ y,Real.exp (γ*periodicLogKernel (x-y)) ∂periodicHaar ι)=periodicGreenExponentialMass (ι := ι) γ :=
  DGRHS.Decoupling.integral_comp_preserving (periodicHaar_preserving_sub_left x)
    (fun y => Real.exp (γ*periodicLogKernel y)) (periodicLogKernel_exp_integrable γ hγ0 hγd).aestronglyMeasurable

lemma periodicStarSplit_integrable (γ : ℝ) (hγ0 : 0≤γ) (hγd : γ<(Fintype.card ι:ℝ)) (n : ℕ) :
    Integrable (fun p : PeriodicTorus ι × (Fin n → PeriodicTorus ι) =>
      ∏ j : Fin n,Real.exp (γ*periodicLogKernel (p.1-p.2 j)))
      ((periodicHaar ι).prod (Measure.pi (fun _ : Fin n => periodicHaar ι))) := by
  let F := fun p : PeriodicTorus ι × (Fin n → PeriodicTorus ι) =>
    ∏ j : Fin n,Real.exp (γ*periodicLogKernel (p.1-p.2 j))
  have hm : Measurable F := Finset.measurable_prod _ (fun j _ =>
    Real.continuous_exp.measurable.comp (measurable_const.mul (periodicLogKernel_measurable.comp
      (measurable_fst.sub ((measurable_pi_apply j).comp measurable_snd)))))
  have hi (x : PeriodicTorus ι) : Integrable (fun y : Fin n → PeriodicTorus ι => F (x,y))
      (Measure.pi (fun _ : Fin n => periodicHaar ι)) :=
    Integrable.fintype_prod (fun _ => (periodicHaar_preserving_sub_left x).integrable_comp_of_integrable
      (periodicLogKernel_exp_integrable γ hγ0 hγd))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall hi,?_⟩
  have he : (fun x : PeriodicTorus ι => ∫ y : Fin n → PeriodicTorus ι,‖F (x,y)‖
      ∂Measure.pi (fun _ : Fin n => periodicHaar ι)) = fun _ => (periodicGreenExponentialMass (ι := ι) γ)^n := by
    funext x
    have hn (y : Fin n → PeriodicTorus ι) : 0≤F (x,y) := Finset.prod_nonneg (fun j _ => (Real.exp_pos _).le)
    simp only [Real.norm_of_nonneg (hn _),F]
    rw [integral_fintype_prod_eq_prod (fun (_ : Fin n) (y : PeriodicTorus ι) => Real.exp (γ*periodicLogKernel (x-y)))]
    simp only [periodicGreenExponential_row_integral γ hγ0 hγd,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [he]
  exact integrable_const _

lemma periodicStarSplit_integral (γ : ℝ) (hγ0 : 0≤γ) (hγd : γ<(Fintype.card ι:ℝ)) (n : ℕ) :
    (∫ p : PeriodicTorus ι × (Fin n → PeriodicTorus ι),
      ∏ j : Fin n,Real.exp (γ*periodicLogKernel (p.1-p.2 j))
      ∂(periodicHaar ι).prod (Measure.pi (fun _ : Fin n => periodicHaar ι))) =
      (periodicGreenExponentialMass (ι := ι) γ)^n := by
  rw [integral_prod _ (periodicStarSplit_integrable γ hγ0 hγd n)]
  have hrow (x : PeriodicTorus ι) :
      (∫ y : Fin n → PeriodicTorus ι,∏ j,Real.exp (γ*periodicLogKernel (x-y j))
        ∂Measure.pi (fun _ : Fin n => periodicHaar ι)) = (periodicGreenExponentialMass (ι := ι) γ)^n := by
    rw [integral_fintype_prod_eq_prod (fun (_ : Fin n) (y : PeriodicTorus ι) => Real.exp (γ*periodicLogKernel (x-y)))]
    simp only [periodicGreenExponential_row_integral γ hγ0 hγd,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simp only [hrow,integral_const,probReal_univ,one_smul]

lemma periodicParticleStar_succAbove (γ : ℝ) (n : ℕ) (i : Fin (n+1)) (x : Fin (n+1) → PeriodicTorus ι) :
    periodicParticleStar γ (n+1) i x =
      ∏ j : Fin n,Real.exp (γ*periodicLogKernel (x i-x (i.succAbove j))) := by
  unfold periodicParticleStar
  rw [Fin.prod_univ_succAbove _ i]
  simp

lemma periodicParticleStar_split (γ : ℝ) (n : ℕ) (i : Fin (n+1))
    (p : PeriodicTorus ι × (Fin n → PeriodicTorus ι)) :
    periodicParticleStar γ (n+1) i ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => PeriodicTorus ι) i).symm p) =
      ∏ j : Fin n,Real.exp (γ*periodicLogKernel (p.1-p.2 j)) := by
  rw [periodicParticleStar_succAbove]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]

/-- Actual proper star integral, uniform in its center index. -/
theorem periodicParticleStar_integrable_integral (γ : ℝ) (hγ0 : 0≤γ) (hγd : γ<(Fintype.card ι:ℝ))
    (N : ℕ) (i : Fin N) :
    Integrable (periodicParticleStar γ N i) (Measure.pi (fun _ : Fin N => periodicHaar ι)) ∧
    (∫ x,periodicParticleStar γ N i x ∂Measure.pi (fun _ : Fin N => periodicHaar ι))=
      (periodicGreenExponentialMass (ι := ι) γ)^(N-1) := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => periodicHaar ι) i).symm
    have hi : Integrable (periodicParticleStar γ (n+1) i) (Measure.pi (fun _ : Fin (n+1) => periodicHaar ι)) := by
      rw [← hp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
      simpa only [Function.comp_def,periodicParticleStar_split] using periodicStarSplit_integrable γ hγ0 hγd n
    refine ⟨hi,?_⟩
    rw [← hp.integral_comp']
    simpa only [periodicParticleStar_split,Nat.add_sub_cancel] using periodicStarSplit_integral γ hγ0 hγd n

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicStarSplit_integrable
#print axioms DGRHS.Periodic.periodicParticleStar_integrable_integral
#check @DGRHS.Periodic.periodicParticleStar_integrable_integral
