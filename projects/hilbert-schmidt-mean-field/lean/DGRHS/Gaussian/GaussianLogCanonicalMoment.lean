import DGRHS.Gaussian.GaussianLogSourceMoment
import DGRHS.Gaussian.LogPhysicalTailComparison

/-! Proper canonical moments use the actual source moment and
proper potential exponential tail. Young's inequality avoids an extra potential
L2 assumption; finite Jensen is derived directly from exp's tangent inequality. -/
noncomputable section
open MeasureTheory Real
open scoped BigOperators
namespace DGRHS.Gaussian
open DGRHS.Concentration

lemma log_exp_finite_mean_le (n : ℕ) (hn : 1 ≤ n) (v : Fin n → ℝ) :
    Real.exp ((∑ i,v i)/(n : ℝ)) ≤ (∑ i,Real.exp (v i))/(n : ℝ) := by
  classical
  let m := (∑ i,v i)/(n : ℝ)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hm : (n : ℝ)*m = ∑ i,v i := by dsimp [m];field_simp
  have hi (i : Fin n) : Real.exp m*(1+v i-m) ≤ Real.exp (v i) := by
    calc
      _ ≤ Real.exp m*Real.exp (v i-m) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (v i-m)]) (Real.exp_pos m).le
      _ = _ := by rw [← Real.exp_add];congr 1;ring
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  have he : (∑ i : Fin n,Real.exp m*(1+v i-m)) = (n : ℝ)*Real.exp m := by
    simp_rw [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    rw [← hm]
    ring
  rw [he] at hs
  exact (le_div_iff₀ hn').mpr (by simpa only [mul_comm] using hs)

lemma log_exp_product_le_half_sum_doubles (x y : ℝ) :
    Real.exp x*Real.exp y ≤ (Real.exp (2*x)+Real.exp (2*y))/2 := by
  have hx : Real.exp (2*x) = (Real.exp x)^2 := by
    rw [show 2*x=x+x by ring,Real.exp_add]
    ring
  have hy : Real.exp (2*y) = (Real.exp y)^2 := by
    rw [show 2*y=y+y by ring,Real.exp_add]
    ring
  rw [hx,hy]
  nlinarith [sq_nonneg (Real.exp x-Real.exp y)]

lemma log_potential_empirical_exp_integrable_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ) (hF : Integrable F μ)
    (c : ℝ) (he : Integrable (fun x => Real.exp (-c*F x)) μ) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun ω : Fin n → Ω => Real.exp (-c/(n : ℝ)*(∑ i,F (ω i))))
      (Measure.pi (fun _ : Fin n => μ)) ∧
    (∫ ω : Fin n → Ω,Real.exp (-c/(n : ℝ)*(∑ i,F (ω i)))
      ∂Measure.pi (fun _ : Fin n => μ)) ≤ ∫ x,Real.exp (-c*F x) ∂μ := by
  classical
  let P := Measure.pi (fun _ : Fin n => μ)
  have hi (i : Fin n) : Integrable (fun ω : Fin n → Ω => Real.exp (-c*F (ω i))) P :=
    integrable_comp_eval (μ := fun _ : Fin n => μ) (i := i) he
  have hS : Integrable (fun ω : Fin n → Ω => (∑ i,Real.exp (-c*F (ω i)))/(n : ℝ)) P :=
    (integrable_finsetSum _ (fun i _ => hi i)).div_const _
  have hFm (i : Fin n) : Integrable (fun ω : Fin n → Ω => F (ω i)) P :=
    integrable_comp_eval (μ := fun _ : Fin n => μ) (i := i) hF
  have hX : AEStronglyMeasurable
      (fun ω : Fin n → Ω => Real.exp (-c/(n : ℝ)*(∑ i,F (ω i)))) P :=
    Real.continuous_exp.comp_aestronglyMeasurable
      ((integrable_finsetSum _ (fun i _ => hFm i)).aestronglyMeasurable.const_mul _)
  have hb (ω : Fin n → Ω) : Real.exp (-c/(n : ℝ)*(∑ i,F (ω i))) ≤
      (∑ i,Real.exp (-c*F (ω i)))/(n : ℝ) := by
    have h := log_exp_finite_mean_le n hn (fun i => -c*F (ω i))
    have harg : (∑ i : Fin n,-c*F (ω i))/(n : ℝ) =
        -c/(n : ℝ)*(∑ i : Fin n,F (ω i)) := by
      rw [← Finset.mul_sum]
      ring
    rw [harg] at h
    exact h
  have hI : Integrable (fun ω : Fin n → Ω => Real.exp (-c/(n : ℝ)*(∑ i,F (ω i)))) P := by
    apply hS.mono' hX
    exact Filter.Eventually.of_forall (fun ω => by rw [Real.norm_of_nonneg (Real.exp_pos _).le];exact hb ω)
  refine ⟨hI,?_⟩
  have hmean : (∫ ω : Fin n → Ω,(∑ i,Real.exp (-c*F (ω i)))/(n : ℝ) ∂P) =
      ∫ x,Real.exp (-c*F x) ∂μ := by
    rw [integral_div,integral_finsetSum _ (fun i _ => hi i)]
    have heval (i : Fin n) : (∫ ω : Fin n → Ω,Real.exp (-c*F (ω i)) ∂P) =
        ∫ x,Real.exp (-c*F x) ∂μ := integral_comp_eval (μ := fun _ : Fin n => μ) (i := i) he.aestronglyMeasurable
    simp_rw [heval]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
    field_simp
  exact (integral_mono hI hS hb).trans_eq hmean

variable {ι : Type*} [Fintype ι]

theorem logPhysicalCanonical_uniform_exponential (β : ℝ) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (htail : Integrable (fun x => Real.exp (-2*β*logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
      (gaussianRieszDensityMeasure ρ)) :
    ∃ C : ℝ,∀ n : ℕ,1 ≤ n →
      Integrable (fun ω => Real.exp (β*iidNegativeStatistic n
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair) ω))
        (Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (β*iidNegativeStatistic n
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair) ω)
        ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ≤ C := by
  classical
  let μ := gaussianRieszDensityMeasure ρ
  let F := logPhysicalPotential μ
  let m := ∫ p,logPhysicalPair p ∂μ.prod μ
  let c := Real.exp (β*m/2)/2
  have hc : 0 ≤ c := by dsimp [c];positivity
  have hF : Integrable F μ := logPhysicalPotential_integrable μ hpair
  have htail' : Integrable (fun x => Real.exp (-(2*β)*F x)) μ := by
    convert htail using 1
    funext x
    congr 1
    dsimp [F,μ]
    ring
  obtain ⟨C,hC⟩ := logPhysicalSource_uniform_exponential (2*β) (by positivity) hd ρ M hM hρ hpair
  refine ⟨c*(C+∫ x,Real.exp (-(2*β)*F x) ∂μ),?_⟩
  intro n hn
  let P := Measure.pi (fun _ : Fin n => μ)
  let X := logPhysicalMomentExponent μ β n
  let A := fun ω : Fin n → EuclideanSpace ℝ ι => β*iidNegativeStatistic n (hoeffdingCentered μ logPhysicalPair) ω
  let Y := fun ω : Fin n → EuclideanSpace ℝ ι => -β/(n : ℝ)*(∑ i,F (ω i))
  have htwice (ω : Fin n → EuclideanSpace ℝ ι) :
      2*X ω = logPhysicalMomentExponent μ (2*β) n ω := by
    dsimp [X,logPhysicalMomentExponent]
    ring
  have hexpY (ω : Fin n → EuclideanSpace ℝ ι) :
      2*Y ω = -(2*β)/(n : ℝ)*(∑ i,F (ω i)) := by dsimp [Y];ring
  obtain ⟨hY,bY⟩ := log_potential_empirical_exp_integrable_bound μ F hF (2*β) htail' n hn
  have hS := (hC n hn).1
  have hmajor : Integrable (fun ω => c*(Real.exp (logPhysicalMomentExponent μ (2*β) n ω)+
      Real.exp (-(2*β)/(n : ℝ)*(∑ i,F (ω i))))) P := (hS.add hY).const_mul c
  have hraw : StronglyMeasurable (logPhysicalPair : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → ℝ) := by
    apply Measurable.stronglyMeasurable
    unfold logPhysicalPair
    fun_prop
  have hAm : Measurable A := (measurable_physical_iidNegativeStatistic n _
    (stronglyMeasurable_hoeffdingCentered μ _ hraw).measurable).const_mul β
  have hb (ω : Fin n → EuclideanSpace ℝ ι) : Real.exp (A ω) ≤
      c*(Real.exp (logPhysicalMomentExponent μ (2*β) n ω)+
        Real.exp (-(2*β)/(n : ℝ)*(∑ i,F (ω i)))) := by
    have hAlgebra : A ω = X ω+Y ω+β*m/2 := by
      dsimp [A,X,Y,F,m,logPhysicalMomentExponent]
      ring
    rw [hAlgebra,Real.exp_add,Real.exp_add]
    have hYoung := mul_le_mul_of_nonneg_left (log_exp_product_le_half_sum_doubles (X ω) (Y ω))
      (Real.exp_pos (β*m/2)).le
    rw [htwice,hexpY] at hYoung
    dsimp [c]
    nlinarith only [hYoung]
  have hI : Integrable (fun ω => Real.exp (A ω)) P := by
    apply hmajor.mono' (Real.continuous_exp.comp_aestronglyMeasurable hAm.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun ω => by rw [Real.norm_of_nonneg (Real.exp_pos _).le];exact hb ω)
  refine ⟨hI,?_⟩
  calc
    _ ≤ ∫ ω,c*(Real.exp (logPhysicalMomentExponent μ (2*β) n ω)+
        Real.exp (-(2*β)/(n : ℝ)*(∑ i,F (ω i)))) ∂P := integral_mono hI hmajor hb
    _ = c*((∫ ω,Real.exp (logPhysicalMomentExponent μ (2*β) n ω) ∂P)+
        ∫ ω,Real.exp (-(2*β)/(n : ℝ)*(∑ i,F (ω i))) ∂P) := by
      rw [integral_const_mul,integral_add hS hY]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (hC n hn).2 bY) hc

end DGRHS.Gaussian

#check DGRHS.Gaussian.log_exp_finite_mean_le
#print axioms DGRHS.Gaussian.log_exp_finite_mean_le
#check DGRHS.Gaussian.log_exp_product_le_half_sum_doubles
#print axioms DGRHS.Gaussian.log_exp_product_le_half_sum_doubles
#check DGRHS.Gaussian.log_potential_empirical_exp_integrable_bound
#print axioms DGRHS.Gaussian.log_potential_empirical_exp_integrable_bound
#check DGRHS.Gaussian.logPhysicalCanonical_uniform_exponential
#print axioms DGRHS.Gaussian.logPhysicalCanonical_uniform_exponential
