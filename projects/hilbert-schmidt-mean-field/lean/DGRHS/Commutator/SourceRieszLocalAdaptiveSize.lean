import DGRHS.Commutator.SourceRieszLocalCenteredCap
import DGRHS.Gaussian.GaussianRieszAdaptiveScale

/-! Source-local gamma*N growth, preserving gamma through the adaptive split.
The final size is the actual supremum of the physical cutoff family, not a
supplied growth premise or a chosen favorable size sequence. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration

lemma sourceRieszLocal_scalar_slope (C D γ N u α A a cap : ℝ)
    (hC : 0<C) (hD : 0≤D) (hγ : 0<γ) (hγ1 : γ≤1) (hN : 0<N) (hu : 1≤u)
    (hα0 : 0≤α) (hα1 : α≤1) (hA : 0≤A) (ha : 0≤a) (hcap : 0≤cap)
    (hAb : A≤D*γ*(1+(4*C*γ*N/u)^α)) (hab : a≤A) (hcapb : cap≤N/2*A) :
    min u cap*(1+a)≤(4*C+D)*(1+2*D)*γ*N := by
  let t := 4*C*γ*N
  have ht : 0<t := by dsimp[t];positivity
  have hu0 : 0<u := by linarith
  have hr : 0≤t/u := (div_pos ht hu0).le
  change A≤D*γ*(1+(t/u)^α) at hAb
  by_cases h : u≤t
  · have hr1 : 1≤t/u := (le_div_iff₀ hu0).2 (by linarith)
    have hp : (t/u)^α≤t/u := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hr1 hα1
    have hAU : A≤2*D*γ*(t/u) := by
      have hmul := mul_le_mul_of_nonneg_left hp (by positivity : 0≤D*γ)
      have hmul1 := mul_le_mul_of_nonneg_left hr1 (by positivity : 0≤D*γ)
      nlinarith
    calc
      _ ≤ u*(1+a) := mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ u*(1+A) := mul_le_mul_of_nonneg_left (by linarith : 1+a≤1+A) hu0.le
      _ ≤ u*(1+2*D*γ*(t/u)) := mul_le_mul_of_nonneg_left (by linarith) hu0.le
      _ = u+2*D*γ*t := by field_simp <;> ring
      _ ≤ t+2*D*γ*t := by linarith
      _ ≤ t*(1+2*D) := by nlinarith [mul_nonneg hD ht.le]
      _ ≤ _ := by dsimp[t];nlinarith [mul_nonneg hD (mul_nonneg (by positivity : 0≤1+2*D) (mul_nonneg hγ.le hN.le))]
  · have hr1 : t/u≤1 := (div_le_one hu0).2 (le_of_not_ge h)
    have hp := Real.rpow_le_one hr hr1 hα0
    have hAU : A≤2*D*γ := by nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : 0≤D*γ)]
    have hcb : cap≤N*D*γ := by nlinarith [mul_le_mul_of_nonneg_left hAU (by positivity : 0≤N/2)]
    calc
      _ ≤ cap*(1+a) := mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ ≤ (N*D*γ)*(1+a) := mul_le_mul_of_nonneg_right hcb (by positivity)
      _ ≤ (N*D*γ)*(1+2*D*γ) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ (N*D*γ)*(1+2*D) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤N*D*γ)
        have hmul := mul_le_mul_of_nonneg_left hγ1 (by positivity : 0≤2*D)
        simpa only [mul_one,add_comm] using add_le_add_left hmul 1
      _ ≤ _ := by nlinarith [mul_nonneg hC.le (mul_nonneg (by positivity : 0≤1+2*D) (mul_nonneg hγ.le hN.le))]

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceRieszLocalAdaptiveScale (s C γ N u : ℝ) : ℝ :=
  gaussianRieszAdaptiveScale 1 (4*C*γ) N u (Fintype.card ι) s

def sourceRieszLocalAdaptiveCap (s C γ N u : ℝ) : ℝ :=
  N/2*(12*γ*(gaussianRieszSourceCoefficient s/s*(sourceRieszLocalAdaptiveScale (ι:=ι) s C γ N u)^(-s)))

lemma sourceRieszLocalAdaptiveSize (μ : Measure E) [IsProbabilityMeasure μ]
    (s C γ : ℝ) (n : ℕ) (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ))
    (hC : 0<C) (hγ : 0<γ) (hγ1 : γ≤1) (σ : ℝ) (hσ : |σ|≤1)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) (N : ℝ) (hN : 0<N) :
    BddAbove (masterCutoffValues μ
      (fun u=>sourceRieszLocalCenteredCutoff μ s (sourceRieszLocalAdaptiveScale (ι:=ι) s C γ N u) n γ σ K v)
      (sourceRieszLocalAdaptiveCap (ι:=ι) s C γ N) 1) ∧
    masterCutoffSize μ
      (fun u=>sourceRieszLocalCenteredCutoff μ s (sourceRieszLocalAdaptiveScale (ι:=ι) s C γ N u) n γ σ K v)
      (sourceRieszLocalAdaptiveCap (ι:=ι) s C γ N) 1 ≤
      (4*C+12*gaussianRieszSourceCoefficient s/s)*(1+2*(12*gaussianRieszSourceCoefficient s/s))*γ*N := by
  let D := 12*gaussianRieszSourceCoefficient s/s
  let α := s/((Fintype.card ι:ℝ)-s)
  let M := (4*C+D)*(1+2*D)*γ*N
  let q := fun u=>sourceRieszLocalCenteredCutoff μ s (sourceRieszLocalAdaptiveScale (ι:=ι) s C γ N u) n γ σ K v
  let cap := sourceRieszLocalAdaptiveCap (ι:=ι) s C γ N
  have hD : 0≤D := by have hc:=gaussianRieszSourceCoefficient_pos s hs;dsimp[D];positivity
  have hdim : 0<(Fintype.card ι:ℝ)-s := by linarith
  have hα0 : 0≤α := (div_pos hs hdim).le
  have hα1 : α≤1 := (div_le_one hdim).2 (by linarith)
  have hb (u : ℝ) (hu : 1≤u) : min u (cap u)*(1+(eLpNormEssSup (q u) (μ.prod μ)).toReal)≤M := by
    let η := sourceRieszLocalAdaptiveScale (ι:=ι) s C γ N u
    let A := D*γ*η^(-s)
    have hu0 : 0<u := by linarith
    have hη : 0<η := (gaussianRieszAdaptiveScale_pos_le 1 (4*C*γ) N u (Fintype.card ι) s (by norm_num) (by positivity) hN hu0).1
    have hAe : (eLpNormEssSup (q u) (μ.prod μ)).toReal≤A := by
      have h:=essential_sourceRieszLocalCenteredCutoff_le μ s η n hs hη γ σ hγ.le hσ hv
      dsimp [q,A,D,η,sourceRieszLocalAdaptiveScale] at *
      convert h using 1 <;> ring
    have hAp : A≤D*γ*(1+(4*C*γ*N/u)^α) := by
      have hi := gaussianRieszAdaptiveScale_inverse_power_le 1 (4*C*γ) N u (Fintype.card ι) s
        (sourceRieszLocalAdaptiveScale (ι:=ι) s C γ N u) (by norm_num) (by positivity) hN hu0 hs hdim
      simp only [sourceRieszLocalAdaptiveScale,max_self,Real.one_rpow] at hi
      have he : (4*C*γ)^α*(N/u)^α=(4*C*γ*N/u)^α := by
        rw [←Real.mul_rpow (by positivity : 0≤4*C*γ) (div_pos hN hu0).le]
        congr 1
        ring
      rw [show s/((Fintype.card ι:ℝ)-s)=α from rfl,he] at hi
      exact mul_le_mul_of_nonneg_left hi (by positivity : 0≤D*γ)
    apply sourceRieszLocal_scalar_slope C D γ N u α A (eLpNormEssSup (q u) (μ.prod μ)).toReal (cap u)
      hC hD hγ hγ1 hN hu hα0 hα1 (by dsimp[A];positivity) ENNReal.toReal_nonneg
      (by dsimp[cap,sourceRieszLocalAdaptiveCap];have hc:=gaussianRieszSourceCoefficient_pos s hs;positivity) hAp hAe
    dsimp [cap,sourceRieszLocalAdaptiveCap,A,D,η]
    ring_nf
    exact le_rfl
  have hf : BddAbove (masterCutoffValues μ q cap 1) := ⟨M,by
    rintro z ⟨u,hu,rfl⟩
    exact hb u hu⟩
  refine ⟨hf,?_⟩
  apply csSup_le
  · exact ⟨min 1 (cap 1)*(1+(eLpNormEssSup (q 1) (μ.prod μ)).toReal),1,le_rfl,rfl⟩
  · rintro z ⟨u,hu,rfl⟩
    exact hb u hu

end DGRHS.Commutator

#check DGRHS.Commutator.sourceRieszLocal_scalar_slope
#print axioms DGRHS.Commutator.sourceRieszLocal_scalar_slope

#check DGRHS.Commutator.sourceRieszLocalAdaptiveScale
#print axioms DGRHS.Commutator.sourceRieszLocalAdaptiveScale

#check DGRHS.Commutator.sourceRieszLocalAdaptiveCap
#print axioms DGRHS.Commutator.sourceRieszLocalAdaptiveCap

#check DGRHS.Commutator.sourceRieszLocalAdaptiveSize
#print axioms DGRHS.Commutator.sourceRieszLocalAdaptiveSize
