import DGRHS.Commutator.SourceRieszLocalMaster
import DGRHS.CLT.SourceRawEnergy

/-! Literal Riesz transport variation and its actual bounded one-body
correction. Proper singular sections and the genuine product integrals are
proved before the local numerator is compared to the checked master field. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceRieszLocalTransportEnergy (ρ : E→ℝ) (s : ℝ) (n : ℕ) (v : E→E)
    (N : ℕ) (ω : Fin N→E) : ℝ :=
  2*DGRHS.CLT.sourceCanonicalModulatedEnergy
    (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (sourceRieszTransportKernel n s v))
    (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b=>sourceRieszTransportKernel n s v (a,b)))
    (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b=>sourceRieszTransportKernel n s v (a,b))) N ω

def sourceRieszLocalTransportCorrection (ρ : E→ℝ) (s : ℝ) (n : ℕ) (v : E→E)
    (N : ℕ) (ω : Fin N→E) : ℝ :=
  -2*(N:ℝ)⁻¹*(∑ i : Fin N,∫ y,sourceRieszTransportKernel n s v (ω i,y) ∂gaussianRieszDensityMeasure ρ)+
    ∫ p,sourceRieszTransportKernel n s v p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)

lemma sourceRieszLocalTransportEnergy_raw (ρ : E→ℝ) (s : ℝ) (n : ℕ) (v : E→E)
    (N : ℕ) (hN : 0<N) (ω : Fin N→E) :
    sourceRieszLocalTransportEnergy ρ s n v N ω=
      ((N:ℝ)^2)⁻¹*DGRHS.CanonicalVariance.offDiagonalSum (sourceRieszTransportKernel n s v) ω-
      2*(N:ℝ)⁻¹*(∑ i : Fin N,∫ y,sourceRieszTransportKernel n s v (ω i,y) ∂gaussianRieszDensityMeasure ρ)+
      ∫ p,sourceRieszTransportKernel n s v p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ) := by
  unfold sourceRieszLocalTransportEnergy hoeffdingCentered
  rw [DGRHS.CLT.sourceCanonicalModulatedEnergy_raw _ _
    (fun a b=>(sourceRieszTransportKernel_symmetric s n v (a,b)).symm) N hN]
  have he : Function.uncurry (fun a b=>sourceRieszTransportKernel n s v (a,b))=sourceRieszTransportKernel n s v := by funext p;cases p;rfl
  rw [he]
  dsimp [DGRHS.interactionEnergy,DGRHS.potential]
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp

lemma sourceRieszLocalTransportEnergy_scaled (ρ : E→ℝ) (s : ℝ) (n : ℕ) (v : E→E)
    (N : ℕ) (hN : 0<N) (ω : Fin N→E) :
    (N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω=
      -2*iidNegativeStatistic N (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (sourceRieszTransportKernel n s v)) ω+
      sourceRieszLocalTransportCorrection ρ s n v N ω := by
  have he := DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent
    (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (sourceRieszTransportKernel n s v))
    (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b=>sourceRieszTransportKernel n s v (a,b)))
    (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b=>sourceRieszTransportKernel n s v (a,b))) (-2) hN ω
  rw [←sourceRieszLocal_energy_normalization (-2)] at he
  dsimp [sourceRieszLocalTransportEnergy,sourceRieszLocalTransportCorrection,DGRHS.potential,DGRHS.interactionEnergy] at *
  nlinarith [he]

lemma sourceRieszLocalTransport_section (s : ℝ) (n : ℕ) (hs : 0<s)
    (hd : s<(Fintype.card ι:ℝ)) {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (x : E) :
    Integrable (fun y=>sourceRieszTransportKernel n s v (x,y)) (gaussianRieszDensityMeasure ρ) ∧
    |∫ y,sourceRieszTransportKernel n s v (x,y) ∂gaussianRieszDensityMeasure ρ|≤
      sourceRieszLocalProfileConstant (ι:=ι) s n*(K:ℝ)^n*gaussianRieszPhysicalPotentialConstant s M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  let A := sourceRieszLocalProfileConstant (ι:=ι) s n*(K:ℝ)^n
  have hA : 0≤A := by have h:= (sourceRieszLocalProfileConstant_properties (ι:=ι) s n).1;dsimp[A];positivity
  have hm : StronglyMeasurable (fun y : E=>sourceRieszTransportKernel n s v (x,y)) :=
    (measurable_sourceRieszTransportKernel s n hv).stronglyMeasurable.comp_measurable (measurable_const.prodMk measurable_id)
  have hF := sourceRiesz_full_potential_bound s hs hd ρ M hM hρ x
  have hi : Integrable (fun y=>sourceRieszTransportKernel n s v (x,y)) μ :=
    (hF.1.const_mul A).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun y=>by
      simpa only [Real.norm_eq_abs] using sourceRieszLocal_full_transport_bound s n hs hv (x,y)))
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ y,|sourceRieszTransportKernel n s v (x,y)| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ:=μ) (fun y : E=>sourceRieszTransportKernel n s v (x,y))
    _ ≤ ∫ y,A*gaussianRieszPhysicalPair s (x,y) ∂μ := integral_mono_ae hi.abs (hF.1.const_mul A)
      (Filter.Eventually.of_forall (fun y=>sourceRieszLocal_full_transport_bound s n hs hv (x,y)))
    _ = A*(∫ y,gaussianRieszPhysicalPair s (x,y) ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hF.2.2 hA

lemma sourceRieszLocalTransport_pair (s : ℝ) (n : ℕ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    Integrable (sourceRieszTransportKernel n s v) ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ∧
    |∫ p,sourceRieszTransportKernel n s v p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)|≤
      sourceRieszLocalProfileConstant (ι:=ι) s n*(K:ℝ)^n*gaussianRieszPhysicalPotentialConstant s M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  let A := sourceRieszLocalProfileConstant (ι:=ι) s n*(K:ℝ)^n
  have hA : 0≤A := by have h:= (sourceRieszLocalProfileConstant_properties (ι:=ι) s n).1;dsimp[A];positivity
  have hF := (memLp_gaussianRieszPhysicalPair s hs (by linarith) ρ M hM hρ).integrable (by norm_num)
  have hi : Integrable (sourceRieszTransportKernel n s v) (μ.prod μ) :=
    (hF.const_mul A).mono' (measurable_sourceRieszTransportKernel s n hv).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p=>by simpa only [Real.norm_eq_abs] using sourceRieszLocal_full_transport_bound s n hs hv p))
  refine ⟨hi,?_⟩
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ x,|∫ y,sourceRieszTransportKernel n s v (x,y) ∂μ| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ:=μ) (fun x : E=>∫ y,sourceRieszTransportKernel n s v (x,y) ∂μ)
    _ ≤ ∫ _ : E,A*gaussianRieszPhysicalPotentialConstant s M ι ∂μ :=
      integral_mono_ae hi.integral_prod_left.abs (integrable_const _)
        (Filter.Eventually.of_forall (fun x=>(sourceRieszLocalTransport_section s n hs (by linarith) hv ρ M hM hρ x).2))
    _ = _ := by simp [A]

lemma abs_sourceRieszLocalTransportCorrection_le (s : ℝ) (n : ℕ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (N : ℕ) (hN : 0<N) (ω : Fin N→E) :
    |sourceRieszLocalTransportCorrection ρ s n v N ω|≤
      3*(sourceRieszLocalProfileConstant (ι:=ι) s n*(K:ℝ)^n)*gaussianRieszPhysicalPotentialConstant s M ι := by
  let B := sourceRieszLocalProfileConstant (ι:=ι) s n*(K:ℝ)^n*gaussianRieszPhysicalPotentialConstant s M ι
  have hm := (sourceRieszLocalTransport_pair s n hs hd hv ρ M hM hρ).2
  have hsum : |∑ i : Fin N,∫ y,sourceRieszTransportKernel n s v (ω i,y) ∂gaussianRieszDensityMeasure ρ|≤(N:ℝ)*B := by
    calc
      _ ≤ ∑ i : Fin N,|∫ y,sourceRieszTransportKernel n s v (ω i,y) ∂gaussianRieszDensityMeasure ρ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin N,B := Finset.sum_le_sum (fun i _=>(sourceRieszLocalTransport_section s n hs (by linarith) hv ρ M hM hρ (ω i)).2)
      _ = _ := by simp
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have ha : |(N:ℝ)⁻¹*(∑ i : Fin N,∫ y,sourceRieszTransportKernel n s v (ω i,y) ∂gaussianRieszDensityMeasure ρ)|≤B := by
    rw [abs_mul,abs_inv,abs_of_pos hn]
    have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
    simpa only [←mul_assoc,inv_mul_cancel₀ hn.ne',one_mul] using h
  unfold sourceRieszLocalTransportCorrection
  rw [show -2*(N:ℝ)⁻¹*(∑ i : Fin N,∫ y,sourceRieszTransportKernel n s v (ω i,y) ∂gaussianRieszDensityMeasure ρ)=
    -2*((N:ℝ)⁻¹*(∑ i : Fin N,∫ y,sourceRieszTransportKernel n s v (ω i,y) ∂gaussianRieszDensityMeasure ρ)) by ring]
  have ht := abs_add_le (-2*((N:ℝ)⁻¹*(∑ i : Fin N,∫ y,sourceRieszTransportKernel n s v (ω i,y) ∂gaussianRieszDensityMeasure ρ)))
    (∫ p,sourceRieszTransportKernel n s v p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))
  rw [abs_mul,show |(-2:ℝ)|=2 by norm_num] at ht
  dsimp[B] at ha
  linarith

lemma sourceRieszLocalTransportCorrection_scaled_bound (s : ℝ) (n : ℕ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) (γ σ : ℝ) (hγ : 0≤γ) (hσ : |σ|≤1)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (N : ℕ) (hN : 0<N) (ω : Fin N→E) :
    σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ*sourceRieszLocalTransportCorrection ρ s n v N ω≤
      (3/4:ℝ)*γ*gaussianRieszPhysicalPotentialConstant s M ι := by
  let ε := sourceRieszLocalCoefficient (ι:=ι) s n K γ
  have hε : 0≤ε := sourceRieszLocalCoefficient_nonneg s n K γ K.coe_nonneg hγ
  have hP : 0≤gaussianRieszPhysicalPotentialConstant s M ι :=
    (sourceRiesz_full_potential_bound s hs (by linarith) ρ M hM hρ (0:E)).2.1.trans
      (sourceRiesz_full_potential_bound s hs (by linarith) ρ M hM hρ (0:E)).2.2
  have hb := abs_sourceRieszLocalTransportCorrection_le s n hs hd hv ρ M hM hρ N hN ω
  have he := sourceRieszLocalCoefficient_mul_le (ι:=ι) s n K γ K.coe_nonneg hγ
  have hr : σ*ε*sourceRieszLocalTransportCorrection ρ s n v N ω≤ε*|sourceRieszLocalTransportCorrection ρ s n v N ω| := by
    calc
      _ ≤ |σ*ε*sourceRieszLocalTransportCorrection ρ s n v N ω| := le_abs_self _
      _ = |σ| * ε * |sourceRieszLocalTransportCorrection ρ s n v N ω| := by rw [abs_mul,abs_mul,abs_of_nonneg hε]
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hσ (mul_nonneg hε (abs_nonneg (sourceRieszLocalTransportCorrection ρ s n v N ω)))]
  have hb' := mul_le_mul_of_nonneg_left hb hε
  have he' := mul_le_mul_of_nonneg_right he hP
  dsimp[ε] at *
  nlinarith [hr,hb',he']

end DGRHS.Commutator

#check DGRHS.Commutator.sourceRieszLocalTransportEnergy
#print axioms DGRHS.Commutator.sourceRieszLocalTransportEnergy

#check DGRHS.Commutator.sourceRieszLocalTransportCorrection
#print axioms DGRHS.Commutator.sourceRieszLocalTransportCorrection

#check DGRHS.Commutator.sourceRieszLocalTransportEnergy_raw
#print axioms DGRHS.Commutator.sourceRieszLocalTransportEnergy_raw

#check DGRHS.Commutator.sourceRieszLocalTransportEnergy_scaled
#print axioms DGRHS.Commutator.sourceRieszLocalTransportEnergy_scaled

#check DGRHS.Commutator.sourceRieszLocalTransport_section
#print axioms DGRHS.Commutator.sourceRieszLocalTransport_section

#check DGRHS.Commutator.sourceRieszLocalTransport_pair
#print axioms DGRHS.Commutator.sourceRieszLocalTransport_pair

#check DGRHS.Commutator.abs_sourceRieszLocalTransportCorrection_le
#print axioms DGRHS.Commutator.abs_sourceRieszLocalTransportCorrection_le

#check DGRHS.Commutator.sourceRieszLocalTransportCorrection_scaled_bound
#print axioms DGRHS.Commutator.sourceRieszLocalTransportCorrection_scaled_bound
