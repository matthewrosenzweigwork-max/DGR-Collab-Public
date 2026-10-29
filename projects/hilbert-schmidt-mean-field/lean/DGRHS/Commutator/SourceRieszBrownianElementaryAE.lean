import DGRHS.Commutator.SourceRieszBrownianMartingale

/-! Continuity-free elementary projection identities for the actual full-
filtration Brownian integral. This extracts the algebraic conditioning argument
already attributed in SourceRieszBrownianStepMartingale and removes its unused
path-continuity premise from the martingale and L2 assertions. The terminal
integral and L2 process definitions remain the identical frozen objects. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem sourceRiesz_brownian_elementary_martingale
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P)
    (hBa : StronglyAdapted F B)
    (hind : ∀ s t,s≤t →
      Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)
    (a b : ℝ≥0) (hab : a≤b) (H : Ω→ℝ) (hH : StronglyMeasurable[F a] H)
    (K : ℝ) (hK : 0≤K) (hb : ∀ᵐ ω ∂P,|H ω|≤K) :
    let V := fun t ω=>H ω*(B (min t b) ω-B (min t a) ω)
    Martingale V F P ∧ (∀ t,MemLp (V t) 2 P) ∧
      (∀ ω,V 0 ω=0) := by
  dsimp only
  let V := fun t ω=>H ω*(B (min t b) ω-B (min t a) ω)
  have hBm (r) : Measurable (B r) := ((hBa r).mono (F.le r)).measurable
  have hHm : AEStronglyMeasurable H P := (hH.mono (F.le a)).aestronglyMeasurable
  have hbn : ∀ᵐ ω ∂P,‖H ω‖≤K := by simpa only [Real.norm_eq_abs] using hb
  have hL2 (t) : MemLp (V t) 2 P :=
    sourceRiesz_memLp_bounded_mul P H _ hHm
      (hB.hasLaw_sub (min t b) (min t a)).hasGaussianLaw.memLp_two K hbn
  have hVa : StronglyAdapted F V := by
    intro t
    by_cases hta : t≤a
    · have he : V t=fun _=>0 := by
        funext ω
        simp only [V,min_eq_left hta,min_eq_left (hta.trans hab),sub_self,mul_zero]
      rw [he]
      exact stronglyMeasurable_const
    · exact (hH.mono (F.mono (le_of_not_ge hta))).mul
        (((hBa (min t b)).mono (F.mono (min_le_left _ _))).sub
          ((hBa (min t a)).mono (F.mono (min_le_left _ _))))
  let Y := fun ω=>H ω*(B b ω-B a ω)
  have hYL2 : MemLp Y 2 P := sourceRiesz_memLp_bounded_mul P H _ hHm
    (hB.hasLaw_sub b a).hasGaussianLaw.memLp_two K hbn
  have hYi := hYL2.integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have hproj (t) : (P[Y | F t])=ᵐ[P] V t := by
    by_cases hta : t≤a
    · have hz := (sourceRiesz_brownian_adapted_step P F B hB hBm a b hab
        (hind a b hab) H hH K hK hb).2.2.1
      have htower := condExp_condExp_of_le (F.mono hta) (F.le a) (f:=Y) (μ:=P)
      have hz' : (P[P[Y | F a] | F t])=ᵐ[P] (fun _=>0) := by
        exact (condExp_congr_ae hz).trans (by simp)
      have he : V t=fun _=>0 := by
        funext ω
        simp only [V,min_eq_left hta,min_eq_left (hta.trans hab),sub_self,mul_zero]
      rw [he]
      exact htower.symm.trans hz'
    · have hat : a≤t := (le_of_not_ge hta)
      by_cases hbt : b≤t
      · have hYm : StronglyMeasurable[F t] Y :=
          (hH.mono (F.mono hat)).mul
            (((hBa b).mono (F.mono hbt)).sub ((hBa a).mono (F.mono hat)))
        rw [condExp_of_stronglyMeasurable (F.le t) hYm hYi]
        exact ae_of_all _ fun ω=>by simp only [Y,V,min_eq_right hbt,min_eq_right hat]
      · have htb : t≤b := (le_of_not_ge hbt)
        let U := fun ω=>H ω*(B b ω-B t ω)
        have hstep := sourceRiesz_brownian_adapted_step P F B hB hBm t b htb
          (hind t b htb) H (hH.mono (F.mono hat)) K hK hb
        have he : Y=U+V t := by
          funext ω
          dsimp only [Y,U,V,Pi.add_apply]
          rw [min_eq_left htb,min_eq_right hat]
          ring
        rw [he]
        have hvint := (hL2 t).integrable (by norm_num : (1:ℝ≥0∞)≤2)
        have hsum := condExp_add hstep.1 hvint (F t)
        rw [condExp_of_stronglyMeasurable (F.le t) (hVa t) hvint] at hsum
        filter_upwards [hsum,hstep.2.2.1] with ω hh hz
        simpa only [Pi.add_apply,hz,zero_add] using hh
  refine ⟨?_,hL2,?_⟩
  · exact (martingale_condExp Y F P).congr hVa hproj
  · intro ω
    simp only [V,min_eq_left (show (0:ℝ≥0)≤b from bot_le),
      min_eq_left (show (0:ℝ≥0)≤a from bot_le),sub_self,mul_zero]


variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
variable (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBa : StronglyAdapted F B)
variable (hind : ∀ s t,s≤t →
  Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)


include hB hBa hind in
lemma sourceRieszBrownianItoRawAssembly_projection_no_continuity (c : SourceRieszBrownianAtom F T →₀ ℝ)
    (t : ℝ≥0) : P[sourceRieszBrownianItoRawAssembly F T B c | F t]=ᵐ[P]
      fun ω=>∑ A∈c.support,(c A*A.value ω)*(B (min t A.b) ω-B (min t A.a) ω) := by
  let U := fun (A : SourceRieszBrownianAtom F T) ω=>(c A*A.value ω)*(B A.b ω-B A.a ω)
  let V := fun (A : SourceRieszBrownianAtom F T) (r : ℝ≥0) ω=>
    (c A*A.value ω)*(B (min r A.b) ω-B (min r A.a) ω)
  have hs (A : SourceRieszBrownianAtom F T) :=
    sourceRiesz_brownian_elementary_martingale P F B hB hBa hind A.a A.b A.hab
      (fun ω=>c A*A.value ω) (stronglyMeasurable_const.mul A.value_measurable)
      ‖c A‖ (norm_nonneg _) (ae_of_all _ fun ω=>by
        rw [←Real.norm_eq_abs,norm_mul]
        simpa using mul_le_mul_of_nonneg_left (A.value_bound ω) (norm_nonneg (c A)))
  have hterminal (A : SourceRieszBrownianAtom F T) : V A (max t A.b)=U A := by
    funext ω
    dsimp only [V,U]
    rw [min_eq_right (le_max_right t A.b),
      min_eq_right (A.hab.trans (le_max_right t A.b))]
  have hi (A : SourceRieszBrownianAtom F T) : Integrable (U A) P := by
    rw [←hterminal A]
    exact ((hs A).2.1 _).integrable one_le_two
  have hp (A : SourceRieszBrownianAtom F T) : P[U A | F t]=ᵐ[P] V A t := by
    rw [←hterminal A]
    exact (hs A).1.2 t (max t A.b) (le_max_left t A.b)
  have hall (S : Finset (SourceRieszBrownianAtom F T)) :
      P[∑ A∈S,U A | F t]=ᵐ[P] ∑ A∈S,V A t := by
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | insert A S hAS ih =>
      rw [Finset.sum_insert hAS,Finset.sum_insert hAS]
      exact (condExp_add (hi A) (integrable_finsetSum' S (fun A _=>hi A)) (F t)).trans ((hp A).add ih)
  have he : sourceRieszBrownianItoRawAssembly F T B c=∑ A∈c.support,U A := by
    funext ω
    simpa only [Finset.sum_apply] using sourceRieszBrownianItoRawAssembly_apply F T B c ω
  rw [he]
  exact (hall c.support).trans (ae_of_all _ fun ω=>by simp only [Finset.sum_apply,V])

lemma sourceRieszBrownianProcess_elementary_no_continuity (c : SourceRieszBrownianAtom F T →₀ ℝ) (t : ℝ≥0) :
    sourceRieszBrownianProcess P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c) t
      =ᵐ[P] fun ω=>∑ A∈c.support,(c A*A.value ω)*(B (min t A.b) ω-B (min t A.a) ω) := by
  apply (condExp_congr_ae (sourceRieszBrownianIntegral_elementary_coe P F T B hB hBa hind c)).trans
  have he : (fun ω=>∑ A∈c.support,(c A*A.value ω)*(B A.b ω-B A.a ω))=
      sourceRieszBrownianItoRawAssembly F T B c :=
    (funext (sourceRieszBrownianItoRawAssembly_apply F T B c)).symm
  rw [he]
  exact sourceRieszBrownianItoRawAssembly_projection_no_continuity P F T B hB hBa hind c t

lemma sourceRieszBrownianProcessL2_terminal_no_continuity (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    sourceRieszBrownianProcessL2 P F T B hB hBa hind g T=
      sourceRieszBrownianIntegral P F T B hB hBa hind g := by
  apply congrFun (DenseRange.equalizer (sourceRieszBrownianAtomAssembly_dense P F T)
    (sourceRieszBrownianProcessL2_continuous P F T B hB hBa hind T)
    (sourceRieszBrownianIntegral P F T B hB hBa hind).continuous (funext fun c=>?_)) g
  simp only [Function.comp_apply]
  apply Lp.ext
  filter_upwards [sourceRieszBrownianProcessL2_coe P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c) T,
    sourceRieszBrownianProcess_elementary_no_continuity P F T B hB hBa hind c T,
    sourceRieszBrownianIntegral_elementary_coe P F T B hB hBa hind c] with ω h1 h2 h3
  rw [h1,h2,h3]
  apply Finset.sum_congr rfl
  intro A _
  rw [min_eq_right A.hbT,min_eq_right (A.hab.trans A.hbT)]

lemma sourceRieszBrownianProcessL2_zero_no_continuity (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    sourceRieszBrownianProcessL2 P F T B hB hBa hind g 0=0 := by
  apply congrFun (DenseRange.equalizer (sourceRieszBrownianAtomAssembly_dense P F T)
    (sourceRieszBrownianProcessL2_continuous P F T B hB hBa hind 0)
    continuous_const (funext fun c=>?_)) g
  simp only [Function.comp_apply]
  apply Lp.ext
  filter_upwards [sourceRieszBrownianProcessL2_coe P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c) 0,
    sourceRieszBrownianProcess_elementary_no_continuity P F T B hB hBa hind c 0,Lp.coeFn_zero (E:=ℝ) (p:=2) (μ:=P)] with ω h1 h2 h3
  simp only [h1,h2,h3,min_eq_left (show (0:ℝ≥0)≤_ from bot_le),sub_self,mul_zero,Finset.sum_const_zero,Pi.zero_apply]


end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_brownian_elementary_martingale
#print axioms DGRHS.Commutator.sourceRiesz_brownian_elementary_martingale
#check @DGRHS.Commutator.sourceRieszBrownianItoRawAssembly_projection_no_continuity
#print axioms DGRHS.Commutator.sourceRieszBrownianItoRawAssembly_projection_no_continuity
#check @DGRHS.Commutator.sourceRieszBrownianProcess_elementary_no_continuity
#print axioms DGRHS.Commutator.sourceRieszBrownianProcess_elementary_no_continuity
#check @DGRHS.Commutator.sourceRieszBrownianProcessL2_terminal_no_continuity
#print axioms DGRHS.Commutator.sourceRieszBrownianProcessL2_terminal_no_continuity
#check @DGRHS.Commutator.sourceRieszBrownianProcessL2_zero_no_continuity
#print axioms DGRHS.Commutator.sourceRieszBrownianProcessL2_zero_no_continuity
