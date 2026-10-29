import DGRHS.Commutator.SourceRieszBrownianConditional

/-! An actual elementary Ito integral in an arbitrary supplied full filtration.
The process is the Brownian increment formula, not an abstract martingale input.
The conditional-projection proof adapts the elementary strategy in Kexing Ying
et al., BrownianMotion/Gaussian/BrownianMotion.lean (revision
0d5b6eb928e616d3b1f774ad7d233c167d9f42c9), and Raphael Coelho's MathFin
ItoIntegralProcessMartingale (f085fd572075c934827f1eb92c4a085941cd21e5).
Both original Apache-2.0 source/license records are preserved in own records.
The coefficient is measurable in the full filtration at its left endpoint.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma sourceRiesz_memLp_bounded_mul (P : Measure Ω) (H Y : Ω→ℝ)
    (hH : AEStronglyMeasurable H P) (hY : MemLp Y 2 P)
    (K : ℝ) (hb : ∀ᵐ ω ∂P,‖H ω‖≤K) : MemLp (fun ω=>H ω*Y ω) 2 P := by
  apply (memLp_two_iff_integrable_sq (hH.mul hY.aestronglyMeasurable)).mpr
  have hbsq : ∀ᵐ ω ∂P,‖H ω^2‖≤K^2 := by
    filter_upwards [hb] with ω hh
    simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg (H ω)) hh 2
  simpa only [Pi.mul_apply,Pi.pow_apply,mul_pow] using
    hY.integrable_sq.bdd_mul (hH.pow 2) hbsq

theorem sourceRiesz_brownian_elementary_integral
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P)
    (hBa : StronglyAdapted F B) (hBc : ∀ ω,Continuous (fun r=>B r ω))
    (hind : ∀ s t,s≤t →
      Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)
    (a b : ℝ≥0) (hab : a≤b) (H : Ω→ℝ) (hH : StronglyMeasurable[F a] H)
    (K : ℝ) (hK : 0≤K) (hb : ∀ᵐ ω ∂P,|H ω|≤K) :
    let V := fun t ω=>H ω*(B (min t b) ω-B (min t a) ω)
    Martingale V F P ∧ (∀ t,MemLp (V t) 2 P) ∧
      (∀ ω,Continuous (fun t=>V t ω)) ∧ (∀ ω,V 0 ω=0) := by
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
  refine ⟨?_,hL2,?_,?_⟩
  · exact (martingale_condExp Y F P).congr hVa hproj
  · intro ω
    exact continuous_const.mul (((hBc ω).comp (continuous_id.min continuous_const)).sub
      ((hBc ω).comp (continuous_id.min continuous_const)))
  · intro ω
    simp only [V,min_eq_left (show (0:ℝ≥0)≤b from bot_le),
      min_eq_left (show (0:ℝ≥0)≤a from bot_le),sub_self,mul_zero]

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_memLp_bounded_mul
#print axioms DGRHS.Commutator.sourceRiesz_memLp_bounded_mul
#check @DGRHS.Commutator.sourceRiesz_brownian_elementary_integral
#print axioms DGRHS.Commutator.sourceRiesz_brownian_elementary_integral
