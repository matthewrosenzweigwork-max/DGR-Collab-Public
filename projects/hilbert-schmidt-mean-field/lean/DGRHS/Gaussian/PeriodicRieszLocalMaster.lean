import DGRHS.Gaussian.PeriodicRieszLocalM1

/-!
Packet P9h, unit 2 (part 25): the torus local threshold `β_loc`, the adaptive size bound, the physical
master cutoff family `MasterCutoffData` for the local exponent, and the uniform exponential moment
(torus versions of `SourceRieszLocalParameters`, `SourceRieszLocalAdaptiveSize`,
`SourceRieszLocalMaster`).
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

lemma periodicRieszCapConst_pos (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    0 < periodicRieszCapConst ι s := by
  unfold periodicRieszCapConst
  have := periodicRieszLongBound_nonneg (ι := ι) s hs 0
  have := periodicRieszMeanConst_nonneg (ι := ι) s hs hs2
  have := (periodicRieszSmoothCoeff_pos (ι := ι) s hs).le
  have := periodicLatticeGaussConst_pos (ι := ι)
  positivity

/-- The slope constant. -/
def periodicRieszDConst (ι : Type u) [Fintype ι] [Nonempty ι] (s : ℝ) : ℝ :=
  4 * periodicRieszCapConst ι s * (4 : ℝ) ^ s

lemma periodicRieszDConst_nonneg (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    0 ≤ periodicRieszDConst ι s := by
  have := (periodicRieszCapConst_pos (ι := ι) s hs hs2).le
  unfold periodicRieszDConst
  positivity

def periodicRieszNormConstant (ι : Type u) [Fintype ι] [Nonempty ι] (s M : ℝ) : ℝ :=
  1 + 16 * |periodicRieszNormControl ι s M| + 4 * Real.sqrt (periodicRieszNormControl ι s M)

def periodicRieszSizeConstant (ι : Type u) [Fintype ι] [Nonempty ι] (s M : ℝ) : ℝ :=
  (4 * periodicRieszAbsConst ι s M + periodicRieszDConst ι s) * (1 + 2 * periodicRieszDConst ι s)

def periodicRieszLocalBeta (s : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) : ℝ :=
  1 / (1 + 7 * |periodicRieszPotConst s hs2 M| +
    glzUniversalTailConstant * periodicRieszNormConstant ι s M +
    2 * glzUniversalTailConstant ^ 2 * periodicRieszSizeConstant ι s M)

lemma periodicRieszNormConstant_bounds (s M : ℝ) :
    0 < periodicRieszNormConstant ι s M ∧
    16 * periodicRieszNormControl ι s M ≤ periodicRieszNormConstant ι s M ∧
    4 * Real.sqrt (periodicRieszNormControl ι s M) ≤ periodicRieszNormConstant ι s M := by
  have ha := abs_nonneg (periodicRieszNormControl ι s M)
  have hs := Real.sqrt_nonneg (periodicRieszNormControl ι s M)
  have hb := le_abs_self (periodicRieszNormControl ι s M)
  unfold periodicRieszNormConstant
  refine ⟨by linarith, by linarith, by linarith⟩

lemma periodicRieszSizeConstant_pos (s M : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hM : 0 ≤ M) : 0 < periodicRieszSizeConstant ι s M := by
  have hA := periodicRieszAbsConst_pos (ι := ι) s M hs hs2 hM
  have hD := periodicRieszDConst_nonneg (ι := ι) s hs hs2
  unfold periodicRieszSizeConstant
  positivity

lemma periodic_beta_generic (P Cn Cs L : ℝ) (hL : 0 < L) (hCn : 0 < Cn) (hCs : 0 < Cs) :
    0 < 1 / (1 + 7 * |P| + L * Cn + 2 * L ^ 2 * Cs) ∧
    ∀ γ : ℝ, 0 < γ → γ ≤ 1 / (1 + 7 * |P| + L * Cn + 2 * L ^ 2 * Cs) →
      γ ≤ 1 ∧ (7 / 4 : ℝ) * γ * P ≤ 1 / 4 ∧ γ * Cn ≤ 1 / L ∧ 2 * L ^ 2 * Cs * γ ≤ 1 := by
  let D := 1 + 7 * |P| + L * Cn + 2 * L ^ 2 * Cs
  have hD : 0 < D := by dsimp [D]; positivity
  have hD1 : 1 ≤ D := by
    dsimp [D]; nlinarith [mul_nonneg hL.le hCn.le, mul_nonneg (sq_nonneg L) hCs.le, abs_nonneg P]
  have hDP : 7 * |P| ≤ D := by
    dsimp [D]; nlinarith [mul_nonneg hL.le hCn.le, mul_nonneg (sq_nonneg L) hCs.le]
  have hDCn : L * Cn ≤ D := by
    dsimp [D]; nlinarith [mul_nonneg (sq_nonneg L) hCs.le, abs_nonneg P]
  have hDCs : 2 * L ^ 2 * Cs ≤ D := by
    dsimp [D]; nlinarith [mul_nonneg hL.le hCn.le, abs_nonneg P]
  constructor
  · change 0 < 1 / D
    positivity
  intro γ hγ hγb
  change γ ≤ 1 / D at hγb
  have hγD : γ * D ≤ 1 := (le_div_iff₀ hD).mp hγb
  have h1 := mul_le_mul_of_nonneg_left hD1 hγ.le
  have hP := mul_le_mul_of_nonneg_left hDP hγ.le
  have hCn' := mul_le_mul_of_nonneg_left hDCn hγ.le
  have hCs' := mul_le_mul_of_nonneg_left hDCs hγ.le
  have hPabs := mul_le_mul_of_nonneg_left (le_abs_self P) hγ.le
  refine ⟨by nlinarith, by nlinarith, ?_, ?_⟩
  · apply (le_div_iff₀ hL).2
    nlinarith
  · nlinarith

lemma periodicRieszLocalBeta_properties (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (M : ℝ) (hM : 0 ≤ M) :
    0 < periodicRieszLocalBeta s hs2 M ∧
    ∀ γ : ℝ, 0 < γ → γ ≤ periodicRieszLocalBeta s hs2 M →
      γ ≤ 1 ∧ (7 / 4 : ℝ) * γ * periodicRieszPotConst s hs2 M ≤ 1 / 4 ∧
      γ * periodicRieszNormConstant ι s M ≤ 1 / glzUniversalTailConstant ∧
      2 * glzUniversalTailConstant ^ 2 * periodicRieszSizeConstant ι s M * γ ≤ 1 :=
  periodic_beta_generic _ _ _ _ glzUniversalTailConstant_pos
    (periodicRieszNormConstant_bounds (ι := ι) s M).1 (periodicRieszSizeConstant_pos s M hs hs2 hM)

/-! ### Adaptive scale and size -/

def periodicRieszLocalAdaptiveScale (s C γ N u : ℝ) : ℝ :=
  gaussianRieszAdaptiveScale (1 / 4) (4 * C * γ) N u (Fintype.card ι) s

def periodicRieszLocalAdaptiveCap (s C γ N u : ℝ) : ℝ :=
  N / 2 * (4 * (γ * periodicRieszCapConst ι s * (periodicRieszLocalAdaptiveScale (ι := ι) s C γ N u) ^ (-s)))

lemma periodicRieszLocalAdaptiveScale_pos_le (s C γ N u : ℝ) (hC : 0 < C) (hγ : 0 < γ) (hN : 0 < N)
    (hu : 0 < u) :
    0 < periodicRieszLocalAdaptiveScale (ι := ι) s C γ N u ∧
      periodicRieszLocalAdaptiveScale (ι := ι) s C γ N u ≤ 1 / 4 :=
  gaussianRieszAdaptiveScale_pos_le (1 / 4) (4 * C * γ) N u (Fintype.card ι) s (by norm_num)
    (by positivity) hN hu

lemma periodicRieszLocalAdaptiveSize (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (s C γ : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hC : 0 < C) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (σ : ℝ) (hσ : |σ| ≤ 1) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (N : ℝ) (hN : 0 < N) :
    BddAbove (masterCutoffValues (periodicCappedDensityMeasure ρ)
      (fun u => periodicRieszCenteredCutoff (periodicCappedDensityMeasure ρ) s
        (periodicRieszLocalAdaptiveScale (ι := ι) s C γ N u) n γ σ K v)
      (periodicRieszLocalAdaptiveCap (ι := ι) s C γ N) 1) ∧
    masterCutoffSize (periodicCappedDensityMeasure ρ)
      (fun u => periodicRieszCenteredCutoff (periodicCappedDensityMeasure ρ) s
        (periodicRieszLocalAdaptiveScale (ι := ι) s C γ N u) n γ σ K v)
      (periodicRieszLocalAdaptiveCap (ι := ι) s C γ N) 1 ≤
      (4 * C + periodicRieszDConst ι s) * (1 + 2 * periodicRieszDConst ι s) * γ * N := by
  let D := periodicRieszDConst ι s
  let μ := periodicCappedDensityMeasure ρ
  let α := s / ((Fintype.card ι : ℝ) - s)
  let M := (4 * C + D) * (1 + 2 * D) * γ * N
  let q := fun u => periodicRieszCenteredCutoff μ s (periodicRieszLocalAdaptiveScale (ι := ι) s C γ N u) n γ σ K v
  let cap := periodicRieszLocalAdaptiveCap (ι := ι) s C γ N
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hD : 0 ≤ D := periodicRieszDConst_nonneg s hs hs2
  have hdim : 0 < (Fintype.card ι : ℝ) - s := by linarith
  have hα0 : 0 ≤ α := (div_pos hs hdim).le
  have hα1 : α ≤ 1 := (div_le_one hdim).2 (by linarith)
  have hCc := (periodicRieszCapConst_pos (ι := ι) s hs hs2).le
  have hb (u : ℝ) (hu : 1 ≤ u) :
      min u (cap u) * (1 + (eLpNormEssSup (q u) (μ.prod μ)).toReal) ≤ M := by
    let η := periodicRieszLocalAdaptiveScale (ι := ι) s C γ N u
    let A := 4 * (γ * periodicRieszCapConst ι s * η ^ (-s))
    have hu0 : 0 < u := by linarith
    have hη := periodicRieszLocalAdaptiveScale_pos_le (ι := ι) s C γ N u hC hγ hN hu0
    have hη2 : 2 * η ≤ periodicRieszTau := by
      have := hη.2
      unfold periodicRieszTau
      linarith
    have hAe : (eLpNormEssSup (q u) (μ.prod μ)).toReal ≤ A :=
      essential_periodicRieszCenteredCutoff_le μ s η n hn hs hs2 hη.1 hη2 γ σ hγ.le hσ hv
    have hAp : A ≤ D * γ * (1 + (4 * C * γ * N / u) ^ α) := by
      have hi := gaussianRieszAdaptiveScale_inverse_power_le (1 / 4) (4 * C * γ) N u (Fintype.card ι) s
        η (by norm_num) (by positivity) hN hu0 hs hdim
      change (max η η) ^ (-s) ≤ _ at hi
      rw [max_self] at hi
      have he : (4 * C * γ) ^ α * (N / u) ^ α = (4 * C * γ * N / u) ^ α := by
        rw [← Real.mul_rpow (by positivity : 0 ≤ 4 * C * γ) (div_pos hN hu0).le]
        congr 1
        ring
      rw [show s / ((Fintype.card ι : ℝ) - s) = α from rfl, he] at hi
      have h4 : ((1 : ℝ) / 4) ^ (-s) = (4 : ℝ) ^ s := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 4), one_div, Real.inv_rpow (by norm_num), inv_inv]
      rw [h4] at hi
      have h41 : (1 : ℝ) ≤ (4 : ℝ) ^ s := Real.one_le_rpow (by norm_num) hs.le
      have ht : 0 ≤ (4 * C * γ * N / u) ^ α := Real.rpow_nonneg (by positivity) _
      have hη' : η ^ (-s) ≤ (4 : ℝ) ^ s * (1 + (4 * C * γ * N / u) ^ α) := by
        refine hi.trans ?_
        nlinarith
      have hk : 0 ≤ γ * periodicRieszCapConst ι s := mul_nonneg hγ.le hCc
      calc A = 4 * (γ * periodicRieszCapConst ι s) * η ^ (-s) := by dsimp [A]; ring
        _ ≤ 4 * (γ * periodicRieszCapConst ι s) * ((4 : ℝ) ^ s * (1 + (4 * C * γ * N / u) ^ α)) :=
          mul_le_mul_of_nonneg_left hη' (by positivity)
        _ = D * γ * (1 + (4 * C * γ * N / u) ^ α) := by dsimp [D, periodicRieszDConst]; ring
    have hAnn : 0 ≤ A := by
      have := Real.rpow_nonneg hη.1.le (-s)
      dsimp [A]; positivity
    have hcap : cap u = N / 2 * A := rfl
    apply sourceRieszLocal_scalar_slope C D γ N u α A (eLpNormEssSup (q u) (μ.prod μ)).toReal (cap u)
      hC hD hγ hγ1 hN hu hα0 hα1 hAnn ENNReal.toReal_nonneg (by rw [hcap]; positivity) hAp hAe
      (by rw [hcap])
  have hf : BddAbove (masterCutoffValues μ q cap 1) := ⟨M, by
    rintro z ⟨u, hu, rfl⟩
    exact hb u hu⟩
  refine ⟨hf, ?_⟩
  apply csSup_le
  · exact ⟨min 1 (cap 1) * (1 + (eLpNormEssSup (q 1) (μ.prod μ)).toReal), 1, le_rfl, rfl⟩
  · rintro z ⟨u, hu, rfl⟩
    exact hb u hu

/-! ### Measurability of the exponent -/

lemma measurable_periodicRieszLocalExponent (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (n : ℕ) (hn : 1 ≤ n) (γ σ : ℝ) {K : ℝ≥0}
    {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ) :
    Measurable (periodicRieszLocalExponent s hs2 ρ M n γ σ K v N) := by
  let μ := periodicCappedDensityMeasure ρ
  have hWm : StronglyMeasurable (periodicRieszPair (ι := ι) s) :=
    (measurable_periodicRieszPair s hs hs2).stronglyMeasurable
  have hT := measurable_physical_iidNegativeStatistic N _
    (stronglyMeasurable_hoeffdingCentered μ _
      (periodicRieszTransportKernel_measurable n hn s hs hs2 hv).stronglyMeasurable).measurable
  have hE := measurable_physical_iidNegativeStatistic N _
    (stronglyMeasurable_hoeffdingCentered μ _ hWm).measurable
  have hF : Measurable (DGRHS.potential μ (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b))) :=
    hWm.integral_prod_right'.measurable
  have hSum : Measurable (fun ω : Fin N → PeriodicTorus ι => ∑ i : Fin N,
      DGRHS.potential μ (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)) (ω i)) :=
    Finset.measurable_sum _ (fun i _ => hF.comp (measurable_pi_apply i))
  have hm : Measurable (fun ω : Fin N → PeriodicTorus ι =>
      (3 / 4 : ℝ) * γ * periodicRieszPotConst s hs2 M -
        2 * σ * periodicRieszCoefficient ι s n K γ * iidNegativeStatistic N
          (hoeffdingCentered μ (periodicRieszTransportKernel n s v)) ω +
      (γ * iidNegativeStatistic N (hoeffdingCentered μ (periodicRieszPair s)) ω +
        γ * ((N : ℝ)⁻¹ * ∑ i : Fin N, DGRHS.potential μ
          (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)) (ω i)) -
        γ * DGRHS.interactionEnergy μ (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)))) :=
    (measurable_const.sub (hT.const_mul _)).add
      (((hE.const_mul γ).add ((hSum.const_mul (N : ℝ)⁻¹).const_mul γ)).sub measurable_const)
  convert hm using 1
  funext ω
  unfold periodicRieszLocalExponent
  rw [periodic_sourceParticleExponent_eq]

/-! ### The master cutoff data -/

/-- Actual physical (M1)-(M3) data and finite size at the local threshold. -/
def periodicRieszLocalMasterData (s : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (γ σ : ℝ) (hγ : 0 < γ) (hσ : |σ| ≤ 1) {K : ℝ≥0}
    {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 1 ≤ N) (hγb : γ ≤ periodicRieszLocalBeta s hs2 M) :
    MasterCutoffData (periodicCappedDensityMeasure ρ) N
      (periodicRieszLocalExponent s hs2 ρ M n γ σ K v N) 1 := by
  let μ := periodicCappedDensityMeasure ρ
  let C := periodicRieszAbsConst ι s M
  let η := fun u => periodicRieszLocalAdaptiveScale (ι := ι) s C γ (N : ℝ) u
  let q := fun u => periodicRieszCenteredCutoff μ s (η u) n γ σ K v
  have hC : 0 < C := periodicRieszAbsConst_pos s M hs hs2 hM
  have hn' : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hN)
  have hη (u : ℝ) (hu : 1 ≤ u) : 0 < η u ∧ 2 * η u ≤ periodicRieszTau := by
    have h := periodicRieszLocalAdaptiveScale_pos_le (ι := ι) s C γ (N : ℝ) u hC hγ hn' (by linarith)
    refine ⟨h.1, ?_⟩
    have := h.2
    unfold periodicRieszTau
    linarith
  have hp := (periodicRieszLocalBeta_properties s hs hs2 M hM).2 γ hγ hγb
  have hγ1 := hp.1
  have hsmall := hp.2.1
  have hNorm := hp.2.2.1
  have hNC := periodicRieszNormControl_nonneg (ι := ι) s M hs hs2 hM
  have hcn := periodicRieszNormConstant_bounds (ι := ι) s M
  have hCcap := periodicRieszCapConst_pos (ι := ι) s hs hs2
  have hL := glzUniversalTailConstant_pos
  have hrowb : 16 * (γ ^ 2 * periodicRieszNormControl ι s M) ≤ 1 / glzUniversalTailConstant := by
    have hsq : γ ^ 2 ≤ γ := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right hsq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hNC)
    have h2 := mul_le_mul_of_nonneg_left hcn.2.1 hγ.le
    nlinarith
  have hopb : 4 * γ * Real.sqrt (periodicRieszNormControl ι s M) ≤ 1 / glzUniversalTailConstant := by
    have h2 := mul_le_mul_of_nonneg_left hcn.2.2 hγ.le
    nlinarith
  refine { kernel := q
           cap := periodicRieszLocalAdaptiveCap (ι := ι) s C γ (N : ℝ)
           measurable := fun u hu => (stronglyMeasurable_periodicRieszCenteredCutoff μ s (η u) n hn hs hs2
             (hη u hu).1 γ σ hv).measurable
           memLp := fun u hu => memLp_periodicRieszCenteredCutoff μ s (η u) n hn hs hs2 (hη u hu).1
             (hη u hu).2 γ σ hγ.le hσ hv ∞
           symmetric := fun u hu => periodicRieszCenteredCutoff_symmetric μ s (η u) n hn hs hs2 (hη u hu).1
             (hη u hu).2 γ σ K v
           canonical := fun u hu => periodicRieszCenteredCutoff_canonical μ s (η u) n hn hs hs2 (hη u hu).1
             (hη u hu).2 γ σ hγ.le hσ hv
           cap_pos := ?_
           compare := fun u hu => ae_periodicRieszLocal_event_reduction s n hn hs hs2 γ σ hγ hσ hv ρ M hM hρ
             N hN hsmall u hu
           capped := ?_
           row := ?_
           joint := ?_
           operator := ?_
           size_finite := (periodicRieszLocalAdaptiveSize ρ s C γ n hn hs hs2 hC hγ hγ1 σ hσ hv (N : ℝ) hn').1 }
  · intro u hu
    have he := (hη u hu).1
    have := Real.rpow_pos_of_pos he (-s)
    change 0 < (N : ℝ) / 2 * (4 * (γ * periodicRieszCapConst ι s * (η u) ^ (-s)))
    positivity
  · intro u hu
    let B := 4 * (γ * periodicRieszCapConst ι s * (η u) ^ (-s))
    have he := (hη u hu).1
    have hB : 0 ≤ B := by
      have := Real.rpow_nonneg he.le (-s)
      dsimp [B]; positivity
    have hb := ae_physical_iidNegativeStatistic_bound μ N hN (q u) (B / 2) (by positivity)
      (Filter.Eventually.of_forall (fun p => by
        have hp := periodicRieszCenteredCutoff_cap μ s (η u) n hn hs hs2 (hη u hu).1 (hη u hu).2 γ σ
          hγ.le hσ hv p
        change |q u p| ≤ B at hp
        have hneg := (neg_le_abs (q u p)).trans hp
        convert hneg using 1
        ring))
    filter_upwards [hb] with ω hω
    calc _ ≤ (N : ℝ) * (B / 2) := hω
      _ = _ := by unfold periodicRieszLocalAdaptiveCap; dsimp [B]; ring
  · intro u hu
    filter_upwards [(periodicRieszCenteredCutoff_square_controls s (η u) n hn hs hs2 (hη u hu).1
      (hη u hu).2 γ σ hγ.le hσ hv ρ M hM hρ).1] with x hx
    exact hx.trans hrowb
  · intro u hu
    exact (periodicRieszCenteredCutoff_square_controls s (η u) n hn hs hs2 (hη u hu).1
      (hη u hu).2 γ σ hγ.le hσ hv ρ M hM hρ).2.trans hrowb
  · intro u hu
    exact (norm_periodicRieszCenteredCutoff_operator s (η u) n hn hs hs2 (hη u hu).1 (hη u hu).2 γ σ
      hγ.le hσ hv ρ M hM hρ).trans hopb

lemma periodicRieszLocalMasterData_growth (s : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (γ σ : ℝ) (hγ : 0 < γ) (hσ : |σ| ≤ 1) {K : ℝ≥0}
    {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 1 ≤ N) (hγb : γ ≤ periodicRieszLocalBeta s hs2 M) :
    2 * glzUniversalTailConstant ^ 2 * masterCutoffSize (periodicCappedDensityMeasure ρ)
      (periodicRieszLocalMasterData s n hn hs hs2 γ σ hγ hσ hv ρ M hM hρ N hN hγb).kernel
      (periodicRieszLocalMasterData s n hn hs hs2 γ σ hγ hσ hv ρ M hM hρ N hN hγb).cap 1 ≤ (N : ℝ) := by
  obtain ⟨hγ1, _, _, hg⟩ := (periodicRieszLocalBeta_properties s hs hs2 M hM).2 γ hγ hγb
  have hn' : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hN)
  have hC := periodicRieszAbsConst_pos (ι := ι) s M hs hs2 hM
  have hb := (periodicRieszLocalAdaptiveSize ρ s (periodicRieszAbsConst ι s M) γ n hn hs hs2 hC hγ hγ1 σ hσ hv
    (N : ℝ) hn').2
  change masterCutoffSize _ _ _ 1 ≤ periodicRieszSizeConstant ι s M * γ * (N : ℝ) at hb
  change 2 * glzUniversalTailConstant ^ 2 * masterCutoffSize (periodicCappedDensityMeasure ρ)
    (fun u => periodicRieszCenteredCutoff (periodicCappedDensityMeasure ρ) s
      (periodicRieszLocalAdaptiveScale (ι := ι) s (periodicRieszAbsConst ι s M) γ (N : ℝ) u) n γ σ K v)
    (periodicRieszLocalAdaptiveCap (ι := ι) s (periodicRieszAbsConst ι s M) γ (N : ℝ)) 1 ≤ (N : ℝ)
  calc _ ≤ 2 * glzUniversalTailConstant ^ 2 * (periodicRieszSizeConstant ι s M * γ * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (2 * glzUniversalTailConstant ^ 2 * periodicRieszSizeConstant ι s M * γ) * (N : ℝ) := by ring
    _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hg hn'.le

/-- Uniform proper local exponential control of the torus local exponent. -/
theorem periodicRieszLocal_exponential_moment (s : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (γ σ : ℝ) (hγ : 0 < γ) (hσ : |σ| ≤ 1) {K : ℝ≥0}
    {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 1 ≤ N) (hγb : γ ≤ periodicRieszLocalBeta s hs2 M) :
    Integrable (fun ω => Real.exp (periodicRieszLocalExponent s hs2 ρ M n γ σ K v N ω))
      (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
    (∫ ω, Real.exp (periodicRieszLocalExponent s hs2 ρ M n γ σ K v N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤
        Real.exp 1 + glzUniversalTailConstant :=
  master_exponential_moment_large (periodicCappedDensityMeasure ρ) N hN _
    (measurable_periodicRieszLocalExponent s hs hs2 ρ M n hn γ σ hv N).aemeasurable 1 le_rfl
    (periodicRieszLocalMasterData s n hn hs hs2 γ σ hγ hσ hv ρ M hM hρ N hN hγb)
    (periodicRieszLocalMasterData_growth s n hn hs hs2 γ σ hγ hσ hv ρ M hM hρ N hN hγb)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicRieszLocalBeta_properties
#print axioms DGRHS.Periodic.periodicRieszLocalAdaptiveSize
#print axioms DGRHS.Periodic.measurable_periodicRieszLocalExponent
#print axioms DGRHS.Periodic.periodicRieszLocalMasterData_growth
#print axioms DGRHS.Periodic.periodicRieszLocal_exponential_moment
