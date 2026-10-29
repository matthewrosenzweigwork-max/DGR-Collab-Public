import LeanResearch.PeriodicAttractiveLogGas.CrossingComponentMeans
import LeanResearch.PeriodicAttractiveLogGas.TwoCellEntropy

/-! The original outside-law square-norm splitting in source lines 2946--2979.
The finite integral and scalar lemmas below are intermediate interfaces;
the source endpoints construct their conditional laws and moments explicitly.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas.EntropyEdgeSplitting

open MeshCells MeshAdjacentCells LabelOccupations CellRestrictions OneCoordinateConditionals
  ConditionalLawEstimates BoundaryCovarianceSplitting ConditionalSourceDerivatives
  ConditionalVarianceAssembly CrossingComponentMeans GreenPointWeights
  ConditionalKernelL2 CoordinateOscillation MovingPoleNumerators

/-- Reverse L2 triangle for two actual measurable representatives. -/
theorem reverse_norm_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (Real.sqrt (∫ x, f x ^ 2 ∂μ) - Real.sqrt (∫ x, g x ^ 2 ∂μ)) ^ 2 ≤
      ∫ x, (f x - g x) ^ 2 ∂μ := by
  let u := hf.toLp f
  let v := hg.toLp g
  have hu : ‖u‖ ^ 2 = ∫ x, f x ^ 2 ∂μ :=
    CenteredL2.norm_sq_eq_integral_sq_representative μ u hf.coeFn_toLp
  have hv : ‖v‖ ^ 2 = ∫ x, g x ^ 2 ∂μ :=
    CenteredL2.norm_sq_eq_integral_sq_representative μ v hg.coeFn_toLp
  have huv : ‖u - v‖ ^ 2 = ∫ x, (f x - g x) ^ 2 ∂μ := by
    apply CenteredL2.norm_sq_eq_integral_sq_representative
    filter_upwards [Lp.coeFn_sub u v, hf.coeFn_toLp, hg.coeFn_toLp] with x hs hfx hgx
    change (u - v) x = u x - v x at hs
    rw [hs, hfx, hgx]
  rw [← hu, ← hv, ← huv, Real.sqrt_sq (norm_nonneg u), Real.sqrt_sq (norm_nonneg v)]
  have h := abs_norm_sub_norm_le u v
  have hh := mul_self_le_mul_self (abs_nonneg _) h
  simpa only [← sq, sq_abs] using hh

/-- The exact factor one half comes from 2 p(1-p) at most one half. -/
theorem norm_splitting {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Ha Hb I II : Ω → ℝ} (hHa : MemLp Ha 2 μ) (hHb : MemLp Hb 2 μ)
    (hI : MemLp I 2 μ) (hII : MemLp II 2 μ)
    (hsplit : ∀ x, Ha x - Hb x = I x + II x) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p * (1 - p) * (Real.sqrt (∫ x, Ha x ^ 2 ∂μ) -
      Real.sqrt (∫ x, Hb x ^ 2 ∂μ)) ^ 2 ≤
      (1 / 2 : ℝ) * ((∫ x, I x ^ 2 ∂μ) + ∫ x, II x ^ 2 ∂μ) := by
  have hR := reverse_norm_sq hHa hHb
  have hsum : (∫ x, (Ha x - Hb x) ^ 2 ∂μ) ≤
      2 * ((∫ x, I x ^ 2 ∂μ) + ∫ x, II x ^ 2 ∂μ) := by
    have hi : Integrable (fun x => (Ha x - Hb x) ^ 2) μ := (hHa.sub hHb).integrable_sq
    have hj : Integrable (fun x => 2 * (I x ^ 2 + II x ^ 2)) μ :=
      (hI.integrable_sq.add hII.integrable_sq).const_mul 2
    have h := integral_mono_ae hi hj (Eventually.of_forall fun x => by
      dsimp only
      rw [hsplit x]
      nlinarith [sq_nonneg (I x - II x)])
    simpa only [integral_const_mul, integral_add hI.integrable_sq hII.integrable_sq] using h
  have hmass : 0 ≤ (∫ x, I x ^ 2 ∂μ) + ∫ x, II x ^ 2 ∂μ :=
    add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left (hR.trans hsum)
    (mul_nonneg hp (sub_nonneg.mpr hp1))
  have hbern := CrossingLogistic.bernoulli_factor_le p
  nlinarith [mul_le_mul_of_nonneg_right hbern hmass]

/-- Algebraic square-root divided differences give the source derivative
bound without introducing a differentiability assumption at endpoints. -/
theorem sqrt_ratio_abs_sub_le {d p r t : ℝ} (hd : 0 < d)
    (hp : d ≤ p) (hr : d ≤ r) (ht : d ≤ t) :
    |Real.sqrt (r / p) - Real.sqrt (t / p)| ≤ |r - t| / (2 * d) := by
  have hp0 : 0 < p := hd.trans_le hp
  have hr0 : 0 ≤ r := hd.le.trans hr
  have ht0 : 0 ≤ t := hd.le.trans ht
  let u := Real.sqrt (r / p)
  let v := Real.sqrt (t / p)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hv : 0 ≤ v := Real.sqrt_nonneg _
  have hu2 : p * u ^ 2 = r := by
    rw [show u ^ 2 = r / p from Real.sq_sqrt (div_nonneg hr0 hp0.le)]
    field_simp
  have hv2 : p * v ^ 2 = t := by
    rw [show v ^ 2 = t / p from Real.sq_sqrt (div_nonneg ht0 hp0.le)]
    field_simp
  have hpu : d ≤ p * u := by
    have hh : d ^ 2 ≤ p * r := by simpa only [sq] using mul_le_mul hp hr hd.le hp0.le
    have hsq : (p * u) ^ 2 = p * r := by nlinarith [congrArg (fun z : ℝ => p * z) hu2]
    nlinarith [mul_nonneg hp0.le hu]
  have hpv : d ≤ p * v := by
    have hh : d ^ 2 ≤ p * t := by simpa only [sq] using mul_le_mul hp ht hd.le hp0.le
    have hsq : (p * v) ^ 2 = p * t := by nlinarith [congrArg (fun z : ℝ => p * z) hv2]
    nlinarith [mul_nonneg hp0.le hv]
  have he : (u - v) * (p * (u + v)) = r - t := by nlinarith [hu2, hv2]
  have heabs := congrArg abs he
  rw [abs_mul, abs_of_nonneg (mul_nonneg hp0.le (add_nonneg hu hv))] at heabs
  apply (le_div_iff₀ (by positivity : 0 < 2 * d)).mpr
  change |u - v| * (2 * d) ≤ |r - t|
  have hl : 2 * d ≤ p * (u + v) := by nlinarith [hpu, hpv]
  exact (mul_le_mul_of_nonneg_left hl (abs_nonneg _)).trans_eq heabs

def crossingRootDifference (p r : ℝ) : ℝ :=
  Real.sqrt (r / p) - Real.sqrt ((1 - r) / (1 - p))

theorem crossingRootDifference_self {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    crossingRootDifference p p = 0 := by
  simp [crossingRootDifference, hp.ne', (sub_pos.mpr hp1).ne']

theorem crossingRootDifference_abs_sub_le {d p r t : ℝ} (hd : 0 < d)
    (hp : d ≤ p) (hp1 : d ≤ 1 - p) (hr : r ∈ Icc d (1 - d))
    (ht : t ∈ Icc d (1 - d)) :
    |crossingRootDifference p r - crossingRootDifference p t| ≤ (1 / d) * |r - t| := by
  have ha := sqrt_ratio_abs_sub_le hd hp hr.1 ht.1
  have hb := sqrt_ratio_abs_sub_le hd hp1
    (show d ≤ 1 - r by linarith [hr.2]) (show d ≤ 1 - t by linarith [ht.2])
  have he : |(1 - r) - (1 - t)| = |r - t| := by
    rw [show (1 - r) - (1 - t) = -(r - t) by ring, abs_neg]
  rw [he] at hb
  calc
    _ = |(Real.sqrt (r / p) - Real.sqrt (t / p)) -
        (Real.sqrt ((1 - r) / (1 - p)) - Real.sqrt ((1 - t) / (1 - p)))| := by
      congr 1
      unfold crossingRootDifference
      ring
    _ ≤ |Real.sqrt (r / p) - Real.sqrt (t / p)| +
        |Real.sqrt ((1 - r) / (1 - p)) - Real.sqrt ((1 - t) / (1 - p))| := abs_sub _ _
    _ ≤ |r - t| / (2 * d) + |r - t| / (2 * d) := add_le_add ha hb
    _ = _ := by ring

theorem crossingRootDifference_lipschitz {d p : ℝ} (hd : 0 < d)
    (hp : d ≤ p) (hp1 : d ≤ 1 - p) :
    LipschitzOnWith ⟨1 / d, by positivity⟩ (crossingRootDifference p) (Icc d (1 - d)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro r hr t ht
  change |crossingRootDifference p r - crossingRootDifference p t| ≤ (1 / d) * |r - t|
  exact crossingRootDifference_abs_sub_le hd hp hp1 hr ht

/-- Exact normalization of a common weight on an equal two-measure mixture. -/
theorem normalized_half_mixture {Ω : Type*} [MeasurableSpace Ω]
    (μa μb : Measure Ω) (w : Ω → ℝ) {Za Zb : ℝ} (ha : 0 < Za) (hb : 0 < Zb) :
    ((2 : ℝ≥0∞)⁻¹ • (μa + μb)).withDensity
        (fun x => ENNReal.ofReal (w x / ((Za + Zb) / 2))) =
      ENNReal.ofReal (Za / (Za + Zb)) • μa.withDensity (fun x => ENNReal.ofReal (w x / Za)) +
      ENNReal.ofReal (Zb / (Za + Zb)) • μb.withDensity (fun x => ENNReal.ofReal (w x / Zb)) := by
  have hsum : 0 < Za + Zb := add_pos ha hb
  have hd (Z : ℝ) (hZ : 0 < Z) :
      (2 : ℝ≥0∞)⁻¹ • (fun x => ENNReal.ofReal (w x / ((Za + Zb) / 2))) =
        ENNReal.ofReal (Z / (Za + Zb)) • (fun x => ENNReal.ofReal (w x / Z)) := by
    funext x
    change (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (w x / ((Za + Zb) / 2)) =
      ENNReal.ofReal (Z / (Za + Zb)) * ENNReal.ofReal (w x / Z)
    rw [show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2 : ℝ) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (div_nonneg hZ.le hsum.le)]
    congr 1
    field_simp
  rw [withDensity_smul_measure, withDensity_add_measure, smul_add]
  congr 1
  · rw [← withDensity_smul' _ _ (by simp), hd Za ha, withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  · rw [← withDensity_smul' _ _ (by simp), hd Zb hb, withDensity_smul' _ _ ENNReal.ofReal_ne_top]

variable {n J : ℕ}

/-- The actual conditional edge kernel is the positive mixture of its
original cell kernels, at every prescribed outside placement. -/
theorem conditional_edge_mixture {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r)
    (Y : Configuration n) (hY : PrescribedOutside (mesh_pos hmesh) η i Y) :
    let hJ := mesh_pos hmesh
    let b := nextCell J hJ a r
    let q := outsideCrossingProbability hJ β i a r Y
    conditionalKernel (edgeCellMeasure J hJ a r) i β Y =
      ENNReal.ofReal q • conditionalKernel (meshCellMeasure J hJ a) i β Y +
      ENNReal.ofReal (1 - q) • conditionalKernel (meshCellMeasure J hJ b) i β Y := by
  let hJ := mesh_pos hmesh
  let b := nextCell J hJ a r
  have hYa := (LabelRatioTransport.prescribedOutside_update_iff hJ η i a Y).mpr hY
  have ha := capped_patch_law hJ hβ hβ₀ hδ hmesh (Function.update η i a) hadm.1 i Y hYa a .cell
  have hb := capped_patch_law hJ hβ hβ₀ hδ hmesh (Function.update η i a) hadm.1 i Y hYa b .cell
  have he := capped_patch_law hJ hβ hβ₀ hδ hmesh (Function.update η i a) hadm.1 i Y hYa a (.edge r)
  let Za := LabelRatioTransport.cellNormalizer hJ a β Y
  let Zb := LabelRatioTransport.cellNormalizer hJ b β Y
  have hZa : 0 < Za := ha.regular_normalizer_pos
  have hZb : 0 < Zb := hb.regular_normalizer_pos
  have hZe : (∫ z, sourceWeight β Y z ∂edgeCellMeasure J hJ a r) = (Za + Zb) / 2 :=
    LabelRatioTransport.edge_normalizer_eq_average hJ a r β Y ha.regular_integrable hb.regular_integrable
  have hq : outsideCrossingProbability hJ β i a r Y = Za / (Za + Zb) :=
    LabelRatioTransport.conditional_crossing_eq hJ (mesh_two_le hmesh) β β₀ i Y a r ha hb he
  have hqc : 1 - outsideCrossingProbability hJ β i a r Y = Zb / (Za + Zb) := by
    rw [hq]
    field_simp
    ring
  dsimp only
  rw [hqc, hq]
  change conditionalKernel (patchMeasure J hJ a (.edge r)) i β Y =
    ENNReal.ofReal (Za / (Za + Zb)) • conditionalKernel (patchMeasure J hJ a .cell) i β Y +
    ENNReal.ofReal (Zb / (Za + Zb)) • conditionalKernel (patchMeasure J hJ b .cell) i β Y
  rw [he.kernel_eq_pointLaw, ha.kernel_eq_pointLaw, hb.kernel_eq_pointLaw]
  change (edgeCellMeasure J hJ a r).withDensity (fun z => ENNReal.ofReal
      (sourceWeight β Y z / ∫ u, sourceWeight β Y u ∂edgeCellMeasure J hJ a r)) =
    ENNReal.ofReal (Za / (Za + Zb)) • (meshCellMeasure J hJ a).withDensity
      (fun z => ENNReal.ofReal (sourceWeight β Y z / Za)) +
    ENNReal.ofReal (Zb / (Za + Zb)) • (meshCellMeasure J hJ b).withDensity
      (fun z => ENNReal.ofReal (sourceWeight β Y z / Zb))
  rw [hZe]
  exact normalized_half_mixture _ _ _ hZa hZb

/-- Integration against the original outside-indexed Markov kernel. -/
def outsideAverage (κ : Kernel (Configuration n) Torus) (i : Fin (n + 1))
    (F : Configuration (n + 1) → ℝ) (Y : Configuration n) : ℝ :=
  ∫ z, F (insertSite i z Y) ∂κ Y

theorem measurable_outsideAverage (κ : Kernel (Configuration n) Torus) [IsSFiniteKernel κ]
    (i : Fin (n + 1)) {F : Configuration (n + 1) → ℝ} (hF : Measurable F) :
    Measurable (outsideAverage κ i F) := by
  have hm : Measurable (fun t : Configuration n × Torus => F (insertSite i t.2 t.1)) :=
    hF.comp ((measurable_insertSite i).comp measurable_swap)
  exact hm.stronglyMeasurable.integral_kernel_prod_right'.measurable

theorem outsideAverage_bound (κ : Kernel (Configuration n) Torus) [IsMarkovKernel κ]
    (i : Fin (n + 1)) {F : Configuration (n + 1) → ℝ} {B : ℝ}
    (hF : ∀ X, |F X| ≤ B) (Y : Configuration n) : |outsideAverage κ i F Y| ≤ B := by
  have hb : ∀ᵐ z ∂κ Y, ‖F (insertSite i z Y)‖ ≤ B := Eventually.of_forall fun z => by
    simpa only [Real.norm_eq_abs] using hF (insertSite i z Y)
  simpa only [outsideAverage, Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := κ Y) hb)

def cellSquareMoment (hJ : 0 < J) (i : Fin (n + 1)) (β : ℝ) (a : MeshIndex J)
    (G : Configuration (n + 1) → ℝ) : Configuration n → ℝ :=
  outsideAverage (conditionalKernel (meshCellMeasure J hJ a) i β) i (fun X => G X ^ 2)

def edgeSquareMoment (hJ : 0 < J) (i : Fin (n + 1)) (β : ℝ) (a : MeshIndex J) (r : Fin 2)
    (G : Configuration (n + 1) → ℝ) : Configuration n → ℝ :=
  outsideAverage (conditionalKernel (edgeCellMeasure J hJ a r) i β) i (fun X => G X ^ 2)

theorem cellSquareMoment_nonneg (hJ : 0 < J) (i : Fin (n + 1)) (β : ℝ) (a : MeshIndex J)
    (G : Configuration (n + 1) → ℝ) (Y : Configuration n) : 0 ≤ cellSquareMoment hJ i β a G Y :=
  integral_nonneg fun _ => sq_nonneg _

theorem measurable_cellSquareMoment (hJ : 0 < J) (i : Fin (n + 1)) (β : ℝ) (a : MeshIndex J)
    {G : Configuration (n + 1) → ℝ} (hG : Measurable G) :
    Measurable (cellSquareMoment hJ i β a G) := measurable_outsideAverage _ i (hG.pow_const 2)

/-- A bounded globally measurable observable has genuine second moments
in every cell kernel, including the Markov version at exceptional inputs. -/
theorem cellSquareMoment_bound (hJ : 0 < J) (i : Fin (n + 1)) (β : ℝ) (a : MeshIndex J)
    {G : Configuration (n + 1) → ℝ} {B : ℝ} (hG : ∀ X, |G X| ≤ B)
    (Y : Configuration n) : cellSquareMoment hJ i β a G Y ≤ B ^ 2 := by
  have hb : ∀ X, |G X ^ 2| ≤ B ^ 2 := fun X => by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [← sq, sq_abs] using mul_self_le_mul_self (abs_nonneg _) (hG X)
  exact (le_abs_self _).trans (outsideAverage_bound _ i hb Y)

/-- Real disintegration derived from the already proved nonnegative
disintegration, with integrability established before conversion. -/
theorem integral_outsideAverage_of_disintegration
    (P : Measure (Configuration (n + 1))) [IsProbabilityMeasure P]
    (κ : Kernel (Configuration n) Torus) [IsMarkovKernel κ] (i : Fin (n + 1))
    (hdis : ∀ (F : Configuration (n + 1) → ℝ≥0∞), Measurable F →
      (∫⁻ X, F X ∂P) = ∫⁻ Y, ∫⁻ z, F (insertSite i z Y) ∂κ Y ∂P.map (removeSite i))
    {F : Configuration (n + 1) → ℝ} (hF : Measurable F) (hF0 : ∀ X, 0 ≤ F X)
    {B : ℝ} (hFb : ∀ X, |F X| ≤ B) :
    (∫ Y, outsideAverage κ i F Y ∂P.map (removeSite i)) = ∫ X, F X ∂P := by
  let ρ := P.map (removeSite i)
  let : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff (measurable_removeSite i).aemeasurable).mpr inferInstance
  have hi : Integrable F P := integrable_bounded P hF hFb
  have hav : Integrable (outsideAverage κ i F) ρ :=
    integrable_bounded ρ (measurable_outsideAverage κ i hF) (outsideAverage_bound κ i hFb)
  have hs (Y : Configuration n) : Integrable (fun z => F (insertSite i z Y)) (κ Y) :=
    integrable_bounded _
      (hF.comp ((measurable_insertSite i).comp (measurable_id.prodMk measurable_const)))
      (fun z => hFb _)
  have he := hdis (fun X => ENNReal.ofReal (F X)) hF.ennreal_ofReal
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hF0)] at he
  have he' : ENNReal.ofReal (∫ X, F X ∂P) =
      ∫⁻ Y, ENNReal.ofReal (outsideAverage κ i F Y) ∂ρ := by
    rw [he]
    apply lintegral_congr_ae
    exact Eventually.of_forall fun Y =>
      (ofReal_integral_eq_lintegral_ofReal (hs Y) (Eventually.of_forall fun z => hF0 _)).symm
  rw [← ofReal_integral_eq_lintegral_ofReal hav
    (Eventually.of_forall fun Y => integral_nonneg fun z => hF0 _)] at he'
  have hn : 0 ≤ ∫ Y, outsideAverage κ i F Y ∂ρ :=
    integral_nonneg fun Y => integral_nonneg fun z => hF0 _
  have hr := congrArg ENNReal.toReal he'
  rw [ENNReal.toReal_ofReal (integral_nonneg hF0), ENNReal.toReal_ofReal hn] at hr
  exact hr.symm

theorem cellSquareMoment_integral (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ n + 1)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) {G : Configuration (n + 1) → ℝ}
    (hG : Measurable G) {B : ℝ} (hGb : ∀ X, |G X| ≤ B) :
    (∫ Y, cellSquareMoment hJ i β a G Y
      ∂(labelGibbsMeasure hJ (Function.update η i a) β).map (removeSite i)) =
      ∫ X, G X ^ 2 ∂labelGibbsMeasure hJ (Function.update η i a) β := by
  let := isProbabilityMeasure_labelGibbsMeasure hJ hN (Function.update η i a) hβ hsub
  apply integral_outsideAverage_of_disintegration _ _ i
    (fun F hF => by simpa only [Function.update_self] using
      lintegral_label_conditionals hJ hJ2 hN (Function.update η i a) i hβ hsub hF)
    (hG.pow_const 2) (fun _ => sq_nonneg _) (B := B ^ 2)
  intro X
  rw [abs_of_nonneg (sq_nonneg _)]
  simpa only [← sq, sq_abs] using mul_self_le_mul_self (abs_nonneg _) (hGb X)

def weightedRoot (p q m : ℝ) : ℝ := Real.sqrt (q / p) * Real.sqrt m

def firstPart (p q ma mb : ℝ) : ℝ := Real.sqrt (q / p) * (Real.sqrt ma - Real.sqrt mb)

def secondPart (p q mb : ℝ) : ℝ := Real.sqrt mb * crossingRootDifference p q

theorem parts_identity (p q ma mb : ℝ) :
    weightedRoot p q ma - weightedRoot (1 - p) (1 - q) mb =
      firstPart p q ma mb + secondPart p q mb := by
  unfold weightedRoot firstPart secondPart crossingRootDifference
  ring

theorem weightedRoot_sq {p q m : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hm : 0 ≤ m) :
    weightedRoot p q m ^ 2 = q / p * m := by
  rw [weightedRoot, mul_pow, Real.sq_sqrt (div_nonneg hq hp), Real.sq_sqrt hm]

theorem measurable_weightedRoot {Ω : Type*} [MeasurableSpace Ω]
    (p : ℝ) {q m : Ω → ℝ} (hq : Measurable q) (hm : Measurable m) :
    Measurable (fun x => weightedRoot p (q x) (m x)) :=
  (Real.continuous_sqrt.measurable.comp (hq.div_const p)).mul
    (Real.continuous_sqrt.measurable.comp hm)

theorem weightedRoot_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {p B : ℝ} (hp : 0 < p)
    {q m : Ω → ℝ} (hq : Measurable q) (hm : Measurable m)
    (hqb : ∀ x, 0 ≤ q x ∧ q x ≤ 1) (hmb : ∀ x, 0 ≤ m x ∧ m x ≤ B) :
    MemLp (fun x => weightedRoot p (q x) (m x)) 2 μ := by
  have hmeas := measurable_weightedRoot p hq hm
  apply (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr
  apply integrable_bounded μ (hmeas.pow_const 2) (B := B / p)
  intro x
  rw [abs_of_nonneg (sq_nonneg _), weightedRoot_sq hp.le (hqb x).1 (hmb x).1]
  calc
    q x / p * m x ≤ 1 / p * B :=
      mul_le_mul (div_le_div_of_nonneg_right (hqb x).2 hp.le) (hmb x).2 (hmb x).1 (by positivity)
    _ = _ := by ring

theorem parts_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {p B : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {q ma mb : Ω → ℝ} (hq : Measurable q) (hma : Measurable ma) (hmb : Measurable mb)
    (hqb : ∀ x, 0 ≤ q x ∧ q x ≤ 1)
    (hmab : ∀ x, 0 ≤ ma x ∧ ma x ≤ B) (hmbb : ∀ x, 0 ≤ mb x ∧ mb x ≤ B) :
    MemLp (fun x => weightedRoot p (q x) (ma x)) 2 μ ∧
      MemLp (fun x => weightedRoot (1 - p) (1 - q x) (mb x)) 2 μ ∧
      MemLp (fun x => firstPart p (q x) (ma x) (mb x)) 2 μ ∧
      MemLp (fun x => secondPart p (q x) (mb x)) 2 μ := by
  have ha := weightedRoot_memLp μ hp hq hma hqb hmab
  have hc := weightedRoot_memLp μ hp hq hmb hqb hmbb
  have hb := weightedRoot_memLp μ (sub_pos.mpr hp1) (measurable_const.sub hq) hmb
    (fun x => show 0 ≤ 1 - q x ∧ 1 - q x ≤ 1 from
      ⟨sub_nonneg.mpr (hqb x).2, by linarith [(hqb x).1]⟩) hmbb
  refine ⟨ha, hb, ?_, ?_⟩
  · convert ha.sub hc using 1
    funext x
    change firstPart p (q x) (ma x) (mb x) = weightedRoot p (q x) (ma x) - weightedRoot p (q x) (mb x)
    unfold firstPart weightedRoot
    ring
  · convert hc.sub hb using 1
    funext x
    change secondPart p (q x) (mb x) = weightedRoot p (q x) (mb x) - weightedRoot (1 - p) (1 - q x) (mb x)
    unfold secondPart crossingRootDifference weightedRoot
    ring

theorem measurable_firstPart {Ω : Type*} [MeasurableSpace Ω]
    (p : ℝ) {q ma mb : Ω → ℝ} (hq : Measurable q) (hma : Measurable ma) (hmb : Measurable mb) :
    Measurable (fun x => firstPart p (q x) (ma x) (mb x)) :=
  (Real.continuous_sqrt.measurable.comp (hq.div_const p)).mul
    ((Real.continuous_sqrt.measurable.comp hma).sub (Real.continuous_sqrt.measurable.comp hmb))

theorem measurable_secondPart {Ω : Type*} [MeasurableSpace Ω]
    (p : ℝ) {q mb : Ω → ℝ} (hq : Measurable q) (hmb : Measurable mb) :
    Measurable (fun x => secondPart p (q x) (mb x)) :=
  (Real.continuous_sqrt.measurable.comp hmb).mul
    ((Real.continuous_sqrt.measurable.comp (hq.div_const p)).sub
      (Real.continuous_sqrt.measurable.comp ((measurable_const.sub hq).div_const (1 - p))))

theorem outside_crossing_bounds (hJ : 0 < J) (i : Fin (n + 1))
    (a : MeshIndex J) (r : Fin 2) (β : ℝ) (Y : Configuration n) :
    0 ≤ outsideCrossingProbability hJ β i a r Y ∧ outsideCrossingProbability hJ β i a r Y ≤ 1 :=
  ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩

/-- Exact squared norms under the original outside law, proved from the
actual tilted component marginals, with no independent disintegration premise. -/
theorem source_squared_norms {β β₀ δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r)
    {G : Configuration (n + 1) → ℝ} (hG : Measurable G) {B : ℝ} (hGb : ∀ X, |G X| ≤ B) :
    let hJ := mesh_pos hmesh
    let b := nextCell J hJ a r
    let P := twoCellGibbsMeasure hJ η i a b β
    let p := (twoCellMixingWeight hJ η i a b β).toReal
    let q := outsideCrossingProbability hJ β i a r
    (∫ Y, weightedRoot p (q Y) (cellSquareMoment hJ i β a G Y) ^ 2 ∂P.map (removeSite i)) =
        ∫ X, G X ^ 2 ∂labelGibbsMeasure hJ (Function.update η i a) β ∧
    (∫ Y, weightedRoot (1 - p) (1 - q Y) (cellSquareMoment hJ i β b G Y) ^ 2 ∂P.map (removeSite i)) =
        ∫ X, G X ^ 2 ∂labelGibbsMeasure hJ (Function.update η i b) β := by
  let hJ := mesh_pos hmesh
  let b := nextCell J hJ a r
  let P := twoCellGibbsMeasure hJ η i a b β
  let ρ := P.map (removeSite i)
  let p := (twoCellMixingWeight hJ η i a b β).toReal
  let q := outsideCrossingProbability hJ β i a r
  have hp := LabelRatioTransport.adjacent_mixing_range hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm
  change lowerBound β₀ / 2 ≤ p ∧ p ≤ 1 - lowerBound β₀ / 2 at hp
  have hc := lowerBound_pos β₀
  have hp0 : 0 < p := by linarith [hp.1]
  have hp1 : 0 < 1 - p := by linarith [hp.2]
  have hqm : Measurable q := measurable_outside_crossing hJ η i a r β
  have hq := outside_crossing_bounds hJ i a r β
  have hcomp := component_outside_marginals hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm
  have hleft : (∫ Y, cellSquareMoment hJ i β a G Y
      ∂(labelGibbsMeasure hJ (Function.update η i a) β).map (removeSite i)) =
      ∫ Y, q Y / p * cellSquareMoment hJ i β a G Y ∂ρ := by
    rw [hcomp.1, integral_withDensity_eq_integral_toReal_smul (hqm.div_const p).ennreal_ofReal
      (Eventually.of_forall fun Y => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    exact Eventually.of_forall fun Y => by
      change (ENNReal.ofReal (q Y / p)).toReal * cellSquareMoment hJ i β a G Y = _
      rw [ENNReal.toReal_ofReal (show 0 ≤ q Y / p from div_nonneg (hq Y).1 hp0.le)]
  have hright : (∫ Y, cellSquareMoment hJ i β b G Y
      ∂(labelGibbsMeasure hJ (Function.update η i b) β).map (removeSite i)) =
      ∫ Y, (1 - q Y) / (1 - p) * cellSquareMoment hJ i β b G Y ∂ρ := by
    rw [hcomp.2]
    change (∫ Y, cellSquareMoment hJ i β b G Y
      ∂ρ.withDensity (fun Y => ENNReal.ofReal ((1 - q Y) / (1 - p)))) = _
    have hweight : Measurable (fun Y => ENNReal.ofReal ((1 - q Y) / (1 - p))) :=
      ((measurable_const.sub hqm).div_const (1 - p)).ennreal_ofReal
    rw [integral_withDensity_eq_integral_toReal_smul hweight
      (Eventually.of_forall fun Y => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    exact Eventually.of_forall fun Y => by
      change (ENNReal.ofReal ((1 - q Y) / (1 - p))).toReal * cellSquareMoment hJ i β b G Y = _
      rw [ENNReal.toReal_ofReal (show 0 ≤ (1 - q Y) / (1 - p) from
        div_nonneg (sub_nonneg.mpr (hq Y).2) hp1.le)]
  constructor
  · calc
      _ = ∫ Y, q Y / p * cellSquareMoment hJ i β a G Y ∂ρ := integral_congr_ae
        (Eventually.of_forall fun Y => weightedRoot_sq hp0.le (hq Y).1 (cellSquareMoment_nonneg _ _ _ _ _ _))
      _ = _ := hleft.symm.trans (cellSquareMoment_integral hJ (mesh_two_le hmesh) hN η i a
        hβ (hβ₀.trans_lt hsub) hG hGb)
  · calc
      _ = ∫ Y, (1 - q Y) / (1 - p) * cellSquareMoment hJ i β b G Y ∂ρ := integral_congr_ae
        (Eventually.of_forall fun Y => weightedRoot_sq hp1.le (sub_nonneg.mpr (hq Y).2)
          (cellSquareMoment_nonneg _ _ _ _ _ _))
      _ = _ := hright.symm.trans (cellSquareMoment_integral hJ (mesh_two_le hmesh) hN η i b
        hβ (hβ₀.trans_lt hsub) hG hGb)

def sourceLeftRoot (hJ : 0 < J) (η : LabelVector J (n + 1)) (i : Fin (n + 1))
    (a : MeshIndex J) (r : Fin 2) (β : ℝ) (G : Configuration (n + 1) → ℝ) (Y : Configuration n) : ℝ :=
  weightedRoot (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal
    (outsideCrossingProbability hJ β i a r Y) (cellSquareMoment hJ i β a G Y)

def sourceRightRoot (hJ : 0 < J) (η : LabelVector J (n + 1)) (i : Fin (n + 1))
    (a : MeshIndex J) (r : Fin 2) (β : ℝ) (G : Configuration (n + 1) → ℝ) (Y : Configuration n) : ℝ :=
  weightedRoot (1 - (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal)
    (1 - outsideCrossingProbability hJ β i a r Y) (cellSquareMoment hJ i β (nextCell J hJ a r) G Y)

def sourceFirstPart (hJ : 0 < J) (η : LabelVector J (n + 1)) (i : Fin (n + 1))
    (a : MeshIndex J) (r : Fin 2) (β : ℝ) (G : Configuration (n + 1) → ℝ) (Y : Configuration n) : ℝ :=
  firstPart (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal
    (outsideCrossingProbability hJ β i a r Y)
    (cellSquareMoment hJ i β a G Y) (cellSquareMoment hJ i β (nextCell J hJ a r) G Y)

def sourceSecondPart (hJ : 0 < J) (η : LabelVector J (n + 1)) (i : Fin (n + 1))
    (a : MeshIndex J) (r : Fin 2) (β : ℝ) (G : Configuration (n + 1) → ℝ) (Y : Configuration n) : ℝ :=
  secondPart (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal
    (outsideCrossingProbability hJ β i a r Y) (cellSquareMoment hJ i β (nextCell J hJ a r) G Y)

theorem source_parts_identity (hJ : 0 < J) (η : LabelVector J (n + 1)) (i : Fin (n + 1))
    (a : MeshIndex J) (r : Fin 2) (β : ℝ) (G : Configuration (n + 1) → ℝ) (Y : Configuration n) :
    sourceLeftRoot hJ η i a r β G Y - sourceRightRoot hJ η i a r β G Y =
      sourceFirstPart hJ η i a r β G Y + sourceSecondPart hJ η i a r β G Y := parts_identity _ _ _ _

section Source

variable {β β₀ δ : ℝ}
  (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
  (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
  (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
  (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r)

include hN hβ hβ₀ hsub hδ₀ hδ hadm

/-- Every norm and both squared split terms are genuine finite integrals
under the actual outside marginal. No positive observable-mass condition is used. -/
theorem source_parts_memLp {G : Configuration (n + 1) → ℝ}
    (hG : Measurable G) {B : ℝ} (hGb : ∀ X, |G X| ≤ B) :
    let hJ := mesh_pos hmesh
    let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
    let ρ := P.map (removeSite i)
    MemLp (sourceLeftRoot hJ η i a r β G) 2 ρ ∧
      MemLp (sourceRightRoot hJ η i a r β G) 2 ρ ∧
      MemLp (sourceFirstPart hJ η i a r β G) 2 ρ ∧
      MemLp (sourceSecondPart hJ η i a r β G) 2 ρ := by
  let hJ := mesh_pos hmesh
  let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
  let : IsProbabilityMeasure P := isProbabilityMeasure_twoCellGibbsMeasure hJ hN η i
    (Ne.symm (nextCell_ne J hJ (mesh_two_le hmesh) a r)) hβ (hβ₀.trans_lt hsub)
  let : IsProbabilityMeasure (P.map (removeSite i)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_removeSite i).aemeasurable).mpr inferInstance
  have hp := LabelRatioTransport.adjacent_mixing_range hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm
  have hc := lowerBound_pos β₀
  apply parts_memLp (P.map (removeSite i)) (by linarith [hp.1]) (by linarith [hp.2])
    (measurable_outside_crossing hJ η i a r β)
    (measurable_cellSquareMoment hJ i β a hG)
    (measurable_cellSquareMoment hJ i β (nextCell J hJ a r) hG)
    (outside_crossing_bounds hJ i a r β) (B := B ^ 2)
  · exact fun Y => ⟨cellSquareMoment_nonneg _ _ _ _ _ _, cellSquareMoment_bound _ _ _ _ hGb Y⟩
  · exact fun Y => ⟨cellSquareMoment_nonneg _ _ _ _ _ _, cellSquareMoment_bound _ _ _ _ hGb Y⟩

/-- The literal source I/II inequality, with all square roots evaluated
at the actual component moments and all expectations under the original outside law. -/
theorem source_splitting {G : Configuration (n + 1) → ℝ}
    (hG : Measurable G) {B : ℝ} (hGb : ∀ X, |G X| ≤ B) :
    let hJ := mesh_pos hmesh
    let b := nextCell J hJ a r
    let P := twoCellGibbsMeasure hJ η i a b β
    let p := (twoCellMixingWeight hJ η i a b β).toReal
    p * (1 - p) * (Real.sqrt (∫ X, G X ^ 2 ∂labelGibbsMeasure hJ (Function.update η i a) β) -
      Real.sqrt (∫ X, G X ^ 2 ∂labelGibbsMeasure hJ (Function.update η i b) β)) ^ 2 ≤
      (1 / 2 : ℝ) * ((∫ Y, sourceFirstPart hJ η i a r β G Y ^ 2 ∂P.map (removeSite i)) +
        ∫ Y, sourceSecondPart hJ η i a r β G Y ^ 2 ∂P.map (removeSite i)) := by
  have hm := source_parts_memLp hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm hG hGb
  have hp := LabelRatioTransport.adjacent_mixing_range hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm
  have hc := lowerBound_pos β₀
  have hh := norm_splitting hm.1 hm.2.1 hm.2.2.1 hm.2.2.2
    (source_parts_identity (mesh_pos hmesh) η i a r β G)
    (show 0 ≤ (twoCellMixingWeight (mesh_pos hmesh) η i a
      (nextCell J (mesh_pos hmesh) a r) β).toReal by positivity)
    (show (twoCellMixingWeight (mesh_pos hmesh) η i a
      (nextCell J (mesh_pos hmesh) a r) β).toReal ≤ 1 by linarith [hp.2])
  have he := source_squared_norms hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm hG hGb
  change (∫ Y, sourceLeftRoot (mesh_pos hmesh) η i a r β G Y ^ 2 ∂_) = _ ∧
    (∫ Y, sourceRightRoot (mesh_pos hmesh) η i a r β G Y ^ 2 ∂_) = _ at he
  rw [he.1, he.2] at hh
  exact hh

end Source

/-- The first part uses the true conditional variance estimate from the
reverse-norm one-site crossing theorem. This scalar helper only clears its positive denominators. -/
theorem firstPart_sq_le {p q ma mb V d : ℝ} (hd : 0 < d) (hp : d ≤ p)
    (hq0 : 0 ≤ q) (hq1 : d ≤ 1 - q)
    (hc : q * (1 - q) * (Real.sqrt ma - Real.sqrt mb) ^ 2 ≤ 2 * V) :
    firstPart p q ma mb ^ 2 ≤ (2 / d ^ 2) * V := by
  have hp0 : 0 < p := hd.trans_le hp
  have hi : p * (1 - q) * firstPart p q ma mb ^ 2 =
      q * (1 - q) * (Real.sqrt ma - Real.sqrt mb) ^ 2 := by
    rw [firstPart, mul_pow, Real.sq_sqrt (div_nonneg hq0 hp0.le)]
    field_simp
  have hprod : d ^ 2 ≤ p * (1 - q) := by
    simpa only [sq] using mul_le_mul hp hq1 hd.le hp0.le
  have hbound := (mul_le_mul_of_nonneg_right hprod (sq_nonneg (firstPart p q ma mb))).trans
    (hi.trans_le hc)
  calc
    _ ≤ (2 * V) / d ^ 2 := (le_div_iff₀ (pow_pos hd 2)).mpr (by nlinarith only [hbound])
    _ = _ := by ring

/-- The second part combines the proved closed-interval square-root
bound with the positive component share of the actual second moment. -/
theorem secondPart_sq_le {p q ma mb m d : ℝ} (hd : 0 < d)
    (hp : d ≤ p) (hp1 : d ≤ 1 - p) (hq : d ≤ q) (hq1 : d ≤ 1 - q)
    (hma : 0 ≤ ma) (hmb : 0 ≤ mb) (hm : m = q * ma + (1 - q) * mb) :
    secondPart p q mb ^ 2 ≤ (1 / d ^ 3) * m * (q - p) ^ 2 := by
  have hp0 : 0 < p := hd.trans_le hp
  have hplt : p < 1 := by linarith
  have hphi := crossingRootDifference_abs_sub_le hd hp hp1
    (show q ∈ Icc d (1 - d) from ⟨hq, by linarith⟩)
    (show p ∈ Icc d (1 - d) from ⟨hp, by linarith⟩)
  rw [crossingRootDifference_self hp0 hplt, sub_zero] at hphi
  have hs : crossingRootDifference p q ^ 2 ≤ (1 / d) ^ 2 * (q - p) ^ 2 := by
    simpa only [← sq, mul_pow, sq_abs] using mul_self_le_mul_self (abs_nonneg _) hphi
  have hdom : d * mb ≤ m := by
    rw [hm]
    nlinarith [mul_le_mul_of_nonneg_right hq1 hmb, mul_nonneg (hd.le.trans hq) hma]
  calc
    _ = mb * crossingRootDifference p q ^ 2 := by rw [secondPart, mul_pow, Real.sq_sqrt hmb]
    _ ≤ mb * ((1 / d) ^ 2 * (q - p) ^ 2) := mul_le_mul_of_nonneg_left hs hmb
    _ = (d * mb) * ((1 / d ^ 3) * (q - p) ^ 2) := by field_simp
    _ ≤ m * ((1 / d ^ 3) * (q - p) ^ 2) := mul_le_mul_of_nonneg_right hdom (by positivity)
    _ = _ := by ring

/-- Source pointwise I/II bounds on every prescribed outside tuple.
The cell mixture, its variance bound and all second-moment integrability
are obtained from the actual original kernels. -/
theorem source_pointwise_parts {β β₀ δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r)
    {G : Configuration (n + 1) → ℝ} (hG : Measurable G) {B : ℝ} (hGb : ∀ X, |G X| ≤ B)
    (Y : Configuration n) (hY : PrescribedOutside (mesh_pos hmesh) η i Y) :
    let hJ := mesh_pos hmesh
    let p := (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal
    let q := outsideCrossingProbability hJ β i a r Y
    sourceFirstPart hJ η i a r β G Y ^ 2 ≤ (8 / lowerBound β₀ ^ 2) *
      variance (fun z => G (insertSite i z Y)) (conditionalKernel (edgeCellMeasure J hJ a r) i β Y) ∧
    sourceSecondPart hJ η i a r β G Y ^ 2 ≤ (8 / lowerBound β₀ ^ 3) *
      edgeSquareMoment hJ i β a r G Y * (q - p) ^ 2 := by
  let hJ := mesh_pos hmesh
  let q := outsideCrossingProbability hJ β i a r Y
  let p := (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal
  let ν := conditionalKernel (edgeCellMeasure J hJ a r) i β Y
  let g := fun z => G (insertSite i z Y)
  have hgm : Measurable g := hG.comp ((measurable_insertSite i).comp (measurable_id.prodMk measurable_const))
  have hg : MemLp g 2 ν := DensityMoments.memLp_of_bounded hgm ⟨B, fun z => hGb _⟩ 2
  have hc := lowerBound_pos β₀
  have hq := LabelRatioTransport.adjacent_conditional_crossing hβ hβ₀ hδ hmesh η i a r hadm Y hY
  change lowerBound β₀ / 2 ≤ q ∧ q ≤ 1 - lowerBound β₀ / 2 at hq
  have hq0 : 0 < q := by linarith [hq.1]
  have hq1 : q < 1 := by linarith [hq.2]
  have hp := LabelRatioTransport.adjacent_mixing_range hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm
  change lowerBound β₀ / 2 ≤ p ∧ p ≤ 1 - lowerBound β₀ / 2 at hp
  have hmix := conditional_edge_mixture hβ hβ₀ hδ hmesh η i a r hadm Y hY
  have hcross := ConditionalNormCrossing.one_site_crossing hq0 hq1 hmix hg
  have hmi := ConditionalNormCrossing.mixture_integrability hq0 hq1 hmix hg
  have hmass := ConditionalNormCrossing.integral_mixture hq0.le hq1.le hmix hmi.2.1 hmi.2.2
  change edgeSquareMoment hJ i β a r G Y = q * cellSquareMoment hJ i β a G Y +
    (1 - q) * cellSquareMoment hJ i β (nextCell J hJ a r) G Y at hmass
  constructor
  · have hh := firstPart_sq_le (by positivity : 0 < lowerBound β₀ / 2) hp.1 hq0.le
      (show lowerBound β₀ / 2 ≤ 1 - q by linarith [hq.2]) hcross
    have he : (2 : ℝ) / (lowerBound β₀ / 2) ^ 2 = 8 / lowerBound β₀ ^ 2 := by field_simp; ring
    rw [he] at hh
    exact hh
  · have hh := secondPart_sq_le (by positivity : 0 < lowerBound β₀ / 2) hp.1
      (show lowerBound β₀ / 2 ≤ 1 - p by linarith [hp.2]) hq.1
      (show lowerBound β₀ / 2 ≤ 1 - q by linarith [hq.2])
      (cellSquareMoment_nonneg hJ i β a G Y)
      (cellSquareMoment_nonneg hJ i β (nextCell J hJ a r) G Y) hmass
    have he : (1 : ℝ) / (lowerBound β₀ / 2) ^ 3 = 8 / lowerBound β₀ ^ 3 := by field_simp; ring
    rw [he] at hh
    exact hh

theorem bounded_observable {N : ℕ} {G : Configuration N → ℝ} (hG : Continuous G) :
    ∃ B : ℝ, ∀ X, |G X| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_univ : IsCompact (univ : Set (Configuration N))).exists_bound_of_continuousOn
    hG.continuousOn
  exact ⟨B, fun X => by simpa only [Real.norm_eq_abs] using hB X (mem_univ X)⟩

section Integrated

variable {β β₀ δ : ℝ}
  (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
  (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
  (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
  (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r)

include hN hβ hβ₀ hsub hδ₀ hδ hadm

/-- Actual weighted one-site square-moment disintegration, including both
integrability statements needed when integrating the second split term. -/
theorem source_weighted_square_integral {G : Configuration (n + 1) → ℝ}
    (hG : Measurable G) {B : ℝ} (hGb : ∀ X, |G X| ≤ B) :
    let hJ := mesh_pos hmesh
    let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
    let p := (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal
    let q := outsideCrossingProbability hJ β i a r
    let W := fun X => G X ^ 2 * (crossingProbability hJ i a r β X - p) ^ 2
    let H := fun Y => edgeSquareMoment hJ i β a r G Y * (q Y - p) ^ 2
    Integrable W P ∧ Integrable H (P.map (removeSite i)) ∧
      (∫ Y, H Y ∂P.map (removeSite i)) = ∫ X, W X ∂P := by
  let hJ := mesh_pos hmesh
  let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
  let p := (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal
  let q := outsideCrossingProbability hJ β i a r
  let κ := conditionalKernel (edgeCellMeasure J hJ a r) i β
  let W := fun X => G X ^ 2 * (crossingProbability hJ i a r β X - p) ^ 2
  let H := fun Y => edgeSquareMoment hJ i β a r G Y * (q Y - p) ^ 2
  let : IsProbabilityMeasure P := isProbabilityMeasure_twoCellGibbsMeasure hJ hN η i
    (Ne.symm (nextCell_ne J hJ (mesh_two_le hmesh) a r)) hβ (hβ₀.trans_lt hsub)
  let : IsProbabilityMeasure (P.map (removeSite i)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_removeSite i).aemeasurable).mpr inferInstance
  have hp := LabelRatioTransport.adjacent_mixing_range hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm
  change lowerBound β₀ / 2 ≤ p ∧ p ≤ 1 - lowerBound β₀ / 2 at hp
  have hc := lowerBound_pos β₀
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 := by linarith [hp.2]
  have hWm : Measurable W := (hG.pow_const 2).mul
    (((measurable_crossing hJ η i a r β).sub measurable_const).pow_const 2)
  have hW0 : ∀ X, 0 ≤ W X := fun X => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hWb : ∀ X, |W X| ≤ B ^ 2 := by
    intro X
    have hq := crossing_bounds hJ i a r β X
    have hqp : |crossingProbability hJ i a r β X - p| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hq.1], by linarith [hq.2]⟩
    have hq2 : (crossingProbability hJ i a r β X - p) ^ 2 ≤ 1 := by
      simpa only [← sq, sq_abs, one_pow] using mul_self_le_mul_self (abs_nonneg _) hqp
    have hG2 : G X ^ 2 ≤ B ^ 2 := by
      simpa only [← sq, sq_abs] using mul_self_le_mul_self (abs_nonneg _) (hGb X)
    rw [abs_of_nonneg (hW0 X)]
    exact (mul_le_mul hG2 hq2 (sq_nonneg _) (sq_nonneg B)).trans_eq (mul_one _)
  have hWi : Integrable W P := integrable_bounded P hWm hWb
  have hinner : outsideAverage κ i W = H := by
    funext Y
    change (∫ z, G (insertSite i z Y) ^ 2 *
      (crossingProbability hJ i a r β (insertSite i z Y) - p) ^ 2 ∂κ Y) = _
    simp only [crossingProbability, removeSite_insertSite]
    change (∫ z, G (insertSite i z Y) ^ 2 * (q Y - p) ^ 2 ∂κ Y) = _
    rw [integral_mul_const]
    rfl
  have hHi : Integrable H (P.map (removeSite i)) := by
    rw [← hinner]
    exact integrable_bounded _ (measurable_outsideAverage κ i hWm) (outsideAverage_bound κ i hWb)
  have he := integral_outsideAverage_of_disintegration P κ i
    (fun F hF => by simpa only [adjacent_measure_self] using
      lintegral_twoCell_conditionals hJ (mesh_two_le hmesh) hN η i i a r hβ (hβ₀.trans_lt hsub) hF)
    hWm hW0 hWb
  rw [hinner] at he
  exact ⟨hWi, hHi, he⟩

/-- The crossing particle contributes exactly the source 4 C_A factor.
The existing actual one-site PI is applied inside the original two-cell law. -/
theorem source_firstPart_integral_le {G : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hG : ConfigurationEuclideanLipschitzWith L G) :
    let hJ := mesh_pos hmesh
    let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
    (∫ Y, sourceFirstPart hJ η i a r β G Y ^ 2 ∂P.map (removeSite i)) ≤
      (4 * finePoincareConstant β₀ / lowerBound β₀ ^ 2 / (J : ℝ) ^ 2) *
        ∫ X, ‖coordinateOrdinaryGradient G i X‖ ^ 2 ∂P := by
  let hJ := mesh_pos hmesh
  let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
  let I := sourceFirstPart hJ η i a r β G
  let V := conditionalVariance hJ i a r β G
  obtain ⟨B, hGb⟩ := bounded_observable hG.continuous
  have hGm := hG.continuous.measurable
  have hIm : Measurable I := measurable_firstPart _ (measurable_outside_crossing hJ η i a r β)
    (measurable_cellSquareMoment hJ i β a hGm)
    (measurable_cellSquareMoment hJ i β (nextCell J hJ a r) hGm)
  have hIi : Integrable (fun Y => I Y ^ 2) (P.map (removeSite i)) :=
    (source_parts_memLp hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm hGm hGb).2.2.1.integrable_sq
  have hIj : Integrable (fun X => I (removeSite i X) ^ 2) P := by
    simpa only [Function.comp_def] using!
      (integrable_map_measure (hIm.pow_const 2).aestronglyMeasurable
        (measurable_removeSite i).aemeasurable).mp hIi
  have hVi : Integrable V P :=
    (adjacent_integrability_and_crossing hJ (mesh_two_le hmesh) hN η i a r hβ
      (hβ₀.trans_lt hsub) hGm hGb).2.2.1
  have hbound : ∀ᵐ X ∂P, I (removeSite i X) ^ 2 ≤ (8 / lowerBound β₀ ^ 2) * V X := by
    filter_upwards [twoCell_ae_closedProduct hJ (mesh_two_le hmesh) hN η i a r hβ
      (hβ₀.trans_lt hsub)] with X hX
    exact (source_pointwise_parts hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm hGm hGb
      (removeSite i X) (closedProduct_prescribedOutside hJ η i a r hX)).1
  have hpi := twoCell_conditionalVariance_energy hN hβ hβ₀ hsub hδ hmesh η i a r hadm hG
  calc
    _ = ∫ X, I (removeSite i X) ^ 2 ∂P :=
      integral_map_of_stronglyMeasurable (measurable_removeSite i) (hIm.pow_const 2).stronglyMeasurable
    _ ≤ ∫ X, (8 / lowerBound β₀ ^ 2) * V X ∂P := integral_mono_ae hIj (hVi.const_mul _) hbound
    _ = (8 / lowerBound β₀ ^ 2) * ∫ X, V X ∂P := integral_const_mul _ _
    _ ≤ (8 / lowerBound β₀ ^ 2) * ((poincareBound β₀ / (J : ℝ) ^ 2) *
        ∫ X, ‖coordinateOrdinaryGradient G i X‖ ^ 2 ∂P) :=
      mul_le_mul_of_nonneg_left hpi (by positivity)
    _ = _ := by unfold finePoincareConstant; ring

/-- The other coordinates contribute exactly the source 8/c_*^3 factor.
The weighted square moment is returned to the original joint Gibbs law by
its proved disintegration; no independent weighted Fubini premise is used. -/
theorem source_secondPart_integral_le {G : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hG : ConfigurationEuclideanLipschitzWith L G) :
    let hJ := mesh_pos hmesh
    let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
    let p := (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal
    (∫ Y, sourceSecondPart hJ η i a r β G Y ^ 2 ∂P.map (removeSite i)) ≤
      (8 / lowerBound β₀ ^ 3) * ∫ X, G X ^ 2 * (crossingProbability hJ i a r β X - p) ^ 2 ∂P := by
  let hJ := mesh_pos hmesh
  let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
  let p := (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal
  let II := sourceSecondPart hJ η i a r β G
  let H := fun Y => edgeSquareMoment hJ i β a r G Y * (outsideCrossingProbability hJ β i a r Y - p) ^ 2
  obtain ⟨B, hGb⟩ := bounded_observable hG.continuous
  have hGm := hG.continuous.measurable
  have hqm := measurable_outside_crossing hJ η i a r β
  have hIIm : Measurable II := measurable_secondPart _ hqm
    (measurable_cellSquareMoment hJ i β (nextCell J hJ a r) hGm)
  have hHm : Measurable H := (measurable_outsideAverage _ i (hGm.pow_const 2)).mul
    ((hqm.sub measurable_const).pow_const 2)
  have hIIi : Integrable (fun Y => II Y ^ 2) (P.map (removeSite i)) :=
    (source_parts_memLp hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm hGm hGb).2.2.2.integrable_sq
  have hIIj : Integrable (fun X => II (removeSite i X) ^ 2) P := by
    simpa only [Function.comp_def] using!
      (integrable_map_measure (hIIm.pow_const 2).aestronglyMeasurable
        (measurable_removeSite i).aemeasurable).mp hIIi
  have hw := source_weighted_square_integral hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm hGm hGb
  have hHj : Integrable (fun X => H (removeSite i X)) P := by
    simpa only [Function.comp_def] using!
      (integrable_map_measure hHm.aestronglyMeasurable (measurable_removeSite i).aemeasurable).mp hw.2.1
  have hbound : ∀ᵐ X ∂P, II (removeSite i X) ^ 2 ≤ (8 / lowerBound β₀ ^ 3) * H (removeSite i X) := by
    filter_upwards [twoCell_ae_closedProduct hJ (mesh_two_le hmesh) hN η i a r hβ
      (hβ₀.trans_lt hsub)] with X hX
    have hh := (source_pointwise_parts hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm hGm hGb
      (removeSite i X) (closedProduct_prescribedOutside hJ η i a r hX)).2
    simpa only [H, mul_assoc] using hh
  calc
    _ = ∫ X, II (removeSite i X) ^ 2 ∂P :=
      integral_map_of_stronglyMeasurable (measurable_removeSite i) (hIIm.pow_const 2).stronglyMeasurable
    _ ≤ ∫ X, (8 / lowerBound β₀ ^ 3) * H (removeSite i X) ∂P :=
      integral_mono_ae hIIj (hHj.const_mul _) hbound
    _ = (8 / lowerBound β₀ ^ 3) * ∫ Y, H Y ∂P.map (removeSite i) := by
      rw [integral_const_mul, integral_map_of_stronglyMeasurable (measurable_removeSite i) hHm.stronglyMeasurable]
    _ = _ := congrArg (fun z : ℝ => (8 / lowerBound β₀ ^ 3) * z) hw.2.2

/-- The source single-edge entropy comparison before the separately
proved weighted-fluctuation estimate. All conditional mixture, L2,
disintegration and one-site Poincare inputs are discharged above. -/
theorem single_edge_entropy_split {G : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hG : ConfigurationEuclideanLipschitzWith L G) :
    let hJ := mesh_pos hmesh
    let b := nextCell J hJ a r
    let P := twoCellGibbsMeasure hJ η i a b β
    let p := (twoCellMixingWeight hJ η i a b β).toReal
    p * (1 - p) * (Real.sqrt (∫ X, G X ^ 2 ∂labelGibbsMeasure hJ (Function.update η i a) β) -
      Real.sqrt (∫ X, G X ^ 2 ∂labelGibbsMeasure hJ (Function.update η i b) β)) ^ 2 ≤
      (2 * finePoincareConstant β₀ / lowerBound β₀ ^ 2 / (J : ℝ) ^ 2) *
        (∫ X, ‖coordinateOrdinaryGradient G i X‖ ^ 2 ∂P) +
      (4 / lowerBound β₀ ^ 3) * ∫ X, G X ^ 2 * (crossingProbability hJ i a r β X - p) ^ 2 ∂P := by
  obtain ⟨B, hGb⟩ := bounded_observable hG.continuous
  have hs := source_splitting hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm hG.continuous.measurable hGb
  have hI := source_firstPart_integral_le hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm hG
  have hII := source_secondPart_integral_le hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm hG
  dsimp only at hs hI hII ⊢
  have ht := mul_le_mul_of_nonneg_left (add_le_add hI hII) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply (hs.trans ht).trans_eq
  ring

end Integrated

end PeriodicAttractiveLogGas.EntropyEdgeSplitting
