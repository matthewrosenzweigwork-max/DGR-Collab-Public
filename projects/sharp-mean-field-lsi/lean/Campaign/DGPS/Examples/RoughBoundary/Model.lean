import DGPS.Examples.RoughBoundary.Feature
import DGPS.Analysis.RateTopology
import DGPS.Model.Data

/-!
# The product interaction of the rough model (RUF008)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 1.6.
-/

open MeasureTheory Set Filter
open scoped Real ENNReal

namespace DGPS.Examples.RoughBoundary.Model

open DGPS.Examples.RoughBoundary.Feature
open DGPS.Analysis.RateTopology (q1 q2 pairPt)

/-- The coupling constant `κ = 11/6`. -/
noncomputable def kappa : ℝ := 11 / 6

/-- The product interaction `W_{L,ε}(x,y) = κ (1 - U(x) · U(y))`. -/
noncomputable def modelW (L ε : ℝ) (x y : Torus 1) : ℝ :=
  kappa * (1 - inner ℝ (Ufeat L ε x) (Ufeat L ε y))

lemma modelW_eq_sq (L ε : ℝ) (x y : Torus 1) :
    modelW L ε x y = (11 / 12) * ‖Ufeat L ε x - Ufeat L ε y‖ ^ 2 := by
  unfold modelW kappa
  rw [norm_sub_sq_real, norm_Ufeat, norm_Ufeat]
  ring

lemma modelW_symm (L ε : ℝ) (x y : Torus 1) : modelW L ε x y = modelW L ε y x := by
  unfold modelW; rw [real_inner_comm]

lemma modelW_diag (L ε : ℝ) (x : Torus 1) : modelW L ε x x = 0 := by
  unfold modelW; rw [real_inner_self_eq_norm_sq, norm_Ufeat]; norm_num

lemma modelW_nonneg (L ε : ℝ) (x y : Torus 1) : 0 ≤ modelW L ε x y := by
  rw [modelW_eq_sq]; positivity

lemma modelW_le (L ε : ℝ) (x y : Torus 1) : modelW L ε x y ≤ 2 * kappa := by
  rw [modelW_eq_sq]
  have h : ‖Ufeat L ε x - Ufeat L ε y‖ ≤ 2 := by
    calc _ ≤ ‖Ufeat L ε x‖ + ‖Ufeat L ε y‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_Ufeat, norm_Ufeat]; norm_num
  have : ‖Ufeat L ε x - Ufeat L ε y‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (Ufeat L ε x - Ufeat L ε y)]
  unfold kappa; nlinarith

lemma continuous_modelW {L : ℝ} (hL : 0 < L) (ε : ℝ) :
    Continuous (fun q : Torus 1 × Torus 1 => modelW L ε q.1 q.2) := by
  have h := continuous_Ufeat hL ε
  unfold modelW
  exact continuous_const.mul (continuous_const.sub
    ((h.comp continuous_fst).inner (h.comp continuous_snd)))

/-- The interaction data `(V, W) = (0, W_{L,ε})` (DEF007). -/
noncomputable def modelData {L : ℝ} (hL : 0 < L) (ε : ℝ) : InteractionData 1 where
  V := fun _ => 0
  W := modelW L ε
  V_continuous := continuous_const
  W_continuous := continuous_modelW hL ε
  W_symm := modelW_symm L ε
  W_diag := modelW_diag L ε

/-! ### Hölder continuity on the product -/

/-- `a^α + b^α ≤ 2^(1-α/2) (a² + b²)^(α/2)`. -/
lemma rpow_add_le {a b α : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h0 : 0 < α) (h1 : α ≤ 2) :
    a ^ α + b ^ α ≤ 2 ^ (1 - α / 2) * Real.sqrt (a ^ 2 + b ^ 2) ^ α := by
  set r : ℝ := α / 2 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by rw [hr]; linarith
  have hA : (a ^ α) ^ (1 / r) = a ^ 2 := by
    rw [← Real.rpow_mul ha]
    have : α * (1 / r) = 2 := by rw [hr]; field_simp
    rw [this]; norm_cast
  have hB : (b ^ α) ^ (1 / r) = b ^ 2 := by
    rw [← Real.rpow_mul hb]
    have : α * (1 / r) = 2 := by rw [hr]; field_simp
    rw [this]; norm_cast
  have hp : (1 : ℝ) ≤ 1 / r := by rw [le_div_iff₀ hr0]; linarith
  have hAn : 0 ≤ a ^ α := Real.rpow_nonneg ha _
  have hBn : 0 ≤ b ^ α := Real.rpow_nonneg hb _
  have hc := (convexOn_rpow hp).2 (Set.mem_Ici.2 hAn) (Set.mem_Ici.2 hBn)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul, hA, hB] at hc
  have hM : 0 ≤ 1 / 2 * a ^ α + 1 / 2 * b ^ α := by positivity
  have h2 : (1 / 2 * a ^ α + 1 / 2 * b ^ α) ≤ ((a ^ 2 + b ^ 2) / 2) ^ r := by
    calc (1 / 2 * a ^ α + 1 / 2 * b ^ α)
        = ((1 / 2 * a ^ α + 1 / 2 * b ^ α) ^ (1 / r)) ^ r := by
          rw [← Real.rpow_mul hM, one_div_mul_cancel hr0.ne', Real.rpow_one]
      _ ≤ ((a ^ 2 + b ^ 2) / 2) ^ r := by
          apply Real.rpow_le_rpow (Real.rpow_nonneg hM _) _ hr0.le
          linarith
  have hs : Real.sqrt (a ^ 2 + b ^ 2) ^ α = (a ^ 2 + b ^ 2) ^ r := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), hr]
    congr 1; ring
  rw [Real.div_rpow (by positivity) (by norm_num)] at h2
  have h2r : (2 : ℝ) ^ (1 - r) = 2 / 2 ^ r := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one]
  rw [hs, h2r]
  calc a ^ α + b ^ α = 2 * (1 / 2 * a ^ α + 1 / 2 * b ^ α) := by ring
    _ ≤ 2 * ((a ^ 2 + b ^ 2) ^ r / 2 ^ r) := by gcongr
    _ = 2 / 2 ^ r * (a ^ 2 + b ^ 2) ^ r := by ring

/-- Hölder constant of `U` on the torus (the RUF005 bound). -/
noncomputable def cU (L ε α : ℝ) : ℝ :=
  2 * π * (2 * (Real.exp L / Zpart L) + |ε| * 6 ^ α * holderConst α)

lemma cU_nonneg {L : ℝ} (hL : 0 < L) (ε α : ℝ) : 0 ≤ cU L ε α := by
  unfold cU
  have := (div_pos (Real.exp_pos L) (zpart_pos hL)).le
  have := holderConst_nonneg α
  positivity

lemma norm_sub_Ufeat_le {L : ℝ} (hL : 0 < L) (ε : ℝ) {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (x y : Torus 1) : ‖Ufeat L ε x - Ufeat L ε y‖ ≤ cU L ε α * torusDist x y ^ α :=
  holder_Ufeat hL ε h0 h1 x y

/-- Hölder continuity of `W` on the Euclidean product torus, with the constant
`κ 2^(1-α/2) [U]_α`. -/
lemma modelW_holder {L : ℝ} (hL : 0 < L) (ε : ℝ) {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (x y x' y' : Torus 1) :
    |modelW L ε x y - modelW L ε x' y'| ≤
      kappa * 2 ^ (1 - α / 2) * cU L ε α *
        Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2) ^ α := by
  have e : modelW L ε x y - modelW L ε x' y' =
      kappa * (inner ℝ (Ufeat L ε x') (Ufeat L ε y') - inner ℝ (Ufeat L ε x) (Ufeat L ε y)) := by
    unfold modelW; ring
  have e2 : inner ℝ (Ufeat L ε x') (Ufeat L ε y') - inner ℝ (Ufeat L ε x) (Ufeat L ε y) =
      -(inner ℝ (Ufeat L ε x - Ufeat L ε x') (Ufeat L ε y) +
        inner ℝ (Ufeat L ε x') (Ufeat L ε y - Ufeat L ε y')) := by
    simp only [inner_sub_left, inner_sub_right]; ring
  have hk : 0 ≤ kappa := by unfold kappa; norm_num
  have hb1 : |inner ℝ (Ufeat L ε x - Ufeat L ε x') (Ufeat L ε y)| ≤
      cU L ε α * torusDist x x' ^ α := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_Ufeat, mul_one]; exact norm_sub_Ufeat_le hL ε h0 h1 x x'
  have hb2 : |inner ℝ (Ufeat L ε x') (Ufeat L ε y - Ufeat L ε y')| ≤
      cU L ε α * torusDist y y' ^ α := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_Ufeat, one_mul]; exact norm_sub_Ufeat_le hL ε h0 h1 y y'
  have hpm := rpow_add_le (torusDist_nonneg' x x') (torusDist_nonneg' y y') h0 (by linarith)
  rw [e, e2, abs_mul, abs_of_nonneg hk, abs_neg]
  calc kappa * |inner ℝ (Ufeat L ε x - Ufeat L ε x') (Ufeat L ε y) +
        inner ℝ (Ufeat L ε x') (Ufeat L ε y - Ufeat L ε y')|
      ≤ kappa * (cU L ε α * (torusDist x x' ^ α + torusDist y y' ^ α)) := by
        gcongr
        calc _ ≤ _ := abs_add_le _ _
          _ ≤ _ := add_le_add hb1 hb2
          _ = _ := by ring
    _ ≤ kappa * (cU L ε α * (2 ^ (1 - α / 2) *
          Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2) ^ α)) := by
        gcongr
        exact cU_nonneg hL ε α
    _ = _ := by ring

/-! ### Sections of smooth periodic test functions on `𝕋²` -/

/-- Affine embeddings `Fin 1 → ℝ → Fin 2 → ℝ` into the coordinate lines. -/
lemma sect_aux {φ : Torus 2 → ℝ} (hφ : IsSmoothPeriodic φ) (ι : (Fin 1 → ℝ) →L[ℝ] (Fin 2 → ℝ))
    (c : Fin 2 → ℝ) (j : Fin 2) (hj : ι (Pi.single 0 1) = Pi.single j 1)
    {f : Torus 1 → ℝ} (hf : ∀ v, f (torusLift v) = φ (torusLift (ι v + c))) :
    IsSmoothPeriodic f ∧ ∀ v, coordPartial 0 f (torusLift v) = coordPartial j φ (torusLift (ι v + c)) := by
  have hfc : f ∘ torusLift = (φ ∘ torusLift) ∘ fun v => ι v + c := by
    funext v; exact hf v
  have hsm : IsSmoothPeriodic f := by
    unfold IsSmoothPeriodic
    rw [hfc]
    exact hφ.comp (ι.contDiff.add contDiff_const)
  refine ⟨hsm, fun v => ?_⟩
  have h1 := (hφ.differentiable (by simp) (ι v + c)).hasFDerivAt.comp v
    ((ι.hasFDerivAt).add_const c)
  have e1 := congrFun (coordPartial_comp_torusLift (d := 1) 0 f) v
  have e2 := congrFun (coordPartial_comp_torusLift (d := 2) j φ) (ι v + c)
  replace e1 : coordPartial 0 f (torusLift v) = _ := e1
  replace e2 : coordPartial j φ (torusLift (ι v + c)) = _ := e2
  rw [e1, e2, hfc, h1.fderiv]
  simp [hj]

/-- Inclusion of the first coordinate line. -/
noncomputable def incl0 : (Fin 1 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ![v 0, 0]
      map_add' := fun v w => by ext i; fin_cases i <;> simp
      map_smul' := fun a v => by ext i; fin_cases i <;> simp }

/-- Inclusion of the second coordinate line. -/
noncomputable def incl1 : (Fin 1 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ![0, v 0]
      map_add' := fun v w => by ext i; fin_cases i <;> simp
      map_smul' := fun a v => by ext i; fin_cases i <;> simp }

lemma pairPt_lift (v w : Fin 1 → ℝ) :
    pairPt (torusLift v) (torusLift w) = torusLift ![v 0, w 0] := by
  funext i; fin_cases i <;> simp [pairPt, torusLift, SharpLSI.liftT]

lemma sect1 {φ : Torus 2 → ℝ} (hφ : IsSmoothPeriodic φ) (y : Torus 1) :
    IsSmoothPeriodic (fun x => φ (pairPt x y)) ∧
      ∀ x, coordPartial 0 (fun x => φ (pairPt x y)) x = coordPartial 0 φ (pairPt x y) := by
  obtain ⟨w, rfl⟩ : ∃ w : Fin 1 → ℝ, y = torusLift w :=
    ⟨SharpLSI.secT y, (SharpLSI.liftT_secT y).symm⟩
  have hv : ∀ v, ((fun x => φ (pairPt x (torusLift w))) (torusLift v)) =
      φ (torusLift (incl0 v + ![0, w 0])) := by
    intro v
    simp only [pairPt_lift]
    congr 2
    ext i; fin_cases i <;> simp [incl0]
  obtain ⟨h1, h2⟩ := sect_aux hφ incl0 ![0, w 0] 0 (by ext i; fin_cases i <;> simp [incl0])
    (f := fun x => φ (pairPt x (torusLift w))) hv
  refine ⟨h1, fun x => ?_⟩
  obtain ⟨v, rfl⟩ : ∃ v : Fin 1 → ℝ, x = torusLift v :=
    ⟨SharpLSI.secT x, (SharpLSI.liftT_secT x).symm⟩
  rw [h2 v, pairPt_lift]
  congr 2
  ext i; fin_cases i <;> simp [incl0]

lemma sect2 {φ : Torus 2 → ℝ} (hφ : IsSmoothPeriodic φ) (x : Torus 1) :
    IsSmoothPeriodic (fun y => φ (pairPt x y)) ∧
      ∀ y, coordPartial 0 (fun y => φ (pairPt x y)) y = coordPartial 1 φ (pairPt x y) := by
  obtain ⟨w, rfl⟩ : ∃ w : Fin 1 → ℝ, x = torusLift w :=
    ⟨SharpLSI.secT x, (SharpLSI.liftT_secT x).symm⟩
  have hv : ∀ v, ((fun y => φ (pairPt (torusLift w) y)) (torusLift v)) =
      φ (torusLift (incl1 v + ![w 0, 0])) := by
    intro v
    simp only [pairPt_lift]
    congr 2
    ext i; fin_cases i <;> simp [incl1]
  obtain ⟨h1, h2⟩ := sect_aux hφ incl1 ![w 0, 0] 1 (by ext i; fin_cases i <;> simp [incl1])
    (f := fun y => φ (pairPt (torusLift w) y)) hv
  refine ⟨h1, fun y => ?_⟩
  obtain ⟨v, rfl⟩ : ∃ v : Fin 1 → ℝ, y = torusLift v :=
    ⟨SharpLSI.secT y, (SharpLSI.liftT_secT y).symm⟩
  rw [h2 v, pairPt_lift]
  congr 2
  ext i; fin_cases i <;> simp [incl1]

/-! ### One-dimensional weak integration by parts -/

lemma inner_two (a b : EuclideanSpace ℝ (Fin 2)) : inner ℝ a b = a 0 * b 0 + a 1 * b 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

lemma integrable_Uprime_comp {L : ℝ} (hL : 0 < L) (ε : ℝ) (j : Fin 2) :
    Integrable (fun x => Uprime L ε x j) (haar 1) := by
  have h := (isWeakGradientLp_Ufeat hL ε (p := 1) le_rfl one_lt_two j).memLp_grad
  have h2 := memLp_coord_of_memLp h 0
  simp only [ENNReal.ofReal_one] at h2
  simpa using h2.integrable le_rfl

lemma integrable_cont {d : ℕ} {f : Torus d → ℝ} (hf : Continuous f) : Integrable f (haar d) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

lemma continuous_Ufeat_comp {L : ℝ} (hL : 0 < L) (ε : ℝ) (j : Fin 2) :
    Continuous fun y => Ufeat L ε y j :=
  (continuous_apply j).comp ((PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ)).comp
    (continuous_Ufeat hL ε))

lemma integrable_Ufeat_mul {L : ℝ} (hL : 0 < L) (ε : ℝ) (j : Fin 2) {f : Torus 1 → ℝ}
    (hf : Continuous f) : Integrable (fun x => Ufeat L ε x j * f x) (haar 1) :=
  integrable_cont ((continuous_Ufeat_comp hL ε j).mul hf)

/-- A bounded continuous function times an `L¹` function is integrable. -/
lemma integrable_Uprime_mul {L : ℝ} (hL : 0 < L) (ε : ℝ) (j : Fin 2) {f : Torus 1 → ℝ}
    (hf : Continuous f) : Integrable (fun x => Uprime L ε x j * f x) (haar 1) := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus 1)).exists_bound_of_continuousOn hf.continuousOn
  exact (integrable_Uprime_comp hL ε j).mul_bdd (c := C) hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa using hC x (Set.mem_univ _))

lemma ibp_comp {L : ℝ} (hL : 0 < L) (ε : ℝ) (j : Fin 2) {ψ : Torus 1 → ℝ}
    (hψ : IsSmoothPeriodic ψ) :
    ∫ x, Ufeat L ε x j * coordPartial 0 ψ x ∂haar 1 = -∫ x, Uprime L ε x j * ψ x ∂haar 1 := by
  have := (isWeakGradientLp_Ufeat hL ε (p := 1) le_rfl one_lt_two j).ibp ψ hψ 0
  simpa using this

lemma integral_coordPartial_zero' {ψ : Torus 1 → ℝ} (hψ : IsSmoothPeriodic ψ) :
    ∫ x, coordPartial 0 ψ x ∂haar 1 = 0 := by
  have h := (isWeakGradient_const (d := 1) 1).ibp ψ hψ 0
  simpa using h

/-- Weak integration by parts for `x ↦ W(x, v)` against a smooth periodic test function. -/
lemma ibp_section {L : ℝ} (hL : 0 < L) (ε : ℝ) (v : Torus 1) {ψ : Torus 1 → ℝ}
    (hψ : IsSmoothPeriodic ψ) :
    ∫ x, modelW L ε x v * coordPartial 0 ψ x ∂haar 1 =
      ∫ x, kappa * inner ℝ (Uprime L ε x) (Ufeat L ε v) * ψ x ∂haar 1 := by
  have hd := hψ.continuous_coordPartial 0
  have hc := hψ.continuous_torus
  set c0 := Ufeat L ε v 0
  set c1 := Ufeat L ε v 1
  have e1 : ∀ x, modelW L ε x v * coordPartial 0 ψ x =
      kappa * coordPartial 0 ψ x - kappa * c0 * (Ufeat L ε x 0 * coordPartial 0 ψ x) -
        kappa * c1 * (Ufeat L ε x 1 * coordPartial 0 ψ x) := by
    intro x; unfold modelW; rw [inner_two]; ring
  have e2 : ∀ x, kappa * inner ℝ (Uprime L ε x) (Ufeat L ε v) * ψ x =
      kappa * c0 * (Uprime L ε x 0 * ψ x) + kappa * c1 * (Uprime L ε x 1 * ψ x) := by
    intro x; rw [inner_two]; ring
  simp_rw [e1, e2]
  rw [integral_sub, integral_sub, integral_add, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_coordPartial_zero' hψ,
    ibp_comp hL ε 0 hψ, ibp_comp hL ε 1 hψ]
  · ring
  · exact (integrable_Uprime_mul hL ε 0 hc).const_mul _
  · exact (integrable_Uprime_mul hL ε 1 hc).const_mul _
  · exact (integrable_cont hd).const_mul _
  · exact (integrable_Ufeat_mul hL ε 0 hd).const_mul _
  · exact ((integrable_cont hd).const_mul _).sub ((integrable_Ufeat_mul hL ε 0 hd).const_mul _)
  · exact (integrable_Ufeat_mul hL ε 1 hd).const_mul _

/-! ### The product torus `𝕋² = Torus 2` -/

/-- `W_{L,ε}` as a function on `Torus 2` (the pair `(x, y)` being `pairPt x y`). -/
noncomputable def Wtor (L ε : ℝ) (p : Torus 2) : ℝ := modelW L ε (q1 p) (q2 p)

/-- The claimed weak gradient `(-κ U'(x)·U(y), -κ U(x)·U'(y))` at the pair `(x, y)`. -/
noncomputable def gradPair (L ε : ℝ) (x y : Torus 1) : Tangent 2 :=
  !₂[-(kappa * inner ℝ (Uprime L ε x) (Ufeat L ε y)),
    -(kappa * inner ℝ (Ufeat L ε x) (Uprime L ε y))]

/-- The claimed weak gradient as a function on `Torus 2`. -/
noncomputable def gradW (L ε : ℝ) (p : Torus 2) : Tangent 2 := gradPair L ε (q1 p) (q2 p)

lemma continuous_q1 : Continuous q1 :=
  continuous_pi fun _ => continuous_apply 0

lemma continuous_q2 : Continuous q2 :=
  continuous_pi fun _ => continuous_apply 1

lemma continuous_Wtor {L : ℝ} (hL : 0 < L) (ε : ℝ) : Continuous (Wtor L ε) := by
  have h := (continuous_modelW hL ε).comp (continuous_q1.prodMk continuous_q2)
  exact h

lemma Wtor_pairPt (L ε : ℝ) (x y : Torus 1) : Wtor L ε (pairPt x y) = modelW L ε x y := by
  simp [Wtor, DGPS.Analysis.RateTopology.q1_pairPt, DGPS.Analysis.RateTopology.q2_pairPt]

lemma gradW_pairPt (L ε : ℝ) (x y : Torus 1) : gradW L ε (pairPt x y) = gradPair L ε x y := by
  simp [gradW, DGPS.Analysis.RateTopology.q1_pairPt, DGPS.Analysis.RateTopology.q2_pairPt]

lemma measurable_Ufeat_vec {L : ℝ} (hL : 0 < L) (ε : ℝ) : Measurable (Ufeat L ε) :=
  (continuous_Ufeat hL ε).measurable

lemma measurable_Uprime_vec {L : ℝ} (hL : 0 < L) (ε : ℝ) : Measurable (Uprime L ε) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp
    (measurable_pi_iff.2 fun j => measurable_Uprime_comp hL ε j)

lemma measurable_gradPair {L : ℝ} (hL : 0 < L) (ε : ℝ) :
    Measurable (fun z : Torus 1 × Torus 1 => gradPair L ε z.1 z.2) := by
  have h1 : Measurable fun z : Torus 1 × Torus 1 => Uprime L ε z.1 :=
    (measurable_Uprime_vec hL ε).comp measurable_fst
  have h2 : Measurable fun z : Torus 1 × Torus 1 => Uprime L ε z.2 :=
    (measurable_Uprime_vec hL ε).comp measurable_snd
  have h3 : Measurable fun z : Torus 1 × Torus 1 => Ufeat L ε z.1 :=
    (measurable_Ufeat_vec hL ε).comp measurable_fst
  have h4 : Measurable fun z : Torus 1 × Torus 1 => Ufeat L ε z.2 :=
    (measurable_Ufeat_vec hL ε).comp measurable_snd
  unfold gradPair
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp
    (measurable_pi_iff.2 fun i => ?_)
  fin_cases i
  · exact (measurable_const.mul (h1.inner h4)).neg
  · exact (measurable_const.mul (h3.inner h2)).neg

lemma norm_gradPair_sq (L ε : ℝ) (x y : Torus 1) :
    ‖gradPair L ε x y‖ ^ 2 = kappa ^ 2 *
      (inner ℝ (Uprime L ε x) (Ufeat L ε y) ^ 2 + inner ℝ (Ufeat L ε x) (Uprime L ε y) ^ 2) := by
  unfold gradPair
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_two]
  ring

/-! ### The `L^p` bound on the gradient -/

lemma abs_inner_Uprime_le (L ε : ℝ) (x y : Torus 1) :
    |inner ℝ (Uprime L ε x) (Ufeat L ε y)| ≤ ‖Uprime L ε x‖ := by
  have := abs_real_inner_le_norm (Uprime L ε x) (Ufeat L ε y)
  rwa [norm_Ufeat, mul_one] at this

lemma norm_gradPair_le (L ε : ℝ) (x y : Torus 1) :
    ‖gradPair L ε x y‖ ^ 2 ≤ kappa ^ 2 * (‖Uprime L ε x‖ ^ 2 + ‖Uprime L ε y‖ ^ 2) := by
  rw [norm_gradPair_sq]
  have h1 := abs_inner_Uprime_le L ε x y
  have h2 : |inner ℝ (Ufeat L ε x) (Uprime L ε y)| ≤ ‖Uprime L ε y‖ := by
    have := abs_real_inner_le_norm (Ufeat L ε x) (Uprime L ε y)
    rwa [norm_Ufeat, one_mul] at this
  have e1 := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
  have e2 := sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2
  have : 0 ≤ kappa ^ 2 := sq_nonneg _
  nlinarith

lemma rpow_gradPair_le (L ε : ℝ) {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (x y : Torus 1) :
    ‖gradPair L ε x y‖ ^ p ≤
      kappa ^ p * (‖Uprime L ε x‖ ^ p + ‖Uprime L ε y‖ ^ p) := by
  have hk : 0 ≤ kappa := by unfold kappa; norm_num
  have hp0 : 0 < p := by linarith
  set a := ‖Uprime L ε x‖
  set b := ‖Uprime L ε y‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have h := norm_gradPair_le L ε x y
  have h1 : ‖gradPair L ε x y‖ ≤ kappa * (a ^ 2 + b ^ 2) ^ ((1:ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    have : kappa * Real.sqrt (a ^ 2 + b ^ 2) = Real.sqrt (kappa ^ 2 * (a ^ 2 + b ^ 2)) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk]
    rw [this]
    exact Real.le_sqrt_of_sq_le h
  calc ‖gradPair L ε x y‖ ^ p ≤ (kappa * (a ^ 2 + b ^ 2) ^ ((1:ℝ) / 2)) ^ p :=
        Real.rpow_le_rpow (norm_nonneg _) h1 hp0.le
    _ = kappa ^ p * (a ^ 2 + b ^ 2) ^ (p / 2) := by
        rw [Real.mul_rpow hk (by positivity), ← Real.rpow_mul (by positivity)]
        congr 2; ring
    _ ≤ kappa ^ p * (a ^ p + b ^ p) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h3 := Real.rpow_add_le_add_rpow (p := p / 2) (a := a ^ 2) (b := b ^ 2)
          (by positivity) (by positivity) (by positivity) (by linarith)
        have e : ∀ t : ℝ, 0 ≤ t → (t ^ 2) ^ (p / 2) = t ^ p := by
          intro t ht
          rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
          congr 1; push_cast; ring
        rwa [e a ha, e b hb] at h3

lemma enorm_rpow_eq (v : EuclideanSpace ℝ (Fin 2)) {p : ℝ} (hp : 0 ≤ p) :
    ‖v‖ₑ ^ p = ENNReal.ofReal (‖v‖ ^ p) := by
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp]

lemma lintegral_gradPair_le {L : ℝ} (hL : 0 < L) (ε : ℝ) {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    ∫⁻ z : Torus 1 × Torus 1, ‖gradPair L ε z.1 z.2‖ₑ ^ p ∂(haar 1).prod (haar 1) ≤
      ENNReal.ofReal (kappa ^ p) *
        (2 * ∫⁻ y, ‖Uprime L ε y‖ₑ ^ p ∂haar 1) := by
  have hp0 : 0 ≤ p := by linarith
  have hm : Measurable fun y : Torus 1 => ‖Uprime L ε y‖ₑ ^ p :=
    (measurable_Uprime_vec hL ε).enorm.pow_const p
  have hk : 0 ≤ kappa ^ p := Real.rpow_nonneg (by unfold kappa; norm_num) p
  calc ∫⁻ z : Torus 1 × Torus 1, ‖gradPair L ε z.1 z.2‖ₑ ^ p ∂(haar 1).prod (haar 1)
      ≤ ∫⁻ z : Torus 1 × Torus 1, ENNReal.ofReal (kappa ^ p) *
          (‖Uprime L ε z.1‖ₑ ^ p + ‖Uprime L ε z.2‖ₑ ^ p) ∂(haar 1).prod (haar 1) := by
        refine lintegral_mono fun z => ?_
        rw [enorm_rpow_eq _ hp0, enorm_rpow_eq _ hp0, enorm_rpow_eq _ hp0,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul hk]
        exact ENNReal.ofReal_le_ofReal (rpow_gradPair_le L ε hp hp2 z.1 z.2)
    _ = ENNReal.ofReal (kappa ^ p) * (2 * ∫⁻ y, ‖Uprime L ε y‖ₑ ^ p ∂haar 1) := by
        have hm1 : Measurable fun z : Torus 1 × Torus 1 => ‖Uprime L ε z.1‖ₑ ^ p :=
          hm.comp measurable_fst
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left hm1,
          (measurePreserving_fst (μ := haar 1) (ν := haar 1)).lintegral_comp hm,
          (measurePreserving_snd (μ := haar 1) (ν := haar 1)).lintegral_comp hm, two_mul]

lemma eLpNorm_gradW_le {L : ℝ} (hL : 0 < L) (ε : ℝ) {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    eLpNorm (fun q => ‖gradW L ε q‖) (ENNReal.ofReal p) (haar 2) ≤
      ENNReal.ofReal (kappa * 2 ^ (1 / p)) *
        eLpNorm (fun y => ‖Uprime L ε y‖) (ENNReal.ofReal p) (haar 1) := by
  have hp0 : 0 < p := by linarith
  have hk : 0 ≤ kappa := by unfold kappa; norm_num
  have hne : ENNReal.ofReal p ≠ 0 := by simp [hp0]
  have hmeas : Measurable fun z : Torus 1 × Torus 1 => ‖gradPair L ε z.1 z.2‖ :=
    (measurable_gradPair hL ε).norm
  have h1 : eLpNorm (fun q => ‖gradW L ε q‖) (ENNReal.ofReal p) (haar 2) =
      eLpNorm (fun z : Torus 1 × Torus 1 => ‖gradPair L ε z.1 z.2‖) (ENNReal.ofReal p)
        ((haar 1).prod (haar 1)) := by
    have := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal p)
      (g := fun z : Torus 1 × Torus 1 => ‖gradPair L ε z.1 z.2‖) hmeas.aestronglyMeasurable
      DGPS.Analysis.RateTopology.measurePreserving_q
    exact this
  rw [h1, eLpNorm_eq_lintegral_rpow_enorm_toReal hne ENNReal.ofReal_ne_top
      hmeas.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hne ENNReal.ofReal_ne_top
      (measurable_Uprime_vec hL ε).norm.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
  simp only [enorm_norm]
  have h2 := lintegral_gradPair_le hL ε hp hp2
  calc (∫⁻ z : Torus 1 × Torus 1, ‖gradPair L ε z.1 z.2‖ₑ ^ p ∂(haar 1).prod (haar 1)) ^ (1 / p)
      ≤ (ENNReal.ofReal (kappa ^ p) * (2 * ∫⁻ y, ‖Uprime L ε y‖ₑ ^ p ∂haar 1)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow h2 (by positivity)
    _ = ENNReal.ofReal (kappa * 2 ^ (1 / p)) * (∫⁻ y, ‖Uprime L ε y‖ₑ ^ p ∂haar 1) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.ofReal_mul hk, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          ← Real.rpow_mul hk, mul_one_div_cancel hp0.ne', Real.rpow_one]
        have h2' : ENNReal.ofReal (2 ^ (1 / p)) = 2 ^ (1 / p) := by
          rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by positivity)]
          simp
        rw [h2', mul_assoc]

/-! ### Memberships -/

lemma memLp_norm_Uprime {L : ℝ} (hL : 0 < L) (ε : ℝ) {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) :
    MemLp (fun y => ‖Uprime L ε y‖) (ENNReal.ofReal p) (haar 1) := by
  have e : (fun y => ‖Uprime L ε y‖) = fun y => 2 * π * ‖dthetaT L ε y‖ := by
    funext y; rw [norm_Uprime, Real.norm_eq_abs]
  rw [e]
  exact (memLp_dthetaT hL ε hp hp2).norm.const_mul (2 * π)

lemma measurable_pairQ : Measurable fun p : Torus 2 => (q1 p, q2 p) :=
  DGPS.Analysis.RateTopology.measurePreserving_q.measurable

lemma memLp_gradW {L : ℝ} (hL : 0 < L) (ε : ℝ) {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) :
    MemLp (gradW L ε) (ENNReal.ofReal p) (haar 2) := by
  have hm : AEStronglyMeasurable (gradW L ε) (haar 2) :=
    ((measurable_gradPair hL ε).comp measurable_pairQ).aestronglyMeasurable
  rw [memLp_iff, ← eLpNorm_norm _ hm]
  refine lt_of_le_of_lt (eLpNorm_gradW_le hL ε hp hp2.le) ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (memLp_norm_Uprime hL ε hp hp2)

lemma memLp_Wtor {L : ℝ} (hL : 0 < L) (ε : ℝ) (p : ℝ≥0∞) : MemLp (Wtor L ε) p (haar 2) := by
  refine MemLp.of_bound (continuous_Wtor hL ε).aestronglyMeasurable (2 * kappa)
    (Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs]
  unfold Wtor
  rw [abs_of_nonneg (modelW_nonneg _ _ _ _)]
  exact modelW_le _ _ _ _

lemma integrable_grad_mul {L : ℝ} (ε : ℝ) (hG : MemLp (gradW L ε) 1 (haar 2)) {φ : Torus 2 → ℝ}
    (hφ : IsSmoothPeriodic φ) (j : Fin 2) :
    Integrable (fun p => gradW L ε p j * φ p) (haar 2) := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus 2)).exists_bound_of_continuousOn
    hφ.continuous_torus.continuousOn
  exact (memLp_coord_of_memLp hG j).integrable le_rfl |>.mul_bdd (c := C)
    hφ.continuous_torus.aestronglyMeasurable
    (Eventually.of_forall fun z => by simpa using hC z (Set.mem_univ _))

/-! ### Integration by parts -/

lemma ibp_zero {L : ℝ} (hL : 0 < L) (ε : ℝ) (hG : MemLp (gradW L ε) 1 (haar 2)) {φ : Torus 2 → ℝ}
    (hφ : IsSmoothPeriodic φ) :
    ∫ p, Wtor L ε p * coordPartial 0 φ p ∂haar 2 = -∫ p, gradW L ε p 0 * φ p ∂haar 2 := by
  have hI1 : Integrable (fun z : Torus 1 × Torus 1 =>
      modelW L ε z.1 z.2 * coordPartial 0 φ (pairPt z.1 z.2)) ((haar 1).prod (haar 1)) := by
    have := (DGPS.Analysis.RateTopology.integrable_torus2
      (fun p => Wtor L ε p * coordPartial 0 φ p)).2
      (integrable_cont ((continuous_Wtor hL ε).mul (hφ.continuous_coordPartial 0)))
    simpa [Wtor_pairPt] using this
  have hI2 : Integrable (fun z : Torus 1 × Torus 1 =>
      gradPair L ε z.1 z.2 0 * φ (pairPt z.1 z.2)) ((haar 1).prod (haar 1)) := by
    have := (DGPS.Analysis.RateTopology.integrable_torus2
      (fun p => gradW L ε p 0 * φ p)).2 (integrable_grad_mul ε hG hφ 0)
    simpa [gradW_pairPt] using this
  rw [← DGPS.Analysis.RateTopology.integral_torus2 (fun p => Wtor L ε p * coordPartial 0 φ p),
    ← DGPS.Analysis.RateTopology.integral_torus2 (fun p => gradW L ε p 0 * φ p)]
  simp only [Wtor_pairPt, gradW_pairPt]
  rw [integral_prod_symm _ hI1, integral_prod_symm _ hI2, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  obtain ⟨hs, hd⟩ := sect1 hφ y
  have h := ibp_section hL ε y hs
  simp only [hd] at h
  simp only
  rw [h, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [gradPair]

lemma ibp_one {L : ℝ} (hL : 0 < L) (ε : ℝ) (hG : MemLp (gradW L ε) 1 (haar 2)) {φ : Torus 2 → ℝ}
    (hφ : IsSmoothPeriodic φ) :
    ∫ p, Wtor L ε p * coordPartial 1 φ p ∂haar 2 = -∫ p, gradW L ε p 1 * φ p ∂haar 2 := by
  have hI1 : Integrable (fun z : Torus 1 × Torus 1 =>
      modelW L ε z.1 z.2 * coordPartial 1 φ (pairPt z.1 z.2)) ((haar 1).prod (haar 1)) := by
    have := (DGPS.Analysis.RateTopology.integrable_torus2
      (fun p => Wtor L ε p * coordPartial 1 φ p)).2
      (integrable_cont ((continuous_Wtor hL ε).mul (hφ.continuous_coordPartial 1)))
    simpa [Wtor_pairPt] using this
  have hI2 : Integrable (fun z : Torus 1 × Torus 1 =>
      gradPair L ε z.1 z.2 1 * φ (pairPt z.1 z.2)) ((haar 1).prod (haar 1)) := by
    have := (DGPS.Analysis.RateTopology.integrable_torus2
      (fun p => gradW L ε p 1 * φ p)).2 (integrable_grad_mul ε hG hφ 1)
    simpa [gradW_pairPt] using this
  rw [← DGPS.Analysis.RateTopology.integral_torus2 (fun p => Wtor L ε p * coordPartial 1 φ p),
    ← DGPS.Analysis.RateTopology.integral_torus2 (fun p => gradW L ε p 1 * φ p)]
  simp only [Wtor_pairPt, gradW_pairPt]
  rw [integral_prod _ hI1, integral_prod _ hI2, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  obtain ⟨hs, hd⟩ := sect2 hφ x
  have h := ibp_section hL ε x hs
  simp only [hd] at h
  simp only
  have e : ∀ y, modelW L ε x y * coordPartial 1 φ (pairPt x y) =
      modelW L ε y x * coordPartial 1 φ (pairPt x y) := fun y => by rw [modelW_symm]
  simp only [e]
  rw [h, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [gradPair, real_inner_comm]

lemma isWeakGradientLp_Wtor {L : ℝ} (hL : 0 < L) (ε : ℝ) {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) :
    IsWeakGradientLp (ENNReal.ofReal p) (Wtor L ε) (gradW L ε) := by
  have h1 : MemLp (gradW L ε) 1 (haar 2) := by
    simpa using memLp_gradW hL ε (p := 1) le_rfl one_lt_two
  refine ⟨memLp_Wtor hL ε _, memLp_gradW hL ε hp hp2, fun φ hφ j => ?_⟩
  match j with
  | 0 => exact ibp_zero hL ε h1 hφ
  | 1 => exact ibp_one hL ε h1 hφ

/-- **Regularity of the product interaction below `H¹`** (RUF008). For `L > 0` and `ε ∈ ℝ`, the
interaction `W_{L,ε}(x,y) = κ (1 - U(x)·U(y))`, `κ = 11/6`, is `(11/12)|U(x)-U(y)|²`, continuous,
symmetric, between `0` and `2κ`, vanishing on the diagonal, Hölder of every order `α < 1` on
`𝕋²` (Euclidean product metric, explicit constant), and lies in `W^{1,p}(𝕋²)` for `1 ≤ p < 2`
with weak gradient `(-κ U'(x)·U(y), -κ U(x)·U'(y))` and `‖∇W‖_p ≤ κ 2^{1/p} ‖U'‖_p`. -/
theorem product_interaction_regularity_below_h1 {L : ℝ} (hL : 0 < L) (ε : ℝ) :
    kappa = 11 / 6 ∧
    (∀ x y : Torus 1, modelW L ε x y = (11 / 12) * ‖Ufeat L ε x - Ufeat L ε y‖ ^ 2) ∧
    Continuous (fun q : Torus 1 × Torus 1 => modelW L ε q.1 q.2) ∧
    (∀ x y : Torus 1, modelW L ε x y = modelW L ε y x) ∧
    (∀ x y : Torus 1, 0 ≤ modelW L ε x y ∧ modelW L ε x y ≤ 2 * kappa) ∧
    (∀ x : Torus 1, modelW L ε x x = 0) ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∀ x y x' y' : Torus 1,
      |modelW L ε x y - modelW L ε x' y'| ≤
        kappa * 2 ^ (1 - α / 2) * cU L ε α *
          Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2) ^ α) ∧
    (∀ x y : Torus 1,
      gradW L ε (pairPt x y) 0 = -(kappa * inner ℝ (Uprime L ε x) (Ufeat L ε y)) ∧
      gradW L ε (pairPt x y) 1 = -(kappa * inner ℝ (Ufeat L ε x) (Uprime L ε y))) ∧
    (∀ p : ℝ, 1 ≤ p → p < 2 →
      IsWeakGradientLp (ENNReal.ofReal p) (Wtor L ε) (gradW L ε) ∧
      eLpNorm (fun q => ‖gradW L ε q‖) (ENNReal.ofReal p) (haar 2) ≤
        ENNReal.ofReal (kappa * 2 ^ (1 / p)) *
          eLpNorm (fun y => ‖Uprime L ε y‖) (ENNReal.ofReal p) (haar 1)) := by
  refine ⟨rfl, modelW_eq_sq L ε, continuous_modelW hL ε, modelW_symm L ε,
    fun x y => ⟨modelW_nonneg L ε x y, modelW_le L ε x y⟩, modelW_diag L ε,
    fun α h0 h1 x y x' y' => modelW_holder hL ε h0 h1 x y x' y', fun x y => ?_,
    fun p hp hp2 => ⟨isWeakGradientLp_Wtor hL ε hp hp2, eLpNorm_gradW_le hL ε hp hp2.le⟩⟩
  rw [gradW_pairPt]
  simp [gradPair]

end DGPS.Examples.RoughBoundary.Model
