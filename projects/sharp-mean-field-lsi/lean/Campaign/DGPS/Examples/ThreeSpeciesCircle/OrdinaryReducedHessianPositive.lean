import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootGraphData

/-!
# Positive amplitude Hessian along the actual retained ordinary branches

The zero-field polynomial supplies the positive two-dimensional blocks. Continuity of
the actual second Frechet derivative gives one common interval for all three SAME branches.
No optimizer-count argument or Hessian-positivity hypothesis is used.
-/

open Filter Topology
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

noncomputable def ordinaryAmplitudeBlock : (ℝ × ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun i : Fin 3 =>
    ![ContinuousLinearMap.fst ℝ ℝ ℝ, ContinuousLinearMap.snd ℝ ℝ ℝ, 0] i)

@[simp] theorem ordinaryAmplitudeBlock_apply (v : ℝ × ℝ) :
    ordinaryAmplitudeBlock v = ![v.1, v.2, 0] := by
  ext i
  fin_cases i <;> rfl

noncomputable def ordinaryAmplitudeLift : (ℝ × ℝ) →L[ℝ] (ℝ × (Fin 3 → ℝ)) :=
  (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod ordinaryAmplitudeBlock

@[simp] theorem ordinaryAmplitudeLift_apply (v : ℝ × ℝ) :
    ordinaryAmplitudeLift v = (0, ![v.1, v.2, 0]) := by
  change (0, ordinaryAmplitudeBlock v) = _
  rw [ordinaryAmplitudeBlock_apply]

private theorem hessian_affine_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : X → ℝ) {O : Set X} (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    (c : X) (L : (ℝ × ℝ) →L[ℝ] X) (x v z : ℝ × ℝ) (hx : c + L x ∈ O) :
    fderiv ℝ (fderiv ℝ (fun y => F (c + L y))) x v z =
      fderiv ℝ (fderiv ℝ F) (c + L x) (L v) (L z) := by
  let G := fun y => c + L y
  let A := fun y => F (G y)
  have hGc : ContDiff ℝ ∞ G := contDiff_const.add L.contDiff
  have hGd : ∀ y, HasFDerivAt G L y := fun y => by
    simpa only [G] using (L.hasFDerivAt.const_add c : HasFDerivAt (fun y => c + L y) L y)
  have hpre : IsOpen (G ⁻¹' O) := hO.preimage hGc.continuous
  have hAc : ContDiffAt ℝ ∞ A x :=
    (hF.contDiffAt (hO.mem_nhds hx)).comp x hGc.contDiffAt
  have hAD : DifferentiableAt ℝ (fderiv ℝ A) x :=
    (hAc.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) (G x) :=
    ((hF.fderiv_of_isOpen hO (m := 1) (by simp)).contDiffAt
      (hO.mem_nhds hx)).differentiableAt (by simp)
  have hfun : (fun y => fderiv ℝ A y z) =ᶠ[𝓝 x]
      fun y => fderiv ℝ F (G y) (L z) := by
    filter_upwards [hpre.mem_nhds hx] with y hy
    change fderiv ℝ (F ∘ G) y z = _
    rw [fderiv_comp y ((hF.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp))
      (hGd y).differentiableAt, (hGd y).fderiv]
    rfl
  have hd := (hDF.hasFDerivAt.clm_apply (hasFDerivAt_const (L z) (G x))).comp x (hGd x)
  have he := congrArg (fun H => H v) hd.fderiv
  change fderiv ℝ (fun y => fderiv ℝ F (G y) (L z)) x v = _ at he
  rw [← hfun.fderiv_eq, fderiv_clm_apply hAD (differentiableAt_const z)] at he
  simpa [A, G] using he

/-- Exact identification of the amplitude Hessian with the actual full second derivative. -/
theorem ordinaryReduced_amplitude_hessian_eq (E : ℝ × (Fin 3 → ℝ) → ℝ)
    {O : Set (ℝ × (Fin 3 → ℝ))} (hO : IsOpen O) (hE : ContDiffOn ℝ ∞ E O)
    (p : ℝ × (Fin 3 → ℝ)) (hp : p ∈ O) (v z : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (fun y : ℝ × ℝ => E (p.1, ![y.1, y.2, p.2 2])))
      (p.2 0, p.2 1) v z =
      fderiv ℝ (fderiv ℝ E) p (ordinaryAmplitudeLift v) (ordinaryAmplitudeLift z) := by
  have hg : ∀ y : ℝ × ℝ,
      (p.1, ![0, 0, p.2 2]) + ordinaryAmplitudeLift y = (p.1, ![y.1, y.2, p.2 2]) := by
    intro y
    ext i <;> simp [ordinaryAmplitudeLift_apply]
  have hx : (p.1, ![0, 0, p.2 2]) + ordinaryAmplitudeLift (p.2 0, p.2 1) = p := by
    rw [hg]
    apply Prod.ext
    · rfl
    · ext i
      fin_cases i <;> rfl
  have hh := hessian_affine_comp E hO hE (p.1, ![0, 0, p.2 2]) ordinaryAmplitudeLift
    (p.2 0, p.2 1) v z (by rwa [hx])
  rw [hx] at hh
  simpa only [hg] using hh

private theorem hessian_Vp_amplitude (p w : Fin 3 → ℝ) (hw : w 2 = 0) :
    fderiv ℝ (fderiv ℝ Vp_STR02922) p w w =
      (HAA_STR02922 p * w 0 + HAB_STR02922 p * w 1) * w 0 +
      (HAB_STR02922 p * w 0 + HBB_STR02922 p * w 1) * w 1 := by
  have hVc : ContDiff ℝ ∞ Vp_STR02922 := by unfold Vp_STR02922; fun_prop
  have hDF : DifferentiableAt ℝ (fderiv ℝ Vp_STR02922) p :=
    ((hVc.fderiv_right (m := 1) (by simp)).differentiable (by simp)) p
  have hfun : ∀ q, fderiv ℝ Vp_STR02922 q w = dA_STR02922 q * w 0 + dB_STR02922 q * w 1 := by
    intro q
    rw [fderiv_Vp_STR02922, hw]
    ring
  have hline := ((hasDerivAt_dA_line_STR02922 p w).mul_const (w 0)).fun_add
    ((hasDerivAt_dB_line_STR02922 p w).mul_const (w 1))
  simp only [hw, mul_zero, sub_zero] at hline
  have hd : HasDerivAt (fun s : ℝ => fderiv ℝ Vp_STR02922 (p + s • w) w)
      ((HAA_STR02922 p * w 0 + HAB_STR02922 p * w 1) * w 0 +
        (HAB_STR02922 p * w 0 + HBB_STR02922 p * w 1) * w 1) 0 := by
    simpa only [hfun, Pi.add_apply] using hline
  have hEval := hDF.hasFDerivAt.clm_apply (hasFDerivAt_const w p)
  have he := congrArg (fun H => H w) hEval.fderiv
  have heq : fderiv ℝ (fun q => fderiv ℝ Vp_STR02922 q w) p w =
      fderiv ℝ (fderiv ℝ Vp_STR02922) p w w := by
    simpa using he
  rw [← heq]
  exact fderiv_line_STR02922 _ p w _ hEval.differentiableAt hd

private theorem zero_slice_amplitude_form (D : OrdinaryRootGraphData) (p : Fin 3 → ℝ) (v : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ D.reduced) (0, p) (ordinaryAmplitudeLift v) (ordinaryAmplitudeLift v) =
      (HAA_STR02922 p * v.1 + HAB_STR02922 p * v.2) * v.1 +
      (HAB_STR02922 p * v.1 + HBB_STR02922 p * v.2) * v.2 := by
  rw [← ordinaryReduced_amplitude_hessian_eq D.reduced D.openO D.smooth_reduced
    (0, p) (D.zero_memO p)]
  have hfun : (fun y : ℝ × ℝ => D.reduced (0, ![y.1, y.2, p 2])) =
      fun y : ℝ × ℝ => Vp_STR02922 (![0, 0, p 2] + ordinaryAmplitudeBlock y) := by
    funext y
    rw [D.reduced_zero, Vp_eq_STR02922]
    simp [ordinaryAmplitudeBlock_apply]
  rw [hfun]
  have hVc : ContDiff ℝ ∞ Vp_STR02922 := by unfold Vp_STR02922; fun_prop
  have hh := hessian_affine_comp Vp_STR02922 isOpen_univ hVc.contDiffOn
    (![0, 0, p 2] : Fin 3 → ℝ) ordinaryAmplitudeBlock (p 0, p 1) v v (Set.mem_univ _)
  have hp : (![0, 0, p 2] : Fin 3 → ℝ) + ordinaryAmplitudeBlock (p 0, p 1) = p := by
    ext i
    fin_cases i <;> simp
  rw [hh, hp, hessian_Vp_amplitude _ _ (by simp)]
  simp

noncomputable def ordinaryAmplitudeBasis (i : Fin 2) : ℝ × ℝ := ![(1, 0), (0, 1)] i

noncomputable def ordinaryAmplitudeEntry (E : ℝ × (Fin 3 → ℝ) → ℝ)
    (p : ℝ × (Fin 3 → ℝ)) (i j : Fin 2) : ℝ :=
  fderiv ℝ (fderiv ℝ E) p (ordinaryAmplitudeLift (ordinaryAmplitudeBasis i))
    (ordinaryAmplitudeLift (ordinaryAmplitudeBasis j))

private theorem amplitude_quadratic_entries (E : ℝ × (Fin 3 → ℝ) → ℝ)
    (p : ℝ × (Fin 3 → ℝ)) (v : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ E) p (ordinaryAmplitudeLift v) (ordinaryAmplitudeLift v) =
      ordinaryAmplitudeEntry E p 0 0 * v.1 ^ 2 +
      ordinaryAmplitudeEntry E p 0 1 * (v.1 * v.2) +
      ordinaryAmplitudeEntry E p 1 0 * (v.1 * v.2) +
      ordinaryAmplitudeEntry E p 1 1 * v.2 ^ 2 := by
  have hv : ordinaryAmplitudeLift v = v.1 • ordinaryAmplitudeLift (ordinaryAmplitudeBasis 0) +
      v.2 • ordinaryAmplitudeLift (ordinaryAmplitudeBasis 1) := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp [ordinaryAmplitudeBasis]
  rw [hv]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  unfold ordinaryAmplitudeEntry
  ring

private theorem amplitude_base_positive (D : OrdinaryRootGraphData) (j : Fin 3) (v : ℝ × ℝ) :
    (1 / 6 : ℝ) * (v.1 ^ 2 + v.2 ^ 2) ≤
      fderiv ℝ (fderiv ℝ D.reduced) (0, D.Z j 0)
        (ordinaryAmplitudeLift v) (ordinaryAmplitudeLift v) := by
  have hz : (0 : ℝ) ∈ Set.Ioo (-D.radius) D.radius := by
    constructor <;> linarith [D.radius_pos]
  have hb0 := D.Z_zero
  have hb1 : D.Z 1 0 = ![-1, Real.sqrt 3, -16 / 15] := by
    rw [(D.Z_rotation 0 hz).1, D.Z_zero, rotP0_STR02923]
  have hb2 : D.Z 2 0 = ![-1, -Real.sqrt 3, -16 / 15] := by
    rw [(D.Z_rotation 0 hz).2, (D.Z_rotation 0 hz).1, D.Z_zero, rotrotP0_STR02923]
  rw [zero_slice_amplitude_form]
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsy := congrArg (fun r : ℝ => r * v.2 ^ 2) hs
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl | rfl
  · rw [hb0]
    norm_num [HAA_STR02922, HAB_STR02922, HBB_STR02922]
    nlinarith [sq_nonneg v.2]
  · rw [hb1]
    norm_num [HAA_STR02922, HAB_STR02922, HBB_STR02922]
    nlinarith [sq_nonneg (v.1 + Real.sqrt 3 / 3 * v.2)]
  · rw [hb2]
    norm_num [HAA_STR02922, HAB_STR02922, HBB_STR02922]
    nlinarith [sq_nonneg (v.1 - Real.sqrt 3 / 3 * v.2)]

private theorem amplitude_perturb_lower (E : ℝ × (Fin 3 → ℝ) → ℝ)
    (p q : ℝ × (Fin 3 → ℝ)) (v : ℝ × ℝ)
    (hc : ∀ i j : Fin 2, |ordinaryAmplitudeEntry E p i j - ordinaryAmplitudeEntry E q i j| ≤ 1 / 24)
    (hb : (1 / 6 : ℝ) * (v.1 ^ 2 + v.2 ^ 2) ≤
      fderiv ℝ (fderiv ℝ E) q (ordinaryAmplitudeLift v) (ordinaryAmplitudeLift v)) :
    (1 / 12 : ℝ) * (v.1 ^ 2 + v.2 ^ 2) ≤
      fderiv ℝ (fderiv ℝ E) p (ordinaryAmplitudeLift v) (ordinaryAmplitudeLift v) := by
  have hm : ∀ a b t : ℝ, |a - b| ≤ 1 / 24 → b * t - (1 / 24 : ℝ) * |t| ≤ a * t := by
    intro a b t h
    have hh := mul_le_mul_of_nonneg_right h (abs_nonneg t)
    rw [← abs_mul] at hh
    have hl := (abs_le.mp hh).1
    nlinarith
  have h00 := hm _ _ (v.1 ^ 2) (hc 0 0)
  have h01 := hm _ _ (v.1 * v.2) (hc 0 1)
  have h10 := hm _ _ (v.1 * v.2) (hc 1 0)
  have h11 := hm _ _ (v.2 ^ 2) (hc 1 1)
  rw [abs_of_nonneg (sq_nonneg _)] at h00 h11
  have hxy : 2 * |v.1 * v.2| ≤ v.1 ^ 2 + v.2 ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|v.1| - |v.2|), sq_abs v.1, sq_abs v.2]
  rw [amplitude_quadratic_entries] at hb ⊢
  nlinarith

/-- One common parameter interval gives an actual positive amplitude Hessian for all
three retained branches, with h and the optimal-rate coordinate fixed in differentiation. -/
theorem ordinaryReduced_amplitude_hessian_positive (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, |h| < δ → ∀ j : Fin 3, ∀ v : ℝ × ℝ,
      (1 / 12 : ℝ) * (v.1 ^ 2 + v.2 ^ 2) ≤
        fderiv ℝ (fderiv ℝ (fun y : ℝ × ℝ => D.reduced (h, ![y.1, y.2, D.Z j h 2])))
          (D.Z j h 0, D.Z j h 1) v v := by
  have hDD : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ D.reduced)) D.O :=
    (D.smooth_reduced.fderiv_of_isOpen D.openO (m := ∞) (by simp)).fderiv_of_isOpen D.openO (m := ∞) (by simp)
  have hentry : ∀ j : Fin 3, ∀ i k : Fin 2,
      ContinuousAt (fun h => ordinaryAmplitudeEntry D.reduced (h, D.Z j h) i k) 0 := by
    intro j i k
    have hz : ContinuousAt (D.Z j) 0 :=
      (D.smoothZ j).continuousOn.continuousAt (Ioo_mem_nhds (by linarith [D.radius_pos]) D.radius_pos)
    have hc := hDD.continuousOn.continuousAt (D.openO.mem_nhds (D.zero_memO (D.Z j 0)))
    have he : ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
        fderiv ℝ (fderiv ℝ D.reduced) p
          (ordinaryAmplitudeLift (ordinaryAmplitudeBasis i))
          (ordinaryAmplitudeLift (ordinaryAmplitudeBasis k))) (0, D.Z j 0) :=
      (hc.clm_apply (continuousAt_const : ContinuousAt
        (fun _ : ℝ × (Fin 3 → ℝ) => ordinaryAmplitudeLift (ordinaryAmplitudeBasis i)) (0, D.Z j 0))).clm_apply
        (continuousAt_const : ContinuousAt
          (fun _ : ℝ × (Fin 3 → ℝ) => ordinaryAmplitudeLift (ordinaryAmplitudeBasis k)) (0, D.Z j 0))
    exact ContinuousAt.comp (f := fun h : ℝ => (h, D.Z j h)) he
      (continuousAt_id.prodMk hz)
  have hev : ∀ j : Fin 3, ∀ i k : Fin 2, ∀ᶠ h in 𝓝 (0 : ℝ),
      |ordinaryAmplitudeEntry D.reduced (h, D.Z j h) i k -
        ordinaryAmplitudeEntry D.reduced (0, D.Z j 0) i k| ≤ 1 / 24 := by
    intro j i k
    have hh := (hentry j i k).tendsto.eventually
      (Metric.ball_mem_nhds (ordinaryAmplitudeEntry D.reduced (0, D.Z j 0) i k)
        (by norm_num : (0 : ℝ) < 1 / 24))
    filter_upwards [hh] with h hh
    exact le_of_lt (by simpa only [Metric.mem_ball, Real.dist_eq] using hh)
  have hall : ∀ᶠ h in 𝓝 (0 : ℝ), ∀ j : Fin 3, ∀ i k : Fin 2,
      |ordinaryAmplitudeEntry D.reduced (h, D.Z j h) i k -
        ordinaryAmplitudeEntry D.reduced (0, D.Z j 0) i k| ≤ 1 / 24 :=
    Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun i => Filter.eventually_all.2 (hev j i)
  obtain ⟨ε, hε, hεall⟩ := Metric.eventually_nhds_iff.1 hall
  let δ := min ε D.radius
  refine ⟨δ, lt_min hε D.radius_pos, min_le_right _ _, fun h hh j v => ?_⟩
  have hhr : h ∈ Set.Ioo (-D.radius) D.radius :=
    abs_lt.mp (hh.trans_le (min_le_right _ _))
  rw [ordinaryReduced_amplitude_hessian_eq D.reduced D.openO D.smooth_reduced
    (h, D.Z j h) (D.branch_memO j h hhr)]
  apply amplitude_perturb_lower D.reduced (h, D.Z j h) (0, D.Z j 0) v
  · exact hεall (by rw [Real.dist_eq, sub_zero]; exact hh.trans_le (min_le_left _ _)) j
  · exact amplitude_base_positive D j v

end DGPS.Examples.ThreeSpeciesCircle
