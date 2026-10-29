import DGPS.Analysis.PeriodicMollification

/-!
# Same exponent Hölder convergence with an intermediate exponent (SEM003)

Lemma-DAG node SEM003
(`DGPS.Analysis.PeriodicMollification.same_exponent_holder_convergence_with_an_intermediate_exponent`).

For `g` on the circle `Torus 1` with `[g]_β < ∞` (`0 < α < β < 1`) and `0 < h < 1/4`, the
mollification `g_h = φ_h * g` (`mollify h g`) satisfies
`‖g_h - g‖_∞ ≤ [g]_β h^β`, `[g_h]_β ≤ [g]_β`, `[g_h - g]_α ≤ 2 [g]_β h^(β-α)` and
`‖g_h - g‖_{C^α} ≤ 3 [g]_β h^(β-α) → 0` as `h → 0+`.

Hölder quantities on the circle are measured with the Euclidean quotient distance
`DGPS.torusDist`; `‖g‖_{C^α} = ‖g‖_∞ + [g]_α`.

R5 notes:
* Placement: this module (importing SEM002's `DGPS.Analysis.PeriodicMollification`) instead of the
  planned `DGPS/Analysis/PeriodicMollification.lean`, which another worker edits; the interface
  name and namespace are unchanged.
* The circle Hölder seminorm, sup norm and `C^α` norm are defined here
  (`torusHolderSeminorm`, `torusSupNorm`, `torusHolderNorm`), mirroring the real-line
  `holderSeminorm`/`supNorm`/`phNorm` of FOU017; finiteness of `[g]_β` is the hypothesis
  `TorusHolderBdd β g`.
* The RUF004 upstream is not needed for the proof: SEM003 is a statement for arbitrary `g`
  with `[g]_β < ∞` (RUF004 supplies this for the rough primitive for the downstream consumers).
-/

open MeasureTheory Set Filter Topology

namespace DGPS.Analysis.PeriodicMollification

/-! ### Hölder quantities on the circle -/

/-- `g` is `β`-Hölder on the circle with some finite constant. -/
def TorusHolderBdd (β : ℝ) (g : Torus 1 → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, |g x - g y| ≤ C * DGPS.torusDist x y ^ β

/-- The Hölder seminorm `[g]_β = sup_{x ≠ y} |g x - g y| / d(x,y)^β` on the circle (junk if
unbounded). -/
noncomputable def torusHolderSeminorm (β : ℝ) (g : Torus 1 → ℝ) : ℝ :=
  ⨆ p : Torus 1 × Torus 1, |g p.1 - g p.2| / DGPS.torusDist p.1 p.2 ^ β

/-- The sup norm `‖g‖_∞` on the circle. -/
noncomputable def torusSupNorm (g : Torus 1 → ℝ) : ℝ := ⨆ x, |g x|

/-- The Hölder norm `‖g‖_{C^α} = ‖g‖_∞ + [g]_α` on the circle. -/
noncomputable def torusHolderNorm (α : ℝ) (g : Torus 1 → ℝ) : ℝ :=
  torusSupNorm g + torusHolderSeminorm α g

theorem torusDist_nonneg (x y : Torus 1) : 0 ≤ DGPS.torusDist x y := Real.sqrt_nonneg _

theorem torusDist_self (x : Torus 1) : DGPS.torusDist x x = 0 :=
  (DGPS.torusDist_metric.1 x)

theorem torusHolderSeminorm_nonneg (β : ℝ) (g : Torus 1 → ℝ) : 0 ≤ torusHolderSeminorm β g :=
  Real.iSup_nonneg fun _ =>
    div_nonneg (abs_nonneg _) (Real.rpow_nonneg (torusDist_nonneg _ _) _)

theorem torusSupNorm_nonneg (g : Torus 1 → ℝ) : 0 ≤ torusSupNorm g :=
  Real.iSup_nonneg fun _ => abs_nonneg _

theorem torusHolderNorm_nonneg (α : ℝ) (g : Torus 1 → ℝ) : 0 ≤ torusHolderNorm α g :=
  add_nonneg (torusSupNorm_nonneg _) (torusHolderSeminorm_nonneg _ _)

theorem torusHolderSeminorm_le {β : ℝ} {g : Torus 1 → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y, |g x - g y| ≤ C * DGPS.torusDist x y ^ β) : torusHolderSeminorm β g ≤ C := by
  refine ciSup_le fun p => ?_
  by_cases hp : DGPS.torusDist p.1 p.2 = 0
  · by_cases hβ : β = 0
    · subst hβ
      rw [hp, Real.rpow_zero, div_one]
      have := h p.1 p.2
      rwa [Real.rpow_zero, mul_one] at this
    · rw [hp, Real.zero_rpow hβ, div_zero]
      exact hC
  · have hpos : 0 < DGPS.torusDist p.1 p.2 ^ β :=
      Real.rpow_pos_of_pos (lt_of_le_of_ne (torusDist_nonneg _ _) (Ne.symm hp)) _
    rw [div_le_iff₀ hpos]
    exact h _ _

theorem torusSupNorm_le {g : Torus 1 → ℝ} {M : ℝ} (h : ∀ x, |g x| ≤ M) : torusSupNorm g ≤ M :=
  ciSup_le h

/-- The pair bound by the seminorm. -/
theorem TorusHolderBdd.abs_sub_le {β : ℝ} {g : Torus 1 → ℝ} (hg : TorusHolderBdd β g)
    (x y : Torus 1) :
    |g x - g y| ≤ torusHolderSeminorm β g * DGPS.torusDist x y ^ β := by
  obtain ⟨C, hC0, hC⟩ := hg
  by_cases hd : DGPS.torusDist x y = 0
  · have hxy : x = y := DGPS.torusDist_metric.2.2.2.1 x y hd
    subst hxy
    rw [sub_self, abs_zero]
    exact mul_nonneg (torusHolderSeminorm_nonneg _ _) (Real.rpow_nonneg (torusDist_nonneg _ _) _)
  · have hpos : 0 < DGPS.torusDist x y ^ β :=
      Real.rpow_pos_of_pos (lt_of_le_of_ne (torusDist_nonneg _ _) (Ne.symm hd)) _
    have hbdd : BddAbove (range fun p : Torus 1 × Torus 1 =>
        |g p.1 - g p.2| / DGPS.torusDist p.1 p.2 ^ β) := by
      refine ⟨C, ?_⟩
      rintro _ ⟨p, rfl⟩
      by_cases hp : DGPS.torusDist p.1 p.2 = 0
      · have hxy : p.1 = p.2 := DGPS.torusDist_metric.2.2.2.1 _ _ hp
        have : |g p.1 - g p.2| = 0 := by rw [hxy]; simp
        simp only [this, zero_div]; exact hC0
      · have hp' : 0 < DGPS.torusDist p.1 p.2 ^ β :=
          Real.rpow_pos_of_pos (lt_of_le_of_ne (torusDist_nonneg _ _) (Ne.symm hp)) _
        rw [div_le_iff₀ hp']
        exact hC _ _
    have := le_ciSup hbdd (x, y)
    simp only at this
    rwa [div_le_iff₀ hpos] at this

theorem TorusHolderBdd.seminorm_nonneg {β : ℝ} {g : Torus 1 → ℝ} (_hg : TorusHolderBdd β g) :
    0 ≤ torusHolderSeminorm β g := torusHolderSeminorm_nonneg _ _

/-! ### Geometry of the quotient distance -/

theorem exists_pt_eq (y : Torus 1) : ∃ t : ℝ, y = pt t := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (y 0)
  refine ⟨t, ?_⟩
  funext i
  fin_cases i
  exact ht.symm

theorem torusDist_pt_le (a b : ℝ) : DGPS.torusDist (pt a) (pt b) ≤ |a - b| := by
  have := DGPS.torusDist_liftT_le (d := 1) (fun _ => a) (fun _ => b)
  simpa [Real.sqrt_sq_eq_abs] using this

theorem torusDist_sub_pt_le (y : Torus 1) (s : ℝ) : DGPS.torusDist (y - pt s) y ≤ |s| := by
  obtain ⟨t, rfl⟩ := exists_pt_eq y
  have h1 : pt t - pt s = pt (t - s) := by
    funext i
    simp [pt, DGPS.torusLift, SharpLSI.liftT]
  rw [h1]
  refine (torusDist_pt_le _ _).trans ?_
  simp

theorem torusDist_sub_right (x y z : Torus 1) :
    DGPS.torusDist (x - z) (y - z) = DGPS.torusDist x y := by
  unfold DGPS.torusDist SharpLSI.flatDist
  simp [sub_sub_sub_cancel_right]

/-! ### Continuity and integrability -/

theorem continuous_of_holderBdd {β : ℝ} (hβ : 0 < β) {g : Torus 1 → ℝ}
    (hg : TorusHolderBdd β g) : Continuous g := by
  obtain ⟨C, hC0, hC⟩ := hg
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, (Metric.nhds_basis_closedBall).tendsto_right_iff]
  intro ε hε
  have hbasis := (DGPS.torusDist_metric.2.2.2.2 x)
  have hδ : 0 < (ε / (C + 1)) ^ (1 / β) := by positivity
  have hmem : {y | DGPS.torusDist x y < (ε / (C + 1)) ^ (1 / β)} ∈ 𝓝 x :=
    hbasis.mem_of_mem hδ
  filter_upwards [hmem] with y hy
  rw [Metric.mem_closedBall, Real.dist_eq]
  have hd0 := torusDist_nonneg x y
  have h1 : DGPS.torusDist x y ^ β ≤ ((ε / (C + 1)) ^ (1 / β)) ^ β :=
    Real.rpow_le_rpow hd0 hy.le hβ.le
  rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hβ.ne', Real.rpow_one] at h1
  have h2 := hC y x
  have h3 : DGPS.torusDist y x = DGPS.torusDist x y := DGPS.torusDist_metric.2.1 y x
  rw [h3] at h2
  calc |g y - g x| ≤ C * DGPS.torusDist x y ^ β := h2
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left h1 hC0
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

theorem holder_integrable_phiH_mul {h : ℝ} (hh : 0 < h) {g : Torus 1 → ℝ} (hg : Continuous g)
    (y : Torus 1) : Integrable (fun s : ℝ => phiH h s * g (y - pt s)) := by
  have hc : Continuous (fun s : ℝ => phiH h s * g (y - pt s)) := by
    have hpt : Continuous (pt : ℝ → Torus 1) := by
      unfold pt DGPS.torusLift SharpLSI.liftT
      fun_prop
    exact (contDiff_phiH hh).continuous.mul (hg.comp (continuous_const.sub hpt))
  refine Continuous.integrable_of_hasCompactSupport hc ?_
  exact (hasCompactSupport_phiH hh).mul_right

/-! ### The core estimates -/

theorem abs_integral_phiH_mul_le {h : ℝ} (hh : 0 < h) {F : ℝ → ℝ} {M : ℝ}
    (hM : ∀ s, phiH h s ≠ 0 → |F s| ≤ M) : |∫ s, phiH h s * F s| ≤ M := by
  have hint : Integrable (fun s => phiH h s * M) := (integrable_phiH hh).mul_const M
  have := norm_integral_le_of_norm_le hint (f := fun s => phiH h s * F s) (Eventually.of_forall
    fun s => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (phiH_nonneg hh s)]
      by_cases h0 : phiH h s = 0
      · simp [h0]
      · exact mul_le_mul_of_nonneg_left (hM s h0) (phiH_nonneg hh s))
  rw [integral_mul_const, integral_phiH hh, one_mul] at this
  simpa [Real.norm_eq_abs] using this

theorem abs_phiH_support_le {h : ℝ} (hh : 0 < h) {s : ℝ} (hs : phiH h s ≠ 0) : |s| ≤ h := by
  have := phiH_support hh (Function.mem_support.2 hs)
  exact abs_le.2 ⟨(mem_Icc.1 this).1, (mem_Icc.1 this).2⟩

variable {β : ℝ} {K h : ℝ} {g : Torus 1 → ℝ}

/-- The mollification does not increase the Hölder constant. -/
theorem abs_mollify_sub_le (hh : 0 < h) (hg : Continuous g)
    (hK : ∀ x y, |g x - g y| ≤ K * DGPS.torusDist x y ^ β) (x y : Torus 1) :
    |mollify h g x - mollify h g y| ≤ K * DGPS.torusDist x y ^ β := by
  have e : mollify h g x - mollify h g y =
      ∫ s, phiH h s * (g (x - pt s) - g (y - pt s)) := by
    unfold mollify
    rw [← integral_sub (holder_integrable_phiH_mul hh hg x) (holder_integrable_phiH_mul hh hg y)]
    congr 1; funext s; ring
  rw [e]
  refine abs_integral_phiH_mul_le hh fun s _ => ?_
  refine (hK _ _).trans (le_of_eq ?_)
  rw [torusDist_sub_right]

/-- The sup-norm bound `|g_h y - g y| ≤ K h^β`. -/
theorem abs_mollify_sub_self_le (hh : 0 < h) (hg : Continuous g) (hK0 : 0 ≤ K) (hβ : 0 ≤ β)
    (hK : ∀ x y, |g x - g y| ≤ K * DGPS.torusDist x y ^ β) (y : Torus 1) :
    |mollify h g y - g y| ≤ K * h ^ β := by
  have e : mollify h g y - g y = ∫ s, phiH h s * (g (y - pt s) - g y) := by
    have h1 : ∫ s, phiH h s * g y = g y := by
      rw [integral_mul_const, integral_phiH hh, one_mul]
    unfold mollify
    conv_lhs => rw [← h1]
    rw [← integral_sub (holder_integrable_phiH_mul hh hg y) ((integrable_phiH hh).mul_const _)]
    congr 1; funext s; ring
  rw [e]
  refine abs_integral_phiH_mul_le hh fun s hs => ?_
  have hs' := abs_phiH_support_le hh hs
  refine (hK _ _).trans (mul_le_mul_of_nonneg_left ?_ hK0)
  exact Real.rpow_le_rpow (torusDist_nonneg _ _) ((torusDist_sub_pt_le y s).trans hs') hβ

/-- Seminorm bound for the difference `g_h - g` at the same exponent `α < β`. -/
theorem abs_sub_mollify_sub_le {α : ℝ} (hα : 0 < α) (hαβ : α < β) (hh : 0 < h) (hg : Continuous g)
    (hK0 : 0 ≤ K) (hK : ∀ x y, |g x - g y| ≤ K * DGPS.torusDist x y ^ β) (x y : Torus 1) :
    |(mollify h g x - g x) - (mollify h g y - g y)| ≤
      2 * K * h ^ (β - α) * DGPS.torusDist x y ^ α := by
  have hβ : 0 ≤ β := by linarith
  set d := DGPS.torusDist x y with hd
  have hd0 : 0 ≤ d := torusDist_nonneg _ _
  have hba : 0 < β - α := by linarith
  rcases le_or_gt d h with hdh | hdh
  · have h1 := abs_mollify_sub_le hh hg hK x y
    have h2 := hK x y
    have : |(mollify h g x - g x) - (mollify h g y - g y)| ≤
        |mollify h g x - mollify h g y| + |g x - g y| := by
      have := abs_sub (mollify h g x - mollify h g y) (g x - g y)
      calc _ = |(mollify h g x - mollify h g y) - (g x - g y)| := by ring_nf
        _ ≤ _ := this
    have hsplit : d ^ β = d ^ α * d ^ (β - α) := by
      rw [← Real.rpow_add' hd0 (by linarith)]; ring_nf
    have hle : d ^ (β - α) ≤ h ^ (β - α) := Real.rpow_le_rpow hd0 hdh hba.le
    calc _ ≤ K * d ^ β + K * d ^ β := this.trans (add_le_add h1 h2)
      _ = 2 * K * (d ^ α * d ^ (β - α)) := by rw [hsplit]; ring
      _ ≤ 2 * K * (d ^ α * h ^ (β - α)) := by
          gcongr
      _ = _ := by ring
  · have h1 := abs_mollify_sub_self_le hh hg hK0 hβ hK x
    have h2 := abs_mollify_sub_self_le hh hg hK0 hβ hK y
    have hsplit : h ^ β = h ^ α * h ^ (β - α) := by
      rw [← Real.rpow_add' hh.le (by linarith)]; ring_nf
    have hle : h ^ α ≤ d ^ α := Real.rpow_le_rpow hh.le hdh.le hα.le
    calc |(mollify h g x - g x) - (mollify h g y - g y)|
        ≤ |mollify h g x - g x| + |mollify h g y - g y| := abs_sub _ _
      _ ≤ K * h ^ β + K * h ^ β := add_le_add h1 h2
      _ = 2 * K * (h ^ α * h ^ (β - α)) := by rw [hsplit]; ring
      _ ≤ 2 * K * (d ^ α * h ^ (β - α)) := by gcongr
      _ = _ := by ring

/-! ### The SEM003 statement -/

/-- **SEM003.** Fix `0 < α < 1` and `α < β < 1`, and a circle function `g` with `[g]_β < ∞`.
For `0 < h < 1/4`: `‖g_h - g‖_∞ ≤ [g]_β h^β`, `[g_h]_β ≤ [g]_β`,
`[g_h - g]_α ≤ 2 [g]_β h^(β-α)` and `‖g_h - g‖_{C^α} ≤ 3 [g]_β h^(β-α)`; moreover
`‖g_h - g‖_{C^α} → 0` as `h → 0+`. -/
theorem same_exponent_holder_convergence_with_an_intermediate_exponent
    {α β : ℝ} (hα0 : 0 < α) (hαβ : α < β) (_hβ1 : β < 1) {g : Torus 1 → ℝ}
    (hg : TorusHolderBdd β g) :
    (∀ h : ℝ, 0 < h → h < 1 / 4 →
      torusSupNorm (fun y => mollify h g y - g y) ≤ torusHolderSeminorm β g * h ^ β ∧
      torusHolderSeminorm β (mollify h g) ≤ torusHolderSeminorm β g ∧
      torusHolderSeminorm α (fun y => mollify h g y - g y) ≤
        2 * torusHolderSeminorm β g * h ^ (β - α) ∧
      torusHolderNorm α (fun y => mollify h g y - g y) ≤
        3 * torusHolderSeminorm β g * h ^ (β - α)) ∧
    Tendsto (fun h : ℝ => torusHolderNorm α (fun y => mollify h g y - g y)) (𝓝[>] 0) (𝓝 0) := by
  have hβ0 : 0 < β := hα0.trans hαβ
  have hcont := continuous_of_holderBdd hβ0 hg
  set K := torusHolderSeminorm β g with hKdef
  have hK0 : 0 ≤ K := torusHolderSeminorm_nonneg _ _
  have hK : ∀ x y, |g x - g y| ≤ K * DGPS.torusDist x y ^ β := hg.abs_sub_le
  have hba : 0 < β - α := by linarith
  have main : ∀ h : ℝ, 0 < h → h < 1 / 4 →
      torusSupNorm (fun y => mollify h g y - g y) ≤ K * h ^ β ∧
      torusHolderSeminorm β (mollify h g) ≤ K ∧
      torusHolderSeminorm α (fun y => mollify h g y - g y) ≤ 2 * K * h ^ (β - α) ∧
      torusHolderNorm α (fun y => mollify h g y - g y) ≤ 3 * K * h ^ (β - α) := by
    intro h hh hh4
    have hsup : torusSupNorm (fun y => mollify h g y - g y) ≤ K * h ^ β :=
      torusSupNorm_le fun y => abs_mollify_sub_self_le hh hcont hK0 hβ0.le hK y
    have hsemi : torusHolderSeminorm β (mollify h g) ≤ K :=
      torusHolderSeminorm_le hK0 fun x y => abs_mollify_sub_le hh hcont hK x y
    have hdiff : torusHolderSeminorm α (fun y => mollify h g y - g y) ≤ 2 * K * h ^ (β - α) :=
      torusHolderSeminorm_le (by positivity) fun x y =>
        abs_sub_mollify_sub_le hα0 hαβ hh hcont hK0 hK x y
    refine ⟨hsup, hsemi, hdiff, ?_⟩
    have hh1 : h < 1 := by linarith
    have hpow : h ^ β ≤ h ^ (β - α) := Real.rpow_le_rpow_of_exponent_ge hh hh1.le (by linarith)
    unfold torusHolderNorm
    calc _ ≤ K * h ^ β + 2 * K * h ^ (β - α) := add_le_add hsup hdiff
      _ ≤ K * h ^ (β - α) + 2 * K * h ^ (β - α) := by gcongr
      _ = _ := by ring
  refine ⟨fun h hh hh4 => ?_, ?_⟩
  · exact main h hh hh4
  · have hlim : Tendsto (fun h : ℝ => 3 * K * h ^ (β - α)) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun h : ℝ => h ^ (β - α)) (𝓝 0) (𝓝 0) := by
        have := (Real.continuousAt_rpow_const 0 (β - α) (Or.inr hba.le)).tendsto
        rwa [Real.zero_rpow hba.ne'] at this
      simpa using (h1.mono_left nhdsWithin_le_nhds).const_mul (3 * K)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · exact Eventually.of_forall fun h => torusHolderNorm_nonneg _ _
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with h hh
      exact (main h hh.1 hh.2).2.2.2

end DGPS.Analysis.PeriodicMollification
