import SharpSymmetricLSI.Paper.Defective5

/-!
# R03 (Proposition 2.2), part 6: explicit conditional densities

For `ν = Q · Leb` on `(𝕋^d)^N` with `c ≤ Q ≤ C` (`c > 0`) and `j < N`:
`margQ p x = ∫ Q(p, x, z) dz` (integrating out the particles after `j`), `Zc p = ∫ margQ p x dx`,
`condDens p = margQ p · / Zc p`. The law of `(past, X_j)` is `(law of past) ⊗ condDens`, hence
`ρ_j(p) = condNext ν j p = condDens p · haar` for a.e. `p` (`condNext_ae_eq`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace SharpLSI

variable {d N : ℕ}

section assemble
variable {j : ℕ} (hj : j < N)

/-- Assemble a configuration from the past, the particle `j` and the rest. -/
def assemble (p : Config j d) (x : Torus d) (z : Config (N - j - 1) d) : Config N d :=
  unflat (reidx (blockIdx j hj) (join (join (flat p) x) (flat z)))

theorem assemble_eq (X : Config N d) :
    assemble hj (past j hj.le X) (X ⟨j, hj⟩) (restC j hj X) = X := by
  unfold assemble
  rw [← reidx_symm_flat]
  funext i k
  simp [reidx, unflat, flat]

theorem past_assemble (p : Config j d) (x : Torus d) (z : Config (N - j - 1) d) :
    past j hj.le (assemble hj p x z) = p := by
  funext i k
  have hi : (Fin.castLE hj.le i).val < j := by simp
  simp [past, assemble, unflat, reidx, blockIdx, hi, join, flat]

theorem cur_assemble (p : Config j d) (x : Torus d) (z : Config (N - j - 1) d) :
    assemble hj p x z ⟨j, hj⟩ = x :=
  flat_reidx_join j hj p x z

theorem measurable_assemble :
    Measurable (fun q : (Config j d × Torus d) × Config (N - j - 1) d =>
      assemble hj q.1.1 q.1.2 q.2) := by
  unfold assemble
  refine measurable_unflat.comp ((measurePreserving_reidx_torus _).measurable.comp ?_)
  exact measurable_join.comp ((measurable_join.comp ((measurable_flat.comp
    (measurable_fst.comp measurable_fst)).prodMk (measurable_snd.comp measurable_fst))).prodMk
    (measurable_flat.comp measurable_snd))

theorem measurePreserving_flat' (n : ℕ) :
    MeasurePreserving (flat : Config n d → UnitAddTorus (Fin n × Fin d)) volume volume :=
  ⟨measurable_flat, map_flat_volume n⟩

theorem measurePreserving_unflat (n : ℕ) :
    MeasurePreserving (unflat : UnitAddTorus (Fin n × Fin d) → Config n d) volume volume := by
  refine ⟨measurable_unflat, ?_⟩
  conv_lhs => rw [← map_flat_volume n]
  rw [Measure.map_map measurable_unflat measurable_flat]
  exact Measure.map_id

theorem measurePreserving_assemble :
    MeasurePreserving (fun q : (Config j d × Torus d) × Config (N - j - 1) d =>
      assemble hj q.1.1 q.1.2 q.2)
      (((volume : Measure (Config j d)).prod (volume : Measure (Torus d))).prod volume) volume := by
  have h0 : MeasurePreserving (fun q : Config j d × Torus d => (flat q.1, q.2))
      ((volume : Measure (Config j d)).prod (volume : Measure (Torus d))) volume :=
    MeasurePreserving.prod (μa := (volume : Measure (Config j d))) (μc := (volume : Measure (Torus d)))
      (measurePreserving_flat' j) (MeasurePreserving.id (volume : Measure (Torus d)))
  have h1 : MeasurePreserving (fun q : (Config j d × Torus d) × Config (N - j - 1) d =>
      ((flat q.1.1, q.1.2), flat q.2))
      (((volume : Measure (Config j d)).prod (volume : Measure (Torus d))).prod volume) volume :=
    MeasurePreserving.prod h0 (measurePreserving_flat' (N - j - 1))
  have h2 := (measurePreserving_join (α := Fin j × Fin d) (β := Fin d)).prod
    (MeasurePreserving.id (volume : Measure (UnitAddTorus (Fin (N - j - 1) × Fin d))))
  have h3 := measurePreserving_join (α := (Fin j × Fin d) ⊕ Fin d) (β := Fin (N - j - 1) × Fin d)
  have h4 := measurePreserving_reidx_torus (blockIdx (d := d) j hj)
  have h5 := measurePreserving_unflat (d := d) N
  exact (h5.comp (h4.comp (h3.comp (h2.comp h1))))

end assemble

section dens
variable {j : ℕ} (hj : j < N) {Q : Config N d → ℝ}

/-- The marginal density of `(past, X_j)`. -/
noncomputable def margQ (Q : Config N d → ℝ) (p : Config j d) (x : Torus d) : ℝ :=
  ∫ z, Q (assemble hj p x z) ∂(volume : Measure (Config (N - j - 1) d))

/-- The marginal density of the past. -/
noncomputable def Zc (Q : Config N d → ℝ) (p : Config j d) : ℝ :=
  ∫ x, margQ hj Q p x ∂haar d

/-- The conditional density of `X_j` given the past. -/
noncomputable def condDens (Q : Config N d → ℝ) (p : Config j d) (x : Torus d) : ℝ :=
  margQ hj Q p x / Zc hj Q p

variable (hQm : Measurable Q) {c C : ℝ} (hc : 0 < c) (hQc : ∀ X, c ≤ Q X) (hQC : ∀ X, Q X ≤ C)

include hQm in
theorem measurable_Q_assemble :
    Measurable (fun q : (Config j d × Torus d) × Config (N - j - 1) d =>
      Q (assemble hj q.1.1 q.1.2 q.2)) :=
  hQm.comp (measurable_assemble hj)

include hQm in
theorem measurable_margQ : Measurable (Function.uncurry (margQ hj Q)) :=
  (measurable_Q_assemble hj hQm).stronglyMeasurable.integral_prod_right'.measurable

include hQm in
theorem measurable_Zc : Measurable (Zc (d := d) hj Q) :=
  (measurable_margQ hj hQm).stronglyMeasurable.integral_prod_right'.measurable

include hQm hQc hQC in
theorem margQ_bounds (p : Config j d) (x : Torus d) : c ≤ margQ hj Q p x ∧ margQ hj Q p x ≤ C :=
  integral_mem_Icc (ρ := (volume : Measure (Config (N - j - 1) d)))
    (f := fun z => Q (assemble hj p x z)) ((hQm.comp ((measurable_assemble hj).comp
    ((measurable_const (a := (p, x))).prodMk measurable_id))).aestronglyMeasurable)
    (fun z => hQc _) (fun z => hQC _)

include hQm hQc hQC in
theorem Zc_bounds (p : Config j d) : c ≤ Zc hj Q p ∧ Zc hj Q p ≤ C :=
  integral_mem_Icc ((measurable_margQ hj hQm).comp (measurable_const.prodMk measurable_id)
    |>.aestronglyMeasurable) (fun x => (margQ_bounds hj hQm hQc hQC p x).1)
    (fun x => (margQ_bounds hj hQm hQc hQC p x).2)

include hQm hc hQc hQC in
theorem condDens_bounds (p : Config j d) (x : Torus d) :
    c / C ≤ condDens hj Q p x ∧ condDens hj Q p x ≤ C / c := by
  obtain ⟨h1, h2⟩ := margQ_bounds hj hQm hQc hQC p x
  obtain ⟨h3, h4⟩ := Zc_bounds hj hQm hQc hQC p
  have hC : 0 < C := hc.trans_le (h1.trans h2)
  unfold condDens
  constructor
  · exact div_le_div₀ (hc.trans_le h1).le h1 (hc.trans_le h3) h4
  · exact div_le_div₀ hC.le h2 hc h3

include hQm hc hQc hQC in
theorem integral_condDens (p : Config j d) : ∫ x, condDens hj Q p x ∂haar d = 1 := by
  unfold condDens
  rw [integral_div]
  exact div_self (hc.trans_le (Zc_bounds hj hQm hQc hQC p).1).ne'

include hQm in
theorem measurable_condDens : Measurable (Function.uncurry (condDens (d := d) hj Q)) :=
  (measurable_margQ hj hQm).div ((measurable_Zc hj hQm).comp measurable_fst)

/-- The conditional kernel. -/
noncomputable def condKer (Q : Config N d → ℝ) : Kernel (Config j d) (Torus d) :=
  Kernel.withDensity (Kernel.const _ (haar d)) (fun p x => ENNReal.ofReal (condDens hj Q p x))

include hQm in
theorem condKer_apply (p : Config j d) : condKer hj Q p = densMeasure (condDens hj Q p) := by
  unfold condKer
  rw [Kernel.withDensity_apply (f := fun p x => ENNReal.ofReal (condDens hj Q p x)) _
    (ENNReal.measurable_ofReal.comp (measurable_condDens hj hQm) :
      Measurable fun q : Config j d × Torus d => ENNReal.ofReal (condDens hj Q q.1 q.2)),
    Kernel.const_apply]
  rfl

include hQm hc hQc hQC in
theorem isMarkovKernel_condKer : IsMarkovKernel (condKer hj Q) := by
  refine ⟨fun p => ?_⟩
  rw [condKer_apply hj hQm]
  exact isProbabilityMeasure_densMeasure' (fun x => le_trans (div_pos hc (hc.trans_le
      ((hQc (Classical.arbitrary _)).trans (hQC _)))).le (condDens_bounds hj hQm hc hQc hQC p x).1)
    (integral_condDens hj hQm hc hQc hQC p)

include hQm hc hQc hQC in
/-- **The basic disintegration identity.** -/
theorem lintegral_pastCur {F : Config j d → Torus d → ℝ≥0∞} (hF : Measurable (Function.uncurry F)) :
    ∫⁻ X, F (past j hj.le X) (X ⟨j, hj⟩) * ENNReal.ofReal (Q X) =
      ∫⁻ p, ∫⁻ x, F p x * ENNReal.ofReal (margQ hj Q p x) ∂haar d := by
  have hG : Measurable fun X : Config N d => F (past j hj.le X) (X ⟨j, hj⟩) * ENNReal.ofReal (Q X) :=
    (hF.comp ((measurable_past hj.le).prodMk (measurable_pi_apply _))).mul
      (ENNReal.measurable_ofReal.comp hQm)
  rw [← (measurePreserving_assemble hj).lintegral_comp hG]
  simp only [past_assemble, cur_assemble]
  have hm := measurable_Q_assemble hj hQm
  rw [lintegral_prod (fun a : (Config j d × Torus d) × Config (N - j - 1) d =>
    F a.1.1 a.1.2 * ENNReal.ofReal (Q (assemble hj a.1.1 a.1.2 a.2)))
    ((hF.comp measurable_fst).mul (ENNReal.measurable_ofReal.comp hm)).aemeasurable]
  have hin : ∀ q : Config j d × Torus d, ∫⁻ z, F q.1 q.2 * ENNReal.ofReal (Q (assemble hj q.1 q.2 z))
      ∂(volume : Measure (Config (N - j - 1) d)) = F q.1 q.2 * ENNReal.ofReal (margQ hj Q q.1 q.2) := by
    intro q
    have hzm : Measurable fun z : Config (N - j - 1) d => Q (assemble hj q.1 q.2 z) :=
      hm.comp ((measurable_const (a := q)).prodMk measurable_id)
    rw [lintegral_const_mul (F q.1 q.2) (f := fun z => ENNReal.ofReal (Q (assemble hj q.1 q.2 z)))
      (ENNReal.measurable_ofReal.comp hzm), margQ, ofReal_integral_eq_lintegral_ofReal]
    · exact Integrable.of_bound hzm.aestronglyMeasurable
        (|c| + |C|) (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_le]
          constructor <;> linarith [hQc (assemble hj q.1 q.2 z), hQC (assemble hj q.1 q.2 z),
            abs_nonneg c, abs_nonneg C, le_abs_self c, le_abs_self C, neg_abs_le c])
    · exact Eventually.of_forall fun z => hc.le.trans (hQc _)
  rw [lintegral_congr hin]
  exact lintegral_prod (fun q : Config j d × Torus d => F q.1 q.2 * ENNReal.ofReal (margQ hj Q q.1 q.2))
    (hF.mul (ENNReal.measurable_ofReal.comp (measurable_margQ hj hQm))).aemeasurable

include hQm hc hQc hQC in
theorem map_past_eq :
    ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Q X)).map (past j hj.le) =
      (volume : Measure (Config j d)).withDensity fun p => ENNReal.ofReal (Zc hj Q p) := by
  ext s hs
  rw [Measure.map_apply (measurable_past hj.le) hs, withDensity_apply _ (measurable_past hj.le hs),
    withDensity_apply _ hs, ← lintegral_indicator (measurable_past hj.le hs),
    ← lintegral_indicator hs]
  have h := lintegral_pastCur hj hQm hc hQc hQC (F := fun p _ => s.indicator 1 p)
    ((measurable_const.indicator hs).comp measurable_fst)
  have e1 : ∀ X, (past j hj.le ⁻¹' s).indicator (fun X => ENNReal.ofReal (Q X)) X =
      s.indicator 1 (past j hj.le X) * ENNReal.ofReal (Q X) := fun X => by
    by_cases hX : past j hj.le X ∈ s
    · simp [Set.indicator_of_mem, hX]
    · simp [Set.indicator_of_notMem, hX]
  simp_rw [e1, h]
  refine lintegral_congr fun p => ?_
  by_cases hp : p ∈ s
  · simp only [Set.indicator_of_mem hp, Pi.one_apply, one_mul]
    rw [Zc, ofReal_integral_eq_lintegral_ofReal]
    · exact Integrable.of_bound ((measurable_margQ hj hQm).comp (measurable_const.prodMk
        measurable_id) |>.aestronglyMeasurable) C (Eventually.of_forall fun x => by
          have := margQ_bounds hj hQm hQc hQC p x
          rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
    · exact Eventually.of_forall fun x => hc.le.trans (margQ_bounds hj hQm hQc hQC p x).1
  · simp [Set.indicator_of_notMem hp]

include hQm hc hQc hQC in
theorem map_pastCur_eq [IsFiniteMeasure ((volume : Measure (Config N d)).withDensity
      fun X => ENNReal.ofReal (Q X))] :
    ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Q X)).map
        (fun X => (past j hj.le X, X ⟨j, hj⟩)) =
      (((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Q X)).map
        (past j hj.le)) ⊗ₘ condKer hj Q := by
  haveI := isMarkovKernel_condKer hj hQm hc hQc hQC
  have hpc : Measurable fun X : Config N d => (past j hj.le X, X ⟨j, hj⟩) :=
    (measurable_past hj.le).prodMk (measurable_pi_apply _)
  refine Measure.ext_prod fun {s t} hs ht => ?_
  rw [Measure.map_apply hpc (hs.prod ht), withDensity_apply _ (hpc (hs.prod ht)),
    ← lintegral_indicator (hpc (hs.prod ht)), Measure.compProd_apply_prod hs ht,
    map_past_eq hj hQm hc hQc hQC, setLIntegral_withDensity_eq_setLIntegral_mul _
      (f := fun p => ENNReal.ofReal (Zc hj Q p)) (g := fun p => condKer hj Q p t)
      (ENNReal.measurable_ofReal.comp (measurable_Zc hj hQm)) ((Kernel.measurable_coe _ ht)) hs]
  have h := lintegral_pastCur hj hQm hc hQc hQC (F := fun p x => s.indicator 1 p * t.indicator 1 x)
    (((measurable_const.indicator hs).comp measurable_fst).mul
      ((measurable_const.indicator ht).comp measurable_snd))
  have e1 : ∀ X, ((fun X => (past j hj.le X, X ⟨j, hj⟩)) ⁻¹' s ×ˢ t).indicator
      (fun X => ENNReal.ofReal (Q X)) X =
      (s.indicator 1 (past j hj.le X) * t.indicator 1 (X ⟨j, hj⟩)) * ENNReal.ofReal (Q X) :=
    fun X => by
      by_cases h1 : past j hj.le X ∈ s <;> by_cases h2 : X ⟨j, hj⟩ ∈ t <;>
        simp [Set.indicator, h1, h2]
  simp_rw [e1, h]
  rw [← lintegral_indicator hs]
  refine lintegral_congr fun p => ?_
  by_cases hp : p ∈ s
  · simp only [Set.indicator_of_mem hp, Pi.one_apply, one_mul]
    have hZ := (Zc_bounds hj hQm hQc hQC p).1
    have hdm : Measurable fun x => ENNReal.ofReal (condDens hj Q p x) :=
      ENNReal.measurable_ofReal.comp ((measurable_condDens hj hQm).comp
        (measurable_const.prodMk measurable_id))
    simp only [Pi.mul_apply]
    rw [condKer_apply hj hQm, densMeasure, withDensity_apply _ ht,
      ← lintegral_const_mul _ hdm, ← lintegral_indicator ht]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ t
    · simp only [Set.indicator_of_mem hx, Pi.one_apply, one_mul]
      rw [← ENNReal.ofReal_mul (hc.le.trans hZ)]
      congr 1
      unfold condDens
      field_simp [(hc.trans_le hZ).ne']
    · simp [Set.indicator_of_notMem hx]
  · simp [Set.indicator_of_notMem hp]
include hQm hc hQc hQC in
/-- **`ρ_j(p) = condDens p · haar`** for a.e. past `p`. -/
theorem condNext_ae_eq [IsProbabilityMeasure ((volume : Measure (Config N d)).withDensity
      fun X => ENNReal.ofReal (Q X))] :
    ∀ᵐ p ∂(((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Q X)).map
        (past j hj.le)),
      condNext ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Q X)) j hj p =
        densMeasure (condDens hj Q p) := by
  haveI := isMarkovKernel_condKer hj hQm hc hQc hQC
  have h := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (measurable_past hj.le)
    (measurable_pi_apply _) (map_pastCur_eq hj hQm hc hQc hQC)
  filter_upwards [h] with p hp
  rw [condNext, hp, condKer_apply hj hQm]

end dens

end SharpLSI
