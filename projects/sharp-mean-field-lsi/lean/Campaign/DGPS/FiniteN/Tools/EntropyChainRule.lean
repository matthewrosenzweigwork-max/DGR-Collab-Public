import DGPS.Foundations.Entropy
import DGPS.FiniteN.Tools.Hubbard
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# FIN015a: the entropy chain rule (disintegration) for a joint law

For a probability measure `η` on `Y`, a Markov kernel `q : Kernel Y X` and
`P = η ⊗ₘ q`, a measurable `g ≥ 0` with `g` and `g log g` `P`-integrable satisfies
`Ent_P(g) = ∫ Ent_{q_y}(g(y,·)) dη(y) + Ent_η(G)`, `G(y) = ∫ g(y,x) dq_y`.

* `entropy_chain_rule_compProd`: native `ℝ≥0∞` form (`DGPS.homogeneousEntropy`).
* `entropy_chain_rule_compProd_real`: real form with `entReal`.
* `entropy_chain_rule_hubbardJoint`: the same for `hubbardJoint`, via
  `hubbardJoint_eq_compProd` (`hubbardJoint = auxLaw ⊗ₘ hubbardKernel`).  Stated for general
  `k`; `k = 2` is the instance used downstream.
* `homogeneousEntropy_map_toLp`, `homogeneousEntropy_map_ofLp`: transport between
  `Fin k → ℝ` and `EuclideanSpace ℝ (Fin k)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DGPS.FiniteN.Tools

/-- Real-valued entropy functional `∫ v log v - (∫ v) log (∫ v)`. -/
noncomputable def entReal {α : Type*} [MeasurableSpace α] (P : Measure α) (v : α → ℝ) : ℝ :=
  ∫ x, v x * Real.log (v x) ∂P - (∫ x, v x ∂P) * Real.log (∫ x, v x ∂P)

theorem entReal_nonneg {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    {v : α → ℝ} (hv : 0 ≤ᵐ[P] v) (hint : Integrable v P)
    (hlog : Integrable (fun x => v x * Real.log (v x)) P) : 0 ≤ entReal P v := by
  set a := ∫ x, v x ∂P with ha
  have ha0 : 0 ≤ a := integral_nonneg_of_ae hv
  unfold entReal
  rcases ha0.eq_or_lt with h0 | h0
  · have hz : v =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg_ae hv hint).mp h0.symm
    have h1 : ∫ x, v x * Real.log (v x) ∂P = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
      · simp
      · filter_upwards [hz] with x hx; simp [hx]
    rw [h1, ← ha, ← h0]; simp
  · have hpt : ∀ x, DGPS.entropyIntegrand a (v x)
        = v x * Real.log (v x) - v x * Real.log a + a - v x := by
      intro x
      unfold DGPS.entropyIntegrand
      rcases eq_or_ne (v x) 0 with h | h
      · rw [h]; simp
      · rw [Real.log_div h h0.ne']; ring
    have i1 : Integrable (fun x => v x * Real.log a) P := hint.mul_const _
    have i2 : Integrable (fun x => v x * Real.log (v x) - v x * Real.log a) P := hlog.sub i1
    have i3 : Integrable (fun x => v x * Real.log (v x) - v x * Real.log a + a) P :=
      i2.add (integrable_const a)
    have hnn : 0 ≤ ∫ x, (v x * Real.log (v x) - v x * Real.log a + a - v x) ∂P := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [hv] with x hx
      simp only [Pi.zero_apply]
      rw [← hpt]; exact DGPS.entropyIntegrand_nonneg h0 hx
    rw [integral_sub i3 hint, integral_add i2 (integrable_const a), integral_sub hlog i1,
      integral_mul_const, integral_const, ← ha] at hnn
    simpa using hnn

section General

variable {Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]

/-- Integrability package for the chain rule. -/
theorem chain_rule_integrable {η : Measure Y} [IsProbabilityMeasure η] {q : Kernel Y X}
    [IsMarkovKernel q] {g : Y × X → ℝ} (hgm : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (hint : Integrable g (η ⊗ₘ q))
    (hlog : Integrable (fun z => g z * Real.log (g z)) (η ⊗ₘ q)) :
    (∀ᵐ y ∂η, Integrable (fun x => g (y, x)) (q y)) ∧
    (∀ᵐ y ∂η, Integrable (fun x => g (y, x) * Real.log (g (y, x))) (q y)) ∧
    Integrable (fun y => ∫ x, g (y, x) ∂(q y)) η ∧
    Integrable (fun y => ∫ x, g (y, x) * Real.log (g (y, x)) ∂(q y)) η ∧
    Integrable (fun y => (∫ x, g (y, x) ∂(q y)) * Real.log (∫ x, g (y, x) ∂(q y))) η ∧
    Integrable (fun y => entReal (q y) (fun x => g (y, x))) η := by
  have h1 := ((Measure.integrable_compProd_iff hint.aestronglyMeasurable).1 hint).1
  have h2 := ((Measure.integrable_compProd_iff hlog.aestronglyMeasurable).1 hlog).1
  have hG : Integrable (fun y => ∫ x, g (y, x) ∂(q y)) η := by
    have := Integrable.integral_compProd (κ := (Kernel.const Unit η)) (η := Kernel.prodMkLeft Unit q)
      (a := ()) (f := g) (by simpa [Measure.compProd] using hint)
    simpa using this
  have hH : Integrable (fun y => ∫ x, g (y, x) * Real.log (g (y, x)) ∂(q y)) η := by
    have := Integrable.integral_compProd (κ := (Kernel.const Unit η)) (η := Kernel.prodMkLeft Unit q)
      (a := ()) (f := fun z => g z * Real.log (g z)) (by simpa [Measure.compProd] using hlog)
    simpa using this
  have hGm : Measurable fun y => ∫ x, g (y, x) ∂(q y) :=
    (hgm.stronglyMeasurable.integral_kernel_prod_right' (κ := q)).measurable
  have hGnn : ∀ y, 0 ≤ ∫ x, g (y, x) ∂(q y) := fun y => integral_nonneg fun x => hg0 _
  have hE : ∀ᵐ y ∂η, 0 ≤ entReal (q y) (fun x => g (y, x)) := by
    filter_upwards [h1, h2] with y a b
    exact entReal_nonneg (Filter.Eventually.of_forall fun x => hg0 _) a b
  have hGlog : Integrable (fun y => (∫ x, g (y, x) ∂(q y)) *
      Real.log (∫ x, g (y, x) ∂(q y))) η := by
    refine Integrable.mono' ((hH.abs.add hG.abs).add (integrable_const 1)) ?_ ?_
    · exact (hGm.mul (Real.measurable_log.comp hGm)).aestronglyMeasurable
    · filter_upwards [hE] with y hy
      have hl := DGPS.self_mul_log_sub_add_one_nonneg (hGnn y)
      unfold entReal at hy
      simp only [Pi.add_apply, Real.norm_eq_abs]
      rw [abs_le]
      constructor
      · have := neg_abs_le (∫ x, g (y, x) ∂(q y))
        have := abs_nonneg (∫ x, g (y, x) * Real.log (g (y, x)) ∂(q y))
        have := abs_of_nonneg (hGnn y)
        linarith
      · have := le_abs_self (∫ x, g (y, x) * Real.log (g (y, x)) ∂(q y))
        have := abs_nonneg (∫ x, g (y, x) ∂(q y))
        linarith
  exact ⟨h1, h2, hG, hH, hGlog, hH.sub hGlog⟩

/-- Entropy chain rule (real form): `Ent_P(g) = ∫ Ent_{q_y}(g(y,·)) dη + Ent_η(G)`. -/
theorem entropy_chain_rule_compProd_real {η : Measure Y} [IsProbabilityMeasure η]
    {q : Kernel Y X} [IsMarkovKernel q] {g : Y × X → ℝ} (hgm : Measurable g)
    (hg0 : ∀ z, 0 ≤ g z) (hint : Integrable g (η ⊗ₘ q))
    (hlog : Integrable (fun z => g z * Real.log (g z)) (η ⊗ₘ q)) :
    entReal (η ⊗ₘ q) g = ∫ y, entReal (q y) (fun x => g (y, x)) ∂η +
      entReal η (fun y => ∫ x, g (y, x) ∂(q y)) := by
  obtain ⟨-, -, hG, hH, hGlog, hE⟩ := chain_rule_integrable hgm hg0 hint hlog
  unfold entReal at hE ⊢
  rw [Measure.integral_compProd hint, Measure.integral_compProd hlog]
  simp only
  rw [integral_sub hH hGlog]
  ring

/-- Entropy chain rule in the native `ℝ≥0∞`-valued form of `homogeneousEntropy`
(`P = η ⊗ₘ q`, `G(y) = ∫ g(y,x) dq_y`). -/
theorem entropy_chain_rule_compProd {η : Measure Y} [IsProbabilityMeasure η]
    {q : Kernel Y X} [IsMarkovKernel q] {g : Y × X → ℝ} (hgm : Measurable g)
    (hg0 : ∀ z, 0 ≤ g z) (hint : Integrable g (η ⊗ₘ q))
    (hlog : Integrable (fun z => g z * Real.log (g z)) (η ⊗ₘ q)) :
    DGPS.homogeneousEntropy (η ⊗ₘ q) g =
      ∫⁻ y, DGPS.homogeneousEntropy (q y) (fun x => g (y, x)) ∂η +
        DGPS.homogeneousEntropy η (fun y => ∫ x, g (y, x) ∂(q y)) := by
  obtain ⟨h1, h2, hG, hH, hGlog, hE⟩ := chain_rule_integrable hgm hg0 hint hlog
  have hGnn : ∀ y, 0 ≤ ∫ x, g (y, x) ∂(q y) := fun y => integral_nonneg fun x => hg0 _
  have hEn : ∀ᵐ y ∂η, 0 ≤ entReal (q y) (fun x => g (y, x)) := by
    filter_upwards [h1, h2] with y a b
    exact entReal_nonneg (Filter.Eventually.of_forall fun x => hg0 _) a b
  have hGn : 0 ≤ entReal η (fun y => ∫ x, g (y, x) ∂(q y)) :=
    entReal_nonneg (Filter.Eventually.of_forall hGnn) hG hGlog
  have hform : ∀ᵐ y ∂η, DGPS.homogeneousEntropy (q y) (fun x => g (y, x)) =
      ENNReal.ofReal (entReal (q y) (fun x => g (y, x))) := by
    filter_upwards [h1, h2] with y a b
    exact DGPS.homogeneousEntropy_eq_formula (Filter.Eventually.of_forall fun x => hg0 _) a b
  have hGform : DGPS.homogeneousEntropy η (fun y => ∫ x, g (y, x) ∂(q y)) =
      ENNReal.ofReal (entReal η (fun y => ∫ x, g (y, x) ∂(q y))) :=
    DGPS.homogeneousEntropy_eq_formula (Filter.Eventually.of_forall hGnn) hG hGlog
  rw [lintegral_congr_ae hform, ← ofReal_integral_eq_lintegral_ofReal hE hEn,
    hGform,
    ← ENNReal.ofReal_add (integral_nonneg_of_ae hEn) hGn,
    DGPS.homogeneousEntropy_eq_formula (Filter.Eventually.of_forall hg0) hint hlog]
  congr 1
  exact entropy_chain_rule_compProd_real hgm hg0 hint hlog

/-- Transport of entropy along a measurable equivalence. -/
theorem homogeneousEntropy_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (e : α ≃ᵐ β) (μ : Measure α) (f : β → ℝ) :
    DGPS.homogeneousEntropy (μ.map e) f = DGPS.homogeneousEntropy μ (fun a => f (e a)) := by
  have hI : ∀ h : β → ℝ, ∫ b, h b ∂(μ.map e) = ∫ a, h (e a) ∂μ := fun h =>
    e.measurableEmbedding.integral_map h
  unfold DGPS.homogeneousEntropy
  rw [hI f]
  split_ifs
  · rfl
  · rw [e.measurableEmbedding.lintegral_map]

end General

section Hubbard

open DGPS.FiniteN.Tools.Hubbard

variable {k : ℕ} {M : Type*} [MeasurableSpace M] {m : Measure M} [IsFiniteMeasure m]
  {U : M → ℝ} {φ : M → Fin k → ℝ} (hyp : HubbardHyp m U φ)
  {D : Matrix (Fin k) (Fin k) ℝ}

/-- The conditional particle kernel `w ↦ (q_w)^{⊗N}` of the Hubbard identity. -/
noncomputable def hubbardKernel (N : ℕ+) : Kernel (Fin k → ℝ) (Fin N → M) where
  toFun w := Measure.pi fun _ : Fin N => siteLaw U φ m w
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
    have h := measurable_kernelFn hyp (s := Set.univ ×ˢ t) (MeasurableSet.univ.prod ht)
    have e : ∀ w, (Measure.pi fun _ : Fin N => siteLaw U φ m w) t = kernelFn U φ m
        (Set.univ ×ˢ t) w := fun w => by
      rw [← pi_siteLaw_slice hyp (MeasurableSet.univ.prod ht) w]
      simp
    simp_rw [e]
    exact h

theorem hubbardKernel_apply (N : ℕ+) (w : Fin k → ℝ) :
    hubbardKernel hyp N w = Measure.pi fun _ : Fin N => siteLaw U φ m w := rfl

instance hubbardKernel_markov (N : ℕ+) : IsMarkovKernel (hubbardKernel hyp N) :=
  ⟨fun w => by
    have := isProbabilityMeasure_siteLaw hyp (m := m) w
    rw [hubbardKernel_apply]
    infer_instance⟩

include hyp in
theorem isProbabilityMeasure_auxLaw (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) :
    IsProbabilityMeasure (auxLaw D h U φ m N) := by
  have := isProbabilityMeasure_hubbardJoint hyp hD h N
  rw [← hubbardJoint_map_fst hyp hD h N]
  infer_instance

/-- `hubbardJoint = auxLaw ⊗ₘ (q_w^{⊗N})` (FIN010 disintegration as a `compProd`). -/
theorem hubbardJoint_eq_compProd (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) :
    hubbardJoint D h U φ m N = auxLaw D h U φ m N ⊗ₘ hubbardKernel hyp N := by
  have := isProbabilityMeasure_auxLaw hyp hD h N
  refine Measure.ext fun s hs => ?_
  rw [hubbardJoint_apply hyp hD h N hs, Measure.compProd_apply hs]
  rfl

include hyp in
/-- Entropy chain rule for `hubbardJoint` (native `ℝ≥0∞` form):
`Ent_{joint}(g) = ∫ Ent_{q_w^{⊗N}}(g(w,·)) dη_N(w) + Ent_{η_N}(G)`, `G(w) = ∫ g(w,x) dq_w^{⊗N}`. -/
theorem entropy_chain_rule_hubbardJoint (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+)
    {g : (Fin k → ℝ) × (Fin N → M) → ℝ} (hgm : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (hint : Integrable g (hubbardJoint D h U φ m N))
    (hlog : Integrable (fun z => g z * Real.log (g z)) (hubbardJoint D h U φ m N)) :
    DGPS.homogeneousEntropy (hubbardJoint D h U φ m N) g =
      ∫⁻ w, DGPS.homogeneousEntropy (Measure.pi fun _ : Fin N => siteLaw U φ m w)
          (fun x => g (w, x)) ∂(auxLaw D h U φ m N) +
        DGPS.homogeneousEntropy (auxLaw D h U φ m N)
          (fun w => ∫ x, g (w, x) ∂(Measure.pi fun _ : Fin N => siteLaw U φ m w)) := by
  have := isProbabilityMeasure_auxLaw hyp hD h N
  rw [hubbardJoint_eq_compProd hyp hD h N] at hint hlog ⊢
  exact entropy_chain_rule_compProd hgm hg0 hint hlog

/-- Transport between `Fin k → ℝ` and `EuclideanSpace ℝ (Fin k)` for entropy: the entropy of
the pushforward of `μ` to `EuclideanSpace` (by `toLp`) of `F` equals the entropy of `μ` of
`F ∘ toLp`.  Apply it to `μ = auxLaw`. -/
theorem homogeneousEntropy_map_toLp (μ : Measure (Fin k → ℝ))
    (F : EuclideanSpace ℝ (Fin k) → ℝ) :
    DGPS.homogeneousEntropy (μ.map (MeasurableEquiv.toLp 2 (Fin k → ℝ))) F =
      DGPS.homogeneousEntropy μ (fun w => F (WithLp.toLp 2 w)) :=
  homogeneousEntropy_map_measurableEquiv (MeasurableEquiv.toLp 2 (Fin k → ℝ)) μ F

/-- The converse transport: from `EuclideanSpace ℝ (Fin k)` to `Fin k → ℝ` via `ofLp`. -/
theorem homogeneousEntropy_map_ofLp (ν : Measure (EuclideanSpace ℝ (Fin k)))
    (f : (Fin k → ℝ) → ℝ) :
    DGPS.homogeneousEntropy (ν.map (MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm) f =
      DGPS.homogeneousEntropy ν (fun z => f (WithLp.ofLp z)) :=
  homogeneousEntropy_map_measurableEquiv (MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm ν f

end Hubbard

end DGPS.FiniteN.Tools
