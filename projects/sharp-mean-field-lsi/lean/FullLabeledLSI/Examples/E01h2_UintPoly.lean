import FullLabeledLSI.Examples.E01h2_Calc

/-!
# Lane D, Task B1: `Uint` along `(ρ + s α₁, s β₁)` is a cubic polynomial; the Hessian formula

For continuous `C, dT C, dT (dT C)` and `s ≥ 0`:
`Uint C ℓ (ρ + s α₁) (s β₁) = u₀ + u₁ s + u₂ s² + u₃ s³`, hence
`UintHess C ℓ ρ α₁ β₁ = 2 u₂ = 4 σ(C''*σ) + 2ℓ σ(C*σ) + 2 ∫ (C'*σ)² dρ + 4 σ((C'*ρ)(C'*σ))`
(`σ F = ∫ F dα₁ - ∫ F dβ₁`).
-/

open MeasureTheory Filter Topology
open scoped Real ENNReal

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

section integrals

theorem integrable_of_cont {f : Torus 1 → ℝ} (hf : Continuous f) (μ : Measure (Torus 1))
    [IsFiniteMeasure μ] : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem continuous_conv {g : Torus 1 → ℝ} (hg : Continuous g) (μ : Measure (Torus 1))
    [IsFiniteMeasure μ] : Continuous fun x => ∫ y, g (x - y) ∂μ := by
  have := continuous_parametric_integral_of_continuous (μ := μ)
    (f := fun x y : Torus 1 => g (x - y)) (hg.comp (continuous_fst.sub continuous_snd))
    (isCompact_univ)
  simpa using this

theorem continuous_convS {g : Torus 1 → ℝ} (hg : Continuous g) (α β : Measure (Torus 1))
    [IsFiniteMeasure α] [IsFiniteMeasure β] : Continuous (convS g α β) := by
  unfold convS intS
  exact (continuous_conv hg α).sub (continuous_conv hg β)

theorem intS_mix {f : Torus 1 → ℝ} (hf : Continuous f) (ρ α₁ β₁ : Measure (Torus 1))
    [IsFiniteMeasure ρ] [IsFiniteMeasure α₁] [IsFiniteMeasure β₁] {s : ℝ} (hs : 0 ≤ s) :
    intS f (ρ + ENNReal.ofReal s • α₁) (ENNReal.ofReal s • β₁) =
      ∫ x, f x ∂ρ + s * intS f α₁ β₁ := by
  unfold intS
  rw [integral_add_measure (integrable_of_cont hf ρ)
    ((integrable_of_cont hf α₁).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hs]
  simp only [smul_eq_mul]; ring

theorem convS_mix {g : Torus 1 → ℝ} (hg : Continuous g) (ρ α₁ β₁ : Measure (Torus 1))
    [IsFiniteMeasure ρ] [IsFiniteMeasure α₁] [IsFiniteMeasure β₁] {s : ℝ} (hs : 0 ≤ s)
    (x : Torus 1) :
    convS g (ρ + ENNReal.ofReal s • α₁) (ENNReal.ofReal s • β₁) x =
      ∫ y, g (x - y) ∂ρ + s * convS g α₁ β₁ x :=
  intS_mix (f := fun y => g (x - y)) (hg.comp (continuous_const.sub continuous_id)) ρ α₁ β₁ hs

end integrals

/-- A functional that is additive and homogeneous on continuous functions. -/
structure LinC (L : (Torus 1 → ℝ) → ℝ) : Prop where
  add : ∀ f g : Torus 1 → ℝ, Continuous f → Continuous g → L (fun x => f x + g x) = L f + L g
  smul : ∀ (c : ℝ) (f : Torus 1 → ℝ), L (fun x => c * f x) = c * L f

theorem LinC.add_smul {L : (Torus 1 → ℝ) → ℝ} (hL : LinC L) {f g : Torus 1 → ℝ}
    (hf : Continuous f) (hg : Continuous g) (c : ℝ) :
    L (fun x => f x + c * g x) = L f + c * L g := by
  rw [hL.add f (fun x => c * g x) hf (continuous_const.mul hg), hL.smul c g]

theorem LinC.add_smul_smul {L : (Torus 1 → ℝ) → ℝ} (hL : LinC L) {f g h : Torus 1 → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) (c d : ℝ) :
    L (fun x => f x + c * g x + d * h x) = L f + c * L g + d * L h := by
  rw [hL.add (fun x => f x + c * g x) (fun x => d * h x) (hf.add (continuous_const.mul hg))
    (continuous_const.mul hh), hL.add_smul hf hg c, hL.smul d h]

theorem linC_integral (ρ : Measure (Torus 1)) [IsFiniteMeasure ρ] :
    LinC (fun F => ∫ x, F x ∂ρ) where
  add f g hf hg := integral_add (integrable_of_cont hf ρ) (integrable_of_cont hg ρ)
  smul c f := integral_const_mul c f

theorem linC_intS (α β : Measure (Torus 1)) [IsFiniteMeasure α] [IsFiniteMeasure β] :
    LinC (fun F => intS F α β) where
  add f g hf hg := by
    unfold intS
    rw [integral_add (integrable_of_cont hf α) (integrable_of_cont hg α),
      integral_add (integrable_of_cont hf β) (integrable_of_cont hg β)]
    ring
  smul c f := by
    unfold intS
    rw [integral_const_mul, integral_const_mul]; ring

section poly

variable (C : Torus 1 → ℝ) (ℓ : ℝ) (ρ α₁ β₁ : Measure (Torus 1))

/-- `g * ρ` for a measure `ρ`. -/
noncomputable def cvM (g : Torus 1 → ℝ) (x : Torus 1) : ℝ := ∫ y, g (x - y) ∂ρ

/-- Coefficients of the cubic. -/
noncomputable def u0 : ℝ :=
  2 * ∫ x, cvM ρ (dT (dT C)) x ∂ρ + ∫ x, cvM ρ (dT C) x ^ 2 ∂ρ + ℓ * ∫ x, cvM ρ C x ∂ρ

noncomputable def u1 : ℝ :=
  2 * (∫ x, convS (dT (dT C)) α₁ β₁ x ∂ρ + intS (cvM ρ (dT (dT C))) α₁ β₁) +
    (∫ x, 2 * (cvM ρ (dT C) x * convS (dT C) α₁ β₁ x) ∂ρ + intS (fun x => cvM ρ (dT C) x ^ 2) α₁ β₁) +
    ℓ * (∫ x, convS C α₁ β₁ x ∂ρ + intS (cvM ρ C) α₁ β₁)

noncomputable def u2 : ℝ :=
  2 * intS (convS (dT (dT C)) α₁ β₁) α₁ β₁ + ∫ x, convS (dT C) α₁ β₁ x ^ 2 ∂ρ +
    2 * intS (fun x => cvM ρ (dT C) x * convS (dT C) α₁ β₁ x) α₁ β₁ +
    ℓ * intS (convS C α₁ β₁) α₁ β₁

noncomputable def u3 : ℝ := intS (fun x => convS (dT C) α₁ β₁ x ^ 2) α₁ β₁

end poly

section mixing

variable {C : Torus 1 → ℝ} (ℓ : ℝ) (h0 : Continuous C) (h1 : Continuous (dT C))
  (h2 : Continuous (dT (dT C))) (ρ α₁ β₁ : Measure (Torus 1)) [IsFiniteMeasure ρ]
  [IsFiniteMeasure α₁] [IsFiniteMeasure β₁]

include h0 h1 h2 in
theorem Uint_mix {s : ℝ} (hs : 0 ≤ s) :
    Uint C ℓ (ρ + ENNReal.ofReal s • α₁) (ENNReal.ofReal s • β₁) =
      u0 C ℓ ρ + u1 C ℓ ρ α₁ β₁ * s + u2 C ℓ ρ α₁ β₁ * s ^ 2 + u3 C α₁ β₁ * s ^ 3 := by
  have P0 : Continuous (cvM ρ C) := continuous_conv h0 ρ
  have P1 : Continuous (cvM ρ (dT C)) := continuous_conv h1 ρ
  have P2 : Continuous (cvM ρ (dT (dT C))) := continuous_conv h2 ρ
  have Q0 : Continuous (convS C α₁ β₁) := continuous_convS h0 α₁ β₁
  have Q1 : Continuous (convS (dT C) α₁ β₁) := continuous_convS h1 α₁ β₁
  have Q2 : Continuous (convS (dT (dT C)) α₁ β₁) := continuous_convS h2 α₁ β₁
  have mL := linC_integral ρ
  have sL := linC_intS α₁ β₁
  have e2 : (fun x => convS (dT (dT C)) (ρ + ENNReal.ofReal s • α₁) (ENNReal.ofReal s • β₁) x) =
      fun x => cvM ρ (dT (dT C)) x + s * convS (dT (dT C)) α₁ β₁ x :=
    funext fun x => convS_mix h2 ρ α₁ β₁ hs x
  have e1 : (fun x => convS (dT C) (ρ + ENNReal.ofReal s • α₁) (ENNReal.ofReal s • β₁) x ^ 2) =
      fun x => cvM ρ (dT C) x ^ 2 + s * (2 * (cvM ρ (dT C) x * convS (dT C) α₁ β₁ x)) +
        s ^ 2 * convS (dT C) α₁ β₁ x ^ 2 := by
    funext x
    rw [convS_mix h1 ρ α₁ β₁ hs x]
    show (cvM ρ (dT C) x + s * convS (dT C) α₁ β₁ x) ^ 2 = _
    ring
  have e0 : (fun x => convS C (ρ + ENNReal.ofReal s • α₁) (ENNReal.ofReal s • β₁) x) =
      fun x => cvM ρ C x + s * convS C α₁ β₁ x :=
    funext fun x => convS_mix h0 ρ α₁ β₁ hs x
  unfold Uint
  rw [e2, e1, e0]
  have c2 : Continuous (fun x => cvM ρ (dT (dT C)) x + s * convS (dT (dT C)) α₁ β₁ x) :=
    P2.add (continuous_const.mul Q2)
  have c1 : Continuous (fun x => cvM ρ (dT C) x ^ 2 + s * (2 * (cvM ρ (dT C) x * convS (dT C) α₁ β₁ x)) +
        s ^ 2 * convS (dT C) α₁ β₁ x ^ 2) :=
    ((P1.pow 2).add (continuous_const.mul (continuous_const.mul (P1.mul Q1)))).add
      (continuous_const.mul (Q1.pow 2))
  have c0 : Continuous (fun x => cvM ρ C x + s * convS C α₁ β₁ x) :=
    P0.add (continuous_const.mul Q0)
  rw [intS_mix c2 ρ α₁ β₁ hs, intS_mix c1 ρ α₁ β₁ hs, intS_mix c0 ρ α₁ β₁ hs]
  have hF1 : Continuous (fun x => cvM ρ (dT C) x ^ 2) := P1.pow 2
  have hF2 : Continuous (fun x => 2 * (cvM ρ (dT C) x * convS (dT C) α₁ β₁ x)) :=
    continuous_const.mul (P1.mul Q1)
  have hF3 : Continuous (fun x => convS (dT C) α₁ β₁ x ^ 2) := Q1.pow 2
  rw [mL.add_smul P2 Q2 s, sL.add_smul P2 Q2 s, mL.add_smul P0 Q0 s, sL.add_smul P0 Q0 s,
    mL.add_smul_smul hF1 hF2 hF3 s (s ^ 2), sL.add_smul_smul hF1 hF2 hF3 s (s ^ 2)]
  unfold u0 u1 u2 u3
  have e3 : ∫ x, 2 * (cvM ρ (dT C) x * convS (dT C) α₁ β₁ x) ∂ρ =
      2 * ∫ x, cvM ρ (dT C) x * convS (dT C) α₁ β₁ x ∂ρ := integral_const_mul _ _
  have e4 : intS (fun x => 2 * (cvM ρ (dT C) x * convS (dT C) α₁ β₁ x)) α₁ β₁ =
      2 * intS (fun x => cvM ρ (dT C) x * convS (dT C) α₁ β₁ x) α₁ β₁ := sL.smul 2 _
  rw [e4]
  simp only [e3]
  ring

end mixing

/-- Second derivative at `0` of a cubic polynomial. -/
theorem iteratedDerivWithin_two_poly (a0 a1 a2 a3 : ℝ) :
    iteratedDerivWithin 2 (fun s : ℝ => a0 + a1 * s + a2 * s ^ 2 + a3 * s ^ 3) (Set.Ici 0) 0 =
      2 * a2 := by
  have hcd : ContDiff ℝ 2 (fun s : ℝ => a0 + a1 * s + a2 * s ^ 2 + a3 * s ^ 3) := by fun_prop
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcd.contDiffAt
    (Set.mem_Ici.2 le_rfl)]
  have d1 : deriv (fun s : ℝ => a0 + a1 * s + a2 * s ^ 2 + a3 * s ^ 3) =
      fun s => a1 + 2 * a2 * s + 3 * a3 * s ^ 2 := by
    funext s
    have h := (((hasDerivAt_const s a0).add ((hasDerivAt_id s).const_mul a1)).add
      ((hasDerivAt_pow 2 s).const_mul a2)).add ((hasDerivAt_pow 3 s).const_mul a3)
    simp only [id] at h
    convert h.deriv using 1
    simp; ring
  have d2 : deriv (fun s : ℝ => a1 + 2 * a2 * s + 3 * a3 * s ^ 2) =
      fun s => 2 * a2 + 6 * a3 * s := by
    funext s
    have h := (((hasDerivAt_const s a1).add ((hasDerivAt_id s).const_mul (2 * a2))).add
      ((hasDerivAt_pow 2 s).const_mul (3 * a3)))
    simp only [id] at h
    convert h.deriv using 1
    simp; ring
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, d1, d2]
  simp

/-- The Hessian formula. -/
theorem UintHess_formula {C : Torus 1 → ℝ} (ℓ : ℝ) (h0 : Continuous C) (h1 : Continuous (dT C))
    (h2 : Continuous (dT (dT C))) (ρ α₁ β₁ : Measure (Torus 1)) [IsFiniteMeasure ρ]
    [IsFiniteMeasure α₁] [IsFiniteMeasure β₁] :
    UintHess C ℓ ρ α₁ β₁ = 2 * u2 C ℓ ρ α₁ β₁ := by
  unfold UintHess
  have heq : Set.EqOn
      (fun s : ℝ => Uint C ℓ (ρ + ENNReal.ofReal s • α₁) (ENNReal.ofReal s • β₁))
      (fun s : ℝ => u0 C ℓ ρ + u1 C ℓ ρ α₁ β₁ * s + u2 C ℓ ρ α₁ β₁ * s ^ 2 + u3 C α₁ β₁ * s ^ 3)
      (Set.Ici 0) := fun s hs => Uint_mix ℓ h0 h1 h2 ρ α₁ β₁ hs
  rw [iteratedDerivWithin_congr heq (Set.mem_Ici.2 le_rfl)]
  exact iteratedDerivWithin_two_poly _ _ _ _

end SharpLSI.FL.Ex.LaneD
