import DGPS.Circle.BesselConcavity
import DGPS.Particle.Gibbs
import DGPS.Model.FreeEnergy
import Mathlib.Analysis.Fourier.AddCircle

/-!
# FIN055: the scalar cosine exact model and its fold parameters

Fix `κ > 2` and write `c(x) = cos 2πx` (`scalarCos`, the real part of the first character of the
circle `𝕋¹`).  The scalar cosine interaction data (`scalarCosine κ h : InteractionData 1`) are
`V = -h c - κ c²/2` and `W(x,y) = κ (c x - c y)²/2`, which is continuous, symmetric and vanishes on
the diagonal.

* `scalarCosine_hamiltonian`: expanding the pairwise squared difference including the diagonal
  terms cancels the one-body quadratic part exactly,
  `H_N(x) = -h ∑ c(xᵢ) - κ (∑ c(xᵢ))² / (2N)`.
* `scalarCosine_freeEnergy`: for every Borel probability `ν` on `𝕋¹`,
  `F_h(ν) = H(ν | m) - h m_c - κ m_c² / 2` with `m_c = ∫ c dν` (in `EReal`).
* The fold parameters: with `g = I₁/I₀ = besselRatio`, `g'` is strictly decreasing from `1/2` to
  `0` (EX004), so for `κ > 2` there is a unique `s_* > 0` with `g'(s_*) = 1/κ`
  (`scalarFoldPoint κ`); `scalarFoldField κ = κ g(s_*) - s_*` is positive because `g' < g/s`, and
  `s_*` is the unique maximiser of `κ g(s) - s` on `s ≥ 0`.  `scalarCosineFold κ` is the model with
  `h` exactly `h_c(κ)`.

The main theorem is `DGPS.FiniteN.scalar_cosine_exact_model_and_fold_parameters`.
-/

open MeasureTheory Filter Topology

namespace DGPS.Models

open DGPS.Circle.BesselMoments DGPS.Circle.BesselConcavity


/-- `c(x) = cos 2πx` on the circle `𝕋^1`, as the real part of the first character. -/
noncomputable def scalarCos (x : DGPS.Torus 1) : ℝ := (fourier 1 (x 0)).re

theorem continuous_scalarCos : Continuous scalarCos :=
  Complex.continuous_re.comp ((map_continuous (fourier (T := 1) 1)).comp (continuous_apply 0))

theorem scalarCos_lift (a : Fin 1 → ℝ) :
    scalarCos (DGPS.torusLift a) = Real.cos (2 * Real.pi * a 0) := by
  have h : (DGPS.torusLift a) 0 = ((a 0 : ℝ) : UnitAddCircle) := rfl
  rw [scalarCos, h, fourier_coe_apply]
  have : (2 * Real.pi * Complex.I * ((1:ℤ) : ℂ) * (a 0 : ℂ) / ((1 : ℝ) : ℂ)) = ((2 * Real.pi * a 0 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

theorem scalarCos_bound (x : DGPS.Torus 1) : |scalarCos x| ≤ 1 := by
  have := Complex.abs_re_le_norm (fourier 1 (x 0))
  simpa [scalarCos] using this

/-- The scalar cosine interaction data `V = -h c - κ c²/2`, `W(x,y) = κ (c x - c y)²/2`. -/
noncomputable def scalarCosine (κ h : ℝ) : DGPS.InteractionData 1 where
  V := fun x => -h * scalarCos x - κ / 2 * scalarCos x ^ 2
  W := fun x y => κ / 2 * (scalarCos x - scalarCos y) ^ 2
  V_continuous := by have := continuous_scalarCos; fun_prop
  W_continuous := by have := continuous_scalarCos; fun_prop
  W_symm := fun x y => by ring
  W_diag := fun x => by simp

theorem scalarCosine_hamiltonian (κ h : ℝ) (N : ℕ+) (x : DGPS.ParticleSpace 1 N) :
    DGPS.particleHamiltonian (scalarCosine κ h) N x =
      -h * ∑ i, scalarCos (x i) - κ * (∑ i, scalarCos (x i)) ^ 2 / (2 * (N : ℝ)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hcard : (Finset.univ : Finset (Fin N)).card = (N : ℕ) := by simp
  have e1 : ∀ c : Fin N → ℝ, ∑ i, ∑ j, (c i - c j) ^ 2 =
      2 * (N : ℝ) * ∑ i, c i ^ 2 - 2 * (∑ i, c i) ^ 2 := by
    intro c
    have h1 : ∀ i, ∑ j, (c i - c j) ^ 2 = (N : ℝ) * c i ^ 2 - 2 * (∑ j, c j) * c i + ∑ j, c j ^ 2 := by
      intro i
      have : ∀ j, (c i - c j) ^ 2 = c i ^ 2 - 2 * c j * c i + c j ^ 2 := fun j => by ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      simp
    simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
    ring
  unfold DGPS.particleHamiltonian scalarCosine
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [e1 (fun i => scalarCos (x i))]
  field_simp
  ring

theorem scalarCosine_freeEnergy (κ h : ℝ) (ν : ProbabilityMeasure (DGPS.Torus 1)) :
    DGPS.freeEnergy (scalarCosine κ h) ν =
      ((DGPS.relativeEntropy (ν : Measure (DGPS.Torus 1)) (DGPS.haar 1) : ENNReal) : EReal) +
        ((-(h * ∫ x, scalarCos x ∂(ν : Measure (DGPS.Torus 1))) -
          κ * (∫ x, scalarCos x ∂(ν : Measure (DGPS.Torus 1))) ^ 2 / 2 : ℝ) : EReal) := by
  set μ : Measure (DGPS.Torus 1) := (ν : Measure (DGPS.Torus 1)) with hμ
  have hc := continuous_scalarCos
  have i1 : Integrable scalarCos μ := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i2 : Integrable (fun x => scalarCos x ^ 2) μ :=
    (hc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hP : DGPS.potentialEnergy (scalarCosine κ h) μ =
      -h * ∫ x, scalarCos x ∂μ - κ / 2 * ∫ x, scalarCos x ^ 2 ∂μ := by
    unfold DGPS.potentialEnergy scalarCosine
    simp only
    rw [integral_sub (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
  have hI : DGPS.interactionEnergy (scalarCosine κ h) μ =
      κ * (∫ x, scalarCos x ^ 2 ∂μ - (∫ x, scalarCos x ∂μ) ^ 2) := by
    unfold DGPS.interactionEnergy scalarCosine
    simp only
    have j1 : Integrable (fun p : DGPS.Torus 1 × DGPS.Torus 1 => scalarCos p.1 ^ 2) (μ.prod μ) :=
      (hc.comp continuous_fst |>.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have j2 : Integrable (fun p : DGPS.Torus 1 × DGPS.Torus 1 => scalarCos p.2 ^ 2) (μ.prod μ) :=
      (hc.comp continuous_snd |>.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have j3 : Integrable (fun p : DGPS.Torus 1 × DGPS.Torus 1 => scalarCos p.1 * scalarCos p.2) (μ.prod μ) :=
      ((hc.comp continuous_fst).mul (hc.comp continuous_snd)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have e : ∀ p : DGPS.Torus 1 × DGPS.Torus 1, κ / 2 * (scalarCos p.1 - scalarCos p.2) ^ 2 =
        κ / 2 * (scalarCos p.1 ^ 2 + scalarCos p.2 ^ 2 - 2 * (scalarCos p.1 * scalarCos p.2)) := fun p => by ring
    simp only [e]
    rw [integral_const_mul,
      integral_sub (f := fun p : DGPS.Torus 1 × DGPS.Torus 1 => scalarCos p.1 ^ 2 + scalarCos p.2 ^ 2)
        (g := fun p : DGPS.Torus 1 × DGPS.Torus 1 => 2 * (scalarCos p.1 * scalarCos p.2))
        (j1.add j2) (j3.const_mul _),
      integral_add j1 j2, integral_const_mul, integral_prod_mul (fun x => scalarCos x) (fun x => scalarCos x)]
    have k1 : ∫ p : DGPS.Torus 1 × DGPS.Torus 1, scalarCos p.1 ^ 2 ∂(μ.prod μ) = ∫ x, scalarCos x ^ 2 ∂μ := by
      have := integral_prod_mul (μ := μ) (ν := μ) (fun x => scalarCos x ^ 2) (fun _ => (1 : ℝ))
      simpa using this
    have k2 : ∫ p : DGPS.Torus 1 × DGPS.Torus 1, scalarCos p.2 ^ 2 ∂(μ.prod μ) = ∫ x, scalarCos x ^ 2 ∂μ := by
      have := integral_prod_mul (μ := μ) (ν := μ) (fun _ => (1 : ℝ)) (fun x => scalarCos x ^ 2)
      simpa using this
    rw [k1, k2]
    ring
  unfold DGPS.freeEnergy
  rw [add_assoc, ← EReal.coe_add]
  congr 2
  rw [hP, hI]
  ring



open DGPS.Circle.BesselMoments DGPS.Circle.BesselConcavity

theorem exists_scalarFoldPoint (κ : ℝ) (hκ : 2 < κ) :
    ∃ s : ℝ, 0 < s ∧ deriv besselRatio s = 1 / κ := by
  have hκ0 : 0 < κ := by linarith
  have hpos : (0 : ℝ) < 1 / κ := by positivity
  have hlt : 1 / κ < 1 / 2 := by
    rw [div_lt_div_iff₀ hκ0 (by norm_num)]; linarith
  obtain ⟨b, hb⟩ := (tendsto_ratioDeriv.eventually (gt_mem_nhds hpos)).and
    (Filter.eventually_gt_atTop 0) |>.exists
  have hivt := intermediate_value_Icc' (le_of_lt hb.2) continuous_ratioDeriv.continuousOn
  have hmem : (1 / κ : ℝ) ∈ Set.Icc (ratioDeriv b) (ratioDeriv 0) := by
    rw [ratioDeriv_zero]; exact ⟨hb.1.le, hlt.le⟩
  obtain ⟨s, hs, hsv⟩ := hivt hmem
  have hs0 : 0 < s := by
    rcases hs.1.eq_or_lt with h | h
    · rw [← h, ratioDeriv_zero] at hsv; linarith
    · exact h
  exact ⟨s, hs0, by rw [deriv_ratio]; exact hsv⟩

theorem scalarFoldPoint_unique {s s' κ : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (h : deriv besselRatio s = 1 / κ) (h' : deriv besselRatio s' = 1 / κ) : s = s' := by
  rw [deriv_ratio] at h h'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := strictAntiOn_ratioDeriv (Set.mem_Ici.mpr hs.le) (Set.mem_Ici.mpr hs'.le) hlt
    linarith
  · have := strictAntiOn_ratioDeriv (Set.mem_Ici.mpr hs'.le) (Set.mem_Ici.mpr hs.le) hgt
    linarith

/-- The fold point `s_*(κ)`: the positive root of `g'(s) = 1/κ` (junk value outside `κ > 2`). -/
noncomputable def scalarFoldPoint (κ : ℝ) : ℝ :=
  Classical.epsilon fun s : ℝ => 0 < s ∧ deriv besselRatio s = 1 / κ

/-- The fold field `h_c(κ) = κ g(s_*) - s_*`. -/
noncomputable def scalarFoldField (κ : ℝ) : ℝ :=
  κ * besselRatio (scalarFoldPoint κ) - scalarFoldPoint κ

theorem scalarFoldPoint_spec (κ : ℝ) (hκ : 2 < κ) :
    0 < scalarFoldPoint κ ∧ deriv besselRatio (scalarFoldPoint κ) = 1 / κ :=
  Classical.epsilon_spec (p := fun s : ℝ => 0 < s ∧ deriv besselRatio s = 1 / κ)
    (exists_scalarFoldPoint κ hκ)

theorem scalarFoldPoint_max (κ : ℝ) (hκ : 2 < κ) :
    ∀ x : ℝ, 0 ≤ x → x ≠ scalarFoldPoint κ →
      κ * besselRatio x - x < κ * besselRatio (scalarFoldPoint κ) - scalarFoldPoint κ := by
  obtain ⟨hs, h⟩ := scalarFoldPoint_spec κ hκ
  set s := scalarFoldPoint κ
  rw [deriv_ratio] at h
  have hκ0 : 0 < κ := by linarith
  have hd : ∀ x, HasDerivAt (fun y => κ * besselRatio y - y) (κ * ratioDeriv x - 1) x := by
    intro x
    exact (((hasDerivAt_ratio x).const_mul κ).sub (hasDerivAt_id' x)).congr_deriv (by ring)
  have hc : Continuous fun y => κ * besselRatio y - y :=
    (continuous_const.mul continuous_besselRatio).sub continuous_id
  have hκs : κ * ratioDeriv s = 1 := by rw [h]; field_simp
  have hmono : StrictMonoOn (fun y => κ * besselRatio y - y) (Set.Icc 0 s) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 s) hc.continuousOn ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hd x).deriv]
    have := strictAntiOn_ratioDeriv (Set.mem_Ici.mpr hx.1.le) (Set.mem_Ici.mpr hs.le) hx.2
    nlinarith
  have hanti : StrictAntiOn (fun y => κ * besselRatio y - y) (Set.Ici s) := by
    refine strictAntiOn_of_deriv_neg (convex_Ici s) hc.continuousOn ?_
    intro x hx
    rw [interior_Ici] at hx
    rw [(hd x).deriv]
    have := strictAntiOn_ratioDeriv (Set.mem_Ici.mpr hs.le) (Set.mem_Ici.mpr (hs.le.trans hx.le)) hx
    nlinarith
  intro x hx0 hxs
  rcases lt_or_gt_of_ne hxs with hlt | hgt
  · exact hmono ⟨hx0, hlt.le⟩ ⟨hs.le, le_rfl⟩ hlt
  · exact hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hgt.le) hgt

theorem scalarFoldField_pos (κ : ℝ) (hκ : 2 < κ) : 0 < scalarFoldField κ := by
  obtain ⟨hs, h⟩ := scalarFoldPoint_spec κ hκ
  have hκ0 : 0 < κ := by linarith
  have h1 := ratioDeriv_lt_div _ hs
  rw [deriv_ratio] at h
  rw [h, lt_div_iff₀ hs] at h1
  unfold scalarFoldField
  have : 1 / κ * scalarFoldPoint κ < besselRatio (scalarFoldPoint κ) := h1
  have h2 := mul_lt_mul_of_pos_left this hκ0
  have : κ * (1 / κ * scalarFoldPoint κ) = scalarFoldPoint κ := by field_simp
  linarith


/-- The scalar cosine model with `h` exactly the fold field `h_c(κ)`. -/
noncomputable def scalarCosineFold (κ : ℝ) : DGPS.InteractionData 1 :=
  scalarCosine κ (scalarFoldField κ)

end DGPS.Models

namespace DGPS.FiniteN

open DGPS.Models DGPS.Circle.BesselMoments

/-- **FIN055.** Scalar cosine exact model and fold parameters.

1. `V = -h c - κ c²/2` and `W = κ (c x - c y)²/2` for `c = cos 2π·` (`c(torusLift a) = cos (2π a₀)`).
2. For every `N` the Hamiltonian is `H_N = -h ∑ c - κ (∑ c)² / (2N)`.
3. For every Borel probability `ν`, `F_h(ν) = H(ν | m) - h m_c - κ m_c² / 2`.
4. For every `κ > 2`: `s_* = scalarFoldPoint κ > 0` is the unique positive solution of
   `g'(s) = 1/κ`, it is the strict maximiser of `κ g(s) - s` on `[0, ∞)`, `h_c = κ g(s_*) - s_* > 0`,
   and `scalarCosineFold κ` is the model with `h = h_c` exactly. -/
theorem scalar_cosine_exact_model_and_fold_parameters :
    (∀ κ h : ℝ, (∀ x, (scalarCosine κ h).V x = -h * scalarCos x - κ / 2 * scalarCos x ^ 2) ∧
      (∀ x y, (scalarCosine κ h).W x y = κ / 2 * (scalarCos x - scalarCos y) ^ 2)) ∧
    (∀ a : Fin 1 → ℝ, scalarCos (DGPS.torusLift a) = Real.cos (2 * Real.pi * a 0)) ∧
    (∀ (κ h : ℝ) (N : ℕ+) (x : DGPS.ParticleSpace 1 N),
      DGPS.particleHamiltonian (scalarCosine κ h) N x =
        -h * ∑ i, scalarCos (x i) - κ * (∑ i, scalarCos (x i)) ^ 2 / (2 * (N : ℝ))) ∧
    (∀ (κ h : ℝ) (ν : ProbabilityMeasure (DGPS.Torus 1)),
      DGPS.freeEnergy (scalarCosine κ h) ν =
        ((DGPS.relativeEntropy (ν : Measure (DGPS.Torus 1)) (DGPS.haar 1) : ENNReal) : EReal) +
          ((-(h * ∫ x, scalarCos x ∂(ν : Measure (DGPS.Torus 1))) -
            κ * (∫ x, scalarCos x ∂(ν : Measure (DGPS.Torus 1))) ^ 2 / 2 : ℝ) : EReal)) ∧
    (∀ κ : ℝ, 2 < κ →
      (0 < scalarFoldPoint κ ∧ deriv besselRatio (scalarFoldPoint κ) = 1 / κ) ∧
      (∀ s : ℝ, 0 < s → deriv besselRatio s = 1 / κ → s = scalarFoldPoint κ) ∧
      (∀ x : ℝ, 0 ≤ x → x ≠ scalarFoldPoint κ →
        κ * besselRatio x - x < κ * besselRatio (scalarFoldPoint κ) - scalarFoldPoint κ) ∧
      scalarFoldField κ = κ * besselRatio (scalarFoldPoint κ) - scalarFoldPoint κ ∧
      0 < scalarFoldField κ ∧
      scalarCosineFold κ = scalarCosine κ (scalarFoldField κ)) := by
  refine ⟨fun κ h => ⟨fun _ => rfl, fun _ _ => rfl⟩, scalarCos_lift, scalarCosine_hamiltonian,
    scalarCosine_freeEnergy, fun κ hκ => ?_⟩
  obtain ⟨hs, h⟩ := scalarFoldPoint_spec κ hκ
  exact ⟨⟨hs, h⟩, fun s hs' h' => scalarFoldPoint_unique hs' hs h' h, scalarFoldPoint_max κ hκ,
    rfl, scalarFoldField_pos κ hκ, rfl⟩

end DGPS.FiniteN
