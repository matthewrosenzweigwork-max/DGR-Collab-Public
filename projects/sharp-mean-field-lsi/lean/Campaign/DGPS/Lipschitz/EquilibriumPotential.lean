import DGPS.Lipschitz.EquilibriumManifold

open MeasureTheory
open scoped ContDiff RealInnerProductSpace

namespace DGPS.Lipschitz

variable {d : ℕ}

section Potential

variable {A : InteractionData d} (m : Measure (Torus d)) [IsProbabilityMeasure m]

theorem lip034_T_apply (f : C(Torus d, ℝ)) (x : Torus d) :
    centeredOperatorC A m f x = Tfun A m f x := by
  rw [centeredOperatorC, ContinuousLinearMap.comp_apply, Tcont_apply]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := m) (𝕜 := ℝ) f] with y hy
  rw [hy]

theorem lip034_T_symm (f g : C(Torus d, ℝ)) :
    ∫ x, f x * centeredOperatorC A m g x ∂m = ∫ x, centeredOperatorC A m f x * g x ∂m := by
  simp_rw [lip034_T_apply, Tfun]
  have hK := centeredKernel_continuous A m
  have hint : Integrable (fun p : Torus d × Torus d =>
      f p.1 * (centeredKernel A m p.1 p.2 * g p.2)) (m.prod m) :=
    (by fun_prop : Continuous fun p : Torus d × Torus d =>
      f p.1 * (centeredKernel A m p.1 p.2 * g p.2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h1 : ∀ x, f x * ∫ y, centeredKernel A m x y * g y ∂m =
      ∫ y, f x * (centeredKernel A m x y * g y) ∂m := fun x => (integral_const_mul _ _).symm
  have h2 : ∀ y, (∫ x, centeredKernel A m y x * f x ∂m) * g y =
      ∫ x, f x * (centeredKernel A m x y * g y) ∂m := fun y => by
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [centeredKernel_symm A m y x]; ring
  simp_rw [h1, h2]
  exact integral_integral_swap hint

/-- The potential `Ψ(f) = ∫ (1+f) log (1+f) dμ + ½ ∫ f · T f dμ` on `C(𝕋)`. -/
noncomputable def lip034_potential (A : InteractionData d) (f : C(Torus d, ℝ)) : ℝ :=
  intCLM m ((1 + f) * nemLog f + (1 / 2 : ℝ) • (f * centeredOperatorC A m f))

theorem lip034_hasFDerivAt_potential {f0 : C(Torus d, ℝ)} (hf : f0 ∈ posSet (Torus d)) :
    HasFDerivAt (lip034_potential (A := A) m)
      (pairCLM m (1 + nemLog f0 + centeredOperatorC A m f0)) f0 := by
  have h1 : HasFDerivAt (fun f : C(Torus d, ℝ) => 1 + f)
      (ContinuousLinearMap.id ℝ C(Torus d, ℝ)) f0 := (hasFDerivAt_id f0).const_add 1
  have h2 := h1.mul (hasFDerivAt_nemLog hf)
  have h3 := (hasFDerivAt_id f0).mul (centeredOperatorC A m).hasFDerivAt
  have h4 := h2.add (h3.const_smul (1 / 2 : ℝ))
  have h5 := (intCLM m).hasFDerivAt.comp f0 h4
  refine h5.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun δ => ?_
  simp
  have e1 : (1 + f0) * (mulOp (invOne f0)) δ = δ := by
    ext x
    have := (hf x).ne'
    simp [mulOp_apply, invOne_apply hf, this]
  have e2 := lip034_T_symm (A := A) m f0 δ
  have hI : ∀ g k : C(Torus d, ℝ), Integrable (fun x => g x * k x) m :=
    fun g k => integrable_cts m (g * k)
  rw [e1]
  simp only [intCLM_apply, pairCLM_apply, ContinuousMap.mul_apply, ContinuousMap.add_apply,
    ContinuousMap.one_apply]
  have e3 : ∀ x, (1 + nemLog f0 x + centeredOperatorC A m f0 x) * δ x =
      δ x + nemLog f0 x * δ x + centeredOperatorC A m f0 x * δ x := fun x => by ring
  simp_rw [e3]
  have i1 : Integrable (fun x => δ x) m := integrable_cts m δ
  rw [integral_add (f := fun x => δ x + nemLog f0 x * δ x)
    (g := fun x => centeredOperatorC A m f0 x * δ x) (i1.add (hI _ _)) (hI _ _),
    integral_add i1 (hI (nemLog f0) δ), e2]
  ring

/-- `Ψ` is the project's free-energy gap `KL(ν‖μ) + ½ ∬ K dν⊗ν` for `ν = (1+h) μ`. -/
theorem lip034_potential_eq_gap {h : C(Torus d, ℝ)} (hpos : h ∈ posSet (Torus d))
    (h0 : ∫ x, h x ∂m = 0) :
    lip034_potential (A := A) m h =
      (InformationTheory.klDiv (perturb m (fun x => 1 + h x)) m).toReal +
        (1 / 2 : ℝ) * ∫ p, centeredKernel A m p.1 p.2
          ∂((perturb m (fun x => 1 + h x)).prod (perturb m (fun x => 1 + h x))) := by
  have hu : Continuous fun x => 1 + h x := continuous_const.add h.continuous
  have h1 : ∫ x, (1 + h x) ∂m = 1 := by
    rw [integral_add (integrable_const _) (integrable_cts m h), h0]; simp
  have hk := (klDiv_perturb (μ := m) hu hpos h1).2
  have hq := integral_kernel_perturb A m h.continuous h0 1 (fun x => by simpa using (hpos x).le)
  simp only [one_mul, one_pow] at hq
  rw [hk, hq]
  have hI : ∀ g k : C(Torus d, ℝ), Integrable (fun x => g x * k x) m :=
    fun g k => integrable_cts m (g * k)
  unfold lip034_potential
  rw [map_add, map_smul, intCLM_apply, intCLM_apply]
  simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.one_apply,
    smul_eq_mul]
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [nemLog_apply hpos]
  · congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [lip034_T_apply]

end Potential

section Gradient

variable {A : InteractionData d} {μ : ProbabilityMeasure (Torus d)}

theorem lip034_pair_ysub {k : ℕ} {φ : Fin k → C(Torus d, ℝ)} (hφ : IsEquilibriumBasis A μ φ)
    {u : C(Torus d, ℝ)} (hu : u ∈ Ysub A μ) (i : Fin k) :
    pairCLM (μ : Measure (Torus d)) (φ i) u = 0 := by
  obtain ⟨e, he, hel⟩ := hφ.toLp_mem i
  have := ((mem_Ysub (A := A) μ u).1 hu).2 e he
  rw [hel, inner_toLp_toLp] at this
  exact this

theorem lip034_phiMap_eq {k : ℕ} (φ : Fin k → C(Torus d, ℝ)) (v : Par k) :
    phiMap φ v = ∑ j, v j • φ j := by
  ext x
  simp [phiMap_apply, ContinuousMap.sum_apply]

theorem lip034_pair_phi_add {k : ℕ} {φ : Fin k → C(Torus d, ℝ)} (hφ : IsEquilibriumBasis A μ φ)
    {u : C(Torus d, ℝ)} (hu : u ∈ Ysub A μ) (v : Par k) (i : Fin k) :
    pairCLM (μ : Measure (Torus d)) (φ i) (phiMap φ v + u) = v i := by
  rw [map_add, lip034_pair_ysub hφ hu, add_zero, lip034_phiMap_eq, map_sum]
  simp [hφ.pair_eq i]

theorem lip034_int_phi_add {k : ℕ} {φ : Fin k → C(Torus d, ℝ)} (hφ : IsEquilibriumBasis A μ φ)
    {u : C(Torus d, ℝ)} (hu : u ∈ Ysub A μ) (v : Par k) :
    intCLM (μ : Measure (Torus d)) (phiMap φ v + u) = 0 := by
  have h1 : intCLM (μ : Measure (Torus d)) u = 0 := by
    rw [intCLM_apply]; exact ((mem_Ysub (A := A) μ u).1 hu).1
  rw [map_add, h1, add_zero, lip034_phiMap_eq, map_sum]
  simp [intCLM_apply, hφ.integral_eq_zero]

end Gradient

section Main

variable {A : InteractionData d} {μ : ProbabilityMeasure (Torus d)}

/-- **S6.** Along the Lyapunov–Schmidt graph, the potential `Ψ(a) = Ψ(∑ aᵢφᵢ + y a)` has
gradient `b(a)`. -/
theorem lip034_potential_gradient {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ)
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν) :
    ∃ U : Set (Par k), IsOpen U ∧ (0 : Par k) ∈ U ∧ ∃ y : Par k → Ysub A μ,
      y 0 = 0 ∧ fderiv ℝ y 0 = 0 ∧ ContDiffOn ℝ ∞ y U ∧
      (∀ a ∈ U, ∀ x, 0 < 1 + (phiMap φ a + (y a : C(Torus d, ℝ))) x) ∧
      ∃ b : Par k → Par k, ContDiffOn ℝ ∞ b U ∧ b 0 = 0 ∧ fderiv ℝ b 0 = 0 ∧
        ∀ a ∈ U, HasGradientAt
          (fun a => lip034_potential (A := A) (μ : Measure (Torus d))
            (phiMap φ a + (y a : C(Torus d, ℝ)))) (b a) a := by
  obtain ⟨U, hUo, h0U, y, hy0, hyd, hsm, -, hpos, b, c, hbsm, -, hb0, hbd, heq⟩ :=
    lip034_euler_expansion hφ hmin
  refine ⟨U, hUo, h0U, y, hy0, hyd, hsm, hpos, b, hbsm, hb0, hbd, fun a ha => ?_⟩
  set m : Measure (Torus d) := (μ : Measure (Torus d)) with hm
  have hd : DifferentiableAt ℝ y a :=
    (hsm.differentiableOn (by simp)).differentiableAt (hUo.mem_nhds ha)
  have hy := hd.hasFDerivAt
  have hsub : HasFDerivAt (fun a => ((y a : Ysub A μ) : C(Torus d, ℝ)))
      ((Ysub A μ).subtypeL.comp (fderiv ℝ y a)) a := by
    have h1 :=
      HasFDerivAt.comp (𝕜 := ℝ) (E := Par k) (F := Ysub A μ) (G := C(Torus d, ℝ))
        (g := (Ysub A μ).subtypeL) (f := y) (g' := (Ysub A μ).subtypeL)
        (f' := fderiv ℝ y a) a (Ysub A μ).subtypeL.hasFDerivAt hy
    simpa [Function.comp_def] using h1
  have hH : HasFDerivAt (fun a => phiMap φ a + ((y a : Ysub A μ) : C(Torus d, ℝ)))
      (phiMap φ + (Ysub A μ).subtypeL.comp (fderiv ℝ y a)) a :=
    (phiMap φ).hasFDerivAt.add hsub
  have hΨ := (lip034_hasFDerivAt_potential (A := A) m
    (f0 := phiMap φ a + ((y a : Ysub A μ) : C(Torus d, ℝ)))
    (fun x => hpos a ha x)).comp a hH
  rw [hasGradientAt_iff_hasFDerivAt]
  refine hΨ.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  set u : Ysub A μ := fderiv ℝ y a v with hu
  have hg : (1 + nemLog (phiMap φ a + ((y a : Ysub A μ) : C(Torus d, ℝ))) +
      centeredOperatorC A m (phiMap φ a + ((y a : Ysub A μ) : C(Torus d, ℝ)))) =
      (1 + c a) • (1 : C(Torus d, ℝ)) + ∑ i, b a i • φ i := by
    ext x
    have := heq a ha x
    rw [← nemLog_apply (fun x => hpos a ha x)] at this
    simp only [ContinuousMap.add_apply, ContinuousMap.one_apply, ContinuousMap.smul_apply,
      ContinuousMap.sum_apply, smul_eq_mul, mul_one]
    linarith
  have hδ : ((phiMap φ + (Ysub A μ).subtypeL.comp (fderiv ℝ y a)) v) =
      phiMap φ v + (u : C(Torus d, ℝ)) := rfl
  simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply]
  rw [hg, hδ]
  have e : pairCLM m ((1 + c a) • (1 : C(Torus d, ℝ)) + ∑ i, b a i • φ i)
      (phiMap φ v + (u : C(Torus d, ℝ))) =
      (1 + c a) * intCLM m (phiMap φ v + (u : C(Torus d, ℝ))) +
        ∑ i, b a i * pairCLM m (φ i) (phiMap φ v + (u : C(Torus d, ℝ))) := by
    simp only [pairCLM_apply, intCLM_apply]
    generalize phiMap φ v + (u : C(Torus d, ℝ)) = δ
    have pt : ∀ x, ((1 + c a) • (1 : C(Torus d, ℝ)) + ∑ i, b a i • φ i) x * δ x =
        (1 + c a) * δ x + ∑ i, b a i * (φ i x * δ x) := fun x => by
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
        ContinuousMap.sum_apply, smul_eq_mul, mul_one]
      rw [add_mul, Finset.sum_mul]
      simp_rw [mul_assoc]
    simp_rw [pt]
    have iδ : Integrable (fun x => δ x) m := integrable_cts m δ
    have iφ : ∀ i, Integrable (fun x => b a i * (φ i x * δ x)) m := fun i =>
      (integrable_cts m (φ i * δ)).const_mul _
    rw [integral_add (iδ.const_mul _) (integrable_finsetSum _ fun i _ => iφ i),
      integral_const_mul, integral_finsetSum _ fun i _ => iφ i]
    simp_rw [integral_const_mul]
  rw [e, lip034_int_phi_add hφ u.2]
  rw [Finset.sum_congr rfl (fun i _ => by rw [lip034_pair_phi_add hφ u.2 v i])]
  simp [inner, mul_comm]

end Main

end DGPS.Lipschitz
