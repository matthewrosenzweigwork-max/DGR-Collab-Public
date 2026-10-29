import DGPS.Particle.Sobolev
import DGPS.Lipschitz.Representatives

/-!
# LIP004: particle force including the diagonal

See `particle_force_including_the_diagonal`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

namespace DGPS.Lipschitz

variable {d : ℕ} {N : ℕ+}

theorem df_measurePreserving_update (i : Fin N) :
    MeasurePreserving (fun p : ParticleSpace d N × Torus d => Function.update p.1 i p.2)
      ((particleHaar d N).prod (haar d)) (particleHaar d N) := by
  refine ⟨measurable_update', ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have : (fun p : ParticleSpace d N × Torus d => Function.update p.1 i p.2) ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
    ext ⟨x, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun k => ?_, by simpa using h i⟩
      by_cases hk : k = i
      · subst hk; simp
      · simpa [Function.update_of_ne hk] using h k
    · rintro ⟨h1, h2⟩ k
      by_cases hk : k = i
      · subst hk; simpa using h2
      · have := h1 k
        simpa [Function.update_of_ne hk] using this
  rw [this, Measure.prod_prod, particleHaar, Measure.pi_pi]
  have e1 : ∏ k, haar d (Function.update s i Set.univ k) = ∏ k ∈ Finset.univ.erase i, haar d (s k) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [Function.update_self, measure_univ, one_mul]
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [e1, mul_comm, Finset.mul_prod_erase Finset.univ (fun k => haar d (s k)) (Finset.mem_univ i)]

theorem df_integral_split (i : Fin N) {h : ParticleSpace d N → ℝ}
    (hh : Integrable h (particleHaar d N)) :
    ∫ x, h x ∂particleHaar d N =
      ∫ x, ∫ t, h (Function.update x i t) ∂haar d ∂particleHaar d N := by
  have hmp := df_measurePreserving_update (d := d) i
  have hint : Integrable (h ∘ fun p : ParticleSpace d N × Torus d => Function.update p.1 i p.2)
      ((particleHaar d N).prod (haar d)) := (hmp.integrable_comp hh.aestronglyMeasurable).2 hh
  calc ∫ x, h x ∂particleHaar d N
      = ∫ x, h x ∂((particleHaar d N).prod (haar d)).map
          (fun p : ParticleSpace d N × Torus d => Function.update p.1 i p.2) := by
        rw [hmp.map_eq]
    _ = ∫ p, h (Function.update p.1 i p.2) ∂(particleHaar d N).prod (haar d) :=
        integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hh.aestronglyMeasurable)
    _ = _ := integral_prod _ hint

/-! ### Slices of smooth periodic tests -/

theorem df_slice_eq (φ : ParticleSpace d N → ℝ) (x : ParticleSpace d N) (i : Fin N) :
    ((fun t => φ (Function.update x i t)) ∘ torusLift) =
      (φ ∘ particleLift) ∘ (Function.update (fun k => SharpLSI.secT (x k)) i) := by
  funext z
  simp only [Function.comp]
  congr 1
  funext k
  by_cases hk : k = i
  · subst hk; simp [particleLift]
  · simp [particleLift, Function.update_of_ne hk, SharpLSI.liftT_secT]

theorem df_isSmoothPeriodic_slice {φ : ParticleSpace d N → ℝ} (hφ : IsSmoothPeriodicParticle φ)
    (x : ParticleSpace d N) (i : Fin N) :
    IsSmoothPeriodic (fun t => φ (Function.update x i t)) := by
  unfold IsSmoothPeriodic
  rw [df_slice_eq]
  exact hφ.comp (contDiff_update _ _ _)

theorem df_coordPartial_slice {φ : ParticleSpace d N → ℝ} (hφ : IsSmoothPeriodicParticle φ)
    (x : ParticleSpace d N) (i : Fin N) (l : Fin d) (t : Torus d) :
    coordPartial l (fun t => φ (Function.update x i t)) t =
      particlePartial i l φ (Function.update x i t) := by
  unfold coordPartial particlePartial
  rw [df_slice_eq]
  have hE : HasFDerivAt (Function.update (fun k => SharpLSI.secT (x k)) i)
      (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (Fin d → ℝ))))
      (SharpLSI.secT t) := hasFDerivAt_update _ _
  have hD : DifferentiableAt ℝ (φ ∘ particleLift)
      (Function.update (fun k => SharpLSI.secT (x k)) i (SharpLSI.secT t)) :=
    (hφ.differentiable (by simp)).differentiableAt
  rw [fderiv_comp _ hD hE.differentiableAt, hE.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  have e1 : (fun k => SharpLSI.secT (Function.update x i t k)) =
      Function.update (fun k => SharpLSI.secT (x k)) i (SharpLSI.secT t) := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  have e2 : (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (Fin d → ℝ))))
      (Pi.single l (1 : ℝ) : Fin d → ℝ) =
        (Pi.single i (Pi.single l (1 : ℝ) : Fin d → ℝ) : Fin N → Fin d → ℝ) := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  rw [e1, e2]

theorem df_integral_coordPartial {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) (j : Fin d) :
    ∫ x, coordPartial j φ x ∂haar d = 0 := by
  have h1 : IsSmoothPeriodic (fun _ : Torus d => (1 : ℝ)) := contDiff_const
  have := hφ.isWeakGradient.ibp (fun _ => 1) h1 j
  have e : ∀ x : Torus d, coordPartial j (fun _ : Torus d => (1 : ℝ)) x = 0 := by
    intro x; simp [coordPartial, Function.comp_def]
  simp only [e, mul_zero, integral_zero, mul_one, smoothGrad_apply] at this
  linarith

theorem df_isWeakGradient_const (c : ℝ) :
    IsWeakGradient (fun _ : Torus d => c) (fun _ => 0) where
  memLp := memLp_const c
  memLp_grad := memLp_const 0
  ibp φ hφ j := by
    simp [integral_const_mul, df_integral_coordPartial hφ j]

/-- Weak integration by parts in one label, from weak gradients of the slices. -/
theorem df_ibp_of_slice {f : ParticleSpace d N → ℝ} {g : ParticleSpace d N → Fin N → Tangent d}
    (i : Fin N) (l : Fin d) (hf : MemLp f 2 (particleHaar d N))
    (hg : MemLp (fun x => g x i l) 2 (particleHaar d N))
    (hslice : ∀ x, IsWeakGradient (fun t => f (Function.update x i t))
      (fun t => g (Function.update x i t) i))
    {φ : ParticleSpace d N → ℝ} (hφ : IsSmoothPeriodicParticle φ) :
    ∫ x, f x * particlePartial i l φ x ∂particleHaar d N =
      -∫ x, g x i l * φ x ∂particleHaar d N := by
  rw [df_integral_split i (integrable_mul_of_memLp_two_particle hf
      (hφ.memLp_top_particlePartial i l)),
    df_integral_split i (integrable_mul_of_memLp_two_particle hg hφ.memLp_top), ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have := (hslice x).ibp _ (df_isSmoothPeriodic_slice hφ x i) l
  simp only [df_coordPartial_slice hφ x i l] at this
  simpa using this


/-! ### Weak gradients of finite sums -/

theorem df_isWeakGradient_sum {ι : Type*} (s : Finset ι) {u : ι → Torus d → ℝ}
    {g : ι → Torus d → Tangent d} (h : ∀ b ∈ s, IsWeakGradient (u b) (g b)) :
    IsWeakGradient (fun t => ∑ b ∈ s, u b t) (fun t => ∑ b ∈ s, g b t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isWeakGradient_zero (d := d)
  | insert a s ha ih =>
    have h1 := (h a (Finset.mem_insert_self a s)).add
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
    simpa only [Finset.sum_insert ha] using h1

/-! ### The core computation -/

theorem df_sum_update_eq {β : Type*} [AddCommMonoid β] (i : Fin N) (x : ParticleSpace d N)
    (t : Torus d) (u : Torus d → β) :
    ∑ a, u (Function.update x i t a) = u t + ∑ a ∈ Finset.univ.erase i, u (x a) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  exact Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

theorem df_double_sum_update_eq (i : Fin N) (x : ParticleSpace d N) (t : Torus d)
    (F : Torus d → Torus d → ℝ) (hsymm : ∀ x y, F x y = F y x) :
    ∑ a, ∑ b, F (Function.update x i t a) (Function.update x i t b) =
      F t t + 2 * ∑ b ∈ Finset.univ.erase i, F t (x b) +
        ∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase i, F (x a) (x b) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  rw [df_sum_update_eq i x t (fun z => F t z)]
  have h2 : ∀ a ∈ Finset.univ.erase i, ∑ b, F (Function.update x i t a) (Function.update x i t b) =
      F (x a) t + ∑ b ∈ Finset.univ.erase i, F (x a) (x b) := by
    intro a ha
    rw [Function.update_of_ne (Finset.ne_of_mem_erase ha),
      df_sum_update_eq i x t (fun z => F (x a) z)]
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib]
  have h3 : ∑ a ∈ Finset.univ.erase i, F (x a) t = ∑ b ∈ Finset.univ.erase i, F t (x b) :=
    Finset.sum_congr rfl fun a _ => hsymm _ _
  rw [h3]; ring


theorem df_memLp_comp_eval {u : Torus d → ℝ} (hu : MemLp u 2 (haar d)) (i : Fin N) :
    MemLp (fun x : ParticleSpace d N => u (x i)) 2 (particleHaar d N) :=
  hu.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => haar d) i)

theorem df_memLp_comp_eval_tangent {u : Torus d → Tangent d} (hu : MemLp u 2 (haar d)) (i : Fin N) :
    MemLp (fun x : ParticleSpace d N => u (x i)) 2 (particleHaar d N) :=
  hu.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => haar d) i)

theorem df_core {V : Torus d → ℝ} {gV gδ : Torus d → Tangent d}
    {F : Torus d → Torus d → ℝ} {B : Torus d → Torus d → Tangent d}
    (hsymm : ∀ x y, F x y = F y x) (hFc : Continuous (Function.uncurry F))
    (hBm : Measurable (Function.uncurry B)) {M : ℝ} (hBM : ∀ x y, ‖B x y‖ ≤ M)
    (hB : ∀ y, IsWeakGradient (fun x => F x y) (fun x => B x y))
    (hV : IsWeakGradient V gV) (hδ : IsWeakGradient (fun x => F x x) gδ) (N : ℕ+) :
    IsParticleHaarWeakGradient N
      (fun x : ParticleSpace d N => ∑ i, V (x i) + (1 / (2 * (N : ℝ))) * ∑ i, ∑ j, F (x i) (x j))
      (fun x i => gV (x i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) +
        (2 * (N : ℝ))⁻¹ • gδ (x i)) := by
  have hmeas2 : ∀ i j : Fin N, Measurable fun x : ParticleSpace d N => (x i, x j) := fun i j =>
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus d × Torus d)).exists_bound_of_continuousOn
    hFc.continuousOn
  have hFmem : ∀ i j : Fin N, MemLp (fun x : ParticleSpace d N => F (x i) (x j)) 2
      (particleHaar d N) := fun i j =>
    MemLp.of_bound (hFc.measurable.comp (hmeas2 i j)).aestronglyMeasurable C
      (Eventually.of_forall fun x => hC (x i, x j) (mem_univ _))
  have hBmem : ∀ i j : Fin N, MemLp (fun x : ParticleSpace d N => B (x i) (x j)) 2
      (particleHaar d N) := fun i j =>
    MemLp.of_bound (hBm.comp (hmeas2 i j)).aestronglyMeasurable M
      (Eventually.of_forall fun x => hBM _ _)
  have hf : MemLp (fun x : ParticleSpace d N =>
      ∑ i, V (x i) + (1 / (2 * (N : ℝ))) * ∑ i, ∑ j, F (x i) (x j)) 2 (particleHaar d N) := by
    have h1 : MemLp (fun x : ParticleSpace d N => ∑ i, V (x i)) 2 (particleHaar d N) :=
      memLp_finsetSum _ fun i _ => df_memLp_comp_eval hV.memLp i
    have h2 : MemLp (fun x : ParticleSpace d N => ∑ i, ∑ j, F (x i) (x j)) 2
        (particleHaar d N) :=
      memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => hFmem i j
    exact h1.add (h2.const_mul _)
  have hg : MemLp (fun (x : ParticleSpace d N) (i : Fin N) => gV (x i) +
      (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) + (2 * (N : ℝ))⁻¹ • gδ (x i)) 2
      (particleHaar d N) := by
    refine memLp_pi_iff.2 fun i => ?_
    have h1 := df_memLp_comp_eval_tangent (N := N) hV.memLp_grad i
    have h2 : MemLp (fun x : ParticleSpace d N => ∑ j ∈ Finset.univ.erase i, B (x i) (x j)) 2
        (particleHaar d N) := memLp_finsetSum _ fun j _ => hBmem i j
    have h3 := df_memLp_comp_eval_tangent (N := N) hδ.memLp_grad i
    have h4 : MemLp (fun x : ParticleSpace d N =>
        (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j)) 2 (particleHaar d N) :=
      h2.const_smul ((N : ℝ)⁻¹)
    have h5 : MemLp (fun x : ParticleSpace d N => (2 * (N : ℝ))⁻¹ • gδ (x i)) 2
        (particleHaar d N) := h3.const_smul ((2 * (N : ℝ))⁻¹)
    have h6 : MemLp (fun x : ParticleSpace d N =>
        gV (x i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j)) 2 (particleHaar d N) :=
      h1.add h4
    exact h6.add h5
  refine ⟨hf, hg, fun φ hφ i l => ?_⟩
  refine df_ibp_of_slice (g := fun (x : ParticleSpace d N) (i : Fin N) => gV (x i) +
      (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) + (2 * (N : ℝ))⁻¹ • gδ (x i))
    i l hf (memLp_particleCoord hg i l) (fun x => ?_) hφ
  have e1 : (fun t => ∑ a, V (Function.update x i t a) + (1 / (2 * (N : ℝ))) *
      ∑ a, ∑ b, F (Function.update x i t a) (Function.update x i t b)) =
      fun t => (V t + ∑ a ∈ Finset.univ.erase i, V (x a)) + (1 / (2 * (N : ℝ))) *
        ((F t t + 2 * ∑ b ∈ Finset.univ.erase i, F t (x b)) +
          ∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase i, F (x a) (x b)) := by
    funext t
    rw [df_sum_update_eq i x t V, df_double_sum_update_eq i x t F hsymm]
  have e2 : (fun t => gV (Function.update x i t i) +
      (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (Function.update x i t i) (Function.update x i t j) +
      (2 * (N : ℝ))⁻¹ • gδ (Function.update x i t i)) =
      fun t => (gV t + 0) + (1 / (2 * (N : ℝ))) • ((gδ t + (2 : ℝ) • ∑ b ∈ Finset.univ.erase i, B t (x b)) + 0) := by
    funext t
    simp only [Function.update_self]
    have : ∑ j ∈ Finset.univ.erase i, B t (Function.update x i t j) =
        ∑ j ∈ Finset.univ.erase i, B t (x j) :=
      Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [this]
    module
  rw [e1, e2]
  refine (hV.add (df_isWeakGradient_const _)).add (((hδ.add
    ((df_isWeakGradient_sum _ fun b _ => hB (x b)).smul 2)).add (df_isWeakGradient_const _)).smul _)

/-! ### Lipschitz consequences -/

theorem df_diag_lipschitz {F : Torus d → Torus d → ℝ} {L : ℝ}
    (hF : ∀ x y x' y', |F x y - F x' y'| ≤
      L * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2)) :
    TorusLipschitzWith (Real.sqrt 2 * L) (fun x => F x x) := by
  intro x y
  have h := hF x x y y
  have e : Real.sqrt (torusDist x y ^ 2 + torusDist x y ^ 2) = Real.sqrt 2 * torusDist x y := by
    have h0 : 0 ≤ torusDist x y := by
      have := (torusDist_comparison x y).1
      exact (dist_nonneg).trans this
    rw [← two_mul, Real.sqrt_mul (by norm_num), Real.sqrt_sq h0]
  rw [e] at h
  calc |F x x - F y y| ≤ L * (Real.sqrt 2 * torusDist x y) := h
    _ = Real.sqrt 2 * L * torusDist x y := by ring

theorem df_section_lipschitz {F : Torus d → Torus d → ℝ} {L : ℝ}
    (hF : ∀ x y x' y', |F x y - F x' y'| ≤
      L * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2)) (y : Torus d) :
    TorusLipschitzWith L (fun x => F x y) := by
  intro x x'
  have h := hF x y x' y
  have h0 : 0 ≤ torusDist x x' := (dist_nonneg).trans (torusDist_comparison x x').1
  simpa [torusDist_metric.1 y, Real.sqrt_sq h0] using h

theorem df_continuous_of_lipschitz {F : Torus d → Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ x y x' y', |F x y - F x' y'| ≤
      L * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2)) :
    Continuous (Function.uncurry F) := by
  have hK : LipschitzWith (⟨L * Real.sqrt 2 * Real.sqrt d * 1, by positivity⟩ : ℝ≥0)
      (Function.uncurry F) := by
    refine LipschitzWith.of_dist_le_mul fun p q => ?_
    rw [Real.dist_eq]
    have h := hF p.1 p.2 q.1 q.2
    have c1 := (torusDist_comparison p.1 q.1).2
    have c2 := (torusDist_comparison p.2 q.2).2
    have d1 : dist p.1 q.1 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_left _ _
    have d2 : dist p.2 q.2 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_right _ _
    have s0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
    have t1 : torusDist p.1 q.1 ≤ Real.sqrt d * dist p q :=
      c1.trans (mul_le_mul_of_nonneg_left d1 s0)
    have t2 : torusDist p.2 q.2 ≤ Real.sqrt d * dist p q :=
      c2.trans (mul_le_mul_of_nonneg_left d2 s0)
    have n1 : 0 ≤ torusDist p.1 q.1 := (dist_nonneg).trans (torusDist_comparison _ _).1
    have n2 : 0 ≤ torusDist p.2 q.2 := (dist_nonneg).trans (torusDist_comparison _ _).1
    have hs : Real.sqrt (torusDist p.1 q.1 ^ 2 + torusDist p.2 q.2 ^ 2) ≤
        Real.sqrt 2 * (Real.sqrt d * dist p q) := by
      rw [← Real.sqrt_sq (mul_nonneg s0 dist_nonneg), ← Real.sqrt_mul (by norm_num)]
      refine Real.sqrt_le_sqrt ?_
      nlinarith
    calc |Function.uncurry F p - Function.uncurry F q|
        ≤ L * Real.sqrt (torusDist p.1 q.1 ^ 2 + torusDist p.2 q.2 ^ 2) := h
      _ ≤ L * (Real.sqrt 2 * (Real.sqrt d * dist p q)) := mul_le_mul_of_nonneg_left hs hL
      _ = (L * Real.sqrt 2 * Real.sqrt d * 1) * dist p q := by ring
      _ = _ := rfl
  exact hK.continuous

/-! ### The clipped gradient in the first variable -/

theorem df_exists_B {F : Torus d → Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ x y x' y', |F x y - F x' y'| ≤
      L * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2)) :
    ∃ B : Torus d → Torus d → Tangent d, Measurable (Function.uncurry B) ∧
      (∀ x y, ‖B x y‖ ≤ L) ∧ ∀ y, IsWeakGradient (fun x => F x y) (fun x => B x y) := by
  classical
  have hFc := df_continuous_of_lipschitz hL hF
  set G : Torus d × Torus d → Tangent d := fun p => smoothGrad (fun z => F z p.2) p.1 with hG
  have hGm : Measurable G := by
    refine (PiLp.continuous_toLp 2 _).measurable.comp (Measurable.of_eval fun j => ?_)
    have hf : Continuous (Function.uncurry fun (y : Torus d) (z : Fin d → ℝ) => F (torusLift z) y) :=
      hFc.comp ((SharpLSI.continuous_liftT.comp continuous_snd).prodMk continuous_fst)
    have := (measurable_fderiv_apply_const_with_param ℝ hf (Pi.single j (1 : ℝ))).comp
      (measurable_snd.prodMk (SharpLSI.measurable_secT.comp measurable_fst) :
        Measurable fun p : Torus d × Torus d => (p.2, SharpLSI.secT p.1))
    exact this
  refine ⟨fun x y => if ‖smoothGrad (fun z => F z y) x‖ ≤ L then smoothGrad (fun z => F z y) x
      else 0, ?_, fun x y => ?_, fun y => ?_⟩
  · have : Measurable fun p : Torus d × Torus d =>
        if ‖G p‖ ≤ L then G p else 0 :=
      Measurable.ite (measurableSet_le hGm.norm measurable_const) hGm measurable_const
    exact this
  · dsimp only
    split_ifs with h
    · exact h
    · simpa using hL
  · obtain ⟨h1, h2⟩ := exists_weak_gradient hL (df_section_lipschitz hF y)
    have h3 : IsWeakGradient (fun x => F x y) (smoothGrad fun z => F z y) :=
      isWeakGradient_iff_isWeakGradientLp.mpr
        ⟨h1.memLp.mono_exponent (by simp), h1.memLp_grad.mono_exponent (by simp), h1.ibp⟩
    refine h3.congr_ae (Filter.EventuallyEq.refl _ _) ?_
    filter_upwards [h2] with x hx
    simp [hx]

theorem df_abs_bound {F : Torus d → Torus d → ℝ} {L : ℝ}
    (hF : ∀ x y x' y', |F x y - F x' y'| ≤
      L * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2)) :
    ∀ x y x' y', |F x y - F x' y'| ≤
      |L| * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2) := fun x y x' y' =>
  (hF x y x' y').trans (mul_le_mul_of_nonneg_right (le_abs_self L) (Real.sqrt_nonneg _))

theorem df_weak_gradient_of_lipschitz {u : Torus d → ℝ} {L : ℝ} (hu : TorusLipschitzWith L u) :
    ∃ g : Torus d → Tangent d, IsWeakGradient u g := by
  have hu' : TorusLipschitzWith |L| u := fun x y =>
    (hu x y).trans (mul_le_mul_of_nonneg_right (le_abs_self L)
      ((dist_nonneg).trans (torusDist_comparison x y).1))
  obtain ⟨h1, -⟩ := exists_weak_gradient (abs_nonneg L) hu'
  exact ⟨_, isWeakGradient_iff_isWeakGradientLp.mpr
    ⟨h1.memLp.mono_exponent (by simp), h1.memLp_grad.mono_exponent (by simp), h1.ibp⟩⟩

/-- **LIP004.** Particle force including the diagonal.

1. For `F` symmetric and Lipschitz for the Euclidean product distance (constant `L`), the diagonal
   `δ(x) = F(x,x)` is Lipschitz (constant `√2 L`).
2. For such `F` there is a measurable, bounded `B` with `B(·, y)` a weak gradient of `F(·, y)` for
   every `y` (the gradient in the first variable), and for every `V ∈ H¹(m)` with weak gradient
   `gV` and every weak gradient `gδ` of the diagonal, the Hamiltonian
   `∑ᵢ V(xᵢ) + (2N)⁻¹ ∑ᵢⱼ F(xᵢ,xⱼ)` is in `H¹(m^N)` with `i`-th gradient component
   `gV(xᵢ) + N⁻¹ ∑_{j≠i} B(xᵢ,xⱼ) + (2N)⁻¹ gδ(xᵢ)`. The values of `B` on the diagonal are never
   used.
3. For Lipschitz interaction data `A` (so `W(x,x) = 0`), there is such a `B` for `W`, and for every
   weak gradient `gV` of `V`, `∇ᵢ H_N = gV(xᵢ) + N⁻¹ ∑_{j≠i} B(xᵢ,xⱼ)` as an
   `IsParticleWeakGradient` (the weak gradient w.r.t. the Gibbs law); weak gradients of `V` exist. -/
theorem particle_force_including_the_diagonal (d : ℕ) :
    (∀ (F : Torus d → Torus d → ℝ) (L : ℝ),
      (∀ x y x' y', |F x y - F x' y'| ≤
        L * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2)) →
      TorusLipschitzWith (Real.sqrt 2 * L) (fun x => F x x)) ∧
    (∀ (F : Torus d → Torus d → ℝ) (L : ℝ), (∀ x y, F x y = F y x) →
      (∀ x y x' y', |F x y - F x' y'| ≤
        L * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2)) →
      ∃ B : Torus d → Torus d → Tangent d, Measurable (Function.uncurry B) ∧
        (∃ M : ℝ, ∀ x y, ‖B x y‖ ≤ M) ∧
        (∀ y, IsWeakGradient (fun x => F x y) (fun x => B x y)) ∧
        (∃ gδ : Torus d → Tangent d, IsWeakGradient (fun x => F x x) gδ) ∧
        ∀ (V : Torus d → ℝ) (gV gδ : Torus d → Tangent d) (N : ℕ+),
          IsWeakGradient V gV → IsWeakGradient (fun x => F x x) gδ →
          IsParticleHaarWeakGradient N
            (fun x : ParticleSpace d N =>
              ∑ i, V (x i) + (1 / (2 * (N : ℝ))) * ∑ i, ∑ j, F (x i) (x j))
            (fun x i => gV (x i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) +
              (2 * (N : ℝ))⁻¹ • gδ (x i))) ∧
    (∀ A : InteractionData d, LipschitzData A →
      (∃ gV : Torus d → Tangent d, IsWeakGradient A.V gV) ∧
      ∃ B : Torus d → Torus d → Tangent d, Measurable (Function.uncurry B) ∧
        (∃ M : ℝ, ∀ x y, ‖B x y‖ ≤ M) ∧
        (∀ y, IsWeakGradient (fun x => A.W x y) (fun x => B x y)) ∧
        ∀ (gV : Torus d → Tangent d) (N : ℕ+), IsWeakGradient A.V gV →
          IsParticleWeakGradient A N (particleHamiltonian A N)
            (fun x i => gV (x i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j))) := by
  have part1 : ∀ (F : Torus d → Torus d → ℝ) (L : ℝ),
      (∀ x y x' y', |F x y - F x' y'| ≤
        L * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2)) →
      TorusLipschitzWith (Real.sqrt 2 * L) (fun x => F x x) :=
    fun F L hF => df_diag_lipschitz hF
  have part2 : ∀ (F : Torus d → Torus d → ℝ) (L : ℝ), (∀ x y, F x y = F y x) →
      (∀ x y x' y', |F x y - F x' y'| ≤
        L * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2)) →
      ∃ B : Torus d → Torus d → Tangent d, Measurable (Function.uncurry B) ∧
        (∃ M : ℝ, ∀ x y, ‖B x y‖ ≤ M) ∧
        (∀ y, IsWeakGradient (fun x => F x y) (fun x => B x y)) ∧
        (∃ gδ : Torus d → Tangent d, IsWeakGradient (fun x => F x x) gδ) ∧
        ∀ (V : Torus d → ℝ) (gV gδ : Torus d → Tangent d) (N : ℕ+),
          IsWeakGradient V gV → IsWeakGradient (fun x => F x x) gδ →
          IsParticleHaarWeakGradient N
            (fun x : ParticleSpace d N =>
              ∑ i, V (x i) + (1 / (2 * (N : ℝ))) * ∑ i, ∑ j, F (x i) (x j))
            (fun x i => gV (x i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) +
              (2 * (N : ℝ))⁻¹ • gδ (x i)) := by
    intro F L hsymm hF
    have hF' := df_abs_bound hF
    obtain ⟨B, hBm, hBM, hB⟩ := df_exists_B (abs_nonneg L) hF'
    refine ⟨B, hBm, ⟨|L|, hBM⟩, hB, df_weak_gradient_of_lipschitz (part1 F L hF), ?_⟩
    intro V gV gδ N hV hδ
    exact df_core hsymm (df_continuous_of_lipschitz (abs_nonneg L) hF') hBm hBM hB hV hδ N
  refine ⟨part1, part2, ?_⟩
  intro A hA
  obtain ⟨LV, hLV⟩ := hA.1
  obtain ⟨LW, hLW⟩ := hA.2
  obtain ⟨B, hBm, hBM, hB, -, hmain⟩ := part2 A.W LW A.W_symm hLW
  refine ⟨df_weak_gradient_of_lipschitz hLV, B, hBm, hBM, hB, fun gV N hV => ?_⟩
  have hδ : IsWeakGradient (fun x => A.W x x) (fun _ => 0) := by
    have : (fun x => A.W x x) = fun _ => (0 : ℝ) := funext A.W_diag
    rw [this]
    exact isWeakGradient_zero
  have := hmain A.V gV (fun _ => 0) N hV hδ
  simp only [smul_zero, add_zero] at this
  exact (isParticleWeakGradient_iff A N _ _).2 this

end DGPS.Lipschitz

/-!
# DEF020: diagonal-force convention

For symmetric Lipschitz `F` with diagonal restriction `δ(x) = F(x,x)`, the pair-interaction energy
`(2N)⁻¹ ∑ⱼₖ F(xⱼ,xₖ)` has `i`-th force `N⁻¹ ∑_{j≠i} B(xᵢ,xⱼ) + (2N)⁻¹ ∇δ(xᵢ)` where `B` is the
gradient of `F` in the first variable. Only the one-variable weak gradient of the restriction `δ`
appears; the ambient gradient of `F` is never evaluated on the diagonal. For zero-diagonal `W`
the `δ`-term vanishes. Both statements are adapters to `particle_force_including_the_diagonal`.
-/

namespace DGPS

variable {d : ℕ}

/-- **DEF020 (off-diagonal force).** For symmetric Lipschitz `F` there is a measurable bounded `B`
with `B(·, y)` a weak gradient of `F(·, y)` for every `y` such that, for every weak gradient `gδ`
of the diagonal restriction `x ↦ F x x`, the pair energy `(2N)⁻¹ ∑ᵢⱼ F(xᵢ,xⱼ)` has weak gradient
with `i`-th component `N⁻¹ ∑_{j≠i} B(xᵢ,xⱼ) + (2N)⁻¹ gδ(xᵢ)`. -/
theorem particle_force_offDiagonal (d : ℕ) (F : Torus d → Torus d → ℝ) (L : ℝ)
    (hsymm : ∀ x y, F x y = F y x)
    (hF : ∀ x y x' y', |F x y - F x' y'| ≤
      L * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2)) :
    ∃ B : Torus d → Torus d → Tangent d, Measurable (Function.uncurry B) ∧
      (∃ M : ℝ, ∀ x y, ‖B x y‖ ≤ M) ∧
      (∀ y, IsWeakGradient (fun x => F x y) (fun x => B x y)) ∧
      ∀ (gδ : Torus d → Tangent d) (N : ℕ+), IsWeakGradient (fun x => F x x) gδ →
        IsParticleHaarWeakGradient N
          (fun x : ParticleSpace d N => (1 / (2 * (N : ℝ))) * ∑ i, ∑ j, F (x i) (x j))
          (fun x i => (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) +
            (2 * (N : ℝ))⁻¹ • gδ (x i)) := by
  have hF' := Lipschitz.df_abs_bound hF
  obtain ⟨B, hBm, hBM, hB⟩ := Lipschitz.df_exists_B (abs_nonneg L) hF'
  refine ⟨B, hBm, ⟨|L|, hBM⟩, hB, fun gδ N hδ => ?_⟩
  have h := Lipschitz.df_core (V := fun _ => (0 : ℝ)) (gV := fun _ => (0 : Tangent d)) hsymm
    (Lipschitz.df_continuous_of_lipschitz (abs_nonneg L) hF') hBm hBM hB isWeakGradient_zero hδ N
  simpa using h

/-- **DEF020 (diagonal restriction).**
1. For `F` Lipschitz for the product distance, the diagonal restriction `x ↦ F x x` is Lipschitz
   and has a weak gradient, an honest one-variable object.
2. If moreover `F` is symmetric with zero diagonal, the pair energy has weak gradient with `i`-th
   component `N⁻¹ ∑_{j≠i} B(xᵢ,xⱼ)`: the diagonal term vanishes.
3. For Lipschitz interaction data `A` (so `W(x,x) = 0`), `∇ᵢ H_N = gV(xᵢ) + N⁻¹ ∑_{j≠i} B(xᵢ,xⱼ)`
   as an `IsParticleWeakGradient` for the Hamiltonian `particleHamiltonian A N`. -/
theorem diagonal_restriction_force (d : ℕ) :
    (∀ (F : Torus d → Torus d → ℝ) (L : ℝ),
      (∀ x y x' y', |F x y - F x' y'| ≤
        L * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2)) →
      TorusLipschitzWith (Real.sqrt 2 * L) (fun x => F x x) ∧
        ∃ gδ : Torus d → Tangent d, IsWeakGradient (fun x => F x x) gδ) ∧
    (∀ (F : Torus d → Torus d → ℝ) (L : ℝ), (∀ x y, F x y = F y x) → (∀ x, F x x = 0) →
      (∀ x y x' y', |F x y - F x' y'| ≤
        L * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2)) →
      ∃ B : Torus d → Torus d → Tangent d, Measurable (Function.uncurry B) ∧
        (∃ M : ℝ, ∀ x y, ‖B x y‖ ≤ M) ∧
        (∀ y, IsWeakGradient (fun x => F x y) (fun x => B x y)) ∧
        ∀ N : ℕ+, IsParticleHaarWeakGradient N
          (fun x : ParticleSpace d N => (1 / (2 * (N : ℝ))) * ∑ i, ∑ j, F (x i) (x j))
          (fun x i => (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j))) ∧
    (∀ A : InteractionData d, LipschitzData A →
      ∃ B : Torus d → Torus d → Tangent d, Measurable (Function.uncurry B) ∧
        (∃ M : ℝ, ∀ x y, ‖B x y‖ ≤ M) ∧
        (∀ y, IsWeakGradient (fun x => A.W x y) (fun x => B x y)) ∧
        ∀ (gV : Torus d → Tangent d) (N : ℕ+), IsWeakGradient A.V gV →
          IsParticleWeakGradient A N (particleHamiltonian A N)
            (fun x i => gV (x i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j))) := by
  refine ⟨fun F L hF => ⟨Lipschitz.df_diag_lipschitz hF,
    Lipschitz.df_weak_gradient_of_lipschitz (Lipschitz.df_diag_lipschitz hF)⟩, ?_, ?_⟩
  · intro F L hsymm hdiag hF
    obtain ⟨B, hBm, hBM, hB, hmain⟩ := particle_force_offDiagonal d F L hsymm hF
    refine ⟨B, hBm, hBM, hB, fun N => ?_⟩
    have hδ : IsWeakGradient (fun x => F x x) (fun _ => 0) := by
      have : (fun x => F x x) = fun _ => (0 : ℝ) := funext hdiag
      rw [this]
      exact isWeakGradient_zero
    simpa using hmain (fun _ => 0) N hδ
  · intro A hA
    obtain ⟨-, B, hBm, hBM, hB, hmain⟩ := (Lipschitz.particle_force_including_the_diagonal d).2.2 A hA
    exact ⟨B, hBm, hBM, hB, hmain⟩

end DGPS
