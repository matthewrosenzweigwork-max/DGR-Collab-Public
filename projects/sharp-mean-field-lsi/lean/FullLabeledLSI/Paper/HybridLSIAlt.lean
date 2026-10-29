import FullLabeledLSI.Paper.HybridLSIAltD

/-!
# The hybrid tilted Gaussian log-Sobolev inequality (7.16) (alternative route)

For `h(x,y) = √κ_R F̃(x,y) e^{u_R(G)/2}` with `F̃ = polyB e c Bs` and `P̃ = κ_R⁻¹ e^{-u_R(G)} Q̃`
(`Q̃ = hybMeasure μ N J`, `G = Gcoll Bs y`):
`(ρ/2) Ent_{P̃}(h²) ≤ ∫ Σ_i |∇_{x_i} h|² dP̃ + ∫ Σ_{i,m} λ_{m+1} (∂_{y_{i,m}} h)² dP̃`,  `ρ = (bRate μ lam C).toReal`.
Proof: entropy subadditivity on `μ^{⊗N} ⊗ P̃_y` (`ent_prod_le`), the Gaussian LSI for the tilted block
(`gauss_lsi_smooth`, `tilted_law`, `Sig_le_mobility`) and the torus LSI (`torus_lsi_bdd`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal ContDiff

noncomputable section

namespace SharpLSI.FL

open SharpLSI SharpLSI.FL.Gross

variable {d N J : ℕ}

/-! ### Transport along the reshape -/

/-- The reshape as a continuous linear map. -/
def reshapeL (N J : ℕ) : (Fin N → Fin J → ℝ) →L[ℝ] (Fin (N * J) → ℝ) :=
  ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin J => ℝ) (finProdFinEquiv.symm k).2).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Fin J → ℝ)
        (finProdFinEquiv.symm k).1)

theorem reshapeL_apply (y : Fin N → Fin J → ℝ) : reshapeL N J y = reshape N J y := by
  funext k
  obtain ⟨⟨i, m⟩, rfl⟩ := finProdFinEquiv.surjective k
  have e : finProdFinEquiv.symm (finProdFinEquiv (i, m)) = (i, m) := Equiv.symm_apply_apply _ _
  simp only [reshapeL, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, e]
  rw [reshape_apply]

theorem reshapeL_single (i : Fin N) (m : Fin J) :
    reshapeL N J (Pi.single i (Pi.single m (1 : ℝ))) = Pi.single (finProdFinEquiv (i, m)) 1 := by
  funext k
  obtain ⟨⟨i', m'⟩, rfl⟩ := finProdFinEquiv.surjective k
  rw [reshapeL_apply, reshape_apply]
  by_cases hi : i' = i
  · subst hi
    by_cases hm : m' = m
    · subst hm; simp
    · have : finProdFinEquiv (i', m') ≠ finProdFinEquiv (i', m) := fun h => hm (by simpa using h)
      simp [hm, this]
  · have : finProdFinEquiv (i', m') ≠ finProdFinEquiv (i, m) := fun h => hi (by simpa using congrArg Prod.fst (finProdFinEquiv.injective h))
    simp [hi, this]

theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (ι : α ≃ᵐ β)
    (m : Measure α) (f : β → ℝ≥0∞) :
    (m.withDensity (f ∘ ι)).map ι = (m.map ι).withDensity f := by
  ext s hs
  rw [Measure.map_apply ι.measurable hs, withDensity_apply _ (ι.measurable hs),
    withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_map_equiv, ← lintegral_indicator (ι.measurable hs)]
  refine lintegral_congr fun a => ?_
  simp only [Set.indicator, Set.mem_preimage, Function.comp]
  rfl


theorem ent_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (ι : α ≃ᵐ β)
    (m : Measure α) (u : β → ℝ) : ent (m.map ι) u = ent m (u ∘ ι) := by
  unfold ent
  have hi : Integrable u (m.map ι) ↔ Integrable (u ∘ ι) m := integrable_map_equiv ι u
  by_cases h : Integrable u (m.map ι)
  · have h' := hi.1 h
    simp only [h, h', ite_true]
    rw [lintegral_map_equiv, integral_map_equiv]
    rfl
  · have h' : ¬ Integrable (u ∘ ι) m := fun h'' => h (hi.2 h'')
    simp only [h, h', ite_false]

/-! ### The hybrid tilted measure and the test function -/

section hyb
variable {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}
  (A : FiniteRankApprox W μ e) (R : ℕ)

/-- The flattening of the Gaussian coordinates, as a measurable equivalence of the hybrid space. -/
def hybFlat (N J : ℕ) :
    (Config N d × (Fin N → Fin J → ℝ)) ≃ᵐ (Config N d × (Fin (N * J) → ℝ)) :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (reshape N J)

/-- **The tilted comparison measure** `P̃ = κ_R⁻¹ e^{-u_R(G)} Q̃` on the hybrid space. -/
def hybTiltAlt (μ : Measure (Torus d)) (A : FiniteRankApprox W μ e) (R J : ℕ) {N : ℕ}
    (B : Finset (Fin N)) : Measure (Config N d × (Fin N → Fin J → ℝ)) :=
  (hybMeasure μ N J).withDensity
    fun w => ENNReal.ofReal (tiltDens A R J B (reshape N J w.2))

/-- The test function `h = √κ_R F̃ e^{u_R(G)/2}`. -/
def hybHAlt (A : FiniteRankApprox W μ e) (R : ℕ) (e : ℕ → Torus d → ℝ) {N J : ℕ}
    (c : (Fin N → Fin (J + 1)) → ℝ) (B : Finset (Fin N))
    (w : Config N d × (Fin N → Fin J → ℝ)) : ℝ :=
  Real.sqrt (kappaR A R) * polyB e c B w * Real.exp (uR A R (zext (Gcoll B w.2)) / 2)

/-- The torus energy density `Σ_i |∇_{x_i} h|²`. -/
def energyX {N J : ℕ} (h : Config N d × (Fin N → Fin J → ℝ) → ℝ)
    (w : Config N d × (Fin N → Fin J → ℝ)) : ℝ :=
  gradPair (fun x => h (x, w.2)) (fun x => h (x, w.2)) w.1

/-- The Gaussian energy density `Σ_{i,m} λ_{m+1} (∂_{y_{i,m}} h)²`. -/
def energyY {N J : ℕ} (lam : ℕ → ℝ) (h : Config N d × (Fin N → Fin J → ℝ) → ℝ)
    (w : Config N d × (Fin N → Fin J → ℝ)) : ℝ :=
  ∑ i : Fin N, ∑ m : Fin J, lam ((m : ℕ) + 1) *
    fderiv ℝ (fun y => h (w.1, y)) w.2 (Pi.single i (Pi.single m 1)) ^ 2

theorem hybTilt_map [IsProbabilityMeasure μ] {N : ℕ} (J : ℕ) (B : Finset (Fin N)) :
    (hybTiltAlt μ A R J B).map (hybFlat N J) =
      (Measure.pi fun _ : Fin N => μ).prod (Pt A R J B) := by
  have hmp : MeasurePreserving (hybFlat N J) (hybMeasure μ N J)
      ((Measure.pi fun _ : Fin N => μ).prod (gpi (N * J))) :=
    MeasurePreserving.prod (MeasurePreserving.id _) (reshape_measurePreserving N J)
  have hmeas : Measurable fun y : Fin (N * J) → ℝ => ENNReal.ofReal (tiltDens A R J B y) := by
    unfold tiltDens
    exact ENNReal.measurable_ofReal.comp
      ((continuous_uT (A := A) (R := R) (J := J) (B := B)).neg.rexp.div_const _).measurable
  unfold hybTiltAlt Pt
  have hf : (fun w : Config N d × (Fin N → Fin J → ℝ) =>
      ENNReal.ofReal (tiltDens A R J B (reshape N J w.2))) =
      (fun z : Config N d × (Fin (N * J) → ℝ) => ENNReal.ofReal (tiltDens A R J B z.2)) ∘
        hybFlat N J := rfl
  rw [hf, map_withDensity_equiv, hmp.map_eq, prod_withDensity_right hmeas]

end hyb

section final
variable {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}
  (A : FiniteRankApprox W μ e) {R : ℕ}

theorem Gc_reshape (B : Finset (Fin N)) (y : Fin N → Fin J → ℝ) :
    Gc J B (reshape N J y) = Gcoll B y := by
  funext m
  rw [Gc_apply]
  unfold Gcoll lowN
  simp only [reshape_apply]

/-- `u_R(G) = uT ∘ reshape`. -/
theorem uR_zext_Gcoll (B : Finset (Fin N)) (y : Fin N → Fin J → ℝ) :
    uR A R (zext (Gcoll B y)) = uT A R J B (reshape N J y) := by
  unfold uT uJ
  rw [Gc_reshape]
  rfl

theorem hybHAlt_eq (c : (Fin N → Fin (J + 1)) → ℝ) (B : Finset (Fin N))
    (w : Config N d × (Fin N → Fin J → ℝ)) :
    hybHAlt A R e c B w = HLA.hh c (fun j => HLA.Yf B j) (fun j => HLA.Xf e B j) (uT A R J B)
      (kappaR A R) w.1 (reshape N J w.2) := by
  rw [HLA.hh_eq]
  unfold hybHAlt HLA.sF
  rw [uR_zext_Gcoll, show polyB e c B w = polyB e c B (w.1, w.2) from rfl, HLA.polyB_eq]
  ring

theorem energyY_eq (lam : ℕ → ℝ) (φ : (Fin (N * J) → ℝ) → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (h : Config N d × (Fin N → Fin J → ℝ) → ℝ) (x : Config N d) (y : Fin N → Fin J → ℝ)
    (hh' : ∀ y', h (x, y') = φ (reshape N J y')) :
    energyY lam h (x, y) =
      HLA.Eyy (fun k : Fin (N * J) => lam ((flatMode k : ℕ) + 1)) φ (reshape N J y) := by
  unfold energyY HLA.Eyy
  have hfun : (fun y' : Fin N → Fin J → ℝ => h (x, y')) = φ ∘ reshapeL N J := by
    funext y'; simp [reshapeL_apply, hh']
  simp only [hfun]
  have hdiff : DifferentiableAt ℝ φ (reshapeL N J y) :=
    (hφ.differentiable (by simp)) _
  have hder : ∀ v, fderiv ℝ (φ ∘ reshapeL N J) y v = fderiv ℝ φ (reshape N J y) (reshapeL N J v) := by
    intro v
    rw [fderiv_comp y hdiff (reshapeL N J).differentiableAt, reshapeL_apply]
    simp
  simp only [hder, reshapeL_single]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin N × Fin J ≃ Fin (N * J)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
  simp [flatMode]

/-- **The hybrid tilted Gaussian log-Sobolev inequality (7.16)** (alternative route).

For `h = √κ_R F̃ e^{u_R(G)/2}`, `F̃ = polyB e c Bs`, and `P̃ = κ_R⁻¹ e^{-u_R(G)} Q̃`,
`(ρ/2) Ent_{P̃}(h²) ≤ ∫ Σ_i |∇_{x_i} h|² dP̃ + ∫ Σ_{i,m} λ_{m+1} (∂_{y_{i,m}} h)² dP̃`,
`ρ = (bRate μ lam C).toReal`. -/
theorem hybrid_lsi_tilted_alt [IsProbabilityMeasure μ] (hac : μ ≪ volume)
    {lam : ℕ → ℝ} (he : IsRefEigenbasis μ e lam) (hC1 : ∀ m, C1T (e m))
    (hrl : RLSLeLamOne μ lam) (hJ : ∀ i ∈ A.s R, i < J) {σ : ℝ} (hσ : 0 < σ)
    (hpos : PosTm A R J σ) {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (A.a R) C)
    (Bs : Finset (Fin N)) (hB : Bs.card < N) (c : (Fin N → Fin (J + 1)) → ℝ) :
    (bRate μ lam C).toReal / 2 *
        (ent (hybTiltAlt μ A R J Bs) (fun w => hybHAlt A R e c Bs w ^ 2)).toReal ≤
      ∫ w, energyX (hybHAlt A R e c Bs) w ∂hybTiltAlt μ A R J Bs +
      ∫ w, energyY lam (hybHAlt A R e c Bs) w ∂hybTiltAlt μ A R J Bs := by
  set ρ : ℝ := (bRate μ lam C).toReal with hρdef
  have hρ0 : 0 ≤ ρ := ENNReal.toReal_nonneg
  have hlam0 : ∀ m : ℕ, 0 ≤ lam (m + 1) := fun m => lam_succ_nonneg he m
  -- nonnegativity of the right-hand side
  have hrhs : 0 ≤ ∫ w, energyX (hybHAlt A R e c Bs) w ∂hybTiltAlt μ A R J Bs +
      ∫ w, energyY lam (hybHAlt A R e c Bs) w ∂hybTiltAlt μ A R J Bs := by
    refine add_nonneg (integral_nonneg fun w => gradPair_nonneg_self _ _)
      (integral_nonneg fun w => ?_)
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun m _ =>
      mul_nonneg (hlam0 _) (sq_nonneg _)
  rcases hρ0.eq_or_lt with h0 | hρpos
  · rw [← h0]; simpa using hrhs
  -- the rate of the torus factor
  have hrtop : rLS μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hrl
  have hbtop : bRate μ lam C ≠ ⊤ := ne_top_of_le_ne_top hrtop (min_le_left _ _)
  have hρa : ρ ≤ (rLS μ).toReal := ENNReal.toReal_mono hrtop (min_le_left _ _)
  have ha0 : 0 < (rLS μ).toReal := lt_of_lt_of_le hρpos hρa
  have hrls : ENNReal.ofReal (rLS μ).toReal ≤ rLS μ := (ENNReal.ofReal_toReal hrtop).le
  -- the flat data
  have hPt : IsProbabilityMeasure (HLA.tPt (uT A R J Bs) (kappaR A R)) := by
    rw [HLA.tPt_eq]; exact isProbabilityMeasure_Pt hJ hσ hpos hB
  have hκ : 0 < kappaR A R := kappa_pos A hJ hσ hpos
  have hcore := HLA.core_lsi (c := c) (Y := fun j => HLA.Yf Bs j) (Xj := fun j => HLA.Xf e Bs j)
    (u := uT A R J Bs) (κ := kappaR A R) (fun j => HLA.tg_Yf Bs j) (HLA.tg_uT A hJ)
    (fun j => HLA.C1C_Xf hC1 Bs j) hκ (fun k : Fin (N * J) => lam ((flatMode k : ℕ) + 1))
    (fun k => hlam0 _) hρ0 ha0 hρa hac hrls
    (fun f hf hL2 hE => HLA.hgl_hybrid hJ hσ hpos hB hC he hrl f hf hL2 hE)
  rw [HLA.tPt_eq, ← hybTilt_map A R J Bs] at hcore
  rw [ent_map_equiv, integral_map_equiv, integral_map_equiv] at hcore
  -- identify the integrands
  have hent : (fun w => HLA.hh c (fun j => HLA.Yf Bs j) (fun j => HLA.Xf e Bs j) (uT A R J Bs)
      (kappaR A R) (hybFlat N J w).1 (hybFlat N J w).2 ^ 2) = fun w => hybHAlt A R e c Bs w ^ 2 := by
    funext w; rw [hybHAlt_eq]; rfl
  have hX : (fun w => gradPair (fun x => HLA.hh c (fun j => HLA.Yf Bs j) (fun j => HLA.Xf e Bs j)
        (uT A R J Bs) (kappaR A R) x (hybFlat N J w).2)
      (fun x => HLA.hh c (fun j => HLA.Yf Bs j) (fun j => HLA.Xf e Bs j)
        (uT A R J Bs) (kappaR A R) x (hybFlat N J w).2) (hybFlat N J w).1) =
      fun w => energyX (hybHAlt A R e c Bs) w := by
    funext w
    unfold energyX
    congr 1 <;> (funext x; rw [hybHAlt_eq]; rfl)
  have hY : (fun w => HLA.Eyy (fun k : Fin (N * J) => lam ((flatMode k : ℕ) + 1))
        (fun g => HLA.hh c (fun j => HLA.Yf Bs j) (fun j => HLA.Xf e Bs j) (uT A R J Bs)
          (kappaR A R) (hybFlat N J w).1 g) (hybFlat N J w).2) =
      fun w => energyY lam (hybHAlt A R e c Bs) w := by
    funext w
    exact (energyY_eq lam _ (HLA.contDiff_hh_slice (c := c) (Xj := fun j => HLA.Xf e Bs j)
      (κ := kappaR A R) (fun j => HLA.tg_Yf Bs j) (HLA.tg_uT A hJ) w.1) (hybHAlt A R e c Bs)
      w.1 w.2 (fun y' => hybHAlt_eq A c Bs (w.1, y'))).symm
  have hent' : ((fun z : Config N d × (Fin (N * J) → ℝ) => HLA.hh c (fun j => HLA.Yf Bs j)
      (fun j => HLA.Xf e Bs j) (uT A R J Bs) (kappaR A R) z.1 z.2 ^ 2) ∘ ⇑(hybFlat N J)) =
      fun w => hybHAlt A R e c Bs w ^ 2 := hent
  rw [hent', hX, hY] at hcore
  exact hcore


/-- The density of `P̃` with respect to `Q̃`: `κ_R⁻¹ e^{-u_R(G)}`. -/
theorem tiltDens_reshape (B : Finset (Fin N)) (y : Fin N → Fin J → ℝ) :
    tiltDens A R J B (reshape N J y) = Real.exp (-uR A R (zext (Gcoll B y))) / kappaR A R := by
  unfold tiltDens; rw [uR_zext_Gcoll]

/-- Integrals against `P̃` are integrals against `Q̃` with the density `κ_R⁻¹ e^{-u_R(G)}`. -/
theorem integral_hybTiltAlt (hκ : 0 < kappaR A R) (B : Finset (Fin N))
    (f : Config N d × (Fin N → Fin J → ℝ) → ℝ) :
    ∫ w, f w ∂hybTiltAlt μ A R J B =
      ∫ w, Real.exp (-uR A R (zext (Gcoll B w.2))) / kappaR A R * f w ∂hybMeasure μ N J := by
  have hm : Measurable fun w : Config N d × (Fin N → Fin J → ℝ) =>
      tiltDens A R J B (reshape N J w.2) := by
    unfold tiltDens
    exact (((continuous_uT (A := A) (R := R) (J := J) (B := B)).neg.rexp.div_const _).measurable).comp
      ((reshape N J).measurable.comp measurable_snd)
  have h0 : ∀ w : Config N d × (Fin N → Fin J → ℝ), 0 ≤ tiltDens A R J B (reshape N J w.2) :=
    fun w => div_nonneg (Real.exp_pos _).le hκ.le
  unfold hybTiltAlt
  rw [HLA.integral_wd hm h0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [tiltDens_reshape]

end final

end SharpLSI.FL

end
