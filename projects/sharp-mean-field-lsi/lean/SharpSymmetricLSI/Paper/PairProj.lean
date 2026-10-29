import SharpSymmetricLSI.Paper.Tensorize

/-!
# Two-particle projections and weak gradients (Phase 3, lane D; R6)

For `i ≠ j`, `y ↦ (y_i, y_j)` from `𝕋^{N×d}` to `𝕋^{2×d}` is measure preserving, and
`y ↦ u(y_i, y_j)` has weak gradient `∇u` placed in blocks `i` and `j`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace SharpLSI

variable {N d : ℕ}

/-- The pair projection `y ↦ (y_i, y_j)`. -/
def projPair (i j : Fin N) (y : UnitAddTorus (Fin N × Fin d)) : UnitAddTorus (Fin 2 × Fin d) :=
  fun q => y (if q.1 = 0 then i else j, q.2)

theorem measurable_projPair (i j : Fin N) : Measurable (projPair (d := d) i j) :=
  measurable_pi_iff.mpr fun q => measurable_pi_apply _

theorem prod_two_points {M : Type*} [CommMonoid M] {i j : Fin N} (hij : i ≠ j) (A B : M) :
    ∏ a : Fin N, (if a = i then A else if a = j then B else 1) = A * B := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
  simp only [if_neg (Ne.symm hij)]
  rw [Finset.prod_eq_one]
  · simp
  · intro a ha
    have h1 : a ≠ j := (Finset.mem_erase.mp ha).1
    have h2 : a ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
    simp [h1, h2]

theorem measurePreserving_projPair {i j : Fin N} (hij : i ≠ j) :
    MeasurePreserving (projPair (d := d) i j) volume volume := by
  refine ⟨measurable_projPair i j, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (measurable_projPair i j) (MeasurableSet.univ_pi hs)]
  set t : Fin N × Fin d → Set UnitAddCircle := fun p =>
    if p.1 = i then s (0, p.2) else if p.1 = j then s (1, p.2) else univ with ht
  have hpre : projPair (d := d) i j ⁻¹' univ.pi s = univ.pi t := by
    ext y
    simp only [mem_preimage, Set.mem_pi, mem_univ, true_implies, projPair, ht, Prod.forall]
    constructor
    · intro h a k
      by_cases hai : a = i
      · subst hai; simpa using h 0 k
      · by_cases haj : a = j
        · subst haj; simpa [hai] using h 1 k
        · simp [hai, haj]
    · intro h b k
      fin_cases b
      · simpa using h i k
      · simpa [Ne.symm hij] using h j k
  rw [hpre, volume_pi, Measure.pi_pi, Fintype.prod_prod_type, Fintype.prod_prod_type,
    Fin.prod_univ_two]
  have : ∀ a : Fin N, ∏ k : Fin d, (volume : Measure UnitAddCircle) (t (a, k)) =
      if a = i then ∏ k, volume (s (0, k)) else if a = j then ∏ k, volume (s (1, k)) else 1 :=
    fun a => by
      by_cases hai : a = i
      · simp [ht, hai]
      · by_cases haj : a = j
        · subst haj; simp [ht, hai]
        · simp [ht, hai, haj]
  simp_rw [this]
  exact prod_two_points hij _ _

/-- The pair projection on `ℝ^{N×d}`. -/
noncomputable def projPairL (i j : Fin N) : (Fin N × Fin d → ℝ) →L[ℝ] (Fin 2 × Fin d → ℝ) :=
  ContinuousLinearMap.pi fun q => ContinuousLinearMap.proj (if q.1 = 0 then i else j, q.2)

theorem projPair_liftT (i j : Fin N) (x : Fin N × Fin d → ℝ) :
    projPair i j (liftT x) = liftT (projPairL i j x) := rfl

theorem projPairL_single {i j : Fin N} (hij : i ≠ j) (p : Fin N × Fin d) :
    projPairL i j (Pi.single p 1) = if p.1 = i then Pi.single (0, p.2) 1
      else if p.1 = j then Pi.single (1, p.2) 1 else 0 := by
  funext q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨b, k⟩ := q
  simp only [projPairL, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
  fin_cases b
  · by_cases h1 : p1 = i
    · subst h1; by_cases hk : k = p2
      · subst hk; simp [Pi.single_apply]
      · simp [Pi.single_apply, Prod.ext_iff, Ne.symm hk]
    · by_cases h2 : p1 = j
      · subst h2; simp [Pi.single_apply, Prod.ext_iff, h1, Ne.symm h1]
      · simp [Pi.single_apply, Prod.ext_iff, h1, h2, Ne.symm h1]
  · by_cases h1 : p1 = i
    · subst h1; simp [Pi.single_apply, Prod.ext_iff, hij, Ne.symm hij]
    · by_cases h2 : p1 = j
      · subst h2; by_cases hk : k = p2
        · subst hk; simp [Pi.single_apply, h1]
        · simp [Pi.single_apply, Prod.ext_iff, h1, Ne.symm hk]
      · simp [Pi.single_apply, Prod.ext_iff, h1, h2, Ne.symm h2]

theorem integrable_comp_projPair {i j : Fin N} (hij : i ≠ j) {u : UnitAddTorus (Fin 2 × Fin d) → ℝ}
    (hu : Integrable u volume) : Integrable (u ∘ projPair i j) volume :=
  (measurePreserving_projPair hij).integrable_comp_of_integrable hu

theorem lintegral_comp_projPair {i j : Fin N} (hij : i ≠ j)
    {F : UnitAddTorus (Fin 2 × Fin d) → ℝ≥0∞} (hF : AEMeasurable F volume) :
    ∫⁻ y, F (projPair i j y) = ∫⁻ x, F x := by
  rw [← lintegral_map' (by rwa [(measurePreserving_projPair hij).map_eq])
    (measurable_projPair i j).aemeasurable, (measurePreserving_projPair hij).map_eq]

/-- The pair-projected gradient. -/
def pairGrad (i j : Fin N) (g : UnitAddTorus (Fin 2 × Fin d) → Fin 2 × Fin d → ℝ)
    (y : UnitAddTorus (Fin N × Fin d)) (p : Fin N × Fin d) : ℝ :=
  if p.1 = i then g (projPair i j y) (0, p.2) else if p.1 = j then g (projPair i j y) (1, p.2)
    else 0

/-- **Weak gradients of two-particle functions.** -/
theorem isWeakGrad_comp_projPair {i j : Fin N} (hij : i ≠ j) {u : UnitAddTorus (Fin 2 × Fin d) → ℝ}
    {g : UnitAddTorus (Fin 2 × Fin d) → Fin 2 × Fin d → ℝ} (h : IsWeakGrad u g)
    (hu : Integrable u volume) (hg : ∀ q, Integrable (fun x => g x q) volume) :
    IsWeakGrad (fun y => u (projPair i j y)) (pairGrad i j g) := by
  set F : ℕ → UnitAddTorus (Fin N × Fin d) → ℝ := fun n y => moll n u (projPair i j y) with hF
  set G : ℕ → UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ :=
    fun n => pairGrad i j (fun x q => moll n (fun z => g z q) x) with hG
  have hpair : ∀ n, IsWeakGrad (F n) (G n) := by
    intro n
    have hΨ : ContDiff ℝ ∞ (moll n u ∘ liftT) := moll_comp_liftT_contDiff n hu
    have hcomp : F n ∘ liftT = (moll n u ∘ liftT) ∘ projPairL i j := by
      funext x; simp [hF, Function.comp, projPair_liftT]
    have hs : ContDiff ℝ 1 (F n ∘ liftT) := by
      rw [hcomp]; exact (hΨ.of_le (by simp)).comp (projPairL i j).contDiff
    have hc := isWeakGrad_of_contDiff hs
    convert hc using 1
    funext y p
    have hd := (((hΨ.differentiable (by simp)) (projPairL i j (secT y))).hasFDerivAt).comp
      (secT y) (projPairL i j).hasFDerivAt
    rw [hcomp, hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    rw [projPairL_single hij]
    have hl : liftT (projPairL i j (secT y)) = projPair i j y := by
      rw [← projPair_liftT, liftT_secT]
    by_cases h1 : p.1 = i
    · simp only [hG, pairGrad, if_pos h1]
      rw [moll_comp_liftT, fderiv_mollL_of_isWeakGrad h n _ (0, p.2), ← hl]
      exact congrFun (moll_comp_liftT n (fun x => g x (0, p.2))) _
    · by_cases h2 : p.1 = j
      · simp only [hG, pairGrad, if_neg h1, if_pos h2]
        rw [moll_comp_liftT, fderiv_mollL_of_isWeakGrad h n _ (1, p.2), ← hl]
        exact congrFun (moll_comp_liftT n (fun x => g x (1, p.2))) _
      · simp [hG, pairGrad, h1, h2]
  have hmeas_u := hu.aestronglyMeasurable
  have hGi : ∀ (gg : UnitAddTorus (Fin 2 × Fin d) → Fin 2 × Fin d → ℝ),
      (∀ q, Integrable (fun x => gg x q) volume) → ∀ p, Integrable (fun y => pairGrad i j gg y p)
        volume := fun gg hgg p => by
    by_cases h1 : p.1 = i
    · simp only [pairGrad, h1, ↓reduceIte]; exact integrable_comp_projPair hij (hgg (0, p.2))
    · by_cases h2 : p.1 = j
      · simp only [pairGrad, if_neg h1, if_pos h2]; exact integrable_comp_projPair hij (hgg (1, p.2))
      · simp [pairGrad, h1, h2]
  refine isWeakGrad_of_tendsto hpair (fun n => integrable_comp_projPair hij (integrable_moll n hu))
    (fun n => hGi _ fun q => integrable_moll n (hg q)) (integrable_comp_projPair hij hu)
    (hGi g hg) ?_ (fun p => ?_)
  · refine (tendsto_moll hu).congr fun n => ?_
    exact (lintegral_comp_projPair hij (F := fun x => ‖moll n u x - u x‖ₑ)
      (((measurable_moll n hu).aestronglyMeasurable.sub hmeas_u).enorm)).symm
  · have key : ∀ q, Tendsto (fun n => ∫⁻ y, ‖moll n (fun z => g z q) (projPair i j y) -
        g (projPair i j y) q‖ₑ) atTop (𝓝 0) := fun q =>
      (tendsto_moll (hg q)).congr fun n =>
        (lintegral_comp_projPair hij (F := fun x => ‖moll n (fun z => g z q) x - g x q‖ₑ)
          (((measurable_moll n (hg q)).aestronglyMeasurable.sub
            (hg q).aestronglyMeasurable).enorm)).symm
    by_cases h1 : p.1 = i
    · simpa [hG, pairGrad, h1] using key (0, p.2)
    · by_cases h2 : p.1 = j
      · simp only [hG, pairGrad, if_neg h1, if_pos h2]; exact key (1, p.2)
      · simp [hG, pairGrad, h1, h2]

end SharpLSI
