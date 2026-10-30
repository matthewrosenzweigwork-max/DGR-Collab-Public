import DGPS.Examples.ThreeSpeciesCircle.OrdinaryDeficitCompactness
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryDeficitDistanceBounds
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootLocalStability
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryReferenceLocalStability

/-! Global fixed-field quadratic deficit control in the original square-root
Haar H1 distance. All local, compactness and tail bounds are supplied by the
actual ordinary producers, for the same retained graph and root triple. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private def rootDistance (σ ρ : AbsoluteDensity 1) : ℝ :=
  ordinaryRootH1Deviation σ ρ σ.sqrt

private theorem rootDistance_nonneg (σ ρ : AbsoluteDensity 1) : 0 ≤ rootDistance σ ρ :=
  add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

private theorem rootDistance_rep (σ ρ : AbsoluteDensity 1) (u : Torus 1 → ℝ)
    (hu : σ.sqrt =ᵐ[haar 1] u) :
    rootDistance σ ρ = ordinaryRootH1Deviation σ ρ u := by
  unfold rootDistance ordinaryRootH1Deviation
  have he : (fun x => ρ.sqrt x - σ.sqrt x) =ᵐ[haar 1] fun x => ρ.sqrt x - u x :=
    hu.mono fun x hx => by
      change ρ.sqrt x - σ.sqrt x = ρ.sqrt x - u x
      rw [hx]
  rw [eLpNorm_congr_ae he]

private theorem rootDistance_measure (σ τ ρ : AbsoluteDensity 1)
    (hμ : (densityMeasure σ : Measure (Torus 1)) = densityMeasure τ) :
    rootDistance σ ρ = rootDistance τ ρ := by
  have hs := AbsoluteDensity.sqrt_ae_eq_of_density_ae_eq
    ((densityMeasure_eq_iff_STR02901 σ τ).1 hμ)
  have hg := (isWeakGradient_weakGradient σ.sqrt_mem).ae_eq
    ((isWeakGradient_weakGradient τ.sqrt_mem).congr_ae hs.symm (EventuallyEq.refl _ _))
  have he : (fun x => ρ.sqrt x - σ.sqrt x) =ᵐ[haar 1] fun x => ρ.sqrt x - τ.sqrt x :=
    hs.mono fun x hx => by
      change ρ.sqrt x - σ.sqrt x = ρ.sqrt x - τ.sqrt x
      rw [hx]
  have heG : (fun x => weakGradient ρ.sqrt ρ.sqrt_mem x - weakGradient σ.sqrt σ.sqrt_mem x)
      =ᵐ[haar 1] fun x => weakGradient ρ.sqrt ρ.sqrt_mem x - weakGradient τ.sqrt τ.sqrt_mem x :=
    hg.mono fun x hx => by
      change weakGradient ρ.sqrt ρ.sqrt_mem x - weakGradient σ.sqrt σ.sqrt_mem x =
        weakGradient ρ.sqrt ρ.sqrt_mem x - weakGradient τ.sqrt τ.sqrt_mem x
      rw [hx]
  unfold rootDistance ordinaryRootH1Deviation
  rw [eLpNorm_congr_ae he, eLpNorm_congr_ae heG]

private def minimumDistance (τ : Fin 4 → AbsoluteDensity 1) (ρ : AbsoluteDensity 1) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => rootDistance (τ i) ρ)

private theorem minimumDistance_nonneg (τ : Fin 4 → AbsoluteDensity 1) (ρ : AbsoluteDensity 1) :
    0 ≤ minimumDistance τ ρ :=
  Finset.le_inf' Finset.univ_nonempty _ (fun i _ => rootDistance_nonneg _ _)

private theorem minimumDistance_le (τ : Fin 4 → AbsoluteDensity 1) (ρ : AbsoluteDensity 1)
    (i : Fin 4) : minimumDistance τ ρ ≤ rootDistance (τ i) ρ :=
  Finset.inf'_le _ (Finset.mem_univ i)

private theorem fixed_roots_global (h : ℝ) (τ : Fin 4 → AbsoluteDensity 1)
    (hcompact : ∀ ρ : ℕ → AbsoluteDensity 1,
      Tendsto (fun n => (ordinaryFisher h (ρ n)).toReal -
        2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h (ρ n)).toReal)
        atTop (𝓝 0) →
      ∃ (φ : ℕ → ℕ) (i : Fin 4), StrictMono φ ∧
        Tendsto (fun n => rootDistance (τ i) (ρ (φ n))) atTop (𝓝 0))
    (hlocal : ∀ i : Fin 4, ∃ η c : ℝ, 0 < η ∧ 0 < c ∧ ∀ ρ : AbsoluteDensity 1,
      rootDistance (τ i) ρ ≤ η → c * rootDistance (τ i) ρ ^ 2 ≤
        (ordinaryFisher h ρ).toReal -
          2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h ρ).toReal) :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ : AbsoluteDensity 1,
      c * minimumDistance τ ρ ^ 2 ≤ (ordinaryFisher h ρ).toReal -
        2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h ρ).toReal := by
  classical
  let Δ := fun ρ : AbsoluteDensity 1 => (ordinaryFisher h ρ).toReal -
    2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h ρ).toReal
  have hΔ : ∀ ρ, 0 ≤ Δ ρ := elementary_ordinary_deficit_nonneg h
  obtain ⟨K, hK, hdist⟩ := ordinary_originalH1_information_bound h (τ 0)
  obtain ⟨C, hC, hcoerc⟩ := ordinaryDeficit_large_information h
  by_contra hn
  push_neg at hn
  let cn := fun n : ℕ => min (1 / ((n : ℝ) + 1)) (1 / (4 * K))
  have hcn : ∀ n, 0 < cn n := fun n => lt_min (by positivity) (by positivity)
  have hc0 : Tendsto cn atTop (𝓝 0) := by
    have hn0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, one_div] using (tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ)
          (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)))
    exact squeeze_zero (fun n => (hcn n).le) (fun n => min_le_left _ _) hn0
  choose ρ hfail using fun n : ℕ => hn (cn n) (hcn n)
  have habsorb (n : ℕ) : Δ (ρ n) ≤ 2 * cn n * K * (1 + 2 * C) := by
    have hd0 := minimumDistance_nonneg τ (ρ n)
    have hdroot := rootDistance_nonneg (τ 0) (ρ n)
    have hminsq := pow_le_pow_left₀ hd0 (minimumDistance_le τ (ρ n) 0) 2
    have hd := hdist (ρ n)
    change rootDistance (τ 0) (ρ n) ^ 2 ≤ K * (1 + (ordinaryFisher h (ρ n)).toReal) at hd
    have hI := hcoerc (ρ n)
    have hf := hfail n
    change Δ (ρ n) < cn n * minimumDistance τ (ρ n) ^ 2 at hf
    have hcm : 2 * cn n * K ≤ 1 / 2 := by
      have hm := mul_le_mul_of_nonneg_right (min_le_right (1 / ((n : ℝ) + 1))
        (1 / (4 * K))) (by positivity : 0 ≤ 2 * K)
      have he : 1 / (4 * K) * (2 * K) = (1 / 2 : ℝ) := by
        field_simp [hK.ne']
        norm_num
      dsimp only [cn]
      nlinarith
    have hfirst := mul_le_mul_of_nonneg_left (hminsq.trans hd) (hcn n).le
    have hsecond := mul_le_mul_of_nonneg_left
      (show (ordinaryFisher h (ρ n)).toReal ≤ 2 * (Δ (ρ n) + C) by
        change (ordinaryFisher h (ρ n)).toReal / 2 - C ≤ Δ (ρ n) at hI
        linarith) (mul_nonneg (hcn n).le hK.le)
    have hthird := mul_le_mul_of_nonneg_right hcm (hΔ (ρ n))
    nlinarith
  have hD : Tendsto (fun n => Δ (ρ n)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => hΔ (ρ n)) habsorb ?_
    simpa using ((hc0.const_mul 2).mul_const K).mul_const (1 + 2 * C)
  obtain ⟨φ, i, hφ, hnear⟩ := hcompact ρ hD
  obtain ⟨η, c, hη, hc, hloc⟩ := hlocal i
  have hev : ∀ᶠ n in atTop, rootDistance (τ i) (ρ (φ n)) ≤ η ∧ cn (φ n) < c := by
    filter_upwards [hnear.eventually (gt_mem_nhds hη),
      (hc0.comp hφ.tendsto_atTop).eventually (gt_mem_nhds hc)] with n hn hm
    exact ⟨hn.le, hm⟩
  obtain ⟨n, hn⟩ := hev.exists
  have hl := hloc (ρ (φ n)) hn.1
  have hm := pow_le_pow_left₀ (minimumDistance_nonneg τ (ρ (φ n)))
    (minimumDistance_le τ (ρ (φ n)) i) 2
  have hlow := mul_le_mul_of_nonneg_left hm hc.le
  have hf := hfail (φ n)
  change Δ (ρ (φ n)) < cn (φ n) * minimumDistance τ (ρ (φ n)) ^ 2 at hf
  have hdpos : 0 < minimumDistance τ (ρ (φ n)) ^ 2 := by
    by_contra hd
    have hz : minimumDistance τ (ρ (φ n)) ^ 2 = 0 := le_antisymm (not_lt.mp hd) (sq_nonneg _)
    rw [hz, mul_zero] at hf
    exact (not_lt_of_ge (hΔ _)) hf
  have hstrict := mul_lt_mul_of_pos_right hn.2 hdpos
  change c * rootDistance (τ i) (ρ (φ n)) ^ 2 ≤ Δ (ρ (φ n)) at hl
  linarith

/-- Minimum of the original stored square-root Haar H1 norm sums over the
canonical reference root and the supplied actual three-root family. -/
noncomputable def ordinaryFourRootH1Distance (h : ℝ) (σ : Fin 3 → AbsoluteDensity 1)
    (ρ : AbsoluteDensity 1) : ℝ :=
  minimumDistance (Fin.cases (ordinaryReferenceAbsolute h) σ) ρ

/-- The actual fixed-field ordinary deficit controls squared distance to its
four equality roots on the full original absolute H1 domain. All graph, local,
compactness and high-energy inputs are discharged by their actual producers. -/
theorem ordinaryDeficit_global_same_graph (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ σ : Fin 3 → AbsoluteDensity 1,
        (∀ j θ, (σ j).density (DGPS.Circle.AngularNormalization.angEquiv.symm θ) =
          rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h))
            (DGPS.Circle.AngularNormalization.angSec θ)) ∧
        ∃ c : ℝ, 0 < c ∧ ∀ ρ : AbsoluteDensity 1,
          c * ordinaryFourRootH1Distance h σ ρ ^ 2 ≤
            (ordinaryFisher h ρ).toReal -
              2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h ρ).toReal := by
  classical
  obtain ⟨δR, hδR, hδRr, hRoots⟩ := ordinaryRoot_same_graph_localHaar D
  obtain ⟨δ0, hδ0, hReference⟩ := threefold_reference_localHaar_stability
  let δ := min δR δ0
  refine ⟨δ, lt_min hδR hδ0, (min_le_left _ _).trans hδRr, fun h hh hhd => ?_⟩
  have hhR : h < δR := hhd.trans_le (min_le_left _ _)
  have hh0 : h < δ0 := hhd.trans_le (min_le_right _ _)
  obtain ⟨σ, hσ, hpos, hmin, hcompact⟩ :=
    ordinaryDeficit_compactness_same_graph D h hh (hhR.trans_le hδRr)
  obtain ⟨u, η, c, hU, hη, hc, hlocalR⟩ := hRoots h hh hhR σ hσ hpos hmin
  obtain ⟨η0, c0, hη0, hc0, hlocal0⟩ := hReference h hh hh0
  let τ : Fin 4 → AbsoluteDensity 1 := Fin.cases (ordinaryReferenceAbsolute h) σ
  have hcompact4 : ∀ ρ : ℕ → AbsoluteDensity 1,
      Tendsto (fun n => (ordinaryFisher h (ρ n)).toReal -
        2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h (ρ n)).toReal)
        atTop (𝓝 0) →
      ∃ (φ : ℕ → ℕ) (i : Fin 4), StrictMono φ ∧
        Tendsto (fun n => rootDistance (τ i) (ρ (φ n))) atTop (𝓝 0) := by
    intro ρ hD
    obtain ⟨φ, ρL, ε, hφ, hε, hae, hclass, hstrong⟩ := hcompact ρ hD
    change Tendsto (fun n => rootDistance ρL (ρ (φ n))) atTop (𝓝 0) at hstrong
    rcases hclass with href | ⟨j, hj⟩
    · refine ⟨φ, 0, hφ, ?_⟩
      change Tendsto (fun n => rootDistance (ordinaryReferenceAbsolute h) (ρ (φ n)))
        atTop (𝓝 0)
      convert hstrong using 1
      funext n
      exact (rootDistance_measure ρL (ordinaryReferenceAbsolute h) (ρ (φ n))
        (href.trans (ordinaryReferenceAbsolute_measure h).symm)).symm
    · refine ⟨φ, j.succ, hφ, ?_⟩
      change Tendsto (fun n => rootDistance (σ j) (ρ (φ n))) atTop (𝓝 0)
      convert hstrong using 1
      funext n
      exact (rootDistance_measure ρL (σ j) (ρ (φ n)) hj).symm
  have hlocal4 : ∀ i : Fin 4, ∃ η c : ℝ, 0 < η ∧ 0 < c ∧ ∀ ρ : AbsoluteDensity 1,
      rootDistance (τ i) ρ ≤ η → c * rootDistance (τ i) ρ ^ 2 ≤
        (ordinaryFisher h ρ).toReal -
          2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h ρ).toReal := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · refine ⟨η0, c0, hη0, hc0, fun ρ hnear => ?_⟩
      exact hlocal0 ρ hnear
    · refine ⟨η, c, hη, hc, fun ρ hnear => ?_⟩
      have he := rootDistance_rep (σ j) ρ (u j) (hU j).2.2
      change rootDistance (σ j) ρ ≤ η at hnear
      change c * rootDistance (σ j) ρ ^ 2 ≤ _
      rw [he]
      exact hlocalR j ρ (by rwa [he] at hnear)
  obtain ⟨cG, hcG, hglobal⟩ := fixed_roots_global h τ hcompact4 hlocal4
  exact ⟨σ, hσ, cG, hcG, hglobal⟩

end DGPS.Examples.ThreeSpeciesCircle
