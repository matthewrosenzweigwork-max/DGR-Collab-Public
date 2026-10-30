import DGPS.Examples.ThreeSpeciesCircle.OrdinaryDeficitGlobal
import DGPS.Examples.ThreeSpeciesCircle.NearestRootMomentError

/-! Actual global ordinary deficit supplies the square-root distance budget for
all finite species families at the SAME retained root triple. No budget-versus-
deficit assumption is added to the final producer. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The finite minimum is attained by one of the SAME four original H1 roots. -/
theorem ordinaryFourRootH1Distance_attained (h : ℝ)
    (σ : Fin 3 → AbsoluteDensity 1) (ρ : AbsoluteDensity 1) :
    ∃ i : Fin 4, ordinaryRootH1Deviation (Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ i)
      ρ (Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ i).sqrt =
        ordinaryFourRootH1Distance h σ ρ := by
  classical
  let f : Fin 4 → ℝ := fun i => ordinaryRootH1Deviation
    (Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ i) ρ
    (Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ i).sqrt
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin 4)) f
    Finset.univ_nonempty
  refine ⟨i, ?_⟩
  change f i = Finset.univ.inf' Finset.univ_nonempty f
  exact le_antisymm (Finset.le_inf' Finset.univ_nonempty _ (fun j hj => hmin j hj))
    (Finset.inf'_le _ hi)

/-- The original square-root L2 distance is bounded by the square of the
stored original H1 norm sum, with no representative replacement. -/
theorem rootDistanceSq_le_originalH1 (σ ρ : AbsoluteDensity 1) :
    rootDistanceSq ρ σ ≤ ordinaryRootH1Deviation σ ρ σ.sqrt ^ 2 := by
  let A := (eLpNorm (fun x => ρ.sqrt x - σ.sqrt x) 2 (haar 1)).toReal
  let B := (eLpNorm (fun x => weakGradient ρ.sqrt ρ.sqrt_mem x -
    weakGradient σ.sqrt σ.sqrt_mem x) 2 (haar 1)).toReal
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hd : MemLp (fun x => ρ.sqrt x - σ.sqrt x) 2 (haar 1) :=
    ρ.memLp_sqrt.sub σ.memLp_sqrt
  have he : A ^ 2 = rootDistanceSq ρ σ := by
    dsimp only [A, rootDistanceSq]
    rw [toReal_eLpNorm_two hd,
      Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
  change rootDistanceSq ρ σ ≤ (A + B) ^ 2
  rw [← he]
  nlinarith

/-- A pointwise exact four-root coercivity estimate yields a genuine attaining
assignment and a count- and weight-independent budget for the actual family. -/
theorem ordinaryFamily_nearest_root_budget (h : ℝ)
    (σ : Fin 3 → AbsoluteDensity 1) {c : ℝ} (hc : 0 < c)
    (hglobal : ∀ ρ : AbsoluteDensity 1,
      c * ordinaryFourRootH1Distance h σ ρ ^ 2 ≤ (ordinaryFisher h ρ).toReal -
        2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h ρ).toReal)
    (F : SpeciesFamily 1) :
    ∃ label : Fin F.count → Fin 4,
      (∀ s, ordinaryRootH1Deviation
        (Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ (label s)) (F.density s)
        (Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ (label s)).sqrt =
          ordinaryFourRootH1Distance h σ (F.density s)) ∧
      rootDistanceBudget F (Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ) label ≤
        (∑ s, F.weight s * ((ordinaryFisher h (F.density s)).toReal -
          2 * (ordinaryLSRate (ordinaryReference h)).toReal *
            (ordinaryEntropy h (F.density s)).toReal)) / c := by
  classical
  choose label hlabel using fun s : Fin F.count => ordinaryFourRootH1Distance_attained h σ (F.density s)
  refine ⟨label, hlabel, ?_⟩
  apply (le_div_iff₀ hc).2
  rw [rootDistanceBudget, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro s hs
  have hroot := rootDistanceSq_le_originalH1
    (Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ (label s)) (F.density s)
  rw [hlabel s] at hroot
  have hpoint := (mul_le_mul_of_nonneg_left hroot hc.le).trans (hglobal (F.density s))
  have hw := mul_le_mul_of_nonneg_left hpoint (F.weight_nonneg s)
  convert hw using 1 <;> ring

private theorem budget_substitution {B D u c K : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hu : 0 ≤ u) (hc : 0 < c) (hK : 0 ≤ K)
    (hbudget : B ≤ D / c) :
    K * (u * Real.sqrt B + B) ≤
      (K * (1 + Real.sqrt (1 / c) + 1 / c)) * (u * Real.sqrt D + D) := by
  let L := 1 + Real.sqrt (1 / c) + 1 / c
  have hcinv : 0 ≤ 1 / c := by positivity
  have hLc : 1 / c ≤ L := by dsimp only [L]; linarith [Real.sqrt_nonneg (1 / c)]
  have hLs : Real.sqrt (1 / c) ≤ L := by dsimp only [L]; linarith
  have hB' : B ≤ L * D := by
    have hh := mul_le_mul_of_nonneg_right hLc hD
    have he : D / c = (1 / c) * D := by ring
    rw [he] at hbudget
    exact hbudget.trans hh
  have hs : Real.sqrt B ≤ L * Real.sqrt D := by
    have hh := Real.sqrt_le_sqrt hbudget
    rw [show D / c = (1 / c) * D by ring,
      Real.sqrt_mul hcinv] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hLs (Real.sqrt_nonneg D))
  have hu' := mul_le_mul_of_nonneg_left hs hu
  have hm := mul_le_mul_of_nonneg_left (add_le_add hu' hB') hK
  convert hm using 1 <;> dsimp only [L] <;> ring

/-- SAME-D actual roots and the actual global ordinary deficit control the
true interacting C error for every original finite family. All constants precede
the count, positive weights and densities; no desired stability premise remains. -/
theorem ordinaryDeficit_C_error_same_graph (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ σ : Fin 3 → AbsoluteDensity 1,
        (∀ j θ, (σ j).density (DGPS.Circle.AngularNormalization.angEquiv.symm θ) =
          rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h))
            (DGPS.Circle.AngularNormalization.angSec θ)) ∧
        ∃ c : ℝ, 0 < c ∧ ∀ a : ℝ, ∃ K : ℝ, 0 < K ∧ ∀ F : SpeciesFamily 1,
          ∃ label : Fin F.count → Fin 4,
            let R := Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ
            let D0 := ∑ s, F.weight s * ((ordinaryFisher h (F.density s)).toReal -
              2 * (ordinaryLSRate (ordinaryReference h)).toReal *
                (ordinaryEntropy h (F.density s)).toReal)
            rootDistanceBudget F R label ≤ D0 / c ∧
            |elementaryC h a (barycenter F) -
              elementaryC h a (barycenter (assignedRootFamily F R label))| ≤
                K * (nonreferenceRootWeight F label * Real.sqrt D0 + D0) := by
  obtain ⟨δ, hδ, hδr, hroots⟩ := ordinaryDeficit_global_same_graph D
  refine ⟨δ, hδ, hδr, fun h hh hhd => ?_⟩
  obtain ⟨σ, hσ, c, hc, hglobal⟩ := hroots h hh hhd
  refine ⟨σ, hσ, c, hc, fun a => ?_⟩
  obtain ⟨K0, hK0, herr⟩ := elementaryC_nearest_root_error hh a
  refine ⟨K0 * (1 + Real.sqrt (1 / c) + 1 / c), by positivity, fun F => ?_⟩
  obtain ⟨label, hlabel, hbudget⟩ := ordinaryFamily_nearest_root_budget h σ hc hglobal F
  refine ⟨label, hbudget, ?_⟩
  let R : Fin 4 → AbsoluteDensity 1 := Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ
  let D0 := ∑ s, F.weight s * ((ordinaryFisher h (F.density s)).toReal -
    2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h (F.density s)).toReal)
  have hD0 : 0 ≤ D0 := Finset.sum_nonneg fun s _ =>
    mul_nonneg (F.weight_nonneg s) (elementary_ordinary_deficit_nonneg h (F.density s))
  have hR : (densityMeasure (R 0) : Measure (Torus 1)) = threefoldReference h :=
    ordinaryReferenceAbsolute_measure h
  exact (herr F R label hR).trans (budget_substitution
    (rootDistanceBudget_nonneg F R label) hD0 (nonreferenceRootWeight_nonneg F label)
    hc hK0.le hbudget)

end DGPS.Examples.ThreeSpeciesCircle
