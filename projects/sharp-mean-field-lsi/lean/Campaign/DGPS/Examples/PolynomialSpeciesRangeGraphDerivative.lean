import DGPS.Examples.PolynomialSpeciesRangeAmplitude

/-! The first-amplitude derivative of the genuine interacting graph vanishes at
the origin, by the actual amplitude kernel and the corrected complement inverse. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem amplitude_path_derivative (a b : ℝ) :
    HasDerivAt (fun z : ℝ => ((z * a, z * b, (0, 0), 0) : PolynomialRangeParameters))
      ((a, b, (0, 0), 0) : PolynomialRangeParameters) 0 := by
  have hd := ((hasDerivAt_id (0 : ℝ)).mul_const a).prodMk
    (((hasDerivAt_id (0 : ℝ)).mul_const b).prodMk
      (hasDerivAt_const (0 : ℝ) (((0, 0), 0) : (ℝ × ℝ) × ℝ)))
  simp only [one_mul, id_eq] at hd
  rw [show (0 : (ℝ × ℝ) × ℝ) = ((0, 0), 0) by ext <;> rfl] at hd
  exact hd

private theorem amplitude_partial_zero (a b : ℝ) :
    fderiv ℝ polynomialRangeMap ((0 : PolynomialRangeParameters), (0 : E_STR02969))
      (((a, b, (0, 0), 0) : PolynomialRangeParameters), (0 : E_STR02969)) = 0 := by
  have hpath := (amplitude_path_derivative a b).prodMk
    (hasDerivAt_const (0 : ℝ) (0 : E_STR02969))
  have hd := ((polynomialRangeMap_smooth.differentiable (by simp)
    ((0 : PolynomialRangeParameters), (0 : E_STR02969))).hasFDerivAt).comp_hasDerivAt_of_eq
      (0 : ℝ) hpath (by
        apply Prod.ext
        · ext <;> simp
        · rfl)
  exact hd.unique (polynomialRangeMap_first_amplitude_line a b)

/-- The graph is produced by the actual interacting IFT and has zero first-amplitude
Fréchet derivative. No estimate on that derivative is a premise. -/
theorem exists_polynomial_range_graph_first_amplitude_zero :
    ∃ (U : Set PolynomialRangeParameters) (N : Set E_STR02969)
      (ψ : PolynomialRangeParameters → E_STR02969),
      IsOpen U ∧ (0 : PolynomialRangeParameters) ∈ U ∧ IsOpen N ∧ (0 : E_STR02969) ∈ N ∧
      ContDiffOn ℝ ∞ ψ U ∧ (∀ p ∈ U, ψ p ∈ N) ∧
      (∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w) ∧
      (∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
        ψ (0, 0, (h, s), γ) = 0) ∧
      fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0 := by
  obtain ⟨U, N, ψ, hU, h0U, hN, h0N, hψ, hψN, hgraph, hzero⟩ := exists_polynomial_range_graph
  have htuple : (0 : PolynomialRangeParameters) = (0, 0, (0, 0), 0) := by ext <;> rfl
  have hψ0 : ψ (0 : PolynomialRangeParameters) = 0 := by
    rw [htuple]
    exact hzero 0 0 0 (by rw [← htuple]; exact h0U)
  have hdir : ∀ a b : ℝ, HasDerivAt
      (fun z : ℝ => ψ (z * a, z * b, (0, 0), 0)) 0 0 := by
    intro a b
    let p := fun z : ℝ => ((z * a, z * b, (0, 0), 0) : PolynomialRangeParameters)
    let w := fun z : ℝ => ψ (p z)
    have hp0 : p 0 = 0 := by
      dsimp only [p]
      simp only [zero_mul]
      exact htuple.symm
    have hψp : DifferentiableAt ℝ ψ (p 0) := by
      rw [hp0]
      exact (hψ.contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)
    have hp : DifferentiableAt ℝ p 0 := (amplitude_path_derivative a b).differentiableAt
    have hw : DifferentiableAt ℝ w 0 := hψp.comp 0 hp
    let v := deriv w 0
    have hpath := (amplitude_path_derivative a b).prodMk hw.hasDerivAt
    have hw0 : w 0 = 0 := by rw [show w 0 = ψ (p 0) from rfl, hp0, hψ0]
    have hd := ((polynomialRangeMap_smooth.differentiable (by simp)
      ((0 : PolynomialRangeParameters), (0 : E_STR02969))).hasFDerivAt).comp_hasDerivAt_of_eq
        (0 : ℝ) hpath (by
          change ((0 : PolynomialRangeParameters), (0 : E_STR02969)) = (p 0, w 0)
          rw [hp0, hw0])
    have hpU : ∀ᶠ z : ℝ in 𝓝 0, p z ∈ U := by
      have hc : Continuous p := by fun_prop
      have h := (hc.tendsto 0).eventually (by rw [hp0]; exact hU.mem_nhds h0U)
      exact h
    have he : (fun z : ℝ => polynomialRangeMap (p z, w z)) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [hpU] with z hz
      exact (hgraph _ hz _ (hψN _ hz)).2 rfl
    have hz := (hasDerivAt_const (0 : ℝ) (0 : Y_STR02969)).congr_of_eventuallyEq he
    have hd0 := hd.unique hz
    have heq : (((a, b, (0, 0), 0) : PolynomialRangeParameters), v) =
        ((((a, b, (0, 0), 0) : PolynomialRangeParameters), (0 : E_STR02969)) +
          ((0 : PolynomialRangeParameters), v)) := by simp
    have hinv : fderiv ℝ polynomialRangeMap ((0 : PolynomialRangeParameters), (0 : E_STR02969))
        ((0 : PolynomialRangeParameters), v) = polynomialOriginRangeEquiv v := by
      have h := congrArg (fun L : E_STR02969 →L[ℝ] Y_STR02969 => L v) polynomialRangeMap_partial_origin
      exact h
    change fderiv ℝ polynomialRangeMap ((0 : PolynomialRangeParameters), (0 : E_STR02969))
      (((a, b, (0, 0), 0) : PolynomialRangeParameters), v) = 0 at hd0
    rw [heq, map_add, amplitude_partial_zero, hinv, zero_add] at hd0
    have hv : v = 0 := polynomialOriginRangeEquiv.injective (by simpa using hd0)
    simpa only [v, hv] using hw.hasDerivAt
  refine ⟨U, N, ψ, hU, h0U, hN, h0N, hψ, hψN, hgraph, hzero, ?_⟩
  let f := fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)
  let q := fun x : ℝ × ℝ => ((x.1, x.2, (0, 0), 0) : PolynomialRangeParameters)
  have hq0 : q 0 = 0 := by ext <;> rfl
  have hq : DifferentiableAt ℝ q 0 := by dsimp only [q]; fun_prop
  have hψq : DifferentiableAt ℝ ψ (q 0) := by
    rw [hq0]
    exact (hψ.contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)
  have hf : DifferentiableAt ℝ f 0 := hψq.comp 0 hq
  apply ContinuousLinearMap.ext
  intro x
  have hl : HasDerivAt (fun z : ℝ => z • x) x 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const x
  have hd := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have hfun : (fun z : ℝ => f (z • x)) = fun z : ℝ => ψ (z * x.1, z * x.2, (0, 0), 0) := rfl
  change HasDerivAt (fun z : ℝ => f (z • x)) _ 0 at hd
  rw [hfun] at hd
  exact hd.unique (hdir x.1 x.2)

end DGPS.Examples.PolynomialSpecies
