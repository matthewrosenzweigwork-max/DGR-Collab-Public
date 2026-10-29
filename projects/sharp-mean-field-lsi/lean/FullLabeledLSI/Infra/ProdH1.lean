import SharpSymmetricLSI.Paper.CosineDissipation
import SharpSymmetricLSI.Infra.ChainRule

/-!
# Product rule for `H¹`-type functions (polarization)

If `u, w ∈ L²` have weak gradients with `L²` components, then `u w` has weak gradient
`w ∇u + u ∇w` (from `isWeakGrad_sq` applied to `u + w`, `u`, `w`).
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

theorem isWeakGrad_mul_L2 {ι : Type*} [Fintype ι] [DecidableEq ι] {u w : UnitAddTorus ι → ℝ}
    {gu gw : UnitAddTorus ι → ι → ℝ} (hu : IsWeakGrad u gu) (hw : IsWeakGrad w gw)
    (hu2 : MemLp u 2 volume) (hw2 : MemLp w 2 volume)
    (hgu : ∀ k, MemLp (fun y => gu y k) 2 volume) (hgw : ∀ k, MemLp (fun y => gw y k) 2 volume) :
    IsWeakGrad (fun y => u y * w y) (fun y k => w y * gu y k + u y * gw y k) := by
  have hs := hu.add hw
  have h1 := isWeakGrad_sq hs (hu2.add hw2) (fun k => (hgu k).add (hgw k))
  have h2 := isWeakGrad_sq hu hu2 hgu
  have h3 := isWeakGrad_sq hw hw2 hgw
  have h := ((h1.add (h2.cmul (-1))).add (h3.cmul (-1))).cmul (1 / 2)
  convert h using 1
  · funext y; ring
  · funext y k; ring

end SharpLSI.FL
