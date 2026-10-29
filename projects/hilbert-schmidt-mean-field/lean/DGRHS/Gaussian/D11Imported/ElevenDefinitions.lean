/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.Definitions

/-! Definitions for the literal dimension-eleven statements in the September
21 manuscript. No regularity, normalization, certificate, or transition
conclusion is assumed by these definitions. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

/-- Representative in the same half-open cube as Section 4. -/
def representative (x : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco (p := (1 : ℝ)) (-(1 / 2 : ℝ)) x).val

def euclideanProfile (x : Fin 11 → ℝ) : ℝ :=
  (5 : ℝ)^11 * (122880 / Real.pi^6) *
    (1 + 25 * ∑ i : Fin 11, (x i)^2)^(-11 : ℤ)

/-- Exactly the periodized profile in (1.20)/(Section 4), not an arbitrary witness. -/
def periodizedProfile (x : Torus 11) : ℝ :=
  ∑' n : Frequency 11, euclideanProfile (fun i => representative (x i) + (n i : ℝ))

def fourierPolynomial (z : ℝ) : ℝ :=
  z^5 + 15*z^4 + 105*z^3 + 420*z^2 + 945*z + 945

def fourierProfile (z : ℝ) : ℝ := Real.exp (-z) * fourierPolynomial z / 945

end DGRHS.Gaussian.D11Imported.HighDim.Eleven
