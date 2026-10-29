import SharpSymmetricLSI.Infra.Torus
import SharpSymmetricLSI.Infra.TorusLift
import SharpSymmetricLSI.Infra.WeakGrad
import SharpSymmetricLSI.Infra.SobolevTorus
import SharpSymmetricLSI.Infra.Mollify
import SharpSymmetricLSI.Infra.MollifyL2
import SharpSymmetricLSI.Infra.SmoothWeakGrad
import SharpSymmetricLSI.Infra.Periodic
import SharpSymmetricLSI.Infra.Entropy
import SharpSymmetricLSI.Infra.EntropyTensor
import SharpSymmetricLSI.Infra.Pinsker
import SharpSymmetricLSI.Infra.Heat
import SharpSymmetricLSI.Infra.HeatCircle
import SharpSymmetricLSI.Infra.HeatTorus
import SharpSymmetricLSI.Infra.Calculus
import SharpSymmetricLSI.Infra.ChainRule
import SharpSymmetricLSI.Infra.Centering
import SharpSymmetricLSI.Infra.Topology.NotContractible
import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D09_ParticleRates
import FullLabeledLSI.Defs.F01_Species
import DGPS.Wave0.Namespace

/-!
# Wave 0 bounded cold-build probe

Building this module builds a bounded slice of the legacy development (static import closure:
50 legacy modules, plus the Mathlib modules they import, which must come from the cache) and
co-imports the campaign namespace, as a first compiled isolation check. The module list is the
hypothesis-independent infrastructure most likely to be adopted in Tranche A; R2 may revise it
before launch. It proves nothing about the campaign targets.
-/

namespace DGPS.Wave0

/-- Compiles only if the campaign namespace coexists with the imported legacy declarations. -/
theorem legacyProbe_coimport :
    DGPS.campaignCheckpoint = "d880f61501024eacf8cdb0c6a7de5c821c02d412" := rfl

end DGPS.Wave0
