import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsFormalGroupLawOfChartOfJetChart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsUniversalChartOfFormalGroupChart

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AddCurve

section Rings
variable (R : Type) [CommRing R] (l : ℕ)

abbrev Tr : Type := AdjoinRoot (Polynomial.X ^ l : Polynomial R)

variable {R l}

def cf (n : ℕ) : Tr R l →ₗ[R] R := (Polynomial.lcoeff R n).comp (AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow l))

variable (R l)

end Rings

section Points
variable {k : Type} [CommRing k]

variable {B : Over (Sp k)}

variable {R : Type} [CommRing R] [Algebra k R]

end Points

end GlobalTheory.AddCurve
