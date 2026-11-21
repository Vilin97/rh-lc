import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterOfLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SecondTwistSmallIffExactlyAtAndFinClause
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField

noncomputable section

namespace GlobalTheory.SmallJumpExample

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits GlobalTheory.HTW GlobalTheory.IndefiniteRowSideFullHecke
open scoped Formalism.Per

theorem isField_bdR (D : D7) (l : ℕ) [Fact l.Prime] : IsField (D.loc l).R.BdR :=
  MulEquiv.isField (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1 (D.locT l).eD.toMulEquiv

section Count

variable {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (n : ℕ)

end Count

variable {D : D7} (L : SizeData₂ D)

end GlobalTheory.SmallJumpExample
