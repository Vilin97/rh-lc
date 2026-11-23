module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.MapInvMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PlaceData
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.EsGenAll
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.EtOfRestrict
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCorrOpEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PEsStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PFixDesc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClosD
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PGrPass
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PHopOp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PLiesOp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.POpCover
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PPlaceData
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PTowES
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.AevalSmulProd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.CharPolEqRootPol
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlowUpFibreSemilocal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PCutStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RepMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RichOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.SatCard
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PTwLoc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PTwJumps
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.UnrPolNegOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PContLeft
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSSLeft
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractHolds

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PGalEx

section

@[expose] public section

theorem UpperTheory.Gal.Mod.galEx : UpperTheory.Gal.Mod.GalEx := UpperTheory.Gal.G3.pGalClosD (UpperTheory.Gal.G3.pSplitsPts UpperTheory.Gal.G3.pIsoPts)
  (UpperTheory.Gal.G3.pOrdEx UpperTheory.Gal.G3.pOrdStep)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.EsStepHolds

section

@[expose] public section

namespace UpperTheory.Gal.Mod

theorem hopOp_holds : HopOp := hopOp @galEx @corrOpEq

theorem towES_holds : TowES := towES esGen_all bcEx (liesOp hopOp_holds @opCover) (fixDesc hopOp_holds)

theorem esStep_holds : UpperTheory.Gal.Int.Geo.ESStep := esStep towES_holds placeData grPass

end UpperTheory.Gal.Mod
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.JumpsOf

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.Int.Geo.jumpsOf :
    UpperTheory.Gal.Int.Geo.JumpsOf := by
  intro E Ω _ _ _ _ _ _ l _ ι a dd U ρ w Q hQ hJ P AI hT A hA O _ _ _ Bw hBw τ LL' τ' hi lam J hl hJm
  obtain ⟨J', h1, h2⟩ := hJ P AI hT A hA O Bw hBw τ LL' τ' hi
  have e : J = (GlobalTheory.RoadWGeo.wtJumps lam).val :=
    Multiset.map_injective Int.cast_injective (hJm.trans (GlobalTheory.RoadWGeo.wtJumps_val lam).symm)
  refine ⟨J', h1, fun j hj => h2 j (hQ _ (GlobalTheory.CongL.LimAtLU.overPl_of_induced ι hA hBw hi) lam hl j ?_)⟩
  rw [e] at hj
  exact hj
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.TwCrys

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.Int.Geo.twCrys :
    UpperTheory.Gal.Int.Geo.TwCrys := by
  intro E Ω _ _ _ _ _ l _ ι dd ρ χ _ _ w c m hχ hρ P AI hT A h O _ _ _ Bw hj
  obtain ⟨c1, -, -, -⟩ := hχ.2 P AI hT A h O Bw hj
  have c2 := hρ P AI hT A h O Bw hj
  have e1 : (rk1 χ).comp (Dec (F := E) A).subtype = rk1 (χ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  have e2 : (tw ρ χ).comp (Dec (F := E) A).subtype =
      tw (ρ.comp (Dec (F := E) A).subtype) (χ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    simp [UpperTheory.V.Af.tw_val]
  rw [e1] at c1
  rw [e2]
  exact (UpperTheory.Gal.TP.Sub.twLoc_holds l P AI hT E Ω A O Bw dd (ρ.comp (Dec (F := E) A).subtype)
    (χ.comp (Dec (F := E) A).subtype)).2 c2 c1
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.TwJ

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.Int.Geo.twJ :
    UpperTheory.Gal.Int.Geo.TwJ := by
  intro E Ω _ _ _ _ _ l _ ι dd ρ χ hρ hχ w c m h1 Q hQ P AI hT A hA O _ _ _ Bw hj τ LL' τ' hi
  obtain ⟨J, hJ, hJQ⟩ := hQ P AI hT A hA O Bw hj τ LL' τ' hi
  obtain ⟨-, -, j1, -⟩ := h1.2 P AI hT A hA O Bw hj
  have e1 : (rk1 χ).comp (Dec (F := E) A).subtype = rk1 (χ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  have e2 : (tw ρ χ).comp (Dec (F := E) A).subtype =
      tw (ρ.comp (Dec (F := E) A).subtype) (χ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    simp [UpperTheory.V.Af.tw_val]
  have j2 := j1 τ LL' τ' hi
  rw [e1] at j2
  have cs : Continuous (ρ.comp (Dec (F := E) A).subtype) := hρ.comp continuous_subtype_val
  have cμ : Continuous (χ.comp (Dec (F := E) A).subtype) := hχ.comp continuous_subtype_val
  refine ⟨J.map (· + m (ι.toRingHom.comp τ)), ?_, fun j hj' => ?_⟩
  · rw [e2]
    exact UpperTheory.Gal.TP.Sub.twJumps_holds l P AI hT E Ω A O Bw dd _ _ cs cμ τ J _ hJ j2
  · exact Multiset.mem_map.2 ⟨_, hJQ _ hj', by simp⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.StepsMain

section

@[expose] public section

namespace UpperTheory.Gal.Int.Geo

theorem steps_of (hC : CrysStep) (hJ : JumpStep) (hP : PhiStep) : Steps :=
  ⟨repEx_holds, Mod.esStep_holds, hC, hJ, hP, cutStep_holds, twES, twCrys, twJ, twPhi, phiOf, satCard, jumpsOf, richOf,
    TP.Sub.charEx, TP.Sub.sSLeft_holds, TP.Sub.contLeft_holds⟩

end UpperTheory.Gal.Int.Geo
end
end
