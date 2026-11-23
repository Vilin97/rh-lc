module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HSepOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PAdExists
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PBallChar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PBaseImm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PConjCharpoly
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PCorrChart
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PCspDim
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PDetOfCharpoly
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.Complex
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PDiagExists
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PEigTop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PEvIntegral
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PExpImm
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFibDet
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFlatAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValSpMapComp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFlatPre
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PHolPi
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PKillsMat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLocSum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLocTan
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PMarkDiag
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PNewtonPoly
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPbFlat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPerCoordLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompLinearEquivIntertwining
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPerNear
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPiLattice
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPowSumRat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPtFibre
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPtHol
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPtImm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRootSumW
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRootSumWOff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRootsFull
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PSimDiag
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTanChart
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTanDeriv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTanExists
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTorusCount
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTraceDual
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTraceLat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTspDiag
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTypeCount
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.ProdTy

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.ExpImm0Of

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR

namespace UpperTheory.Gal.W2

theorem expImm0_of : ExpImm0 := by
  intro X A _ g y e he w hw
  obtain ⟨v, hv, -⟩ := he.2.2.2.1 w
  have hv0 : IsDerivAt0 (fun z => Over.Hom.left (e z)) 0 (Over.Hom.left v) := by
    refine ⟨hv.1, fun U h f => (hv.2 U h f).trans ?_⟩
    have hb : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ Over.Hom.left v = Over.Hom.left (e 0) := hv.1
    have h' : ⊤ ≤ (Over.Hom.left (e 0)) ⁻¹ᵁ U := by
      rw [← hb]
      exact fun x _ => h trivial
    rw [hw U f h', map_zero]
  exact (he.2.2.2.2 v hv.1).unique hv hv0

end UpperTheory.Gal.W2
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PDetReal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.detReal_of :
    UpperTheory.Gal.W2.DetReal := by
  intro W _ _ _ f
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_eq, Complex.mul_conj]
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PExtendEmb

section

@[expose] public section

open NumberField

namespace UpperTheory.Gal.W2

theorem extendEmb_of : ExtendEmb := by
  intro F _ _ φ
  have hker : RingHom.ker φ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast] at hn
    rw [Ideal.mem_bot]
    exact_mod_cast hn
  have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hker
  refine ⟨IsFractionRing.lift (K := F) hinj, fun c => ?_⟩
  exact (IsFractionRing.lift_algebraMap (K := F) hinj c).symm

end UpperTheory.Gal.W2
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFlatComp

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.flatComp_of :
    UpperTheory.Gal.W2.FlatComp := by
  intro V _ _ Y Y' f s v₀ w h U a hU
  have hU' : ⊤ ≤ s v₀ ⁻¹ᵁ (f ⁻¹ᵁ U) := hU
  have e : (fun v => valAt' (s v ≫ f) U a) =
      fun v => valAt' (s v) (f ⁻¹ᵁ U) ((f.appLE U (f ⁻¹ᵁ U) le_rfl).hom a) :=
    funext fun v => GlobalTheory.ExpCoord.valAt'_comp (s v) f U a
  rw [e]
  exact h _ _ hU'
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPerLin

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.perLin_of :
    UpperTheory.Gal.W2.PerLin := by
  intro O _ bar g ρ D P P' H hP hH hc hP'
  have hdet : LinearMap.det (Matrix.toLin' H) ≠ 0 := by rwa [LinearMap.det_toLin']
  let h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearMap.equivOfDetNeZero _ hdet
  have happ : ∀ z, h z = H *ᵥ z := fun z => rfl
  have key := IsPeriod.comp_linearEquiv O bar D g ρ ρ P h hP (fun a z => by
    rw [happ, happ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc])
  have hEq : P' = (↑h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).toAddMonoidHom.comp P := by
    ext x
    simp [hP', happ]
  rw [hEq]
  exact key
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTriCharpoly

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.triCharpoly_of :
    UpperTheory.Gal.W2.TriCharpoly := by
  intro V W _ _ _ _ _ _ T Θ R G hG
  let bV := Module.finBasis ℂ V
  let bW := Module.finBasis ℂ W
  have hM : LinearMap.toMatrix (bV.prod bW) (bV.prod bW) G =
      Matrix.fromBlocks (LinearMap.toMatrix bV bV T) 0 (LinearMap.toMatrix bV bW R)
        (LinearMap.toMatrix bW bW Θ) := by
    ext (i | i) (j | j) <;>
      simp [LinearMap.toMatrix_apply, Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
        Module.Basis.prod_apply, hG]
  rw [← LinearMap.charpoly_toMatrix G (bV.prod bW), ← LinearMap.charpoly_toMatrix T bV,
    ← LinearMap.charpoly_toMatrix Θ bW, hM, Matrix.charpoly_fromBlocks_zero₁₂]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpolyHolds

section

@[expose] public section

namespace UpperTheory.Gal.W2

theorem TanDeriv_holds : TanDeriv := tanDeriv_of

theorem FlatAffine_holds : FlatAffine := flatAffine_of

theorem ConjCharpoly_holds : ConjCharpoly := conjCharpoly_of

theorem TanChart_holds : TanChart := tanChart_of TanDeriv_holds FlatAffine_holds ConjCharpoly_holds

theorem TanExists_holds : TanExists := tanExists_of

theorem FlatComp_holds : FlatComp := flatComp_of

theorem FlatPre_holds : FlatPre := flatPre_of

theorem PbFlat_holds : PbFlat := pbFlat_of FlatAffine_holds

theorem ExpImm0_holds : ExpImm0 := expImm0_of

theorem ExpImm_holds : ExpImm := expImm_of FlatComp_holds FlatPre_holds PbFlat_holds ExpImm0_holds

theorem HolPi_holds : HolPi := holPi_of

theorem PerNear_holds : PerNear := perNear_of

theorem PerCoordLoc_holds : PerCoordLoc := perCoordLoc_of

theorem PerLin_holds : PerLin := perLin_of

theorem AdExists_holds : AdExists := adExists_of

theorem BaseImm_holds : BaseImm := baseImm_of PerNear_holds PerCoordLoc_holds

theorem PtFibre_holds : PtFibre := ptFibre_of

theorem PtHol_holds : PtHol := ptHol_of HolPi_holds PtFibre_holds

theorem PtImm_holds : PtImm := ptImm_of FlatComp_holds FlatPre_holds PtFibre_holds ExpImm_holds

theorem TriCharpoly_holds : TriCharpoly := triCharpoly_of

theorem DetOfCharpoly_holds : DetOfCharpoly := detOfCharpoly_of

theorem CorrChart_holds : CorrChart := corrChart_of AdExists_holds PerLin_holds PtFibre_holds

theorem LocTan_holds : LocTan := locTan_of TanChart_holds PerNear_holds BaseImm_holds PtHol_holds PtImm_holds PtFibre_holds CorrChart_holds TriCharpoly_holds

theorem DetReal_holds : DetReal := detReal_of

theorem TorusCount_holds : TorusCount := torusCount_of DetReal_holds

theorem PiLattice_holds : PiLattice := piLattice_of

theorem LocSum_holds : LocSum := locSum_of LocTan_holds TorusCount_holds PiLattice_holds PtFibre_holds CorrChart_holds DetOfCharpoly_holds

theorem SimDiag_holds : SimDiag := simDiag_of

theorem ExtendEmb_holds : ExtendEmb := extendEmb_of

theorem KillsMat_holds : KillsMat := killsMat_of

theorem HSep_holds : HSep := hSep_of

theorem DiagExists_holds : DiagExists := diagExists_of SimDiag_holds ExtendEmb_holds KillsMat_holds HSep_holds

theorem TypeCount_holds : TypeCount := typeCount_of

theorem TraceLat_holds : TraceLat := traceLat_of

theorem TraceDual_holds : TraceDual := traceDual_of

theorem NewtonPoly_holds : NewtonPoly := newtonPoly_of

theorem PowSumRat_holds : PowSumRat := powSumRat_of TraceLat_holds TraceDual_holds

theorem RootsFull_holds : RootsFull := rootsFull_of TypeCount_holds PowSumRat_holds NewtonPoly_holds KillsMat_holds

theorem MarkDiag_holds : MarkDiag := markDiag_of TypeCount_holds

theorem TspDiag_holds : TspDiag := tspDiag_of

theorem BallChar_holds : BallChar := ballChar_of TypeCount_holds TspDiag_holds

theorem CspDim_holds : CspDim := cspDim_of SimDiag_holds ExtendEmb_holds TypeCount_holds MarkDiag_holds BallChar_holds

theorem FibDet_holds : FibDet := fibDet_of

theorem FibW_holds : FibW := fibW_of

theorem EvIntegral_holds : EvIntegral := evIntegral_of

theorem EigTop_holds : EigTop := eigTop_of AdExists_holds DiagExists_holds TypeCount_holds RootsFull_holds MarkDiag_holds BallChar_holds FibDet_holds FibW_holds EvIntegral_holds

theorem RootSumW_holds : RootSumW := rootSumW_of

theorem RootSumWOff_holds : RootSumWOff := rootSumWOff_of

end UpperTheory.Gal.W2
end
end
