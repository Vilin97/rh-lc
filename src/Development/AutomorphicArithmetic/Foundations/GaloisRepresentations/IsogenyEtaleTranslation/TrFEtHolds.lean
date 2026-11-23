module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PAlFEt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PBridge
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PCxFinOf
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormallyUnramifiedOfCompOfEtaleOfSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PDimUniq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PPowFEt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InvMemLatMonoidOfMemAwaySupp
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PTanIso
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PTrFEt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PTrScal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PWitScal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.TrEqRe
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.FixedPointsIntBaseHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.FibrePowerTowerAdmissibleLevel

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PDescEt

section

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

namespace UpperTheory.Gal.FixZ

theorem descEt_of : DescEt := by
  intro A B C c f hc hs hf hcf
  exact GlobalTheory.etale_of_comp_of_etale_of_surjective c f

end UpperTheory.Gal.FixZ
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PDescFin

section

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

namespace UpperTheory.Gal.FixZ

theorem descFin_of : DescFin := by
  intro A B C c f hc hs he hfin
  have : UniversallyClosed f := UniversallyClosed.of_comp_surjective c f
  have : IsProper f := { }
  have : LocallyQuasiFinite f := GlobalTheory.TangentCrit.locallyQuasiFinite_of_formallyUnramified f
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end UpperTheory.Gal.FixZ
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PEtCancel

section

@[expose] public section

open AlgebraicGeometry in
theorem UpperTheory.Gal.FixZ.etCancel_of :
    UpperTheory.Gal.FixZ.EtCancel := by
  intro A B C E f g f' hg hfin1 het1 hfin2 het2
  have h1 : AlgebraicGeometry.IsSeparated (CategoryTheory.CategoryStruct.comp g f') :=
    inferInstance
  have h2 : AlgebraicGeometry.IsSeparated g := AlgebraicGeometry.IsSeparated.of_comp g f'
  have h3 : AlgebraicGeometry.FormallyUnramified g :=
    AlgebraicGeometry.FormallyUnramified.of_comp g f'
  exact ⟨AlgebraicGeometry.IsFinite.of_comp f g, AlgebraicGeometry.Etale.of_comp f g⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PLegOf

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField

namespace UpperTheory.Gal.FixZ

theorem legOf_of : LegOf := by
  intro p _ D G L gb k T N' N h b
  obtain ⟨π, o, ψ, φ, hw, hs, htr, he⟩ := T.tr_eq N' N h b.1 b.2
  refine ⟨W2.Leg.mk π o ψ φ hs ⟨htr.1, htr.2.1, htr.2.2.1, htr.2.2.2.2⟩, he, fun α => ?_⟩
  simp only [LocalSmoothExtension.leg, LocalSmoothExtension.al, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, he, Category.assoc]
  rfl

end UpperTheory.Gal.FixZ

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PScalEx

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (Integ)
open scoped TensorProduct

theorem UpperTheory.Gal.FixZ.scalEx_of :
    UpperTheory.Gal.G3.SysOf → UpperTheory.Gal.FixZ.ScalEx := by
  intro hS p _ D G L h hI
  obtain ⟨f, u, c, k, hsys, -, hk, -⟩ := hS p D G L h hI
  have hkp : k.Coprime p := hsys.2.1
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h1 : p = 1 := by simpa using hkp
    exact (Fact.out : p.Prime).one_lt.ne' h1
  have hone : IsIntAf (1 : AfP p) := fun v => by rw [map_one]; exact one_mem _
  have hact : ∀ v, L.actG (GlobalTheory.W2.scalarAf G (GlobalTheory.W2.natUnit p k hk0)) v = k • v :=
    GlobalTheory.W2.actG_natScalar L k hk0
  refine ⟨k, GlobalTheory.W2.scalarAf G (GlobalTheory.W2.natUnit p k hk0), Nat.pos_of_ne_zero hk0, hkp,
    ⟨fun g => GlobalTheory.W2.scalarAf_comm _ g, hact, 1, 1, hone, hone, one_mul 1, ?_⟩, ?_, ?_⟩
  · show ((GlobalTheory.W2.natUnit p k hk0 : (AfP p)ˣ) : AfP p) * (GlobalTheory.W2.natUnit p k hk0 : (AfP p)ˣ) = ((k ^ 2 : ℕ) : AfP p) * 1
    have e : ((GlobalTheory.W2.natUnit p k hk0 : (AfP p)ˣ) : AfP p) = (k : AfP p) := by
      show algebraMap ℚ (AfP p) (k : ℚ) = _
      rw [map_natCast]
    rw [e, mul_one]; push_cast; ring
  · intro v hv
    rw [hact]
    exact nsmul_mem hv k
  · intro v hv
    rw [map_mul, Module.End.mul_apply, hact]
    exact hk v hv
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.TranslationFiniteEtaleOfIsogenyData

section

@[expose] public section

namespace UpperTheory.Gal.FixZ

theorem translation_finite_etale_of_isogeny_data (h1 : G3.SysOf) (h2 : G3.RelComp) (h3 : G3.WitUniq) (h4 : G3.IsogFEt) (h5 : G3.PowSm) : TrFEt :=
  trFEt_of h5 (scalEx_of h1) (trScal_of h3 h4 (witScal_of h2) powFEt_of) etCancel_of descEt_of descFin_of

theorem tower_fixed_points_of_isogeny_data (h1 : G3.SysOf) (h2 : G3.RelComp) (h3 : G3.WitUniq) (h4 : G3.IsogFEt) (h5 : G3.PowSm) : LocalSmoothExtension.FixK :=
  bridge_of (translation_finite_etale_of_isogeny_data h1 h2 h3 h4 h5) (alFEt_of h4 powFEt_of) legOf_of wtEq_of tanIso_of dimUniq_of cxFinOf_of
    W2.fixedPoints_int_base_holds W2.FixZ_holds

end UpperTheory.Gal.FixZ
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.TrFEtHolds

section

@[expose] public section

namespace UpperTheory.Gal.FixZ

theorem FixK_holds : LocalSmoothExtension.FixK := tower_fixed_points_of_isogeny_data G3.sysOf_holds G3.relComp_holds G3.witUniq_holds G3.isogFEt_holds G3.powSm_holds

end UpperTheory.Gal.FixZ
end
end
