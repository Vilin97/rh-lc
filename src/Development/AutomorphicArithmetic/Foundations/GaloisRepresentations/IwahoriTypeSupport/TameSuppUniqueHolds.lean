module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.HasTypeVecIff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockIndexMonotone
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.GrpFacts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJLeviMulJPlus
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.NumberTheory.NumberField.CMField
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.JacProd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.LocHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.SuppOfTypeOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TypeToIw

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.FinTri

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori

theorem UpperTheory.Gal.TypesAndIwahori.finTri :
    UpperTheory.Gal.TypesAndIwahori.FinTri := by
  intro R _ N s d hd h hh
  have hp : h ∈ parab R (stdBlocks d hd) := by
    rw [mem_parab_iff]
    intro a b i j hba
    exact hh _ _ (GlobalTheory.CompanionTheory.BlockIndex.stdBlocks_lt_of_lt d hd hba i j)
  refine ⟨hp, fun a => ?_⟩
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_upperTriangular]
  · apply Finset.prod_congr rfl
    intro j _
    exact leviProj_apply R (stdBlocks d hd) ⟨h, hp⟩ a j j
  · intro i j hij
    rw [leviProj_apply]
    apply hh
    have hij' : (j : ℕ) < (i : ℕ) := hij
    rw [Fin.lt_def, stdBlocks_val, stdBlocks_val]
    omega
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IwahoriNeBotOfSpherical

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong.LimitAtL

theorem mem_fixed {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] {ρ : Representation k G V}
    {H : Subgroup G} {v : V} : v ∈ GlobalTheory.PRep.fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  show (∀ h : H, ρ (h : G) v = ((1 : H →* kˣ) h : k) • v) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.2⟩

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime]
  {a : ℕ}

end GlobalTheory.Cong.LimitAtL

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.JacOfType

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori

theorem UpperTheory.Gal.TypesAndIwahori.jacOfType :
    UpperTheory.Gal.TypesAndIwahori.Loc → UpperTheory.Gal.TypesAndIwahori.JacOfType := by
  intro L k _ _ _ _ N s d e V _ _ π hs hi θ μ hμ ⟨v, hv0, hv⟩
  have hadm : IsAdmissible π := (L.bz k).1 (Fin N) V π hs hi
  have hb := L.mp k N s d e V π hadm
  have hJ : KOne k (Fin N) ⊔ (unipRad k e ⊓ KO k (Fin N)) = proRad k e :=
    (GlobalTheory.LocGL.IwahoriFactor.proRad_eq_sup e).symm
  rw [hJ] at hb
  have key : ∀ g ∈ proRad k e, π g v = v := by
    intro g hg
    have hp : g ∈ parahoric k e := proRad_le_parahoric e hg
    have h1 : parahoricProj k e ⟨g, hp⟩ = 1 := (parahoricProj_eq_one_iff e ⟨g, hp⟩).2 hg
    have h2 : π g v = ((typeChar e θ ⟨g, hp⟩ : ℂˣ) : ℂ) • v := hv ⟨g, hp⟩
    have h3 : typeChar e θ ⟨g, hp⟩ = 1 := by
      show leviChar _ θ (parahoricProj k e ⟨g, hp⟩) = 1
      rw [h1, map_one]
    rw [h2, h3, Units.val_one, one_smul]
  have hfix : v ∈ fixed π (proRad k e) := GlobalTheory.Cong.LimitAtL.mem_fixed.2 key
  have h0 : (0 : V) ∈ fixed π (proRad k e) := zero_mem _
  refine ⟨Submodule.Quotient.mk v, fun hy => hv0 (hb.injOn hfix h0 ?_), fun x hx => ?_⟩
  · simpa using hy
  · have h1 : jacU e π x (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π (leviEmb k e x) v) := rfl
    have h2 := hv ⟨leviEmb k e x, leviEmb_mem_parahoric e ⟨x, hx⟩⟩
    have h3 : π (leviEmb k e x) v = ((typeChar e θ ⟨leviEmb k e x, leviEmb_mem_parahoric e ⟨x, hx⟩⟩ : ℂˣ) : ℂ) • v := h2
    have h4 : ∀ a, ((μ a (GeneralLinearGroup.det (x a)) : ℂˣ) : ℂ) =
        ((θ a (GeneralLinearGroup.det (redLevi k _ ⟨x, hx⟩ a)) : ℂˣ) : ℂ) := by
      intro a
      have h5 := (hμ a).detChar_eq ⟨x a, hx a trivial⟩
      rw [redLevi_apply]
      exact congrArg (fun u : ℂˣ => (u : ℂ)) h5
    have h6 : parahoricProj k e ⟨leviEmb k e x, leviEmb_mem_parahoric e ⟨x, hx⟩⟩ = redLevi k _ ⟨x, hx⟩ :=
      parahoricProj_leviEmb e ⟨x, hx⟩
    rw [h1, h3, typeChar_apply, h6, Units.coe_prod, Submodule.Quotient.mk_smul]
    simp only [h4]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TameSuppUniqueHolds

section

@[expose] public section

namespace UpperTheory.Gal.TypesAndIwahori

theorem suppOfType_holds : SuppOfType := suppOfType_of loc_holds (typeToIw finTri)

theorem topB_holds : TopB := topB_of (jacOfType loc_holds) grpFacts (jacProd loc_holds)

end UpperTheory.Gal.TypesAndIwahori
end
end
