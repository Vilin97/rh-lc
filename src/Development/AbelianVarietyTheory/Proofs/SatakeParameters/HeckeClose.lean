module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypesSeparatedByInertPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHeckeOperatorsRowsIntertwineThetaLiftsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSeparatingInertEigenvaluePassageStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodGenericCharacterOfSeriesTypes
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorsRowsLiftsRationalAdjointClosed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeThetaLevel3Exists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypesSeparatedByInertPlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

theorem _root_.GlobalTheory.T.finite_types_separated_by_inert_places : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ((∃ tr, R.TrISem F tr ∧ ∀ (j : Fin D.R.m), ∀ p ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, ∀ p' ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, (∃ k : A3.okI A3.A.μ0 × List ℕ, p.2 (k.1.1, k.2) ≠ p'.2 (k.1.1, k.2)) → ∃ k : A3.okI A3.A.μ0 × List ℕ, tr j p.2 (k.1.1, k.2) ≠ tr j p'.2 (k.1.1, k.2)) → R.TrISem F A3.trI ∧ A3.fam3.TrISep) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → A3.fam3.TypesSep3 := by
  first | exact @GlobalTheory.Hk3.typesSep3_of_pin | exact GlobalTheory.Hk3.typesSep3_of_pin | (intros; apply GlobalTheory.Hk3.typesSep3_of_pin <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorsRowsLiftsRationalAdjointClosedStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.okH_inertRationalAdjoint_of_weakCharacterisation_inertJunk : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → InertJunk A3 → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) ∧ (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) := by
  first | exact @GlobalTheory.InertOkH.heckeOperators_rows_lifts_rational_adjointClosed | exact GlobalTheory.InertOkH.heckeOperators_rows_lifts_rational_adjointClosed | (intros; apply GlobalTheory.InertOkH.heckeOperators_rows_lifts_rational_adjointClosed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeThetaLevel3ExistsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heckeTheta_level3_exists : HoweUnram → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → (R.toCx3 F).PartsW false → A3.fam3.TypesSep3 → ((∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr) → R.TrISem F A3.trI ∧ A3.fam3.TrISep) → ∃ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW := by
  first | exact @GlobalTheory.Hk3.heckeTheta_level3_exists_alt | exact GlobalTheory.Hk3.heckeTheta_level3_exists_alt | (intros; apply GlobalTheory.Hk3.heckeTheta_level3_exists_alt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeClose

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.HeckeClose

theorem heckeClose : HoweUnram → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ s, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → InertJunk A3 → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → ((∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr) → R.TrISem F A3.trI ∧ A3.fam3.TrISep) → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → (R.toCx3 F).PartsW false → ((∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) ∧ (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint)) ∧ R.PHecke F ∧ A3.fam3.TypesSep3 ∧ ∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr := by
  intro hH hHC hCD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hJ hSer hPass hU hGU hGE hLW hA hB hPos hParts
  have hLI : GlobalTheory.Chain.LiftInteg D := GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hCD D
  have hS : SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCD R.toRealDat
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨tr, htr⟩ := GlobalTheory.T.exists_separating_inert_eigenvalue_passage hH R F hLI hC hEx hS hJ hX hB hPos
  have hTS : A3.fam3.TypesSep3 :=
    GlobalTheory.T.finite_types_separated_by_inert_places hCD hH R F hLI hOk hC hEx ⟨fun t k => hJ.R t k.1 k.2, fun j t k => hJ.L j t k.1 k.2⟩ hPass hPos hB
  have hG : GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ := (GlobalTheory.GoodGenericSer.goodGenericCharacter_of_seriesTypes R F hC s hOk hSer).2
  have hR := GlobalTheory.T.exists_hecke_operators_rows_intertwine_theta_lifts hH hHC hCD R F hLI hC hEx hJ hB hPos
  have hL := GlobalTheory.T.heckeTheta_level3_exists hH hHC hCD R F hLI hC hEx hJ s hOk hG hU hGU hGE hLW hA hPos hB hParts hTS hPass
  exact ⟨GlobalTheory.T.okH_inertRationalAdjoint_of_weakCharacterisation_inertJunk R F hC hJ, ⟨hR, hL⟩, hTS, tr, htr⟩

end GlobalTheory.Hk3.HeckeClose

end
end
end
