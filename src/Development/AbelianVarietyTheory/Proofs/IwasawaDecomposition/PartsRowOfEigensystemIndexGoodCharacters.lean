module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfMemISup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasEigEigOfType
public import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypeHasSphericalHeckeEigensystem
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointInjectiveOnPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullAlgebraPartLeSplitHeckePartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePolynomialsOfCarriedEigensystemStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypePartLeEigensystemPartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartLeEigensystemPartPrincipalLevelStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypeHasSphericalHeckeEigensystemStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

theorem _root_.GlobalTheory.T.row_type_has_spherical_hecke_eigensystem : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ SF, IsSF R SF → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π, π ∈ principalLevelFrame.OccRows R.θ PY (R.MY 0) (fun b => (levS _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun b => (levChi _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun _ => R.e0) → ∀ i0, ∃ c, principalLevelFrame.IsEigOf (PW i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF π c := by
  first | exact @GlobalTheory.RowEig.row_type_eig | exact GlobalTheory.RowEig.row_type_eig | (intros; apply GlobalTheory.RowEig.row_type_eig <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSphericalEigensystemFirstLiftBaseLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.EigEx

theorem stdPsi_of_stdFrame {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n}
    (h : StdFrame hF P) : GlobalTheory.StdFrame.StdPsi hF P := h

theorem isSF_ssetF {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {R : RealDat3 D A3 Ks} {F : Face3 D A3} (h : R.WeakCharacterisation F) :
    GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat A3.A.μ0) := by
  classical
  have hQ : R.Q A3.A.μ0 = ∅ := (GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 h.base.lev).1
  have hS : R.Sb = R.Pg := h.allPl
  intro v
  unfold SsetF
  rw [hQ, hS, Finset.union_empty, Finset.mem_image]
  refine exists_congr fun PP => and_congr_right fun _ => ?_
  rw [HeightOneSpectrum.ext_iff]
  rfl

theorem exists_hasEig : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ π : D.what₂.FT, ∃ c, HasEig R F Y π c := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH _ hgen π
  have hμ : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  unfold HasEig
  rw [hμ]
  exact GlobalTheory.T.row_type_has_spherical_hecke_eigensystem R.toRealDat F.lv2 hH.ok.ok2 (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex).1 hgen _
    (isSF_ssetF hP.char) Y.hF Y.PY Y.PW (stdPsi_of_stdFrame Y.stdPsi.1) (fun i => stdPsi_of_stdFrame (Y.stdPsi.2 i)) _
    (principalLevelFrame.rowRepR_occ R.θ (Y.eFT π)) ⟨0, Y.hm⟩

end GlobalTheory.Mem.R3.EigEx

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSphericalEigensystemFirstLiftBaseLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.exists_sphericalEigensystem_firstLift_baseLevel : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ π : D.what₂.FT, ∃ c, HasEig R F Y π c := by
  first | exact @GlobalTheory.Mem.R3.EigEx.exists_hasEig | exact GlobalTheory.Mem.R3.EigEx.exists_hasEig | (intros; apply GlobalTheory.Mem.R3.EigEx.exists_hasEig <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrtLeHPartOfCarries

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

theorem isSF_ssetF_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hW : R.WeakCharacterisation F) (hC : GlobalTheory.Hk3.Core R.toRealDat F.lv2) :
    GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat A3.A.μ0) := by
  intro v
  have hQ := (GlobalTheory.T.theta_lift_levels_good_primes_properties R.toRealDat F.lv2 hC.lev).1
  have hS : R.Sb = R.Pg := hW.allPl
  unfold SsetF
  rw [hQ, hS]
  simp only [Finset.union_empty, Finset.mem_image]
  refine exists_congr fun PP => and_congr_right fun _ => ?_
  exact ⟨fun h => by rw [← h]; rfl, fun h => HeightOneSpectrum.ext h⟩



theorem prt_le_hPart_of_carries : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ (π : D.what₂.FT) c p, HasEig R F Y π c → R.Carries p c → (Y.Ish.prt : D.what₂.FT → Submodule ℂ (AmbT (R.MY 0))) π ≤ (hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A3.A.ok A3.A.μ0) R.pl A3.A.q (RealDat.polE (A := A3.A) p.1.1)).map (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap := by
  intro _ _ _ hR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH _ π c p hE hc
  obtain ⟨hC, hSF, -, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex
  have hS := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hR R.toRealDat
  have hμ : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  have hSF' : GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) := by
    rw [hμ]; exact isSF_ssetF_base R F hP.char hC
  have hinj := GlobalTheory.AdjPart.adjoint_injective_on_part R
    ⟨hH.prim.posScal.1, fun i t p => hH.prim.posScal.2 i t p _⟩ hH.prim.thmB
  have hlab := GlobalTheory.T.heckePolynomials_of_carried_eigensystem R F (GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hR D) hH.ok hP.char hH.aux.ex hS hinj p c hc
  have hpart := (GlobalTheory.T.full_algebra_part_le_split_hecke_part R.toRealDat F.lv2 (s := 1) hH.ok.ok2 hC _ hSF' c (RealDat.polE (A := A3.A) p.1.1)).1
    fun P hP => (hlab P hP).1
  rw [Y.prtE π]
  refine Submodule.map_mono fun U hU => ?_
  obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.rowTypePart_le_eigensystemPart R.toRealDat F.lv2 (s := 1) hC hS _ hSF' Y.hF Y.PY Y.PW Y.stdPsi.1 Y.stdPsi.2
    _ _ c hE true U hU
  exact hpart x hx

end GlobalTheory.Mem.R3
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrtWLeHPart

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3



theorem prtW_le_hPart : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ (π : D.what₂.FT) c p, HasEig R F Y π c → R.Carries p c → ∀ i : Fin D.R.m, (Y.IL.prtW : ∀ i : Fin D.R.m, D.what₂.FT → Submodule ℂ (AmbT (R.MW i (sg0 D A3.A)))) i π ≤ (hPart (R.MW i (sg0 D A3.A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A3.A.ok A3.A.μ0) R.pl A3.A.q (RealDat.polW (A := A3.A) p.1.1)).map (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).toLinearMap := by
  intro _ _ _ hcusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH _ π c p hc hcar i
  obtain ⟨hC, -, -, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex
  have ht : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  have hQ : R.Q A3.A.μ0 = ∅ := (GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hC.lev).1
  have hSb : R.Sb = R.Pg := hP.char.allPl
  have hSF : GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) := by
    classical
    intro v
    unfold SsetF
    rw [ht, hQ, hSb, Finset.union_empty, Finset.mem_image]
    refine exists_congr fun PP => and_congr_right fun _ => ?_
    rw [← underPl_asIdeal]
    exact ⟨fun h => by rw [h], fun h => HeightOneSpectrum.ext h⟩
  have hlab := GlobalTheory.T.heckePolynomials_of_carried_eigensystem R F (GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hcusp D) hH.ok hP.char hH.aux.ex
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hcusp R.toRealDat)
    (GlobalTheory.AdjPart.adjoint_injective_on_part R ⟨hH.prim.posScal.1, fun i t p => hH.prim.posScal.2 i t p _⟩ hH.prim.thmB)
    p c hcar
  rw [Y.prtWE i π]
  refine Submodule.map_mono fun U hU => ?_
  obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.typePart_le_eigensystemPart_principalLevel R.toRealDat F.lv2 hH.ok.ok2 hC _ hSF Y.hF Y.PY Y.PW Y.stdPsi.1 Y.stdPsi.2
    _ ⟨0, Y.hm⟩ c hc i U hU
  exact (GlobalTheory.T.full_algebra_part_le_split_hecke_part R.toRealDat F.lv2 hH.ok.ok2 hC _ hSF c _).2 i (fun P hP => (hlab P hP).2) x hx

end GlobalTheory.Mem.R3
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdPsiOfStdFrame

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.IsotPart

theorem stdPsi_of_stdFrame {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E}
    {P : principalLevelFrame.RowPsi V n} (h : GlobalTheory.Mem.R3.StdFrame hF P) : GlobalTheory.StdFrame.StdPsi hF P := h



theorem isot_le_part : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ (π : D.what₂.FT) c p, HasEig R F Y π c → R.Carries p c → ∀ i : Fin D.R.m, D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i p).comap (Y.mj.eW i) := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH _ π c p hE hC i
  obtain ⟨hcore, hSF, -, hW⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex
  have hQ : R.Q A3.A.μ0 = ∅ := (GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hcore.lev).1
  have ht : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  have hSF' : GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) := by
    intro v
    have hS : R.Sb = R.Pg := hP.char.allPl
    rw [ht]
    unfold SsetF
    rw [hQ, hS]
    simp only [Finset.union_empty, Finset.mem_image]
    constructor
    · rintro ⟨PP, h1, rfl⟩
      exact ⟨PP, h1, rfl⟩
    · rintro ⟨PP, h1, h2⟩
      exact ⟨PP, h1, HeightOneSpectrum.ext h2⟩
  have hEq : SsetF R.toRealDat (Y.tupT D.what₂.mu0) = R.SF := by
    ext v
    rw [hSF v, hSF' v]
  unfold HasEig at hE
  rw [hEq] at hE
  intro y hy
  have hy' := (Y.tied.lift.isot i π y).1 hy
  rw [Y.prtWE, Y.mjRead] at hy'
  obtain ⟨U, hU, hUy⟩ := hy'
  obtain ⟨x, hx, hxU⟩ := GlobalTheory.T.typePart_le_eigensystemPart_principalLevel R.toRealDat F.lv2 hH.ok.ok2 hcore R.SF hSF Y.hF Y.PY Y.PW
    (stdPsi_of_stdFrame Y.stdPsi.1) (fun j => stdPsi_of_stdFrame (Y.stdPsi.2 j)) _ _ c hE i U hU
  have h1 : U = (R.HW i (sg0 D A3.A)).e (Y.mj.eW i y) :=
    (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).injective hUy
  have h2 : x = Y.mj.eW i y := (hcore.models.HW i (sg0 D A3.A)).1 (hxU.trans h1)
  rw [Submodule.mem_comap, ← h2]
  rw [← hW] at hx
  exact (le_iSup₂ (f := fun (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c) => R.Wc' i c) c hC) hx

end GlobalTheory.Mem.R3.IsotPart
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartsRowOfEigensystemIndexGoodCharacters

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3

theorem partsRec_of_eig : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D), Pins R F cG → Holds R F → HostHyp D → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → (∀ (i : Fin D.R.m) π (c : A3.fam3.base3.Ix) (e : D.what₂.LL →+* ℂ), D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) → Xd.logLam ((i : ℕ) + 1) π e = Real.log (R.lam3 i A3.A.μ0 c (InfinitePlace.mk e))) → ∃ (E : EigIdx D Xd) (labPi : E.Pi → A3.A.fam.base.Ix) (piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ), PartsRec R.toRealDat F.lv2 Y.tupT Y.hm Y.PY Y.PW Y.eFT E labPi piOf Y.Ish.prt Y.IL.prtW := by
  intro hW hDS hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Xd hP hH hHost hgen hLam
  have e1 := GlobalTheory.T.exists_sphericalEigensystem_firstLift_baseLevel hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost hgen
  have e2 := GlobalTheory.Mem.EigCarry.carries_of_hasEig hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have e3 := GlobalTheory.Mem.R3.IsotPart.isot_le_part hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have e4 := GlobalTheory.Mem.R3.prt_le_hPart_of_carries hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have e5 := GlobalTheory.Mem.R3.prtW_le_hPart hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have hc : Formalism.L2.Col.PairComm (A3.fam3.F.R A3.fam3.F.μ0).op := (hH.ok.ok2.what₂ A3.fam3.F.μ0).comm
  classical

  have hE : ∀ π, HasEig R F Y π (eigOfType R F Y π) := fun π => hasEig_eigOfType (e1 π)
  have hK : ∀ π, ∃ p, R.Carries p (eigOfType R F Y π) := fun π => e2 π _ (hE π)
  let Pi : Type := Set.range (eigOfType R F Y)
  have hPi : ∀ c : Pi, ∃ p, R.Carries p c.1 := by
    rintro ⟨c, π, rfl⟩
    exact hK π
  let labP : Pi → A3.fam3.base3.Ix := fun c => (hPi c).choose
  let E : EigIdx D Xd :=
    { Pi := Pi
      fin := Set.fintypeRange _
      dec := Classical.decEq _
      cOf := fun π => ⟨eigOfType R F Y π, π, rfl⟩
      lam_const := by
        intro j hj π π' e h1 h2 hcc
        have hc' : eigOfType R F Y π = eigOfType R F Y π' := congrArg Subtype.val hcc
        obtain ⟨p, hp⟩ := hK π
        have hp' : R.Carries p (eigOfType R F Y π') := hc' ▸ hp
        have hj' : 1 ≤ j ∧ j ≤ D.R.m := Finset.mem_Icc.1 hj
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        have hk : k < D.R.m := by omega
        have a1 := hLam ⟨k, hk⟩ π p e h1 (e3 π _ p (hE π) hp ⟨k, hk⟩)
        have a2 := hLam ⟨k, hk⟩ π' p e h2 (e3 π' _ p (hE π') hp' ⟨k, hk⟩)
        exact a1.trans a2.symm }
  refine ⟨E, fun c => A3.fam3.toIx2 hc (labP c), Subtype.val, ?_⟩
  refine ⟨fun π => rfl, Subtype.val_injective, ?_, ?_⟩
  · intro π
    exact e4 π _ _ (hE π) (hPi _).choose_spec
  · intro i π
    have h5 := e5 π _ _ (hE π) (hPi (E.cOf π)).choose_spec i
    exact h5

end GlobalTheory.Mem.R3

end
end
end
