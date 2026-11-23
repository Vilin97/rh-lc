module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ClassCountBoundAtConstructedPoints
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
public import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements
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
public import Formalism.LocalRingCardinality.PrincipalHermitianLattice
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Formalism.LocalToGlobal.GroupLattices.JointServices.LevelOperatorFixesImage
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveRowsMapBijectiveColumnLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField

namespace GlobalTheory

theorem prim_rows_surjective : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → ∀ (Zs : DefSub A3.fam3.amb3) (S1 : IndefData (A3.side3 F.P1 F.ψ1 Zs)), (R.toCx3 F).zs = Zs → HEq ((R.toCx3 F).data F.cr true) S1 → Function.Surjective ((A3.side3 F.P1 F.ψ1 Zs).Pq A3.A.μ0).mulVec ∧ Function.Surjective (S1.ι A3.A.μ0).mulVec := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hsep hW hP Zs S1 hz hS
  subst hz
  have hS' := eq_of_heq hS
  subst hS'
  have hR := complex_data_conditions_base_level_of_primitive_links hok hsep hW hP
  exact ⟨(hR.wf true).Pq_surj _, (CxData.rowMat_bij _ _ true (hR.what₂ true).1 (hR.ratMu true) _).2⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveRowsMapBijectiveColumnLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField

theorem _root_.GlobalTheory.T.primitiveRows_map_bijective_columnLevel : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → ∀ (Zs : DefSub A3.fam3.amb3) (S1 : IndefData (A3.side3 F.P1 F.ψ1 Zs)), (R.toCx3 F).zs = Zs → HEq ((R.toCx3 F).data F.cr true) S1 → Function.Surjective ((A3.side3 F.P1 F.ψ1 Zs).Pq A3.A.μ0).mulVec ∧ Function.Surjective (S1.ι A3.A.μ0).mulVec := by
  first | exact @GlobalTheory.prim_rows_surjective | exact GlobalTheory.prim_rows_surjective | (intros; apply GlobalTheory.prim_rows_surjective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowSideIotaMapsFixedColumnsOntoOfMatrices

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions

theorem GlobalTheory.rowSide_iota_maps_fixedColumns_onto_of_matrices : ∀ (D : D7) (μ : D.what₂.Tup) (n nV dQ d : ℕ) (jA : (Fin n → D.what₂.LL) →ₛₗ[D.what₂.embLL] (RowSide.sharp D).Amb μ) (E : Matrix (Fin n) (Fin n) D.what₂.LL) (V : Matrix (Fin n) (Fin nV) D.what₂.LL) (Pq : Matrix (Fin dQ) (Fin nV) D.what₂.LL) (ι : Matrix (Fin d) (Fin dQ) D.what₂.LL) (eRR : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] (RowSide.sharp D).RR.V), (∀ x, (RowSide.sharp D).eOp μ (jA x) = jA (E.mulVec x)) → (∀ F, E.mulVec (V.mulVec F) = V.mulVec F) → Function.Surjective Pq.mulVec → Function.Surjective ι.mulVec → (∀ F, (RowSide.sharp D).iota μ (jA (V.mulVec F)) = (RowSide.sharp D).jEE (eRR (ι.mulVec (Pq.mulVec F)))) → (D.what₂.V0 μ).map (D.what₂.iota μ) = ⊤ := by
  intro D μ n nV dQ d jA E V Pq ι eRR hE hV hP hι hio
  have hi : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
    unfold RowSide.iota Rows.Data.iota
    rw [PrimeDegreeVariant.sharp_downTo]
    rfl
  have hV0 : (RowSide.sharp D).V0 μ = D.what₂.V0 μ := rfl
  rw [eq_top_iff, ← (RowSide.sharp D).jEE_basis.2, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨y, hy⟩ := hι (eRR.symm ((RowSide.sharp D).RR.b i))
  obtain ⟨F, hF⟩ := hP y
  have h1 := hio F
  rw [hF, hy, LinearEquiv.apply_symm_apply, hi] at h1
  refine ⟨jA (V.mulVec F), ?_, h1⟩
  rw [← hV0]
  exact ⟨jA (V.mulVec F), by rw [hE, hV]⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.V0MapIotaEqTopDefinite

section

@[expose] public section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef NumberField

theorem GlobalTheory.V0_map_iota_eq_top_of_definite : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 Ty T : Type) (m : ℕ) (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A3.side3 Ps ψs Zs)) (Sp : SPer Dc) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc), DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I → (∃ s, A3.A.fam.Ok s) → Function.Surjective ((A3.side3 Ps ψs Zs).Pq A3.A.μ0).mulVec → Function.Surjective (S1.ι A3.A.μ0).mulVec → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D G _ _ Pl0 I0 Ty T m A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc Sp C NuC I hD hOk hPq hι
  obtain ⟨s, hs⟩ := hOk

  have key := GlobalTheory.rowSide_iota_maps_fixedColumns_onto_of_matrices D (I.tup A3.A.μ0) _ _ _ _
    (I.jA A3.A.μ0) (rE D A3.A Ps ψs A3.A.μ0) (rV0 D A3.A Ps ψs A3.A.μ0)
    ((A3.side3 Ps ψs Zs).Pq A3.A.μ0) (S1.ι A3.A.μ0) I.eRR
    (fun x => (hD.sharp.forms A3.A.μ0).op_eq x)
    (fun F => Formalism.L2.G.ServJoint.level_operator_fixes_image hs Ps ψs (A3.fam3.toSub2 Zs) A3.A.μ0 F)
    hPq hι (fun F => hD.sharp.iota A3.A.μ0 F)
  rw [hD.tup.mu0] at key
  exact key
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.V0MapIotaEqTopDefiniteStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef NumberField

theorem _root_.GlobalTheory.T.V0_map_iota_eq_top_definite : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 Ty T : Type) (m : ℕ) (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A3.side3 Ps ψs Zs)) (Sp : SPer Dc) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc), DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I → (∃ s, A3.A.fam.Ok s) → Function.Surjective ((A3.side3 Ps ψs Zs).Pq A3.A.μ0).mulVec → Function.Surjective (S1.ι A3.A.μ0).mulVec → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  first | exact @GlobalTheory.V0_map_iota_eq_top_of_definite | exact GlobalTheory.V0_map_iota_eq_top_of_definite | (intros; apply GlobalTheory.V0_map_iota_eq_top_of_definite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowMapSurjectiveOfPrimitiveRows

section

@[expose] public section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField

namespace GlobalTheory

theorem rowMap_surjective_of_primitiveRows_alt : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A3.side3 Ps ψs Zs)) (Sp : SPer Dc) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc) (Dcf : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 Ps ψs Zs)) (Spf : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (s : ℕ), DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I → A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3) → PrimRows3 R (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3) → (R.toCx3 (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3)).zs = Zs → HEq ((R.toCx3 (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3)).data (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3).cr true) S1 → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R P0 ψ0 Ps ψs Zs S0 S1 X0 Dc Sp C NuC I Dcf Spf Zscf s hD hOk hSep hW hP hzs hS1
  obtain ⟨h1, h2⟩ := GlobalTheory.T.primitiveRows_map_bijective_columnLevel D G Pl0 I0 T A3 Ks R ⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ s hOk hSep hW hP Zs S1 hzs hS1
  exact GlobalTheory.T.V0_map_iota_eq_top_definite D G Pl0 I0 (List ℕ) T D.R.m A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc Sp C NuC I hD ⟨s, hOk.ok2⟩ h1 h2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowMapSurjectiveOfPrimitiveRowsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField

theorem _root_.GlobalTheory.T.rowMap_surjective_of_primitiveRows : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A3.side3 Ps ψs Zs)) (Sp : SPer Dc) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc) (Dcf : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 Ps ψs Zs)) (Spf : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (s : ℕ), DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I → A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3) → PrimRows3 R (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3) → (R.toCx3 (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3)).zs = Zs → HEq ((R.toCx3 (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3)).data (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3).cr true) S1 → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  first | exact @GlobalTheory.rowMap_surjective_of_primitiveRows_alt | exact GlobalTheory.rowMap_surjective_of_primitiveRows_alt | (intros; apply GlobalTheory.rowMap_surjective_of_primitiveRows_alt <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.V0MapIotaEqTopOfReal

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx NumberField
namespace GlobalTheory
theorem V0_map_iota_eq_top_of_real_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) (_ : Field Ks) (_ : NumberField Ks) (_ : Algebra Ks D.what₂.LL) (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (s : ℕ), P.A3.fam3.Ok3 s → P.A3.fam3.TypesSep3 → PrimRows3 Q.Rl Q.F → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S Ks _ _ _ Q s hOk hSep hPrim
  haveI : IsTotallyComplex D.what₂.LL := D.tcLL
  exact GlobalTheory.T.rowMap_surjective_of_primitiveRows D P.Gp P.Pl0 P.I0 P.T P.A3 Ks Q.Rl P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.Dc P.Sp P.C P.NuC P.I
    Dcf Spf Zscf s P.tied.div hOk hSep Q.charW hPrim Q.zs Q.s1
end GlobalTheory
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.V0MapIotaEqTopOfRealStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx NumberField

theorem _root_.GlobalTheory.T.V0_map_iota_eq_top_real_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) (_ : Field Ks) (_ : NumberField Ks) (_ : Algebra Ks D.what₂.LL) (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (s : ℕ), P.A3.fam3.Ok3 s → P.A3.fam3.TypesSep3 → PrimRows3 Q.Rl Q.F → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  first | exact @_root_.GlobalTheory.V0_map_iota_eq_top_of_real_alt | exact _root_.GlobalTheory.V0_map_iota_eq_top_of_real_alt | (intros; apply _root_.GlobalTheory.V0_map_iota_eq_top_of_real_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowJOnOfRealisations

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx NumberField GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.JOnRow
theorem row_jOn_of_realisations_alt : ∀ (Bd : BdT) (Q' : V4.Slot) (Lk : LkT Bd), Row Q' Lk (AtAll fun D O _ _ => ∃ (Rc : _root_.Formalism.L2.RecTAlt O.ex) (P : RowSideFamily O.ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) (_ : Field Ks) (_ : NumberField Ks) (_ : Algebra Ks D.what₂.LL) (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (s : ℕ), P.A3.fam3.Ok3 s ∧ P.A3.fam3.TypesSep3 ∧ PrimRows3 Q.Rl Q.F) → R0.JInvariantConditionAtConstructedPoints Q' Lk := by
  intro Bd Q' Lk h
  refine Row.imp h fun 𝒜 σ _ hA => ?_
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ hc _ => ?_⟩⟩
  refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
  have hx' : Fm.x1 < x := by linarith
  obtain ⟨Rc, P, Dcf, Spf, Zscf, S, Ks, i1, i2, i3, Q, s, h1, h2, h3⟩ := hA Fm (w3_a hc) x hx' i
  exact _root_.GlobalTheory.T.V0_map_iota_eq_top_real_alt _ _ _ _ _ _ _ _ _ Rc P Dcf Spf Zscf S Ks i1 i2 i3 Q s h1 h2 h3
end GlobalTheory.JOnRow
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowJOnOfRowHPA

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.JOnBundle
theorem row_jOn_of_row_hPA_alt : ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition Q Lk → R0.JInvariantConditionAtConstructedPoints Q Lk := by
  intro Q Lk h
  apply _root_.GlobalTheory.JOnRow.row_jOn_of_realisations_alt _root_.GlobalTheory.Fc.BundleCondition Q Lk
  refine Row.imp h fun 𝒜 σ _ hA => ?_
  intro eps Fm hc x hx i
  have hb := hA Fm hc x hx i
  exact ⟨(σ Fm hc x hx i).R, (σ Fm hc x hx i).P, _, _, _, (σ Fm hc x hx i).S, _, inferInstance, inferInstance, inferInstance,
    (σ Fm hc x hx i).B.Q, 1, (σ Fm hc x hx i).C.ok1, hb.2, hb.1⟩
end GlobalTheory.Fc.JOnBundle
end
end
end
end
