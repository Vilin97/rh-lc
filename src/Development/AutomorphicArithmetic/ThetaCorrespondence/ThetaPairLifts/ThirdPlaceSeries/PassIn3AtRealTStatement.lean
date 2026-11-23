module

public import Formalism.LocalToGlobal.Divisibility.NumericScaleExponentEqExtended
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.PrimitivePackageFullHecke
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFamilyGivenCharactersMultiplicityOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCharacterPlacewiseCuspidalParabolicProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspIndProdCharOfIsProdCuspChar
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteEpsilonOperator
public import Formalism.LocalToGlobal.IndefiniteReal.TransferStatement
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.CoordRat
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatMuOfRowTest
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReordEqConj
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityLinearCharacterEqCharacterSum

section

@[expose] public section

open Formalism.L2.DIV NumberField Module

noncomputable section

namespace GlobalTheory.multiplicity_linearCharacter_eq_characterSum

theorem nOf_eq_charSum : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (τ : Representation K G W) (H : Subgroup G) [Fintype H] (ψ : H →* Kˣ), (Formalism.IndefR.IndefiniteEpsilonOperator.nOf τ ⟨H, ψ⟩ : K) = (Nat.card H : K)⁻¹ * ∑ h : H, Formalism.IndefR.TransferLatticeStatement.charOf τ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) := by
  intro K _ _ G _ _ W _ _ _ τ H _ ψ
  classical
  have hc : (Nat.card H : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  set T : Module.End K W := ∑ h : H, (((ψ h)⁻¹ : Kˣ) : K) • τ (h : G) with hT
  have hep : Formalism.IndefR.IndefiniteEpsilonOperator.epOp τ ⟨H, ψ⟩ = (Nat.card H : K)⁻¹ • T := by
    unfold Formalism.IndefR.IndefiniteEpsilonOperator.epOp
    congr 1
    rw [hT]
    simp only [map_inv]
    congr!
  have h1 : ∀ a : H, ((((ψ a)⁻¹ : Kˣ) : K) • τ (a : G)) * T = T := by
    intro a
    rw [hT, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun h => ?_
    simp [smul_smul, mul_comm]
  have h2 : T * T = (Nat.card H : K) • T := by
    conv_lhs => rw [hT, Finset.sum_mul, ← hT]
    rw [Finset.sum_congr rfl fun a _ => h1 a]
    simp [Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]
  have hid : IsIdempotentElem (Formalism.IndefR.IndefiniteEpsilonOperator.epOp τ ⟨H, ψ⟩) := by
    rw [IsIdempotentElem, hep, smul_mul_smul_comm, h2, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have htr := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
  unfold Formalism.IndefR.IndefiniteEpsilonOperator.nOf Formalism.IndefR.IndefiniteEpsilonOperator.epSp

  rw [← htr, hep, map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl

end GlobalTheory.multiplicity_linearCharacter_eq_characterSum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityLinearCharacterEqCharacterSumStatement

section

@[expose] public section

open Formalism.L2.DIV NumberField

theorem _root_.GlobalTheory.T.multiplicity_linearCharacter_eq_characterSum : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (τ : Representation K G W) (H : Subgroup G) [Fintype H] (ψ : H →* Kˣ), (Formalism.IndefR.IndefiniteEpsilonOperator.nOf τ ⟨H, ψ⟩ : K) = (Nat.card H : K)⁻¹ * ∑ h : H, Formalism.IndefR.TransferLatticeStatement.charOf τ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) := by
  first | exact @GlobalTheory.multiplicity_linearCharacter_eq_characterSum.nOf_eq_charSum | exact GlobalTheory.multiplicity_linearCharacter_eq_characterSum.nOf_eq_charSum | (intros; apply GlobalTheory.multiplicity_linearCharacter_eq_characterSum.nOf_eq_charSum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatMuPOfRowTest

section

@[expose] public section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


open Formalism.IndefR.Rat Formalism.IndefR.Cx.CxData in
theorem ratMuP_of_rowTest : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), Formalism.IndefR.Rat.RowTest (R.toCx3 F) → R.PrincipalLevelBijective F → (R.toCx3 F).RATmu (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R F hT hH2
  obtain ⟨N, ψ, hψ, hr⟩ := hT
  obtain ⟨hinj0, hall⟩ := hH2
  intro t i k
  have hmem : (R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t (Pi.single k 1) ∈
      LinearMap.range ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false A3.A.fam.μ0) := by
    rw [← (hall t).2]; exact LinearMap.mem_range_self _ _
  have key := coord_rat _ ψ hψ ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false A3.A.fam.μ0) hinj0
    (fun j l => by rw [CxData.iC, Formalism.IndefR.Rat.lin_single]; exact hr _ _ _)
    (solve ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false A3.A.fam.μ0)
      ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t (Pi.single k 1)))
    (fun j => by rw [solve_spec _ _ hmem, CxData.iC, Formalism.IndefR.Rat.lin_single]; exact hr _ _ _) i
  obtain ⟨a, ha⟩ := key
  exact ⟨a, ha⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesCardAndResidueLe

section

@[expose] public section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem typePlaces_card_and_residue_le : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.grp_record → R.Pg.card = 2 * D.R.f ∧ ∀ PP ∈ R.Pg, min (D.host.g 0) (D.host.g 1) ≤ Nat.card (kP PP) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h
  obtain ⟨_, plg, iso, -⟩ := h
  refine ⟨?_, fun PP hPP => ?_⟩
  · rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, ← Nat.card_congr plg, Nat.card_sigma]
    have hk : ∀ k : Fin 2, Nat.card (D.nd.PlG k) = D.R.f := fun k => by
      rw [← D.nd.card_PlG k]
      exact @Nat.card_eq_fintype_card _ (_)
    simp only [hk, Fin.sum_univ_two, two_mul]
  · obtain ⟨kv, hkv⟩ := plg.surjective ⟨PP, hPP⟩
    have h1 : Nat.card (kP (plg kv).1) = D.host.g kv.1 := by
      rw [← Nat.card_congr (iso kv).toEquiv, Nat.card_zmod]
    rw [hkv] at h1
    change _ ≤ Nat.card (kP (⟨PP, hPP⟩ : R.Pg).1)
    rw [h1]
    generalize kv.1 = k
    fin_cases k
    · exact min_le_left _ _
    · exact min_le_right _ _

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PassIn3OfRows

section

@[expose] public section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem passIn3_of_rows : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (C CH : ℝ), R.WeakCharacterisation F → A3.fam3.Ok3 1 → PrimRows3 R F → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D → (R.num F C CH).de = 8 * (D.R.f : ℝ) * (D.R.r : ℝ) / ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) → (R.num F C CH).la = Real.log (Fintype.card G) → PassIn3 R F C CH := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R F C CH hC hOk hP hser hadm hde hla
  classical
  have hlev : R.toRealDat.grp_levels F.lv2 := hC.base.grp.levels
  have hrec : R.toRealDat.grp_record := hC.base.grp.record
  have hirr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  have hind := GlobalTheory.T.goodCharacter_placewise_cuspidal_parabolic_product D G Pl0 T A3.A Ks R.toRealDat hrec hser hirr
  letI i0 : Fintype F.P0 := Fintype.ofFinite _
  letI i1 : Fintype F.P1 := Fintype.ofFinite _
  have hone : ∀ χ ∈ A3.A.X, ∑ h : F.P0, χ (h : G) * (((F.ψ0 h)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) = (Fintype.card F.P0 : D.what₂.LL) :=
    @GlobalTheory.RealOneVector.typeSum_base_eq_card D G _ _ Pl0 T A3.A Ks _ _ _ R.toRealDat F.lv2 hlev hind i0
  obtain ⟨S, iS, Ws, iA, iM, iF, τ, hgood, hchars, hm1⟩ :=
    GlobalTheory.T.exists_goodFamily_given_characters_multiplicityOne D.what₂.LL G A3.A.X hirr F.P0 F.ψ0 hone
  obtain ⟨hcard, hres⟩ := GlobalTheory.typePlaces_card_and_residue_le D G Pl0 T A3.A Ks R.toRealDat hrec
  have hcol := @GlobalTheory.ColumnMultSum.columnMult D G _ _ Pl0 T A3.A Ks _ _ _ R.toRealDat F.lv2 hlev hcard hres hadm hirr hind i1
  refine ⟨S, iS, Ws, iA, iM, iF, τ, (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar R.Pg D.R.k : ℝ), ?_⟩
  refine ⟨GlobalTheory.ratMuP_of_rowTest D G Pl0 I0 T A3 Ks R F hP.rowTest hP.h2P, hgood, hchars, hm1, ?_, ?_, ?_⟩
  · exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar_pos R.Pg D.R.k
  · intro s
    obtain ⟨n, hn, hb⟩ := hcol (Formalism.IndefR.TransferLatticeStatement.charOf (τ s)) ((hchars _).2 ⟨s, rfl⟩)
    have hnOf := GlobalTheory.T.multiplicity_linearCharacter_eq_characterSum D.what₂.LL G (Ws s) (τ s) F.P1 F.ψ1
    have heq : Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) ⟨F.P1, F.ψ1⟩ = n := by
      apply Nat.cast_injective (R := D.what₂.LL)
      rw [hnOf]
      exact hn
    rw [heq]
    have hde' : ((faceOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F).zs).Z.num C CH).de = _ := hde
    rw [hde']
    have := abs_le.1 hb
    constructor <;> nlinarith [this.1, this.2]
  · exact hla

end GlobalTheory
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PassIn3AtRealT

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory
theorem passIn3_at_realT_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Del h0 : ℕ) (c : ℝ) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf (fun Zs => let z := Formalism.L2.DIV.ZscOfNum3 P.A3 P.P0 P.ψ0 (Formalism.L2.DIV.ofRecord D L Del h0) (Equiv.refl _) L.Nc Zs; { z with l6m := fun j => z.l6m j - c * z.l6u, l6u := 0 }) S Ks), IsTotallyComplex D.what₂.LL → Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D → P.A3.fam3.Ok3 1 → PrimRows3 Q.Rl Q.F → ∀ C CH : ℝ, PassIn3 Q.Rl Q.F C CH := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Del h0 c S Ks _ _ _ Q hTC hadm hOk hP C CH
  haveI : IsTotallyComplex D.what₂.LL := hTC
  exact GlobalTheory.passIn3_of_rows D P.Gp P.Pl0 P.I0 P.T P.A3 Ks Q.Rl Q.F C CH Q.charW hOk hP
    (fun k => ⟨_, Rc.T.n.types.O k, Rc.T.n.types.eSer_def k⟩) hadm rfl rfl
end GlobalTheory
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PassIn3AtRealTStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.indefScale_theta_degree : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Del h0 : ℕ) (c : ℝ) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf (fun Zs => let z := Formalism.L2.DIV.ZscOfNum3 P.A3 P.P0 P.ψ0 (Formalism.L2.DIV.ofRecord D L Del h0) (Equiv.refl _) L.Nc Zs; { z with l6m := fun j => z.l6m j - c * z.l6u, l6u := 0 }) S Ks), IsTotallyComplex D.what₂.LL → Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D → P.A3.fam3.Ok3 1 → PrimRows3 Q.Rl Q.F → ∀ C CH : ℝ, PassIn3 Q.Rl Q.F C CH := by
  first | exact @_root_.GlobalTheory.passIn3_at_realT_alt | exact _root_.GlobalTheory.passIn3_at_realT_alt | (intros; apply _root_.GlobalTheory.passIn3_at_realT_alt <;> assumption)
end
end
end
