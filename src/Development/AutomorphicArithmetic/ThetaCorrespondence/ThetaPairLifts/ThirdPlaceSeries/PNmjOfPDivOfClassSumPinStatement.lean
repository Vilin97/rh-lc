module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassSumPinT
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NXNMjT
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
public import Formalism.LocalToGlobal.ClassRec
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
public import Formalism.LocalToGlobal.Divisibility.HeckeRI
public import Formalism.LocalToGlobal.HilbertRowConditions.ColumnsFunctionAtSubspaces
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeFamilyAdoptionFirstStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeFamilyAdoptionSecondAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionThird

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ClassSumLift

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
  {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem theta_cast (j : ℕ) (μ ν : D.what₂.Tup) (h : μ = ν) (x : D.what₂.MtL μ j) :
    D.what₂.thetaP ν j (D.what₂.jMt ν j (h ▸ x)) = D.what₂.thetaP μ j (D.what₂.jMt μ j x) := by
  subst h; rfl

theorem exists_heq_fin {K : Type} {a b : ℕ} (h : a = b) (z : Fin a → K) : ∃ y : Fin b → K, HEq z y := by
  subst h; exact ⟨z, HEq.rfl⟩

theorem exists_cast (j : ℕ) (μ ν : D.what₂.Tup) (h : μ = ν) (x : D.what₂.MtL ν j) :
    ∃ x' : D.what₂.MtL μ j, x = h ▸ x' := by
  subst h; exact ⟨x, rfl⟩


end GlobalTheory.ClassSumLift
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EMEqThPe

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.ClassSumLift
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
  {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem indefDown_dW_eq_finrank_WL (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    (P.A3.indefDown P.S0).dW i = Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i) := by
  have hz := Q.zs
  have hs := Q.s0
  have key : ∀ (Z : DefSub P.A3.fam3.amb3) (S' : IndefData (P.A3.side3 P.P0 P.ψ0 Z)), Z = P.Zs → HEq S' P.S0 →
      P.S0.dW i = S'.dW i := by
    intro Z S' h1 h2
    subst h1
    rw [eq_of_heq h2]
  exact key _ _ hz hs
theorem exists_sum_smul_eq_of_isKsForm (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) (hk : (Q.Rl.FW i).IsKsForm)
    (v : Fin (Q.Rl.nW i) → D.what₂.LL) :
    ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK Q.Sx ((i : ℕ) + 1)),
      (Q.nexp.fi i).e (∑ k, a k • (show ↥(Q.Sx.A ((i : ℕ) + 1)).WK from f k).1) = v := by
  obtain ⟨n, b, hb, -, -, -, hs⟩ := hk
  have hv : v ∈ Submodule.span D.what₂.LL (Set.range b) := by rw [hs]; trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
  refine ⟨n, a, fun k => (⟨(Q.nexp.fi i).e.symm (b k), ((Q.nexp.fi i).wk _).2 (by
    rw [LinearEquiv.apply_symm_apply]; exact hb k)⟩ : ↥(Q.Sx.A ((i : ℕ) + 1)).WK), ?_⟩

  rw [map_sum, ← ha]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  congr 1
  exact (Q.nexp.fi i).e.apply_symm_apply _

theorem at_index_alt (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) (hP : _root_.GlobalTheory.ExportPin.IndefiniteClassSumCondition B.Q)
    (hD : DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I)
    (w : D.what₂.places.Pl) (i : Fin D.R.m) (h1 : 1 ≤ (i : ℕ) + 1) (h2 : (i : ℕ) + 1 ≤ D.R.m)
    (hw : D.what₂.muAt w ≠ D.what₂.mu0)
    (jD : (Y.MjH ((i : ℕ) + 1)).V → B.Q.Sx.WL ((i : ℕ) + 1))
    (hjD : ∀ (x : (Y.MjH ((i : ℕ) + 1)).V)
      (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL),
      HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD x) = jDL B.Q.Rl B.Q.F.lv2 i y)
    (eMj : (Y.MjH ((i : ℕ) + 1)).V → FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)]
      D.nexp.Fm (ex.nch.twI w) ((i : ℕ) + 1) (ex.nch.sd w))
    (hsum : ∀ (x : (Y.MjH ((i : ℕ) + 1)).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx ((i : ℕ) + 1)),
      jD x = ∑ k, a k • (show ↥(B.Q.Sx.A ((i : ℕ) + 1)).WK from f k).1 →
      eMj x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)]
          (B.Q.nexp.eF (ex.nch.twI w) ((i : ℕ) + 1) (ex.nch.sd w) h1 h2).symm
            ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k))
    (x : D.what₂.MtL (D.what₂.muTw w) ((i : ℕ) + 1)) (hx : x ∈ Idx.TjV D (D.what₂.muTw w) ((i : ℕ) + 1))
    (z : (Y.MjH ((i : ℕ) + 1)).V)
    (hz : Y.jM _ z = D.what₂.thetaP (D.what₂.muTw w) _ (D.what₂.jMt (D.what₂.muTw w) _ x)) :
    eMj z = NChoice.thPe D ex.nch w ((i : ℕ) + 1) (ex.nch.eMt w ((i : ℕ) + 1) x) := by
  have ht : P.I.tup (Qr.tupT (D.what₂.muAt w)) = D.what₂.muTw w :=
    (Qr.tupTie _ (Or.inr ⟨w, rfl⟩)).trans ((D.what₂.muAt_or w).resolve_left hw)
  obtain ⟨x', e1⟩ := exists_cast ((i : ℕ) + 1) _ _ ht x
  obtain ⟨c, rfl⟩ := (P.I.eMt i _).surjective x'
  obtain ⟨y, e2⟩ := exists_heq_fin (_root_.GlobalTheory.ClassSumLift.indefDown_dW_eq_finrank_WL B.Q i) (((P.A3.indefDown P.S0).θ i _).mulVec
        ((lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i _).mulVec c))
  obtain ⟨n, a, f, e3⟩ := _root_.GlobalTheory.ClassSumLift.exists_sum_smul_eq_of_isKsForm B.Q i (B.fw.ks i) (jDL B.Q.Rl B.Q.F.lv2 i y)
  rw [hP w i h1 h2 _ ht hw c x e1 hx y e2 n a f e3]
  apply hsum
  apply (B.Q.nexp.fi i).e.injective
  rw [e3]
  apply hjD
  have : z = P.JM.eW i (((P.A3.indefDown P.S0).θ i (Qr.tupT (D.what₂.muAt w))).mulVec
        ((lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i (Qr.tupT (D.what₂.muAt w))).mulVec c)) := by
    apply Idx.jM_inj Y
    rw [hz, P.tied.mjH.j_eq, ← hD.thTheta, e1]
    exact theta_cast _ _ _ ht _
  rw [this, LinearEquiv.symm_apply_apply]
  exact e2
end GlobalTheory.ClassSumLift

theorem GlobalTheory.ClassSumLift.eM_eq_thPe_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I → _root_.GlobalTheory.ExportPin.IndefiniteClassSumCondition B.Q → (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) → (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) → ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → ∀ x ∈ Idx.TjV D (D.what₂.muTw w) j, ∀ y : (Y.MjH j).V, Y.jM j y = D.what₂.thetaP (D.what₂.muTw w) j (D.what₂.jMt (D.what₂.muTw w) j x) → eM w j y = NChoice.thPe D ex.nch w j (ex.nch.eMt w j x) := by
  intro D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B _ Qr jD eM hD hP hread hsum w j hw h1 h2 x hx y hy
  obtain ⟨i, rfl⟩ : ∃ i : Fin D.R.m, (i : ℕ) + 1 = j := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  exact _root_.GlobalTheory.ClassSumLift.at_index_alt B Qr hP hD w i h1 h2 hw (jD ((i : ℕ) + 1)) (fun x y h => hread i x y h) (eM w ((i : ℕ) + 1))
    (fun x n a f h => hsum w ((i : ℕ) + 1) h1 h2 x n a f h) x hx y hy
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EMEqThPeStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lattice_family_adoption_third_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I → _root_.GlobalTheory.ExportPin.IndefiniteClassSumCondition B.Q → (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) → (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) → ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → ∀ x ∈ Idx.TjV D (D.what₂.muTw w) j, ∀ y : (Y.MjH j).V, Y.jM j y = D.what₂.thetaP (D.what₂.muTw w) j (D.what₂.jMt (D.what₂.muTw w) j x) → eM w j y = NChoice.thPe D ex.nch w j (ex.nch.eMt w j x) := by
  first | exact @_root_.GlobalTheory.ClassSumLift.eM_eq_thPe_alt | exact _root_.GlobalTheory.ClassSumLift.eM_eq_thPe_alt | (intros; apply _root_.GlobalTheory.ClassSumLift.eM_eq_thPe_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NmjTAtTied

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.BigTop.PtAt.nmjT_at_tied_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q), NChTie D ex.nch → DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I → _root_.GlobalTheory.ExportPin.IndefiniteClassSumCondition B.Q → _root_.Formalism.IndefR.NX.RealExpansionMajorant B.Q B.Q.cG B.Q.Sx B.Q.nexp ex.nch := by
  intro D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hP hR hTie hDiv hPin
  obtain ⟨jD, eM, hAg, hKs, hSum, hEmb, hLi⟩ := _root_.GlobalTheory.T.lattice_family_adoption_first_alt D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hP hR hTie
  have hLat := _root_.GlobalTheory.T.lattice_family_adoption_second_alt D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hP hR jD eM hTie hAg hSum
  have hTh := _root_.GlobalTheory.T.lattice_family_adoption_third_alt D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hP hR jD eM hDiv hPin hAg hSum
  exact ⟨jD, hAg, ⟨{ eMj := eM, eMj_li := hLi, eMj_lat := hLat, eMj_th := hTh, ks := hKs, eMj_sum := hSum, embW_Ks := hEmb }⟩⟩
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NmjTAtTiedStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lattice_family_adoption_fourth_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q), NChTie D ex.nch → DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I → _root_.GlobalTheory.ExportPin.IndefiniteClassSumCondition B.Q → _root_.Formalism.IndefR.NX.RealExpansionMajorant B.Q B.Q.cG B.Q.Sx B.Q.nexp ex.nch := by
  first | exact @_root_.GlobalTheory.BigTop.PtAt.nmjT_at_tied_alt | exact _root_.GlobalTheory.BigTop.PtAt.nmjT_at_tied_alt | (intros; apply _root_.GlobalTheory.BigTop.PtAt.nmjT_at_tied_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PNmjOfPDivOfClassSumPin

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
theorem pNmj_of_pDiv_of_classSumPin_alt :
    ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c),
      _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c b → GlobalTheory.ExportPin.ClassSumPin b.pt → _root_.GlobalTheory.Fc.Ind.NormJumpPointSummands D O c b :=
  fun D O _ b hdiv hpin =>
    _root_.GlobalTheory.T.lattice_family_adoption_fourth_alt D _ _ _ _ _ _ _ O.ex _ _ _ _ _ _ b.B b.pins b.Rr O.ex.nch_tie hdiv hpin
end GlobalTheory.Fc.Ind
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PNmjOfPDivOfClassSumPinStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.pNmj_of_pDiv_classSumPin : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c b → GlobalTheory.ExportPin.ClassSumPin b.pt → _root_.GlobalTheory.Fc.Ind.NormJumpPointSummands D O c b := by
  first | exact @_root_.GlobalTheory.Fc.Ind.pNmj_of_pDiv_of_classSumPin_alt | exact _root_.GlobalTheory.Fc.Ind.pNmj_of_pDiv_of_classSumPin_alt | (intros; apply _root_.GlobalTheory.Fc.Ind.pNmj_of_pDiv_of_classSumPin_alt <;> assumption)
end
end
end
