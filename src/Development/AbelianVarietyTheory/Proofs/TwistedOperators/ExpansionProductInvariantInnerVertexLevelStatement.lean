module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColMapEqColMapV
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowRealAverageHoweDualityFockComponentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmEqSumLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdPartialEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingExpansionProductFunctionLocalInvariant
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMtCutPartCompl
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacesPartMovedLevelKeepsStandardHomLattice
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingExpansionProductFunctionLocalInvariantStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.unfoldingExpansion_productFunction_localInvariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) →
    (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ}, β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    (∀ d ∈ τ.support, ∀ j', (d.1 j').e = e) →
    ∀ (T₁ : (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)) (T₂ : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ)),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j)) 1 (S.Z.vac (.top t j)) T₁ →
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) T₂ →
    ∀ c₁ c₂ : ℂ, W.om (.top t j) (1, ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) (S.Z.vac (.top t j)) =
        c₁ • T₁ (fun x => halfInd e (stdLatO S (.top t j)) (actO _ _ 1⁻¹ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ x)) →
      W.om (.top t (j + 1)) (((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        c₂ • T₂ (fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x)) →
    ∀ (x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (τ.sum fun d a => a * (c₁ * c₂) * (∏ j', movedFn S d j hj ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) j' (x j')) * ∏ i, (d.2 i).fn (y i)) =
        τ.sum fun d a => a * (∏ j', (d.1 j').fn (x j')) * ∏ i, (d.2 i).fn (y i) := by
  first | exact @GlobalTheory.TopLevelInv.local_invariant | exact GlobalTheory.TopLevelInv.local_invariant | (intros; apply GlobalTheory.TopLevelInv.local_invariant <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacesPartMovedLevelKeepsStandardHomLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.offPlacesPart_movedLevel_keeps_standardHomLattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ u : WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)),
      u ∈ stdLatO S (.top t (j + 1)) ↔ ∃ u₀ ∈ stdLatO S (.top t (j + 1)),
        u = actO _ _ (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1)))
          ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))))) 1 u₀ := by
  first | exact @GlobalTheory.OffPartLattice.offPart_keeps_stdLatO | exact GlobalTheory.OffPartLattice.offPart_keeps_stdLatO | (intros; apply GlobalTheory.OffPartLattice.offPart_keeps_stdLatO <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacMoveHigh

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove in
theorem vac_move_high : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) Tm →
      ∃ c : ℂ, W.om (.top t (j + 1)) (((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        c • Tm fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x) := by
  intro D T L sc G W U S t ht Φ β j hj k hk e he Tm hTm
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hee : e * e = e := ho.idem
  have hce : e * cA D e = 0 := he.2
  have hf := idem_conj_sum hee hce
  have hW := W.om_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)
  have hvac := S.Z.vac_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)
  have hS := GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on (.top (j + 1)) (show j + 1 ≤ D.R.m by omega))
  have hT := GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on (.top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega))
  set g : GA D (G.V (.top (j + 1))) := ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) :
    FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))) with hgdef
  have key := GlobalTheory.SplitLinear.splitLinearModel D W.ψ _ _ _ _ _ hW _ _ hS hT (locPl G t) e he _ hvac.2.theta hvac.2.lat 1
    one_ne_zero Tm hTm (cutPart (e + cA D e) _ g) 1 (suppAt_cutPart hee hce _ g) (GlobalTheory.SplitLinear.suppAt_one e _) _ _
    (GlobalTheory.VecInv.isDetAt_detAt e hee _ _) (GlobalTheory.VecInv.isDetAt_detAt e hee _ _) _ (GlobalTheory.isSBHalf_halfInd e _)
  have hinf : infPart D (e + cA D e) = 0 := by
    rw [RingHom.map_add (f := _), ho.infPart_eq, infPart_cA ho.infPart_eq, add_zero]
  have hgfin : g ∈ GfC (G.V (.top (j + 1))) := ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))).2
  have hg1fin : cutPart (e + cA D e) _ g ∈ GfC (G.V (.top (j + 1))) :=
    GlobalTheory.IdemSupport.mem_GfC_of_suppF _ hinf (suppAt_cutPart hee hce _ g)
  have hg2fin : cutPart (1 - (e + cA D e)) _ g ∈ GfC (G.V (.top (j + 1))) := by
    have e1 : cutPart (1 - (e + cA D e)) _ g = (cutPart (e + cA D e) _ g)⁻¹ * g := by
      rw [eq_inv_mul_iff_mul_eq, ← cutPart_mul hf]
    rw [e1]
    exact mul_mem (inv_mem hg1fin) hgfin
  have hΛ : ∀ u, u ∈ stdLatO S (.top t (j + 1)) ↔
      ∃ u₀ ∈ stdLatO S (.top t (j + 1)), u = actO _ _ (cutPart (1 - (e + cA D e)) _ g) 1 u₀ :=
    GlobalTheory.T.offPlacesPart_movedLevel_keeps_standardHomLattice S ht j hj k hk e he
  have hV := G.isV (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega) fun _ h => by cases h
  have hV' := G.isV (X := .top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega) fun _ h => by cases h
  have hv' := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ _ hW W.θ_is _ _ _ _ _ _ _ _ (cutPart (1 - (e + cA D e)) _ g) 1
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ hg2fin τ, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ (one_mem _) τ, Matrix.mul_one, Matrix.one_mul]) hΛ _ hvac
  obtain ⟨c₂, -, hc₂⟩ := GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ hV.sigOK hV'.sigOK
    (W.cart_is _ (show j + 1 ≤ D.R.m by omega)) (W.cart_is _ (show j + 1 + 1 ≤ D.R.m by omega)) _ _ hS hT _ _ hvac hv'
  have hvacTm : Tm (halfInd e (stdLatO S (.top t (j + 1)))) = S.Z.vac (.top t (j + 1)) := by
    have := hTm.vac
    rwa [one_smul] at this
  refine ⟨c₂ * ((splitFacO (G.chrS (.top t (j + 1) : Pair T)) (G.chrT (.top t (j + 1) : Pair T))
      (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g))
      (GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1) : ℂ) *
    (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T))
      (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g))
      (GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1) : ℂ)), ?_⟩
  calc W.om (.top t (j + 1)) (g, 1) (S.Z.vac (.top t (j + 1)))
      = W.om (.top t (j + 1)) (cutPart (e + cA D e) _ g, 1)
          (W.om (.top t (j + 1)) (cutPart (1 - (e + cA D e)) _ g, 1) (S.Z.vac (.top t (j + 1)))) := by
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, ← cutPart_mul hf]
    _ = c₂ • W.om (.top t (j + 1)) (cutPart (e + cA D e) _ g, 1) (S.Z.vac (.top t (j + 1))) := by
        rw [hc₂, map_smul]
    _ = _ := by
        rw [← hvacTm]
        erw [key]
        conv_rhs => rw [mul_smul, ← map_smul]
        congr 2
        funext x
        rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.SplitLinear.subst_eq, halfInd_cutPart hee hce]
        rfl

end GlobalTheory.ExpansionInvariance

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionProductInvariantInnerVertexLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

theorem product_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}
    {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) →
    (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))), finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj →
    ∀ (w : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)))
      (z : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (τ.sum fun d a => a * (∏ j', movedCol S d j hj ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))) j' (w j')) *
          ∏ i, S.Z.vec (d.2 i) (z i)) =
        τ.sum fun d a => a * (∏ j', S.Z.vec (d.1 j') (w j')) * ∏ i, S.Z.vec (d.2 i) (z i) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL₀ hde hcc ht hβ hexp hvec j hj k hk w z
  classical
  have hexp' := hexp
  obtain ⟨e, he, hsupp, -⟩ := hexp
  by_cases hτ : τ = 0
  · subst hτ; simp
  obtain ⟨d₀, hd₀⟩ : ∃ d, d ∈ τ.support := by
    obtain ⟨d, hd⟩ := Finsupp.ne_iff.1 hτ
    exact ⟨d, Finsupp.mem_support_iff.2 (by simpa using hd)⟩
  have hmc : ∀ j' : Fin D.R.m, ∃ Tm, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j')) 1
      (S.Z.vac (.top t j')) Tm := fun j' => by
    obtain ⟨f, hf⟩ := (hvec d₀ hd₀).1 j'
    obtain ⟨Tm, hTm⟩ := hf.1
    refine ⟨Tm, ?_⟩
    rw [← ((hsupp d₀ hd₀).1 j').2.1]
    exact hTm
  have hmr : ∀ i : Fin D.R.m, ∃ Tm, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.chi i D.R.m)) 1
      (S.Z.vac (.chi i D.R.m)) Tm := fun i => by
    obtain ⟨f, hf⟩ := (hvec d₀ hd₀).2 i
    obtain ⟨Tm, hTm⟩ := hf.1
    refine ⟨Tm, ?_⟩
    rw [← ((hsupp d₀ hd₀).2 i).2.1]
    exact hTm
  choose Tc hTc using hmc
  choose Tr hTr using hmr
  have hvc : ∀ d ∈ τ.support, ∀ j', S.Z.vec (d.1 j') = Tc j' (d.1 j').fn := fun d hd j' =>
    vec_eq_model S _ ((hsupp d hd).1 j').2.2 ((hvec d hd).1 j') _ (by rw [((hsupp d hd).1 j').2.1]; exact hTc j')
  have hvr : ∀ d ∈ τ.support, ∀ i, S.Z.vec (d.2 i) = Tr i (d.2 i).fn := fun d hd i =>
    vec_eq_model S _ ((hsupp d hd).2 i).2.2 ((hvec d hd).2 i) _ (by rw [((hsupp d hd).2 i).2.1]; exact hTr i)
  set g : FinPt G (.top (j + 1)) := (S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) with hg
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.columnArrow_realAverage_howeDuality_fockComponent S ht (Φ := Φ) (β := β) j hj k hk e he (Tc ⟨j, by omega⟩) (hTc ⟨j, by omega⟩)
  obtain ⟨c₂, hc₂⟩ := vac_move_high S ht j hj k hk e he (Tc ⟨j + 1, hj⟩) (hTc ⟨j + 1, hj⟩)
  have hla : ∀ X : Node, DefNode D.R.m X → (∀ i, X ≠ .grid 0 i) → X.InRange D.R.m →
      Submodule.IsFullLattice D.host.E (G.Λ X) := fun X _ h0 hX =>
        GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ (G.isV hX h0).sd
  have hsb : ∀ d ∈ τ.support, ∀ j' : Fin D.R.m, IsSBHalf e (stdLatO S (.top t j')) (d.1 j').fn := fun d hd j' => by
    have h1 := (d.1 j').sb
    rw [((hsupp d hd).1 j').2.1] at h1
    have hj₀ : (j' : ℕ) ≤ D.R.m := Nat.le_of_lt j'.2
    have hj₁ : (j' : ℕ) + 1 ≤ D.R.m := j'.2
    letI := hla (.top j') hj₀ (by simp) hj₀
    letI := hla (.top (j' + 1)) hj₁ (by simp) hj₁
    letI : Submodule.IsFullLattice D.host.E (S.N.latS (.top t j')) :=
      GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ (S.N.selfDual (X := .top j') hj₀)
    letI : Submodule.IsFullLattice D.host.E (S.N.latT (.top t j')) :=
      GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ (S.N.selfDual (X := .top (j' + 1)) hj₁)
    exact VecEx.isSBHalf_of_lattices inferInstance inferInstance inferInstance inferInstance
      (GlobalTheory.PlaceDatum.infPart_idemSum he) h1
  have hmv : ∀ d ∈ τ.support, ∀ j', movedCol S d j hj g j' =
      (Function.update (Function.update (1 : Fin D.R.m → ℂ) ⟨j, by omega⟩ c₁) ⟨j + 1, hj⟩ c₂ j') •
        Tc j' (movedFn S d j hj g j') := fun d hd j' => by
    rcases eq_or_ne j' ⟨j + 1, hj⟩ with rfl | h1
    · simp only [movedCol, movedFn, Function.update_self]
      rw [hvc d hd]
      exact GlobalTheory.SplitLinear.om_model_of_base D W.ψ _ _ _ _ _ (S.N.latS (.top t (j + 1))) (S.N.latT (.top t (j + 1))) e
        (S.Z.vac (.top t (j + 1))) _ (W.om_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega))
        (S.N.selfDual (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega))
        (S.N.selfDual (X := .top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega))
        (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he)
        (S.Z.vac_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)).2.theta (hTc ⟨j + 1, hj⟩) _ _ c₂ hc₂ _ (hsb d hd ⟨j + 1, hj⟩)
    rcases eq_or_ne j' ⟨j, by omega⟩ with rfl | h2
    · simp only [movedCol, movedFn, Function.update_of_ne h1, Function.update_self]
      rw [hvc d hd]
      exact GlobalTheory.SplitLinear.om_model_of_base D W.ψ _ _ _ _ _ (S.N.latS (.top t j)) (S.N.latT (.top t j)) e
        (S.Z.vac (.top t j)) _ (W.om_is (.top t j) (show j + 1 ≤ D.R.m by omega))
        (S.N.selfDual (X := .top j) (show j ≤ D.R.m by omega))
        (S.N.selfDual (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega))
        (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he)
        (S.Z.vac_is (.top t j) (show j + 1 ≤ D.R.m by omega)).2.theta (hTc ⟨j, by omega⟩) _ _ c₁ hc₁ _ (hsb d hd ⟨j, by omega⟩)
    · simp only [movedCol, movedFn, Function.update_of_ne h1, Function.update_of_ne h2, Pi.one_apply, one_smul]
      exact hvc d hd j'
  have hprod : ∏ j' : Fin D.R.m, Function.update (Function.update (1 : Fin D.R.m → ℂ) ⟨j, by omega⟩ c₁) ⟨j + 1, hj⟩ c₂ j' =
      c₁ * c₂ := by
    have hne : (⟨j, by omega⟩ : Fin D.R.m) ≠ ⟨j + 1, hj⟩ := fun h => by simp [Fin.ext_iff] at h
    rw [Finset.prod_update_of_mem (Finset.mem_univ _), Finset.prod_update_of_mem (by simp [hne])]
    simp only [Pi.one_apply, Finset.prod_const_one, mul_one]
    ring
  let X : Fin D.R.m ⊕ Fin D.R.m → Type := Sum.elim (fun j' => WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)))
    fun i => WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))
  let Tt : ∀ a, (X a → ℂ) →ₗ[ℂ] (X a → ℂ) := fun a => match a with
    | .inl j' => Tc j'
    | .inr i => Tr i
  let F : PureDat G t → ∀ a, X a → ℂ := fun d a => match a with
    | .inl j' => (d.1 j').fn
    | .inr i => (d.2 i).fn
  let F' : PureDat G t → ∀ a, X a → ℂ := fun d a => match a with
    | .inl j' => movedFn S d j hj g j'
    | .inr i => (d.2 i).fn
  let yy : ∀ a, X a := fun a => match a with
    | .inl j' => w j'
    | .inr i => z i
  have key := sum_prod_map_congr Tt τ.support τ.support (fun d => τ d) (fun d => τ d * (c₁ * c₂)) F F' (fun x => by
    have := GlobalTheory.T.unfoldingExpansion_productFunction_localInvariant S hL₀ hde hcc ht hβ hexp' j hj k hk e he (fun d hd j' => ((hsupp d hd).1 j').2.1) _ _ (hTc ⟨j, by omega⟩)
      (hTc ⟨j + 1, hj⟩) c₁ c₂ hc₁ hc₂ (fun j' => x (.inl j')) (fun i => x (.inr i))
    simp only [Finsupp.sum] at this
    simp only [Fintype.prod_sum_type]
    refine (Finset.sum_congr rfl fun d _ => ?_).trans (this.trans (Finset.sum_congr rfl fun d _ => ?_))
    · exact (mul_assoc _ _ _).symm
    · exact mul_assoc _ _ _) yy
  simp only [Fintype.prod_sum_type] at key
  have hL : (∑ d ∈ τ.support, τ d * (∏ j', movedCol S d j hj g j' (w j')) * ∏ i, S.Z.vec (d.2 i) (z i)) =
      ∑ d ∈ τ.support, τ d * (c₁ * c₂) * ((∏ j', Tc j' (movedFn S d j hj g j') (w j')) * ∏ i, Tr i (d.2 i).fn (z i)) :=
    Finset.sum_congr rfl fun d hd => by
      simp only [hmv d hd, hvr d hd, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, hprod]; ring
  have hR : (∑ d ∈ τ.support, τ d * (∏ j', S.Z.vec (d.1 j') (w j')) * ∏ i, S.Z.vec (d.2 i) (z i)) =
      ∑ d ∈ τ.support, τ d * ((∏ j', Tc j' (d.1 j').fn (w j')) * ∏ i, Tr i (d.2 i).fn (z i)) :=
    Finset.sum_congr rfl fun d hd => by simp only [hvc d hd, hvr d hd]; ring
  simp only [Finsupp.sum]
  rw [hL, hR]
  exact key

end GlobalTheory.ExpansionInvariance

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionProductInvariantInnerVertexLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.expansion_product_invariant_inner_vertex_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}
    {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))), finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj →
    ∀ (w : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)))
      (z : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (τ.sum fun d a => a * (∏ j', movedCol S d j hj ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))) j' (w j')) *
          ∏ i, S.Z.vec (d.2 i) (z i)) =
        τ.sum fun d a => a * (∏ j', S.Z.vec (d.1 j') (w j')) * ∏ i, S.Z.vec (d.2 i) (z i) := by
  first | exact @GlobalTheory.ExpansionInvariance.product_invariant | exact GlobalTheory.ExpansionInvariance.product_invariant | (intros; apply GlobalTheory.ExpansionInvariance.product_invariant <;> assumption)
end
end
