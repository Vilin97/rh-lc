module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionsSpannedHeckeTwistedStandardFrameStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EWCastSymmWtStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MapMemISupIsLinAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftAutomorphicForm
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
import Mathlib.Tactic.Linter.Style
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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemOmIOfThetaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupChars
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.Automorphisms.PlaceA
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InnerTheta

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.ThetaRead
open MeasureTheory Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.RecTie
  Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.ThetaTri
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Pair
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
end Pair
section Unit
variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
end Unit
section Row
variable {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
end Row
section Forms
variable {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} {X : GlobalTheory.NJoin.RealAt D cf nch tp}
  {M : MtFam D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
end Forms
section Canon
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp)

theorem integral_theta_evaluation_thetaKO {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (k : ℕ) (hk : j.1 + 1 = k) (Y : RowMod D P.rep k)
    (hc : GlobalTheory.NJoin.IsCanon X j hk Y) (x : D.what₂.Mt μ k) (y : D.what₂.Mj k) :
    inner ℂ y (D.what₂.thetaP μ k x) = (_root_.GlobalTheory.ThetaTri.canonicalConstant hc : ℂ) *
      ∫ g in X.R.fdW j, star (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc ⟨Y.φ y, Y.φ_mem y⟩ g) *
        (∫ h in X.R.fdV j (X.tupT μ), thetaKO (X.R.ωP j (X.tupT μ)) h g
          (_root_.GlobalTheory.ThetaTri.standardSchwartzFunctionMap j (X.tupT μ) (X.fn hμ j (hk.symm ▸ x) h)) ∂(X.R.νV j (X.tupT μ))) ∂(X.R.νW j) := by
  subst hk
  obtain ⟨-, -, -, -, hB, hφ⟩ := Classical.choose_spec (Classical.choose_spec hc)
  refine (Y.φ_inner _ _).trans ((hB _ (Y.φ_mem _) _ (Y.φ_mem _)).trans (congrArg (fun z => (_root_.GlobalTheory.ThetaTri.canonicalConstant hc : ℂ) * z) ?_))
  exact ipM_theta X hμ j x y (_root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (Y.φ y)) (_root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (Y.φ (D.what₂.thetaP μ (j.1 + 1) x))) (hφ y) (hφ _)
end Canon
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (x : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) (y : D.what₂.Mj (D.nd.j i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)), (F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = (P.M.loc i).real x → inner ℂ y (D.what₂.thetaP (D.nd.mu i) (D.nd.j i) x) = _root_.GlobalTheory.ThetaTri.canonicalPairingValue A i j hj hc hμ (_root_.GlobalTheory.ThetaTri.standardSchwartzFunctionMap j (X.tupT (D.nd.mu i))) F ⟨Y.φ y, Y.φ_mem y⟩ := by
  intro hL D P X A i j hj Y hc hμ x y F hF
  have hf : _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F = X.fn hμ j (hj.symm ▸ x) := by
    refine Eq.trans ?_ (ext_real_cast X.given.core.models.cV A hμ j _ hj (D.nd.j_range i).1 (D.nd.j_range i).2 x)
    show (X.R.cV j).ext (fun k => (_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm
      ((F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) (A.a j * preF (A.PV j) k))) = _
    rw [hF]
    rfl
  rw [_root_.GlobalTheory.ThetaRead.integral_theta_evaluation_thetaKO X hμ j _ hj Y hc x y, ← hf]
  rfl
end GlobalTheory.ThetaRead
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InnerThetaStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.theta_lift_automorphic_form_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (x : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) (y : D.what₂.Mj (D.nd.j i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)), (F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = (P.M.loc i).real x → inner ℂ y (D.what₂.thetaP (D.nd.mu i) (D.nd.j i) x) = _root_.GlobalTheory.ThetaTri.canonicalPairingValue A i j hj hc hμ (_root_.GlobalTheory.ThetaTri.standardSchwartzFunctionMap j (X.tupT (D.nd.mu i))) F ⟨Y.φ y, Y.φ_mem y⟩ := by
  first | exact @_root_.GlobalTheory.ThetaRead.main_alt_alt | exact _root_.GlobalTheory.ThetaRead.main_alt_alt | (intros; apply _root_.GlobalTheory.ThetaRead.main_alt_alt <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LiftedCharactersAgree

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDatumChars

theorem xi_eq_of_heq {D : D7} {C C' : Formalism.L2.Host.CharFrame D} {n : NChoice D} (h : C = C')
    (T : Formalism.L2.Host.TupTied D C n) (T' : Formalism.L2.Host.TupTied D C' n) (hT : HEq T T') : T.xi = T'.xi := by
  subst h; rw [eq_of_heq hT]

end GlobalTheory.WeilDatumChars
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeilChars

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.WeilDatumChars
theorem weil_chars_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (X.R.toLevCh.mu (X.tupT (D.nd.mu i))) X.R.eta (j.1 + 1)).1 (P.tp.tup (D.nd.mu i) j) ∧ Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (X.R.toLevCh.mu (X.tupT (D.nd.mu i))) X.R.eta (j.1 + 1)).2 (P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹) := by
  intro hL D P X A i j hj
  have hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) :=
    Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩
  have hlev := X.recR.base.lev
  have hx : X.R.toLevCh.xiH (X.tupT (D.nd.mu i)) = P.tp.xi (D.nd.mu i) := by
    rw [X.recR.tupXi _ hμ, xi_eq_of_heq X.cfEq X.Tp P.tp X.tpEq]
  have hxi := hlev.xi (X.tupT (D.nd.mu i))
  rw [hx] at hxi
  have hm := hlev.mu0 j
  have he := hlev.eta
  have hC : X.R.toLevCh.C = P.cf := X.cfEq
  rw [hC] at hm he
  exact ⟨GlobalTheory.Mem.TupChar.chrEq_mul hm hxi, GlobalTheory.ClassScalarValue.chrEq_mul_inv hm hxi he⟩
end GlobalTheory.WeilDatumChars
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeilCharsStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.chrTh_chrEq_tup_and_tup_mul_eta_inv : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (X.R.toLevCh.mu (X.tupT (D.nd.mu i))) X.R.eta (j.1 + 1)).1 (P.tp.tup (D.nd.mu i) j) ∧ Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (X.R.toLevCh.mu (X.tupT (D.nd.mu i))) X.R.eta (j.1 + 1)).2 (P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹) := by
  first | exact @_root_.GlobalTheory.WeilDatumChars.weil_chars_alt | exact _root_.GlobalTheory.WeilDatumChars.weil_chars_alt | (intros; apply _root_.GlobalTheory.WeilDatumChars.weil_chars_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsThetaMod

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.ThetaTri.nonempty_thetaMod_of_isCanon : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)), GlobalTheory.NJoin.IsCanon X j hj Y → Nonempty (ThetaMod D P.M i Y (P.tp.tup (D.nd.mu i) j) P.cf.eta) := by
  intro hHC hCR hL D P X A i j hj Y hc
  have hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) :=
    Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩
  have hC := X.given.core
  have hth : ∀ v, Formalism.IndefR.Datum.IsThetaFunO X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j)
      (_root_.GlobalTheory.ThetaTri.standardSchwartzFunctionMap j (X.tupT (D.nd.mu i)) v) := fun v => hC.thP.pt_theta j _ _
  have h0 : _root_.GlobalTheory.ThetaTri.standardSchwartzFunctionMap j (X.tupT (D.nd.mu i)) ∈ _root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ :=
    _root_.GlobalTheory.T.theta_lift_linear_form_alt hHC hCR hL D P X A i j hj Y hc hμ _ hth
  refine ⟨{ Ω := ↥(_root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ)
            ω := _root_.GlobalTheory.ThetaTri.omegaMapAtLocal A i j hj hc hμ
            Λ := _root_.GlobalTheory.ThetaTri.canonicalPairingMap A i j hj hc hμ
            inv := fun h g φ F F' y y' hF hy => _root_.GlobalTheory.T.theta_lift_equivariance_alt hL D P X A i j hj Y hc hμ h g φ.1 φ.2 F F' y y' hF hy
            φ₀ := ⟨_, h0⟩
            read := fun x y F hF => _root_.GlobalTheory.T.theta_lift_automorphic_form_alt hL D P X A i j hj Y hc hμ x y F hF
            loc := ?_ }⟩
  intro s μw ηw hμw hηw
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.T.chrTh_chrEq_tup_and_tup_mul_eta_inv hL D P X A i j hj
  have hv : ∀ v, _root_.GlobalTheory.ThetaTri.standardSchwartzFunctionMap j (X.tupT (D.nd.mu i)) v ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.nV) (Fin D.R.r)
      (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) → ℂ))
      (_ : IsLinAt (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) s μw ηw ι ∧
        ∀ Φ, Formalism.IndefR.Datum.IsThetaFunO X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) (ι Φ)),
      LinearMap.range ι := fun v =>
    GlobalTheory.T.thetaFunctions_spanned_heckeTwisted_standardFrame D X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) D.R.nV D.R.r (A.PV j) (X.PW j) A.hF
      (A.stdV j) (A.stdW j) _ _ (X.R.ωP j (X.tupT (D.nd.mu i))) (hC.thP.ωP j _) _ _ h1 h2 s μw ηw hμw hηw _ (hth v)
  have hlin := _root_.GlobalTheory.ThetaTri.mem_iSup_range_isLinAt_valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i)))
    (Formalism.IndefR.Datum.IsThetaFunO X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j))
    (· ∈ _root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ)
    (fun β f hf => _root_.GlobalTheory.T.theta_lift_linear_form_alt hHC hCR hL D P X A i j hj Y hc hμ _ fun v => by
      simpa [GlobalTheory.ThetaTri.single1] using Formalism.IndefR.Fock.CCR.theta_smul hf (β v))
    s μw ηw _ hv
  exact GlobalTheory.ThetaTri.mem_iSup_isLinAt_omSub _ _ _ _ _ _ _ _ _ s μw ηw h0 hlin
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsThetaModStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.nonempty_theta_mod_of_is_canon : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)), GlobalTheory.NJoin.IsCanon X j hj Y → Nonempty (ThetaMod D P.M i Y (P.tp.tup (D.nd.mu i) j) P.cf.eta) := by
  first | exact @_root_.GlobalTheory.ThetaTri.nonempty_thetaMod_of_isCanon | exact _root_.GlobalTheory.ThetaTri.nonempty_thetaMod_of_isCanon | (intros; apply _root_.GlobalTheory.ThetaTri.nonempty_thetaMod_of_isCanon <;> assumption)
end
end
end
