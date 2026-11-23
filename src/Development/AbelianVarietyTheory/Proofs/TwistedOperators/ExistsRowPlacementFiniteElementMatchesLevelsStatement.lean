module

public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteElementConjRowLevelCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsCompareByLevelMatchingEvaluationStatement
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateMaximalCompactMemParahoricLevelStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionConjugatedUnitaryElementEqOneIff
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElementStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.goodAt_reduction_conjugated_unitary_element : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, GoodAt X k (cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k)))) := by
  first | exact @GlobalTheory.RedFrame.goodAt_kap_red | exact GlobalTheory.RedFrame.goodAt_kap_red | (intros; apply GlobalTheory.RedFrame.goodAt_kap_red <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionConjugatedUnitaryElementEqOneIffStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.reduction_conjugated_unitary_element_eq_one_iff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, (cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) = 1 ↔ k ∈ X.B.I.Kg X.B.g) := by
  first | exact @GlobalTheory.KapRed.red_kap_eq_one_iff | exact GlobalTheory.KapRed.red_kap_eq_one_iff | (intros; apply GlobalTheory.KapRed.red_kap_eq_one_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightTranslateCompactLiftActsByReduction

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowActLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levelCharacter_rowDatum_eq_one_of_reduction_one (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (x : GL (Fin (Yc D 0).rank) (EAf D))
    (hx : rTup (R.βY 0) (R.dat0 P) x = 1) : levFn (R.βY 0) (R.dat0 P) x = 1 := by
  unfold levFn
  rw [hx, blockDiagonalExtendByOnePrimeField_one]
  simp [Formalism.IndefR.Links.LevCh.dat0, datY]

theorem levelCharacter_flag_rowDatum_eq_one (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (x : GL (Fin (Yc D 0).rank) (EAf D)) :
    levFn (R.βY 0) (flagL (R.dat0 P)) x = 1 := by
  have h2 : ext1 (flagL (R.dat0 P)).P.H (flagL (R.dat0 P)).P.chi (rTup (R.βY 0) (flagL (R.dat0 P)) x) = 1 :=
    subgroupCharExtension_one_apply _ _
  unfold levFn
  rw [h2]
  simp [flagL, withP, Formalism.IndefR.Links.LevCh.dat0, datY]

theorem mem_lev_of_flag1 (R : RealDat D A Ks) (P P' : LevelP R.Pg D.R.r ℂ) {κ : GA D (Yc D 0)}
    (hκ : κ ∈ levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 P'))) :
    κ ∈ levS (Yc D 0) (R.βY 0) (R.dat0 P) ∧
      levChi (Yc D 0) (R.βY 0) (R.dat0 P) κ = levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 P')) κ := by
  obtain ⟨h1, h2, h3⟩ := hκ
  have h3' : rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = 1 := Subgroup.mem_bot.1 h3
  refine ⟨⟨h1, h2, ?_⟩, ?_⟩
  · show rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) ∈ (R.dat0 P).P.H
    rw [h3']; exact Subgroup.one_mem _
  · unfold levChi
    rw [levelCharacter_rowDatum_eq_one_of_reduction_one R P _ h3', levFn_flag1, levelCharacter_flag_rowDatum_eq_one]

theorem hasType_flag1_of_mem (R : RealDat D A Ks) (P P' : LevelP R.Pg D.R.r ℂ) {T : MMap (R.MY 0)}
    (hT : T ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 P)) (levChi (Yc D 0) (R.βY 0) (R.dat0 P)))
    (v : (R.MY 0).Vec) : HasType (Yc D 0) (R.βY 0) (flag1L (R.dat0 P')) (T v) := by
  induction hT using Submodule.span_induction with
  | mem S hS =>
    intro κ hκ g
    obtain ⟨hm, hc⟩ := mem_lev_of_flag1 R P P' hκ
    rw [hS.lev v κ hm g, hc]
  | zero =>
    intro κ _ g
    simp
  | add S S' _ _ hS hS' =>
    intro κ hκ g
    simp only [MultilinearMap.add_apply, Pi.add_apply]
    rw [hS κ hκ g, hS' κ hκ g, mul_add]
  | smul c S _ hS =>
    intro κ hκ g
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [hS κ hκ g, mul_left_comm]

theorem act_kap : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, ∀ T ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), ∀ (v : (MP R).Vec) (g : GA D (Yc D 0)), (T : MMap (MP R)) v (g * kap X h t k) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) ((T : MMap (MP R)) v) g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod cG t hιE hpin hE0 ht hConj hFrame k hk T' hT v g
  have hl := GlobalTheory.T.conjugate_maximalCompact_mem_parahoricLevel R F X h hLev hGrp hMod cG t hιE hpin hE0 ht hConj hFrame k hk
  have hlift : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv)
      (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) (kap X h t k) := ⟨hl.1, hl.2, rfl⟩
  have hType := hasType_flag1_of_mem R (R.levR F true) R.triv hT v
  have hs := level_action_spec hType ⟨_, hlift⟩ _ hlift g
  have hc : levChi (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) (kap X h t k) = 1 := by
    unfold levChi; rw [levelCharacter_flag_rowDatum_eq_one]; rfl
  show _ = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) _ _ g
  rw [hs, hc, inv_one, one_mul]

end GlobalTheory.RowActLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightTranslateCompactLiftActsByReductionStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rightTranslate_compactLift_acts_by_reduction : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, ∀ T ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), ∀ (v : (MP R).Vec) (g : GA D (Yc D 0)), (T : MMap (MP R)) v (g * kap X h t k) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) ((T : MMap (MP R)) v) g := by
  first | exact @GlobalTheory.RowActLift.act_kap | exact GlobalTheory.RowActLift.act_kap | (intros; apply GlobalTheory.RowActLift.act_kap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroupStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.surjective_reduction_onto_finiteLevelGroup : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ γ : G0g D.nd, ∃ k ∈ X.B.I.Kset, cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) = γ := by
  first | exact @GlobalTheory.SeeMatchOnto.onto | exact GlobalTheory.SeeMatchOnto.onto | (intros; apply GlobalTheory.SeeMatchOnto.onto <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowLevelMatchAtOfLevelConjugation

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem conj_mem_and_char_eq_of_levelConjugation {H : Type} [Group H] (t s : H) (J J' : Set H) (χ χ' : H → ℂ)
    (hc : ∀ k, (k ∈ J ↔ t⁻¹⁻¹ * k * t⁻¹ ∈ J') ∧ (k ∈ J → χ' (t⁻¹⁻¹ * k * t⁻¹) = χ k)) (hs : s ∈ J') :
    t⁻¹ * s * t ∈ J ∧ χ (t⁻¹ * s * t) = χ' s := by
  have e : t⁻¹⁻¹ * (t⁻¹ * s * t) * t⁻¹ = s := by group
  have h := hc (t⁻¹ * s * t)
  rw [e] at h
  exact ⟨h.1.2 hs, (h.2 (h.1.2 hs)).symm⟩

theorem conj_mul_eq_mul_conj_group {H : Type} [Group H] (t a b : H) : t⁻¹ * (a * b) * t = (t⁻¹ * a * t) * (t⁻¹ * b * t) := by
  group

theorem rowLevelMatchAt_of_conjLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → RowLevelMatchAt R F X h t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod cG t hιE hPin hE0 ht hConj hFrame
  obtain ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ := hPin
  refine ⟨(R.eG.trans cG).symm, fun k => cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))), ?_, ?_, ?_⟩
  · intro k hk
    have e2 : (iotaX X h).toMulEquiv ((iotaX X h).symm (1, k)) = (1, k) :=
      (iotaX X h).toMulEquiv.apply_symm_apply (1, k)
    have hs : (iotaX X h).symm (1, k) ∈ (iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2} := by
      rw [Set.mem_preimage, e2]; exact ⟨rfl, hk⟩
    have hA := conj_mem_and_char_eq_of_levelConjugation (H := GA D (Yc D 0)) t ((iotaX X h).symm (1, k)) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) (fun k' => hConj k') hs
    refine ⟨hA.1, hA.2.trans ?_⟩
    show star (X.chi2 ((iotaX X h).toMulEquiv ((iotaX X h).symm (1, k))).2) = _
    rw [e2]
  · obtain hl := GlobalTheory.T.conjugate_maximalCompact_mem_parahoricLevel R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame
    refine ⟨⟨GlobalTheory.T.goodAt_reduction_conjugated_unitary_element R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame, ?_,
      GlobalTheory.T.surjective_reduction_onto_finiteLevelGroup R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame,
      GlobalTheory.T.reduction_conjugated_unitary_element_eq_one_iff R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame⟩, ?_⟩
    · intro k hk k' hk'
      have e1 : (iotaX X h).symm (1, k * k') = (iotaX X h).symm (1, k) * (iotaX X h).symm (1, k') := by
        rw [← map_mul, Prod.mk_mul_mk, one_mul]
      have e : kap X h t (k * k') = kap X h t k * kap X h t k' := by
        unfold kap; rw [e1]; exact conj_mul_eq_mul_conj_group (H := GA D (Yc D 0)) t _ _
      show cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t (k * k')))) = cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) * cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k')))
      rw [e, map_mul, Formalism.L2.DIV.rTup_mul (hl k hk).2 (hl k' hk').2]
      exact map_mul cG _ _
    · intro k hk T hT v g
      rw [GlobalTheory.T.rightTranslate_compactLift_acts_by_reduction R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame k hk T hT v g]
      have e3 : R.eG ((R.eG.trans cG).symm (cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))))) = rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k)) := by
        rw [MulEquiv.symm_trans_apply]
        exact (congrArg (fun y => R.eG (R.eG.symm y)) (cG.symm_apply_apply _)).trans (R.eG.apply_symm_apply _)
      rw [e3]
  · intro γ
    unfold RealDat.eC
    rw [hE0 γ, hcoef, MulEquiv.apply_symm_apply]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowLevelMatchAtOfLevelConjugationStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowLevelMatchAt_of_levelConjugation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → RowLevelMatchAt R F X h t := by
  first | exact @GlobalTheory.rowLevelMatchAt_of_conjLevel | exact GlobalTheory.rowLevelMatchAt_of_conjLevel | (intros; apply GlobalTheory.rowLevelMatchAt_of_conjLevel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRowPlacementFiniteElementMatchesLevels

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem rowPlacement_iota_eq {D : D7} {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.IndefR.RationalEmbedding.inst D)
    (ι : GA D (Yc D 0) ≃* I.GA) (hι : HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv) :
    ι = ((Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm)).toMulEquiv := by
  subst h
  have := eq_of_heq hι
  subst this
  rfl

theorem rowPlacement_exists : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp X) (h : X.B.I = Formalism.IndefR.RationalEmbedding.inst D) (ι : GA D (Yc D 0) ≃* X.B.I.GA) (tS : GA D (Yc D 0)) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → IdempotentRealFixed D → HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → tS ∈ GfC (Yc D 0) → ((∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h t) → ConjLevel (tS)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h tS) → (∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h t) ∧ ∃ c' : ℝ, EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd ι tS c' := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X Gd h ι tS cG hlev hgrp hmod hhost hE0 hι hιE hpin htS hmove
  have hιeq : ι = (iotaX X h).toMulEquiv := rowPlacement_iota_eq h ι hι
  subst hιeq
  have hfirst : ∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)))
      (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)))
      ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2})
      (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) ∧ RowLevelMatchAt R F X h t := by
    obtain ⟨t, ht, hconj, hframe⟩ := GlobalTheory.T.exists_finite_element_conj_rowLevel_character R F X h hlev hgrp hmod
    exact ⟨t, ht, hconj, GlobalTheory.T.rowLevelMatchAt_of_levelConjugation R F X h hlev hgrp hmod cG t hιE hpin hE0 ht hconj hframe⟩
  obtain ⟨hconjS, hmatchS⟩ := hmove hfirst
  exact ⟨hfirst, GlobalTheory.T.goodRows_compare_by_levelMatching_evaluation hDS R F X h hlev hgrp hmod hhost hιE Gd tS htS hconjS hmatchS⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRowPlacementFiniteElementMatchesLevelsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rowPlacement_finiteElement_matches_levels : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp X) (h : X.B.I = Formalism.IndefR.RationalEmbedding.inst D) (ι : GA D (Yc D 0) ≃* X.B.I.GA) (tS : GA D (Yc D 0)) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → IdempotentRealFixed D → HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → tS ∈ GfC (Yc D 0) → ((∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h t) → ConjLevel (tS)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h tS) → (∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h t) ∧ ∃ c' : ℝ, EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd ι tS c' := by
  first | exact @GlobalTheory.rowPlacement_exists | exact GlobalTheory.rowPlacement_exists | (intros; apply GlobalTheory.rowPlacement_exists <;> assumption)
end
end
