module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedP
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemGluedIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierOneSubNormCongrZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCoprimeOfCongrMulOneSubModLevel
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBesUnscaledDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsVTOver
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentCompletionIffCharacterDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentPowCompletionTrivialAtSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineOfGlued
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulVecSingleAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MemLineIff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChartZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselAwayPlaces

section

@[expose] public section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix

noncomputable section

namespace GlobalTheory.MiTop.LineAtT

variable {D : D7}

def UnitScal (v : GlobalTheory.FinPl.Pl D) (t : D.host.E) : Prop :=
  ∀ a ∈ idAt D (· = v), incA D t * a ∈ intAt D (· = v) ↔ a ∈ intAt D (· = v)

theorem UnitScal.mul {v : GlobalTheory.FinPl.Pl D} {s t : D.host.E} (hs : UnitScal v s) (ht : UnitScal v t) : UnitScal v (s * t) := fun a ha => by
  rw [RingHom.map_mul, mul_assoc, hs _ (Ideal.mul_mem_left _ _ ha), ht a ha]

theorem UnitScal.cancel {v : GlobalTheory.FinPl.Pl D} {s t : D.host.E} (hst : UnitScal v (s * t)) (ht : UnitScal v t) : UnitScal v s := fun a ha => by
  rw [← hst a ha, ← ht _ (Ideal.mul_mem_left _ _ ha), RingHom.map_mul, ← mul_assoc, mul_comm (incA D t)]

theorem unitAt_one (v : GlobalTheory.FinPl.Pl D) : UnitScal v 1 := fun a _ => by rw [RingHom.map_one, one_mul]

theorem UnitScal.pow {v : GlobalTheory.FinPl.Pl D} {s : D.host.E} (hs : UnitScal v s) (n : ℕ) : UnitScal v (s ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact unitAt_one v
  | succ n ih => rw [pow_succ]; exact ih.mul hs

theorem UnitScal.neg {v : GlobalTheory.FinPl.Pl D} {s : D.host.E} (hs : UnitScal v s) : UnitScal v (-s) := fun a ha => by
  rw [← hs a ha, RingHom.map_neg, neg_mul]
  exact ⟨fun h => neg_neg (incA D s * a) ▸ GlobalTheory.IdVGen.intAt_neg' h, GlobalTheory.IdVGen.intAt_neg'⟩

theorem unitAt_of {v : GlobalTheory.FinPl.Pl D} {s : D.host.E} (hs : s ≠ 0)
    (h : ∀ a ∈ intAt D (· = v), incA D s * a ∈ intAt D (· = v) ∧ incA D s⁻¹ * a ∈ intAt D (· = v)) : UnitScal v s := fun a _ => by
  refine ⟨fun h1 => ?_, fun h1 => (h a h1).1⟩
  have := (h _ h1).2
  rwa [← mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hs, RingHom.map_one, one_mul] at this

theorem unitAt_nat {v : GlobalTheory.FinPl.Pl D} {N : ℕ} (hv : (N : 𝓞 D.host.F) ∉ v.asIdeal) : UnitScal v (N : D.host.E) := by
  have hN : (N : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    rintro rfl
    exact hv (by simp)
  refine unitAt_of hN fun a ha => ⟨GlobalTheory.SeeSaw.StdOff.incA_mul_mem_intAt hv ?_ a ha, GlobalTheory.SeeSaw.StdOff.incA_mul_mem_intAt hv ?_ a ha⟩
  · rw [← Nat.cast_mul]; exact isIntegral_natCast _
  · rw [mul_inv_cancel₀ hN]; exact isIntegral_one

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unitAt_val (p : SplitPt D k) {t : D.host.E} (h1 : valuation k (p.pr (incA D t)) = 1)
    (h2 : valuation k (p.pr (incA D (star t))) = 1) : UnitScal p.v t := fun a ha => by
  rw [GluedLine.mem_intAt_iff p (Ideal.mul_mem_left _ _ ha), GluedLine.mem_intAt_iff p ha, RingHom.map_mul, RingHom.map_mul (cA D),
    RingHom.map_mul, GlobalTheory.FinPl.FrameLat.cA_incA]
  simp only [Valuation.mem_integer_iff, map_mul, h1, h2, one_mul]

theorem psiE_triv {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (p : SplitPt D k) (hU : p.UnitAA) {s : AE D}
    (hs : s ∈ idAt D (· = p.v)) : (∀ o ∈ intAt D (· = p.v), psiE ψ (s * o) = 1) ↔ s ∈ intAt D (· = p.v) := by
  rw [← GlobalTheory.SeeSaw.DiffDual.idV_dI_iff D ψ hψ p.v s hs, ← (GlobalTheory.Core.Mi.LatMatch.idV_dI_pow_unit D k p hU 1 s).1, pow_one]

theorem psiE_ne {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (p : SplitPt D k) (hU : p.UnitAA)
    (q : GlobalTheory.LatPair.Unif k) : ∃ s, psiE ψ s ≠ 1 := by
  by_contra hc
  push_neg at hc
  have h := (psiE_triv hψ p hU (GlobalTheory.FinPl.FrameLat.sec_mem_idAt p q.inv)).1 fun o _ => hc _
  have h1 := GluedLine.pr_mem_of_intAt p h.2
  rw [p.pr_sec] at h1
  have h2 : IsUnit (q.1 : 𝒪[k]) := IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ q.ne_zero))
  exact q.mem_max h2

theorem ne_zero_of_line {L : TH.HSp D} {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) : ζ ≠ 0 := by
  rintro rfl
  exact h.2 (by simp)

theorem vecB_ne {S A L : TH.HSp D} (o : OrthDec S A L) {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) : vecB o ζ ≠ 0 := fun e => by
  apply h.2
  have e' : o.iB *ᵥ ζ = 0 := e
  rw [← o.isoB, ← Matrix.mulVec_mulVec, e', Matrix.mulVec_zero, dotProduct_zero]

theorem wittDecomposition_inclusion_mulVec_rationalVector {S S₀ : TH.HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) :
    d.j0 *ᵥ ratV z = ratV (d.i₀ *ᵥ z) := funext fun r => (RingHom.map_mulVec (incA D) d.i₀ z r).symm

theorem first_scale (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word)
    {ψ : AddChar (AF D.host.F) ℂ} (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀) (hE : IdE X)
    (hψ : IsStdChar D ψ (-1)) (hne : ∃ s, psiE ψ s ≠ 1) (hr : 0 < D.R.rS) (B : SBes X h u ψ (D.sp.X 0)) {μ : D.host.E}
    (hμ : μ ≠ 0) (hz : ∀ r, (B.d.i₀ *ᵥ vecB B.o B.ζ) r = μ * X.ιE (X.zR u (Fin.cast (rank_eq X h) r))) :
    ∃ lam : D.host.E, (lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)) ∧ ∀ r, B.d.jX r ⟨0, hr⟩ =
      incA D (μ * lam ^ D.R.rS) * incA D (X.ιE (X.eR ⟨0, hr⟩ (Fin.cast (rank_eq X h) r))) := by
  obtain ⟨lam, hl, hB⟩ := exists_sBes_scaled_dual D X h u ψ F₀ tr hE hψ
  obtain ⟨B', -, -, hz', he, -⟩ := hB μ B.vA hμ
  refine ⟨lam, hl, fun r => ?_⟩
  rw [FirstVec.first_eq (d' := B'.d) (z := vecB B.o B.ζ) (z' := vecB B'.o B'.ζ) hne (vecB_ne _ B.line) (vecB_ne _ B'.line)
    (by rw [wittDecomposition_inclusion_mulVec_rationalVector, wittDecomposition_inclusion_mulVec_rationalVector, funext hz, funext hz']) (Subgroup.ext fun n => (B.tieN n).trans (B'.tieN n).symm)
    (fun n hn => star_injective ((B.tieψ n hn).trans (B'.tieψ n ((B'.tieN n).2 ((B.tieN n).1 hn))).symm)) hr r,
    ← RingHom.map_mul]
  exact congrArg (incA D) (he r ⟨0, hr⟩)

end GlobalTheory.MiTop.LineAtT


end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedPrim

section

@[expose] public section



section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod
namespace GlobalTheory.MiTop
section Prim
open GlobalTheory.FinPl
variable {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
variable {v : VCom c} {o : TDat c k ι}
end Prim
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
def PlacedPrimitiveConditions : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type)
    (v : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg),
    f.c.Is ∧ v.Is ∧ _root_.GlobalTheory.Fam.CommutingVectorTie f v ∧ ShapeOff v o ∧ GPin G ∧ _root_.GlobalTheory.Fam.LocalGroupReading f G pl ∧ _root_.GlobalTheory.MiTop.LocalBottomCompatibility f B v o G ∧ TopPrim v o
variable {f B}
end GlobalTheory.MiTop
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedPrimIff

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix ValuativeRel IsLocalRing
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc GlobalTheory.IwaPlace NumberField Filter
open GlobalTheory.GoodPos
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.MiTop.Scale.Glue
open GlobalTheory.FinPl.FrameLat
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.MiTop.Scale.Glue
namespace GlobalTheory.MiTop.Scale
variable {D : D7}
section Com
variable {c : Comm D} {v : VCom c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} {o : TDat c k ι}
end Com
end GlobalTheory.MiTop.Scale
namespace GlobalTheory.MiTop
open Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links GlobalTheory.MiS GlobalTheory.Core.Mi GlobalTheory.Fam GlobalTheory.MiTop.Scale
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} {f : _root_.GlobalTheory.Fam.FamilyCharacter W u}
  {B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)}
theorem placedPrim_iff_placedP : _root_.GlobalTheory.MiTop.PlacedPrimitiveConditions f B ↔ _root_.GlobalTheory.MiTop.PlacedConditions f B := by
  unfold _root_.GlobalTheory.MiTop.PlacedPrimitiveConditions _root_.GlobalTheory.MiTop.PlacedConditions
  simp only [topPrim_iff]
theorem rank_X_succ_pos (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : 0 < (f.c.X (j + 1)).rank := by
  refine lt_of_lt_of_eq ?_ (Formalism.L2.Forms.rankN D (j + 1) (by omega)).symm
  unfold Ranks.N
  positivity
end GlobalTheory.MiTop
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LineIdealAtOwnPrime

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
noncomputable section
namespace GlobalTheory.MiTop.LineAtT
variable {D : D7}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.MiTop.LineAtT

open GlobalTheory.MiTop.LineAtT GlobalTheory.MiTop.Scale GlobalTheory.GoodPos GlobalTheory.IwaPlace GlobalTheory.FinPlLoc in
theorem GlobalTheory.MiTop.line_ideal_at_own_prime_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (hr : 1 ≤ D.R.rS) u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → ∀ c ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = v) ↔ c ∈ GlobalTheory.FinPl.intAt D (· = v)) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u f B hP v hv hTv c hc
  obtain ⟨k, _, _, _, _, ι, v', o, n, G, pl, hcI, hvI, hVT, hSh, hGP, hGR, hBT, hpr⟩ := _root_.GlobalTheory.MiTop.placedPrim_iff_placedP.2 hP
  have h0 : 0 + 2 * D.R.rS + 2 = D.R.m := by
    show 0 + 2 * (D.R.m / 2 - 1) + 2 = D.R.m
    obtain ⟨k, hk⟩ := D.R.m_even
    have := D.R.two_le_m
    omega
  obtain ⟨i, rfl⟩ := (hSh.pre.tP v).1 ((hVT.tP v).2 hTv)
  have hU := (hSh.pre.char i).2
  have hψ : IsStdChar D W.Q.Rl.ψ (-1) := hcI.std
  have hm := GlobalTheory.StMoves.moves_inv (hVT.moves 0 (by omega) (· = (o.p i).v) fun p hp hg => by
    obtain ⟨PP, h1, h2⟩ := (hVT.gP p).1 hg
    exact hv PP h1 (h2.symm.trans hp))
  refine (hm _ fun r => Ideal.mul_mem_right _ _ hc).symm.trans ?_
  obtain ⟨μ, lam, hml, hz, hτ⟩ := hBT.norm
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have hμ : μ ≠ 0 := left_ne_zero_of_mul (by rw [hml]; exact neg_ne_zero.2 (pow_ne_zero _ hξ))
  have hj : 2 * D.R.rS + 2 * 0 + 2 = D.R.m := by omega
  obtain ⟨lam', hl', hval⟩ := hSh.pre.lam _ hj
  have hll : lam = lam' := smul_left_injective _ (ne_zero_of_line (f.c.bes _ 0 hj).line) ((hτ _ hj).symm.trans hl')
  subst hll
  have uμ : UnitScal (o.p i).v μ := UnitScal.cancel (hml ▸ ((unitAt_of hξ hU.1).pow _).neg) (unitAt_val _ (hval i).1 (hval i).2)
  have hcop : Nat.Coprime (D.mem u).A.T W.S.X.B.g := by
    obtain ⟨M, h1, h2⟩ := GlobalTheory.TorusCong.one_sub_T_zmod D W.S.X u
    exact GlobalTheory.TorusCop.natCoprime_of_zmod_mul_one_sub _ _ _ M (Nat.pos_of_ne_zero (Formalism.L2.SG.Pf.modulus_g_ne_zero W.S.X)) h1 h2
  have ug : UnitScal (o.p i).v (W.S.X.B.g : D.host.E) := unitAt_nat fun hg => by
    obtain ⟨a, b, hab⟩ := (Nat.Coprime.cast (R := 𝓞 D.host.F) hcop)
    exact (o.p i).v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ hTv) (Ideal.mul_mem_left _ _ hg)))
  obtain ⟨l, hl, he⟩ := first_scale W.S.X W.Q.instEq u _ (W.S.tr u) hW.bot.idE hψ (psiE_ne hψ _ hU o.q) hr B hμ hz
  have ul : UnitScal (o.p i).v l := by
    rcases hl with e | e <;> rw [e]
    exacts [ug, ug.neg]
  have hl0 : l ≠ 0 := by
    have hg : ((W.S.X.B.g : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.L2.SG.Pf.modulus_g_ne_zero W.S.X)
    rcases hl with e | e <;> rw [e]
    exacts [hg, neg_ne_zero.2 hg]
  have ht0 : μ * l ^ D.R.rS ≠ 0 := mul_ne_zero hμ (pow_ne_zero _ hl0)
  have ut := uμ.mul (ul.pow D.R.rS)
  have hQ : ∀ Bl : BesLev D D.R.rS, Bl = f.c.B 0 D.R.rS h0 → ∀ LV : GlobalTheory.FinPl.Lat Bl.V, HEq LV (v'.N 0) → ∀ j,
      ∀ a ∈ idAt D (· = (o.p i).v), colMul Bl.d.jX j a ∈ latV Bl.V LV (· = (o.p i).v) ↔ a ∈ intAt D (· = (o.p i).v) := by
    rintro _ rfl LV hLV
    obtain rfl := eq_of_heq hLV
    intro j a ha
    have hlam : lam ≠ 0 := right_ne_zero_of_mul (by rw [hml]; exact neg_ne_zero.2 (pow_ne_zero _ hξ))
    obtain ⟨α, hα⟩ := GlobalTheory.IdeleAA.exists_idele_AA D f.c.ψ hcI.std
    have u1 := isU_alpha hU hSh.pre.line (hα _).1
    have u2 : IsU (o.p i).v ((xiU D * cU α : (AE D)ˣ) : AE D) := (isU_xi hU).mul u1.conj
    have u3 : IsU (o.p i).v ((α * (xiU D * cU α)⁻¹ : (AE D)ˣ) : AE D) := u1.mul (u2.inv (Units.mul_inv _))
    have u4 : IsU (o.p i).v ((xiU D * α * cU α : (AE D)ˣ) : AE D) := ((isU_xi hU).mul u1).mul u1.conj
    have u5 : IsU (o.p i).v (((xiU D * α * cU α) ^ (D.R.rS - j.1) *
        ((α * (xiU D * cU α)⁻¹) ^ (D.R.rS + 1) * inU lam hlam) : (AE D)ˣ) : AE D) := by
      rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
      exact (u4.pow _).mul ((u3.pow _).mul (isU_of_val _ (hval i).1 (hval i).2))
    refine (iso_line_all hcI hSh hpr (_root_.GlobalTheory.MiTop.rank_X_succ_pos f) hlam hτ (hα _).1 (fun s hs => ?_) _ 0 h0 j a ha).trans
      (u5.inv (Units.mul_inv _) a ha).symm
    rw [(hα _).2 s hs, mul_inv, mul_inv, Units.val_mul, Units.val_mul, cU_inv, xiU, inU_inv]
  generalize μ * l ^ D.R.rS = t at he ht0 ut
  have hc' : incA D t⁻¹ * c ∈ idAt D (· = (o.p i).v) := Ideal.mul_mem_left _ _ hc
  have e1 : incA D t * (incA D t⁻¹ * c) = c := by
    rw [← mul_assoc, ← RingHom.map_mul, mul_inv_cancel₀ ht0, RingHom.map_one, one_mul]
  have h1 := (hQ B.lev (hBT.lev h0) (v'.N 0) HEq.rfl ⟨0, hr⟩ _ hc').trans (ut _ hc').symm
  rw [e1] at h1
  refine Iff.trans (iff_of_eq (congrArg (· ∈ latV (D.sp.Y 0) (v'.N 0) (· = (o.p i).v)) (funext fun r => ?_))) h1
  refine Eq.trans ?_ (congrArg (incA D t⁻¹ * c * ·) (he r)).symm
  exact (congrArg (· * _) e1.symm).trans (by rw [mul_comm (incA D t), mul_assoc])
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedBesselAwayPlacesAltBis

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.placed_bessel_away_places_alt_bis : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (hr : 1 ≤ D.R.rS) u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → ∀ c ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = v) ↔ c ∈ GlobalTheory.FinPl.intAt D (· = v)) := by
  first | exact @_root_.GlobalTheory.MiTop.line_ideal_at_own_prime_alt | exact _root_.GlobalTheory.MiTop.line_ideal_at_own_prime_alt | (intros; apply _root_.GlobalTheory.MiTop.line_ideal_at_own_prime_alt <;> assumption)
end
end
end
