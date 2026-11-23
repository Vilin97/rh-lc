module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumMatApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemMulAAOfTrace
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthAtSumLatO
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualCOfGramOne

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms GlobalTheory.StepData
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.LocMod.IntFrameStd

variable {D : D7}

theorem isSelfDualC_of_gram_one {S : HSp D} (hG : S.gram = 1) (L : Lat S)
    (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank) : IsSelfDualC S L := by
  have hm : ∀ x : Fin S.rank → D.host.E, x ∈ Examples₂.stdLat _ ↔ ∀ i, IsIntegral ℤ (x i) := fun x => by
    rw [Examples₂.stdLat, Module.Basis.mem_span_iff_repr_mem]
    exact forall_congr' fun i => ⟨fun ⟨b, hb⟩ => by rw [← show _ = x i from hb]; exact b.2,
      fun h => ⟨⟨_, h⟩, rfl⟩⟩
  have hLe : L = Examples₂.stdLat _ := by
    ext z
    rw [hL z, hm]
    rfl
  subst hLe
  refine ⟨Examples₂.stdLat_isLattice _, fun y => GlobalTheory.Ker.Inhab.selfDual_diag (fun _ => false) _ (fun i k => ?_) y⟩
  rw [hG, Matrix.one_apply]
  simp [Examples₂.sgn]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.LocMod.IntFrameStd
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosNormLineSelfDualAndTopLatticeSplits

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowShape

variable {D : D7}

theorem pLine_gram_eq_one : (pLine D).gram = 1 := by
  rw [pLine_gram]
  ext i j
  fin_cases i; fin_cases j
  simp [antiDiagonalSignGramMatrix]
  rfl

theorem mem_topL_iff (z : Fin (pLine D).rank → D.host.E) : z ∈ topL D ↔ z ∈ GlobalTheory.AdForm.intVec D (pLine D).rank := by
  simp only [topL, latPi, Submodule.mem_pi, Set.mem_univ, true_implies, FractionalIdeal.coe_one, Submodule.mem_one]
  show _ ↔ ∀ k, IsIntegral ℤ (z k)
  refine forall_congr' fun k => ⟨?_, fun h => ⟨⟨z k, h⟩, rfl⟩⟩
  rintro ⟨b, hb⟩
  rw [← hb]
  exact b.2

theorem isSelfDualC_topL : IsSelfDualC (pLine D) (topL D) :=
  GlobalTheory.LocMod.IntFrameStd.isSelfDualC_of_gram_one pLine_gram_eq_one _ mem_topL_iff

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem topLat_eq_sumLatO (G : GridData L sc) :
    G.Λ (.top D.R.m) = GlobalTheory.Core.Rk.SumBox.sumLatO (topOrth G) (G.Λ (.grid D.R.m D.R.m)) (topL D) := by
  have e : G.Λ (.top D.R.m) = G.sp.topDec.lat (G.Λ (.grid D.R.m D.R.m)) (fun _ => 1) := G.sp.topLat
  rw [e]
  ext x
  rw [GlobalTheory.Core.Rk.SumBox.mem_sumLatO]
  constructor
  · rintro ⟨y, hy, u, hu, rfl⟩
    exact ⟨y, hy, u, Submodule.mem_pi.2 fun p _ => hu p, rfl⟩
  · rintro ⟨y, hy, u, hu, rfl⟩
    exact ⟨y, hy, u, fun p => Submodule.mem_pi.1 hu p (Set.mem_univ _), rfl⟩

theorem topLat_orthAt (G : GridData L sc) (v : Pl D) :
    OrthAt (topOrth G) (G.Λ (.top D.R.m)) (G.Λ (.grid D.R.m D.R.m)) (topL D) v := by
  rw [topLat_eq_sumLatO G]
  exact GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ (topOrth G) _ _ v

theorem topL_selfDual_orthAt : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => IsSelfDualC _ (GlobalTheory.RowShape.topL D) ∧
    ∀ v, GlobalTheory.FinPl.OrthAt (topOrth ch.G) (ch.G.Λ (.top D.R.m)) (ch.G.Λ (.grid D.R.m D.R.m)) (GlobalTheory.RowShape.topL D) v :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ =>
    ⟨isSelfDualC_topL, fun v => topLat_orthAt ch.G v⟩⟩⟩

end GlobalTheory.RowShape
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosNormLineSelfDualAndTopLatticeSplitsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.posNormLine_selfDual_and_topLattice_splits : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => IsSelfDualC _ (GlobalTheory.RowShape.topL D) ∧
    ∀ v, GlobalTheory.FinPl.OrthAt (topOrth ch.G) (ch.G.Λ (.top D.R.m)) (ch.G.Λ (.grid D.R.m D.R.m)) (GlobalTheory.RowShape.topL D) v := by
  first | exact @GlobalTheory.RowShape.topL_selfDual_orthAt | exact GlobalTheory.RowShape.topL_selfDual_orthAt | (intros; apply GlobalTheory.RowShape.topL_selfDual_orthAt <;> assumption)
end
end
