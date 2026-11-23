module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.PhiPG0
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeibnizOrderOfExactSequences
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiGpCommutationHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgCommutationHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgRankZeroHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PsiGpCommutationHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueSequenceHolds
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.HighestDerivativeProducts.IsSmoothCharDpowM

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeibnizOrderOfExactSequencesStatement

section

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

theorem _root_.GlobalTheory.T.leibniz_order_of_exact_sequences : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ResSeq k → PsiGP k → PhiGP k → PsiPG k → PhiPG k → PhiPG0 k → LeibnizOrd k := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.Main.leibnizOrd_of_parts | exact GlobalTheory.CompanionTheory.LeibOrd.Main.leibnizOrd_of_parts | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.Main.leibnizOrd_of_parts <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgRankZeroHoldsStatement

section

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

theorem _root_.GlobalTheory.T.phi_pg_rank_zero_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PhiPG0 k := by
  first | exact @GlobalTheory.CompanionTheory.MirLevi.phiPG0_holds | exact GlobalTheory.CompanionTheory.MirLevi.phiPG0_holds | (intros; apply GlobalTheory.CompanionTheory.MirLevi.phiPG0_holds <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PsiGpCommutationHoldsStatement

section

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

theorem _root_.GlobalTheory.T.psi_gp_commutation_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PsiGP k := by
  first | exact @GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP | exact GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP | (intros; apply GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueSequenceHoldsStatement

section

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

theorem _root_.GlobalTheory.T.residue_sequence_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ResSeq k := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.resSeq | exact GlobalTheory.CompanionTheory.BZRes.resSeq | (intros; apply GlobalTheory.CompanionTheory.BZRes.resSeq <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.HighestDerivativeProducts.HighestDerivProd

section

@[expose] public section

namespace GlobalTheory.RgGu.Leib.Hand

theorem leibnizOrd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    LeibnizOrd k :=
  GlobalTheory.T.leibniz_order_of_exact_sequences k (GlobalTheory.T.residue_sequence_holds k) (GlobalTheory.T.psi_gp_commutation_holds k) (GlobalTheory.T.phi_gp_commutation_holds k) (GlobalTheory.CompanionTheory.BZPsiPG.Hand.psiPG k) (GlobalTheory.CompanionTheory.BZPhiPG.phiPG k)
    (GlobalTheory.T.phi_pg_rank_zero_holds k)

end GlobalTheory.RgGu.Leib.Hand
end
end
