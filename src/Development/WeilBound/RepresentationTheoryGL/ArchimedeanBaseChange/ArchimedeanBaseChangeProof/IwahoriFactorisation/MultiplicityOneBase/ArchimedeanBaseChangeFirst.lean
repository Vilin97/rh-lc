module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlace
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStableTwistedOrbitalUnitEqLatticeSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaUnitaryGroupEveryResidueOfLie
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchAllRanksStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaLieAlgebraUnitaryGroupOfJacquetRallisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyNrmLConj

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlaceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.exists_unramifiedQuadraticDatum_at_inertPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, ¬ IsSplitAt w → ∃ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) ∧ (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) ∧ (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) ∧ qV E w = K.q ^ 2 := by
  first | exact @GlobalTheory.InertUQ.exists_uq | exact GlobalTheory.InertUQ.exists_uq | (intros; apply GlobalTheory.InertUQ.exists_uq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStableTwistedOrbitalUnitEqLatticeSumStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.inertPlace_stableTwistedOrbital_unit_eq_latticeSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (a : ℕ) (Q : (w.adicCompletion E)[X]), Q.Monic → Q.natDegree = a → Q.Separable → IsCsr w Q → ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = Q.map e.symm.toRingHom ∧ stTw a w Q ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) = (B.stSum : ℂ) := by
  first | exact @GlobalTheory.InertTwUnit.twisted_unit_eq_stSum | exact GlobalTheory.InertTwUnit.twisted_unit_eq_stSum | (intros; apply GlobalTheory.InertTwUnit.twisted_unit_eq_stSum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaUnitaryGroupEveryResidueOfLieStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.unitLemma_unitary_group_every_residue_of_lie : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.OrbitAll.identity_of_lie | exact GlobalTheory.UnitLemma.OrbitAll.identity_of_lie | (intros; apply GlobalTheory.UnitLemma.OrbitAll.identity_of_lie <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaUnramifiedProductUnitaryGroups

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem unitLemma_identity_unconditional :
    ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 →
      (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ :=
  GlobalTheory.T.unitLemma_unitary_group_every_residue_of_lie (GlobalTheory.T.unitLemma_lieAlgebra_unitaryGroup_of_jacquetRallis GlobalTheory.T.jacquetRallisUnitMatch_all_ranks).1

end GlobalTheory.UnitLemma
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaUnramifiedProductUnitaryGroupsStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.unitLemma_unramified_product_unitary_groups : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.unitLemma_identity_unconditional | exact GlobalTheory.UnitLemma.unitLemma_identity_unconditional | (intros; apply GlobalTheory.UnitLemma.unitLemma_identity_unconditional <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriTrivialCase.IwahoriTrivialLemmas.UnitProductIndicatorTwist

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem PositivityTheory.BcbA.Ties.unit_product_indicator_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (w : Pl E), ¬ IsSplitAt w → ∀ Q₁ Q₂ : (w.adicCompletion E)[X], Q₁.Separable → Q₂.Separable → stTw2 a b w Q₁ Q₂ ((((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) : Subgroup _) : Set _).indicator 1) = stTw a w Q₁ ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) * stTw b w Q₂ ((GlobalTheory.LFun.KGL w (n := b) : Set (GLw b w)).indicator 1) :=
  GlobalTheory.BCT.UnitProd.stTw2_unit
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.MultiplicityOneBase.ArchimedeanBaseChangeFirst

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

theorem PositivityTheory.Rg.Bc.ArchbcB.B.archimedean_base_change_first : PositivityTheory.Rg.Bc.ArchbcB.B.M1 := by
  intro E _ _ _ hE w hw n a b hab Q₁ Q₂ hm₁ hm₂ hd₁ hd₂ hsep hc₁ hc₂
  obtain ⟨K, e, he1, he2, he3, he4⟩ := GlobalTheory.T.exists_unramifiedQuadraticDatum_at_inertPlace E hE w hw
  have hs₁ : Q₁.Separable := hsep.of_mul_left
  have hs₂ : Q₂.Separable := hsep.of_mul_right
  obtain ⟨B₁, hg₁, hP₁, hst₁⟩ := GlobalTheory.T.inertPlace_stableTwistedOrbital_unit_eq_latticeSum E hE w hw K e he1 he2 he3 he4 a Q₁ hm₁ hd₁ hs₁ hc₁
  obtain ⟨B₂, hg₂, hP₂, hst₂⟩ := GlobalTheory.T.inertPlace_stableTwistedOrbital_unit_eq_latticeSum E hE w hw K e he1 he2 he3 he4 b Q₂ hm₂ hd₂ hs₂ hc₂
  have hk := GlobalTheory.T.inertPlace_kappaOrbital_unit_eq_signedLatticeSum E hE w hw K e he1 he2 he3 he4 n Q₁ Q₂ hm₁ hm₂ (by omega) hsep hc₁ hc₂ B₁ B₂ hg₁ hg₂ hP₁ hP₂
  have hsepP : (B₁.P * B₂.P).Separable := by
    rw [hP₁, hP₂, ← Polynomial.map_mul]
    exact hsep.map
  have hid := GlobalTheory.T.unitLemma_unramified_product_unitary_groups K B₁ B₂ hg₁ hg₂ hsepP
  unfold GlobalTheory.UnitLemma.InvAlg.Identity at hid
  have hv : GlobalTheory.UnitLemma.val K.O (resultant B₁.P B₂.P) = ordL (resultant Q₁ Q₂) := by
    rw [he3, hP₁, hP₂]
    have h1 : (Q₁.map e.symm.toRingHom).natDegree = Q₁.natDegree :=
      Polynomial.natDegree_map_eq_of_injective e.symm.injective _
    have h2 : (Q₂.map e.symm.toRingHom).natDegree = Q₂.natDegree :=
      Polynomial.natDegree_map_eq_of_injective e.symm.injective _
    rw [h1, h2, Polynomial.resultant_map_map]
    simp
  rw [PositivityTheory.BcbA.Ties.unit_product_indicator_twist E hE a b w hw Q₁ Q₂ hs₁ hs₂, hst₁, hst₂, hk, ← Rat.cast_mul, ← hid, Rat.cast_mul]
  congr 1
  rw [hv]
  unfold delta absHalf
  rw [if_neg hw, he4]
  set v := ordL (resultant Q₁ Q₂)
  have hq : Real.sqrt (((K.q ^ 2 : ℕ) : ℝ) ^ (-v)) = (K.q : ℝ) ^ (-v) := by
    rw [Nat.cast_pow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast]
    exact Real.sqrt_sq (zpow_nonneg (Nat.cast_nonneg _) _)
  rw [hq]
  push_cast
  rw [neg_eq_neg_one_mul, mul_zpow, ← _root_.inv_zpow', inv_neg_one]

theorem PositivityTheory.Rg.Bc.ArchbcB.B.m1 : PositivityTheory.Rg.Bc.ArchbcB.B.M1 :=
  PositivityTheory.Rg.Bc.ArchbcB.B.archimedean_base_change_first
end
end
