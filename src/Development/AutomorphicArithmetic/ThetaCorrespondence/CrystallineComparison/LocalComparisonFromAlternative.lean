module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.CFDefs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.ZD
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.CFIncl
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Comparison
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Period
public import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.Assembly
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LocalComparisonOfComparison
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.MemKerPowIff

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.CFPlain

section

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable (l : ℕ) [Fact l.Prime]


theorem zB_eq (z : ℤ_[l]) : Per.zB l z = algebraMap ℚ_[l] (Reformulated.AutPerF.Bcris l (Cmp6.OC l)) (z : ℚ_[l]) := by
  show algebraMap (Reformulated.AutPerF.Acris l (Cmp6.OC l)) (Reformulated.AutPerF.Bcris l (Cmp6.OC l))
      (algebraMap (Reformulated.AutPerF.Ainf l (Cmp6.OC l)) (Reformulated.AutPerF.Acris l (Cmp6.OC l))
        (Reformulated.AutPerF.Ainf.ofPadicInt l (Cmp6.OC l) z)) = _
  rw [Reformulated.AutPerF.Bcris.algebraMap_padicInt]
  rfl


theorem zD_eq (z : ℤ_[l]) : Per.zD l z = algebraMap ℚ_[l] (Reformulated.AutPerF.BdR l (Cmp6.OC l)) (z : ℚ_[l]) := by
  rw [← Reformulated.AutPerF.Bcris.toBdR_algebraMap_padic, ← zB_eq]
  show algebraMap (Reformulated.AutPerF.BdRPlus l (Cmp6.OC l)) (Reformulated.AutPerF.BdR l (Cmp6.OC l))
      (algebraMap (Reformulated.AutPerF.AinfInv l (Cmp6.OC l)) (Reformulated.AutPerF.BdRPlus l (Cmp6.OC l))
        (algebraMap (Reformulated.AutPerF.Ainf l (Cmp6.OC l)) (Reformulated.AutPerF.AinfInv l (Cmp6.OC l))
          (Reformulated.AutPerF.Ainf.ofPadicInt l (Cmp6.OC l) z))) =
    Reformulated.AutPerF.Bcris.toBdR l (Cmp6.OC l)
      (algebraMap (Reformulated.AutPerF.Acris l (Cmp6.OC l)) (Reformulated.AutPerF.Bcris l (Cmp6.OC l))
        (algebraMap (Reformulated.AutPerF.Ainf l (Cmp6.OC l)) (Reformulated.AutPerF.Acris l (Cmp6.OC l))
          (Reformulated.AutPerF.Ainf.ofPadicInt l (Cmp6.OC l) z)))
  rw [Reformulated.AutPerF.Bcris.toBdR_algebraMap_acris, Reformulated.AutPerF.Acris.toBdRPlus_algebraMap]
  rfl

set_option maxRecDepth 20000 in
theorem integer_to_crystalline_compat : ∀ z : ℤ_[l], equivCrystalline l (Per.zB l z) = Per6.zB l z := by
  intro z
  show Cmp6.cBc l (Per.zB l z) = _
  rw [zB_eq]
  exact (Cmp6.compat_native l).1 z
set_option maxRecDepth 20000 in
theorem integer_to_deRham_compat : ∀ z : ℤ_[l], equivDeRham l (Per.zD l z) = Per6.zD l z := by
  intro z
  show Cmp6.cD l (Per.zD l z) = _
  rw [zD_eq]
  exact (Cmp6.compat_native l).2.1 z
set_option maxRecDepth 20000 in
theorem deRham_plus_algebraMap_compat : ∀ y : Per.BdRp l, equivDeRham l (algebraMap (Per.BdRp l) (Per.BdR l) y) = algebraMap (Per6.BdRp l) (Per6.BdR l) (equivDeRhamPlus l y) := by
  intro y
  exact (Cmp6.compat_native l).2.2.1 y
set_option maxRecDepth 20000 in
theorem theta_deRham_compat : ∀ y : Per.BdRp l, Per6.θD l (equivDeRhamPlus l y) = Per.θD l y := by
  intro y
  exact (Cmp6.compat_native l).2.2.2.1 y
set_option maxRecDepth 20000 in
theorem galois_action_crystalline_compat : ∀ (g : GQ l) (b : Per.Bcris l), equivCrystalline l (Per.σB g b) = Per6.σB g (equivCrystalline l b) := by
  intro g b
  exact (Cmp6.compat_native l).2.2.2.2.1 g b
set_option maxRecDepth 20000 in
theorem galois_action_deRham_compat : ∀ (g : GQ l) (x : Per.BdR l), equivDeRham l (Per.σD g x) = Per6.σD g (equivDeRham l x) := by
  intro g x
  exact (Cmp6.compat_native l).2.2.2.2.2.1 g x
set_option maxRecDepth 20000 in
theorem frobenius_crystalline_compat : ∀ b : Per.Bcris l, equivCrystalline l (Per.φB l b) = Per6.φB l (equivCrystalline l b) := by
  intro b
  exact (Cmp6.compat_native l).2.2.2.2.2.2.1 b
set_option maxRecDepth 20000 in
theorem filtration_deRham_compat : ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔ equivDeRham l x ∈ Per6.FilD l a := by
  intro a x
  exact (Cmp6.compat_native l).2.2.2.2.2.2.2.1 a x
set_option maxRecDepth 20000 in
theorem ainf_to_crystalline_compat : ∀ a : Ainf l, equivCrystalline l (Per.aB l a) = Per6.aB l a := by
  intro a
  exact (Cmp6.compat_native l).2.2.2.2.2.2.2.2.2 a

end Formalism.BasicNotions.CmpTie
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LocTied6OfCmp

section

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

def toCompanionTheory {eB : Per.Bcris l ≃+* Per6.Bcris l} {eD : Per.BdR l ≃+* Per6.BdR l} {eP : Per.BdRp l ≃+* Per6.BdRp l}
    (h : Compat l eB eD eP) {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) : LocTied6 l P AI := by
  refine
    { eB := T.eB.trans eB
      eD := T.eD.trans eD
      zB := fun z => ?_
      zD := fun z => ?_
      om := fun x => ?_
      actB := fun g b => ?_
      actD := fun g b => ?_
      frob := fun b => ?_
      incl := ?_
      fil := fun K a x => ?_
      t := ?_
      ιA := fun a => ?_ }
  · rw [RingEquiv.trans_apply, T.zB z, h.zB z]
  · rw [RingEquiv.trans_apply, T.zD z, h.zD z]
  · obtain ⟨y, hy, hθ⟩ := T.om x
    exact ⟨eP y, by rw [RingEquiv.trans_apply, hy, h.alg y], by rw [h.θ y]; exact hθ⟩
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.actB g b, h.σB]
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.actD g b, h.σD]
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.frob b, h.φB]
  · have H := (h.incl _).1 T.incl
    convert H using 1
    ext x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.trans_apply, RingEquiv.symm_trans_apply]
  · rw [T.fil K a x, RingEquiv.trans_apply, h.fil a]
  · obtain ⟨y, hy, he⟩ := T.t
    exact ⟨eP y, (h.log AI y).1 hy, by rw [RingEquiv.trans_apply, he, h.alg y]⟩
  · rw [RingEquiv.trans_apply, T.ιA a, h.aB a]

theorem locTied6_of_cmp (hC : Cmp l) (P : LocPrime l) (AI : LocAinf l P) :
    Nonempty (LocTied l P AI) → Nonempty (LocTied6 l P AI) := by
  rintro ⟨T⟩
  obtain ⟨eB, eD, eP, h⟩ := hC
  exact ⟨toCompanionTheory h T⟩

end Formalism.BasicNotions.CmpTie
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LogarithmCompat

section

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable (l : ℕ) [Fact l.Prime]

set_option maxRecDepth 20000 in
theorem logarithm_compat : ∀ {P : LocPrime l} (AI : LocAinf l P) (y : Per.BdRp l), Per.IsLog l AI.ε y ↔ Per6.IsLog l AI.ε (equivDeRhamPlus l y) := by
  intro P AI y
  exact (LogF.isLog_iff l AI.ε y).trans (Cmp6.isLogA_iff_cP l AI.ε y)

end Formalism.BasicNotions.CmpTie
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LocalComparisonFromAlternative

section

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

theorem compat_F (l : ℕ) [Fact l.Prime] : Compat l (equivCrystalline l) (equivDeRham l) (equivDeRhamPlus l) :=
  ⟨integer_to_crystalline_compat l, integer_to_deRham_compat l, deRham_plus_algebraMap_compat l, theta_deRham_compat l, galois_action_crystalline_compat l, galois_action_deRham_compat l, frobenius_crystalline_compat l, crystalline_deRham_inclusion_compat l, filtration_deRham_compat l, fun AI y => logarithm_compat l AI y,
    ainf_to_crystalline_compat l⟩

theorem cmp_F (l : ℕ) [Fact l.Prime] : Cmp l := ⟨_, _, _, compat_F l⟩

theorem locTied6_F : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (P : Formalism.BasicNotions.LocPrime l) (AI : Formalism.BasicNotions.LocAinf l P),
    Nonempty (Formalism.BasicNotions.LocTied l P AI) → Nonempty (Formalism.BasicNotions.LocTied6 l P AI) :=
  fun l _ P AI => locTied6_of_cmp (cmp_F l) P AI

theorem local_comparison_from_alternative : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (P : Formalism.BasicNotions.LocPrime l) (AI : Formalism.BasicNotions.LocAinf l P),
    Nonempty (Formalism.BasicNotions.LocTied6 l P AI) → Nonempty (Formalism.BasicNotions.LocTied l P AI) :=
  fun l _ P AI => local_comparison_of_comparison (cmp_F l) P AI

end Formalism.BasicNotions.CmpTie
end
end
end
