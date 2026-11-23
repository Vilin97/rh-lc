module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.RowProps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.CompatTOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.PlainRec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.ConjDecSurj
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.SumAEOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BciNarrowSwap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DualOfWeights
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EqOneOfUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PseudoLocalLanglandsDescent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TGalAEOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSameOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSplitSat
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.OnePart

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.V.Af.Gu

theorem UpperTheory.V.Z.Desc.W.onePart :
    UpperTheory.V.Z.Desc.W.OnePart := by
  intro hJS hTw E _ _ _ n c hn a d P π had hw
  obtain ⟨s, -⟩ := hJS E (Σ i : Fin c, Fin (d i)) Unit (fun x => a x.1) (fun _ => n)
    (fun x => CG.mk ((P x.1).twist
      (GlobalTheory.HeckeGal.Model.absPow E (-(((x.2 : ℕ) : ℝ) - ((d x.1 : ℝ) - 1) / 2)))))
    (fun _ => CG.mk π) (fun x => (had x.1).1) (fun _ => hn)
    (hw.mono fun w ⟨S, h1, h2⟩ => ⟨_, fun _ => satTot w d S, fun x => hTw E _ _ _ w _ (h1 x.1), fun _ => h2, by
      simp only [neg_neg, Finset.univ_unique, Finset.sum_singleton, satTot]
      exact Fintype.sum_sigma _⟩)
  have hc : ∑ i, d i = 1 := by simpa using Fintype.card_congr s
  have hle : c ≤ ∑ i, d i := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => (had i).2)
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  refine ⟨by omega, fun i => le_antisymm ?_ (had i).2⟩
  rw [← hc]
  exact Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.SatTw

section

@[expose] public section

theorem UpperTheory.V.Z.Desc.W.satTw :
    UpperTheory.V.Z.Desc.W.SatTw := by
  intro E _ _ _ a P s w B h
  have h1 := (GlobalTheory.CuspRep.CG.HasSat.twist_absPow h s).1
  have h2 := (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s).2.1 w
  have h3 : GlobalTheory.WeilDeligne.qPow w (-s) = (GlobalTheory.HeckeGal.Model.absPow E s).val w := by
    refine Units.ext ?_
    rw [h2, GlobalTheory.WeilDeligne.coe_qPow]
    simp only [Formalism.ConjugateSelfDual.normV, Complex.ofReal_neg]
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [h3]
  exact h1
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JPTRow

section

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.GalN.V UpperTheory.V.Z.Win UpperTheory.V.Z.Desc.W UpperTheory.Zero.LLC
theorem UpperTheory.V.Z.Desc.W.same_of_prints_of_rT (P : _root_.UpperTheory.V.Af.Hypotheses') (hR : RowT) : Same :=
  _root_.UpperTheory.V.Z.Desc.W.same_of_statement P (_root_.UpperTheory.BaseChangeIdentities.bcSpeh_alt (_root_.UpperTheory.BaseChangeIdentities.bridge P.litN.aut.bc P.litN.loc.bern)) satTw (sumAEOf satTw (_root_.UpperTheory.V.Z.Desc.W.galAEOf_alt P hR)) _root_.UpperTheory.V.Z.Desc.W.splitSat_alt onePart
theorem UpperTheory.V.Z.Desc.W.point_property_of_isJ_arith_rep_autCsd : RowT →
    _root_.UpperTheory.V.Af.HypothesesH' → Z.Desc.DescWeak → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J →
    ∀ (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), 2 ≤ n → n ≤ 4 → x.Arith h →
    x.IsRep ρ → Continuous ρ → IsAutCsdA ι ρ → (∀ g ∈ Ine (F := L) (s.A s.v0), ρ g = 1) →
    (∀ v : Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v) ∧
      ∀ i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype) →
    J ≤ RingHom.ker x :=
  fun hR PH => _root_.UpperTheory.V.Z.Desc.W.jPT_of_alt recTExists (compatTOf hR plainRec) plainRec (_root_.UpperTheory.V.Z.Desc.W.same_of_prints_of_rT PH.toClassicalTheorems hR) _root_.UpperTheory.V.Z.Desc.W.sphT_alt _root_.UpperTheory.V.Z.Desc.W.pseudo_local_langlands_descent unlOf PH
end
end
end
