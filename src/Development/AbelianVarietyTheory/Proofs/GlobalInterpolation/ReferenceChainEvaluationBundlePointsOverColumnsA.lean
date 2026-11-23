module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ReferenceChainEvaluationAtBundlePoints
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.HermitianForms.TiedSym
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CardResidueFieldTotallyRealTypePrime
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
public import Formalism.LocalToGlobal.HermitianForms.DefsGH
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ComplexRootOfUnityMemRangeOfIsPrimitiveRoot
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPrimitiveRootsCoeffFieldTrueColumns
public import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralPendingObjectSymmetricFormsLevel
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassMapEstimateOfPartial
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FormsExtendHolds
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormBoundOfInjectiveStable
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.SymmetricClausesOfFormsNorm
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.SymmetricClausesOfFormsNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BranchingNormIdentityTrueColumnsMembers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardColumnComparisonsTrueColumns
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerMapTie
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PropertyAtConstructedPointsOfTrueColumnsViewStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CardResidueFieldTotallyRealTypePrimeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.card_residue_field_totally_real_type_prime : ∀ (D : D7) (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal → Nat.card (kv D.host.F v) = D.host.g i := by
  first | exact @GlobalTheory.SplitResidueCard.card_kv | exact GlobalTheory.SplitResidueCard.card_kv | (intros; apply GlobalTheory.SplitResidueCard.card_kv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GLevHChiPowEqOneAndMemRange

section

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem gLevH_chi_pow_eq_one_and_mem_range : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (gp : Fin 2 → ℕ) (G : GLoc F E σ gp) (H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))) (lam : ∀ a v h, H a v h →* ℂˣ) (_ : GLevH S G H lam) (K : Type) [Field K] (s : K →+* ℂ) (N : ℕ), (∀ i, (gp i).Prime) → (∀ a v h M, ((lam a v h M : ℂˣ) : ℂ) ^ N = 1 ∧ ∃ r : K, s r = ((lam a v h M : ℂˣ) : ℂ)) → ∀ x : S.U, ((S.chi x : ℂˣ) : ℂ) ^ N = 1 ∧ ∃ r : K, s r = ((S.chi x : ℂˣ) : ℂ) := by
  intro F E _ _ _ _ _ σ n J T f bad S gp G H lam L K _ s N _ hl x
  have hmul : ∀ a b : ℂ, (a ^ N = 1 ∧ ∃ r : K, s r = a) → (b ^ N = 1 ∧ ∃ r : K, s r = b) →
      ((a * b) ^ N = 1 ∧ ∃ r : K, s r = a * b) := by
    rintro a b ⟨ha, r, hr⟩ ⟨hb, r', hr'⟩
    exact ⟨by rw [mul_pow, ha, hb, one_mul], r * r', by rw [map_mul, hr, hr']⟩
  have hone : (1 : ℂ) ^ N = 1 ∧ ∃ r : K, s r = 1 := ⟨one_pow N, 1, map_one s⟩
  rw [L.chi_eq x]
  refine Finset.prod_induction _ (fun z : ℂ => z ^ N = 1 ∧ ∃ r : K, s r = z) hmul hone ?_
  intro a _
  refine finprod_induction (fun z : ℂ => z ^ N = 1 ∧ ∃ r : K, s r = z) hone hmul ?_
  intro v
  refine finprod_induction (fun z : ℂ => z ^ N = 1 ∧ ∃ r : K, s r = z) hone hmul ?_
  intro h
  obtain ⟨h1, r, hr⟩ := hl a v h (L.red a v h x)
  exact ⟨by rw [inv_pow, h1, inv_one], r⁻¹, by rw [map_inv₀, hr]⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LamJMemRangeAndPowEqOne

section

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem lamJ_mem_range_and_pow_eq_one :
    ∀ (k K : Type) [Field k] [Field K] (s : K →+* ℂ) (p : ℕ), p.Prime → Nat.card k = p →
      (∃ ζ : K, IsPrimitiveRoot ζ p) → (∃ ζ : K, IsPrimitiveRoot ζ (p - 1)) →
      ∀ (n : ℕ) (ψ : AddChar k ℂ) (χ : ℕ → MulChar k ℂ) (a t nb skip : ℕ)
        (M : Matrix (Fin n) (Fin n) k),
        (∃ r : K, s r = lamJ ψ χ a t nb skip M) ∧
          (lamJ ψ χ a t nb skip M ≠ 0 → lamJ ψ χ a t nb skip M ^ (p * (p - 1)) = 1) := by
  intro k K _ _ s p hp hk ⟨ζ, hζ⟩ ⟨ξ, hξ⟩ n ψ χ a t nb skip M
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact hp.ne_zero)
  letI : Fintype k := Fintype.ofFinite k
  have hk' : Fintype.card k = p := by rw [← Nat.card_eq_fintype_card]; exact hk
  have hψ : ∀ x : k, ψ x ^ p = 1 := by
    intro x
    rw [← AddChar.map_nsmul_eq_pow, ← hk, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
  have hχ : ∀ (i : ℕ) (x : k), χ i x ≠ 0 → χ i x ^ (p - 1) = 1 := by
    intro i x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (MulChar.map_zero _)
    rw [← map_pow, ← hk', FiniteField.pow_card_sub_one_eq_one x hx0, map_one]
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hψr : ∀ x : k, ψ x ∈ s.range := fun x =>
    complex_rootOfUnity_mem_range_of_isPrimitiveRoot K s p ζ hp.pos hζ _ (hψ x)
  have hχr : ∀ (i : ℕ) (x : k), χ i x ∈ s.range := by
    intro i x
    by_cases hx : χ i x = 0
    · rw [hx]; exact zero_mem _
    · exact complex_rootOfUnity_mem_range_of_isPrimitiveRoot K s (p - 1) ξ hp1 hξ _ (hχ i x hx)
  unfold lamJ
  refine ⟨?_, ?_⟩
  · exact mul_mem (hψr _) (prod_mem fun i _ => hχr i _)
  · intro h
    have h2 := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h)
    rw [mul_pow, pow_mul, hψ, one_pow, one_mul, mul_comm p, pow_mul, ← Finset.prod_pow,
      Finset.prod_eq_one (fun i hi => hχ i _ (h2 i hi)), one_pow]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChiLastStepFiniteOrderSymTie

section

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem chi_last_step_finite_order_symTie : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf), (∀ i, (∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i)) ∧ ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i - 1)) → ∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U, (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) := by
  intro D u Ch chOf Tf hζ
  have hpos : ∀ i, 0 < D.host.g i * (D.host.g i - 1) := fun i =>
    Nat.mul_pos (D.host.g_prime i).pos (Nat.sub_pos_of_lt (D.host.g_prime i).one_lt)
  refine ⟨∏ i, D.host.g i * (D.host.g i - 1), Finset.prod_pos fun i _ => hpos i, ?_⟩
  refine GlobalTheory.gLevH_chi_pow_eq_one_and_mem_range _ _ _ _ _ _ _ _ _ _ _ _ _ Tf.glevM D.what₂.LL D.what₂.embLL _ D.host.g_prime ?_
  intro a v h M
  have key : (∃ r : D.what₂.LL, D.what₂.embLL r = ((Tf.lamM a v h M : ℂˣ) : ℂ)) ∧
      (((Tf.lamM a v h M : ℂˣ) : ℂ) ≠ 0 → ((Tf.lamM a v h M : ℂˣ) : ℂ) ^ (D.host.g a * (D.host.g a - 1)) = 1) := by
    rw [Tf.lamM_eq]
    unfold lamSym
    exact GlobalTheory.lamJ_mem_range_and_pow_eq_one _ D.what₂.LL D.what₂.embLL _ (D.host.g_prime a) (GlobalTheory.T.card_residue_field_totally_real_type_prime D a v h) (hζ a).1 (hζ a).2
      _ _ _ _ _ _ _ _
  refine ⟨?_, key.1⟩
  obtain ⟨c, hc⟩ : D.host.g a * (D.host.g a - 1) ∣ ∏ i, D.host.g i * (D.host.g i - 1) :=
    Finset.dvd_prod_of_mem (fun i => D.host.g i * (D.host.g i - 1)) (Finset.mem_univ a)
  rw [hc, pow_mul, key.2 (Units.ne_zero _), one_pow]

end GlobalTheory
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormBoundHolds

section

@[expose] public section

namespace Formalism.L2.GlobalTheoryTheory.Br

theorem norm_bound_holds : NormBoundAtInfinity := norm_bound_of_injective_stable class_injective_holds stabiliser_bijective_holds

end Formalism.L2.GlobalTheoryTheory.Br
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.BlockActions.SymmetricLevelClausesHold

section

@[expose] public section

namespace Formalism.L2.GlobalTheoryTheory.Br

theorem symmetric_level_clauses_hold : ClassMapPropertiesOfSymmetricForms := symmetric_clauses_of_four class_injective_holds stabiliser_bijective_holds forms_extend_holds norm_bound_holds

end Formalism.L2.GlobalTheoryTheory.Br
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsMapOfSymmetricComparisonLowerMapFiniteChar

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

namespace GlobalTheory.RedPt0

theorem formsMap_of_symmetricComparison_lowerMap_finiteChar : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf), Formalism.L2.Rows.LowerMapTieS Tf → Formalism.L2.Ker.BeOnTie D u → (∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U, (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ)) → Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u := by
  intro D u Ch chOf Tf hL hB hC
  obtain ⟨P, h4⟩ := GlobalTheory.RedPt0Pend.exists_integralPendingObject_symmetricFormsLevel D u Ch chOf Tf hL hB hC
  exact Formalism.MainNotions.product_first_zeroth_parts.classMap_estimate_of_partial P h4 (Formalism.L2.GlobalTheoryTheory.Br.symmetric_level_clauses_hold D u Ch chOf Tf hL hB)

end GlobalTheory.RedPt0
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsMapAtEveryTrueColumnMember

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem formsMap_at_every_trueColumnMember : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : (I.rec7 l Z).what₂.Word), Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (I.rec7 l Z) u := by
  intro B X I hOk hP l Z u
  obtain ⟨C, hC, -⟩ := GlobalTheory.Mem.Col2.TC.colsTiedSym_std I hOk hP l Z
  have hF := hC u
  have hL := GlobalTheory.Mem.Col2.LowerTie.lowerMap_tie I hOk hP l Z u _ _ (C.forms u) hF
  have hB := GlobalTheory.Mem.Col2.TC.beOnTie_true I hOk hP l Z u
  have hR : ∀ i, (∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i)) ∧
      ∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i - 1) :=
    fun i => GlobalTheory.trueCols_exists_primitiveRoots I hOk l Z i
  exact GlobalTheory.RedPt0.formsMap_of_symmetricComparison_lowerMap_finiteChar (I.rec7 l Z) u _ _ (C.forms u) hL hB
    (GlobalTheory.chi_last_step_finite_order_symTie (I.rec7 l Z) u _ _ (C.forms u) hR)

end GlobalTheory.Mem.Col2.TC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsMapAtEveryTrueColumnMemberStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.aux_of_ok_of_pins : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : (I.rec7 l Z).what₂.Word), Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (I.rec7 l Z) u := by
  first | exact @GlobalTheory.Mem.Col2.TC.formsMap_at_every_trueColumnMember | exact GlobalTheory.Mem.Col2.TC.formsMap_at_every_trueColumnMember | (intros; apply GlobalTheory.Mem.Col2.TC.formsMap_at_every_trueColumnMember <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ReferenceChainEvaluationBundlePointsOverColumnsA

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fc.PeriodEntriesOverColumns

theorem constructedPoint_referenceChainWord_formsMap (Q : V4.Slot) (hQ : OverCols Q) (K : Ctx) (β : BPt K) (hq : β.Is Q) :
    ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 β.D u :=
  GlobalTheory.T.property_at_constructedPoints_of_trueColumnsView (fun D _ => ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u)
    (fun _ _ _ w Z _ _ _ _ _ => GlobalTheory.T.aux_of_ok_of_pins w.I w.ok w.pins w.l Z)
    K β (hQ _ _ _ _ _ hq)

theorem referenceChainEvaluation_bundlePoints_overColumns : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.ReferenceChainEvaluationAtBundlePoints Q Lk :=
  fun Q hQ _ Lk => Row0.row (validForConstructedPointClasses_eventuallyWorkingClass (R := fun D _ => ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u)
    (EvP.of_all fun _ K _ β hq => constructedPoint_referenceChainWord_formsMap Q hQ K β hq)) Lk

end GlobalTheory.Fc.PeriodEntriesOverColumns

end
end
end
