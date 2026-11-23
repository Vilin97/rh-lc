module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivOfGlobalSectionPowNumEquivMultiple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasNonzeroSecPowOfAmpleSubAmple
public import Mathlib.AlgebraicGeometry.Properties
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
import Mathlib.Order.CompletePartialOrder
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfIsNef
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosKltAddSmulEffectiveDivisorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSeparatingTwoPointsAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffQDivAddOfIsQCart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalMultipleAddQWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtLcAtOfLeCoeffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulIntersectionLeOfNefClassOnClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfIsNef
import Mathlib.Algebra.Order.Star.Rat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectivePointFlagHom

section

@[expose] public section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagQ

theorem eq_genericPoint_of_krullDim_zero {X : Scheme.{0}} [IsIntegral X] (h : topologicalKrullDim X = 0) (x : X) :
    x = genericPoint X := by
  by_contra hx
  have hlt : (⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩ : TopologicalSpace.IrreducibleCloseds X) <
      ⟨closure {genericPoint X}, isIrreducible_singleton.closure, isClosed_closure⟩ := by
    refine lt_of_le_of_ne ?_ ?_
    · exact (specializes_iff_closure_subset.1 (genericPoint_specializes x))
    · intro he
      have : closure ({x} : Set X) = closure {genericPoint X} := congrArg TopologicalSpace.IrreducibleCloseds.carrier he
      exact hx ((specializes_iff_closure_subset.2 this.ge).antisymm (genericPoint_specializes x)).eq
  have : (0 : WithBot ℕ∞) < topologicalKrullDim X := Order.krullDim_pos_iff.2 ⟨_, _, hlt⟩
  rw [h] at this
  exact lt_irrefl _ this

end GlobalTheory.FlagQ
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleAddEffectiveOfNefBig

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KodairaNefBig

theorem isAffine_of_dim_zero {X : Scheme.{0}} [IsIntegral X] (h : topologicalKrullDim X = 0) :
    IsAffine X := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have hU' : U = ⊤ := eq_top_iff.2 fun x _ => by
    rw [GlobalTheory.FlagQ.eq_genericPoint_of_krullDim_zero h x]; exact hmem
  subst hU'
  haveI : IsAffine (⊤ : X.Opens) := hU
  exact IsAffine.of_isIso X.topIso.inv

theorem prod_le {d : ℕ} (q : ℤ) (hq : 1 ≤ q) (n : Fin (d + 1) → Fin 2 → ℤ)
    (h0 : ∀ j, 0 ≤ n 0 j ∧ n 0 j ≤ 2) (hs : ∀ (i : Fin d) j, 0 ≤ n i.succ j ∧ n i.succ j ≤ q)
    (a : Fin (d + 1) → Fin 2) : ∏ i, n i (a i) ≤ 2 * q ^ d := by
  rw [Fin.prod_univ_succ]
  have hp : ∏ i : Fin d, n i.succ (a i.succ) ≤ ∏ _i : Fin d, q :=
    Finset.prod_le_prod₀ (fun i _ => (hs i _).1) fun i _ => (hs i _).2
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hp
  exact mul_le_mul (h0 _).2 hp (Finset.prod_nonneg fun i _ => (hs i _).1) (by norm_num)

end GlobalTheory.KodairaNefBig


open GlobalTheory.KodairaNefBig in
theorem GlobalTheory.exists_ample_add_eff_of_isNef_isBig : GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (N : LB X) (hN : N.IsLB), IsNef ℂ N → IsBig ℂ N → ∃ (a : ℕ) (A : LB X) (hA : A.IsLB) (E₀ : CartierDiv X), 0 < a ∧ IsAmpleLB A ∧ E₀.Eff ∧ a • cls N hN = cls A hA + cls (toLB E₀) (isLB_toLB E₀) := by
  intro hNN X _ _ p hp N hN hnef hbig
  letI := algebraΓOfHom p
  have hp' : IsProjOver (strHom ℂ (X := X)) := by rwa [strHom_eq (f := p) fun _ => rfl]
  obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver hp
  obtain ⟨D, hD, -⟩ := hbig.growth
  cases D with
  | zero =>
    have := isAffine_of_dim_zero (X := X) (by simpa using hD)
    refine ⟨1, N, hN, 0, one_pos, isAmpleLB_of_isAffine hN, CartierDiv.eff_zero, ?_⟩
    rw [one_smul, ← toPic_apply, map_zero, add_zero]
  | succ d =>
    have := isNoetherian_of_isProjOver hp
    have hV := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom ℂ X) (GlobalTheory.structureModule X)
      hp' (d := d + 1) (by rw [QCoh.suppDim_structureModule]; exact hD.le)
    let P : Fin 2 → LB X := ![N, A]
    have hPn : ∀ j, IsNef ℂ (P j) := fun j => by
      fin_cases j
      exacts [hnef, hA.isNef]
    have hP : ∀ j, (P j).IsLB := fun j => (hPn j).isLB
    have hI : ∀ a : Fin (d + 1) → Fin 2, 0 ≤ interNum ℂ (GlobalTheory.structureModule X) (P ∘ a) :=
      fun a => hNN.1.interNum_nonneg hp' hD fun i => hPn (a i)
    set S : ℤ := ∑ a : Fin (d + 1) → Fin 2, interNum ℂ (GlobalTheory.structureModule X) (P ∘ a) with hSdef
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => hI a
    have hT : 0 < topSelfIntersection ℂ N (d + 1) := (hNN.2.2.isBig_iff hp' hD hnef).1 hbig
    set q : ℕ := 2 * (d + 1) * S.toNat + 1 with hqdef
    have hqS : (q : ℤ) = 2 * (d + 1) * S + 1 := by
      rw [hqdef]; push_cast [Int.toNat_of_nonneg hS0]; ring
    have hq1 : (1 : ℤ) ≤ q := by rw [hqS]; nlinarith
    let L : LB X := tens A (lbPow N q)
    have hL : IsAmpleLB L := IsAmpleLB.tens_of_isNef hNN ℂ X p hp A _ hA (hnef.pow hA q)
    let B : LB X := lbPow A 2
    have hB : IsAmpleLB B := (isAmpleLB_pow_iff hA.isLB (by norm_num)).2 hA
    let M : LB X := tens (lbPow N q) (dual A)
    have hM : M.IsLB := isLB_tens (isLB_lbPow hN q) (isLB_dual hA.isLB)
    have hclsL : cls L hL.isLB = (q : ℤ) • cls N hN + cls A hA.isLB := by
      rw [cls_tens hA.isLB (isLB_lbPow hN q), cls_lbPow hN, natCast_zsmul, add_comm]
    have hclsB : cls B hB.isLB = (2 : ℤ) • cls A hA.isLB := by
      rw [cls_lbPow hA.isLB]; norm_cast
    have hclsM : cls M hM = (q : ℤ) • cls N hN - cls A hA.isLB := by
      rw [cls_tens (isLB_lbPow hN q) (isLB_dual hA.isLB), cls_lbPow hN, cls_dual hA.isLB,
        natCast_zsmul, sub_eq_add_neg]
    have e : cls L hL.isLB = cls M hM + cls B hB.isLB := by
      rw [hclsL, hclsM, hclsB]; abel

    have e₁ := hV.interNum_of_cls_eq_sum hP (Q := fun _ => L) (fun _ => hL.isLB)
      (fun _ => ![(q : ℤ), 1]) (fun _ => by
        rw [Fin.sum_univ_two, hclsL]
        simp [P])
    have hlow : (q : ℤ) ^ (d + 1) * topSelfIntersection ℂ N (d + 1) ≤ topSelfIntersection ℂ L (d + 1) := by
      rw [topSelf_def ℂ L, e₁]
      have hnn : ∀ a : Fin (d + 1) → Fin 2,
          0 ≤ (∏ i, (![(q : ℤ), 1] : Fin 2 → ℤ) (a i)) * interNum ℂ (GlobalTheory.structureModule X) (P ∘ a) :=
        fun a => mul_nonneg (Finset.prod_nonneg fun i _ => by
          rcases Fin.exists_fin_two.1 ⟨a i, rfl⟩ with h | h <;> rw [h] <;> simp <;> omega) (hI a)
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun a _ => hnn a)
        (Finset.mem_univ (fun _ => (0 : Fin 2))))
      simp only [Matrix.cons_val_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rfl

    let n : Fin (d + 1) → Fin 2 → ℤ := Fin.cons ![0, 2] (fun _ => ![(q : ℤ), 1])
    have e₂ := hV.interNum_of_cls_eq_sum hP (Q := Fin.cons B (fun _ : Fin d => L))
      (Fin.cases hB.isLB fun _ => hL.isLB) n (fun i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · rw [Fin.sum_univ_two]
          simp only [Fin.cons_zero, n]
          rw [hclsB]
          simp [P]
        · rw [Fin.sum_univ_two]
          simp only [Fin.cons_succ, n]
          rw [hclsL]
          simp [P])
    have hup : interNum ℂ (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X)
        ≤ 2 * (q : ℤ) ^ d * S := by
      rw [e₂, hSdef, Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right ?_ (hI a)
      refine prod_le (q : ℤ) hq1 n (fun j => ?_) (fun i j => ?_) a
      · rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with h | h <;> subst h <;> simp [n]
      · rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with h | h <;> subst h <;> simp [n] <;> omega
    have hineq : ((d : ℤ) + 1) * interNum ℂ (GlobalTheory.structureModule X)
        (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection ℂ L (d + 1) := by
      have hqd : (0 : ℤ) < (q : ℤ) ^ d := pow_pos (by omega) d
      have hd1 : (0 : ℤ) ≤ (d : ℤ) + 1 := by positivity
      calc ((d : ℤ) + 1) * interNum ℂ (GlobalTheory.structureModule X)
            (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X)
          ≤ ((d : ℤ) + 1) * (2 * (q : ℤ) ^ d * S) := mul_le_mul_of_nonneg_left hup hd1
        _ = (q : ℤ) ^ d * (2 * (d + 1) * S) := by ring
        _ < (q : ℤ) ^ d * q := mul_lt_mul_of_pos_left (by rw [hqS]; omega) hqd
        _ = (q : ℤ) ^ (d + 1) * 1 := by ring
        _ ≤ (q : ℤ) ^ (d + 1) * topSelfIntersection ℂ N (d + 1) :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
        _ ≤ topSelfIntersection ℂ L (d + 1) := hlow
    obtain ⟨r, hr, hs⟩ := exists_hasNonzeroSec_pow_of_ample_sub_ample ℂ X hp' d hD.le L B M hL hB hM
      e hineq
    obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 hs
    refine ⟨q * r, lbPow A r, isLB_lbPow hA.isLB r, divOfSec (isLB_lbPow hM r) s hs,
      Nat.mul_pos (Nat.succ_pos _) hr, (isAmpleLB_pow_iff hA.isLB hr).2 hA,
      eff_divOfSec_of_sec _ s hs, ?_⟩
    rw [← toPic_apply, (presents_divOfRatSec _ (isRatSec_ratOfSec s hs)).toPic_eq,
      cls_lbPow hA.isLB, cls_lbPow hM, hclsM]
    first
      | module
      | (simp only [← natCast_zsmul, smul_sub, smul_smul, Nat.cast_mul]; rw [mul_comm (r : ℤ)]; abel)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleAddEffectiveOfNefBigStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.exists_ample_add_effective_of_nef_big : GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (N : LB X) (hN : N.IsLB), IsNef ℂ N → IsBig ℂ N → ∃ (a : ℕ) (A : LB X) (hA : A.IsLB) (E₀ : CartierDiv X), 0 < a ∧ IsAmpleLB A ∧ E₀.Eff ∧ a • cls N hN = cls A hA + cls (toLB E₀) (isLB_toLB E₀) := by
  first | exact @GlobalTheory.exists_ample_add_eff_of_isNef_isBig | exact GlobalTheory.exists_ample_add_eff_of_isNef_isBig | (intros; apply GlobalTheory.exists_ample_add_eff_of_isNef_isBig <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSeparatingTwoPointsAmpleStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.exists_section_separating_two_points_ample : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ρ : ℚ) (h : ℕ → ℚ) (x₁ x₂ : X), M.IsLB → IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → ∑ e ∈ Finset.Icc 1 n, h e < ρ → ∃ s : M.Sec, (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s) := by
  first | exact @GlobalTheory.PairStep.exists_sec_separating_two_points_of_ample | exact GlobalTheory.PairStep.exists_sec_separating_two_points_of_ample | (intros; apply GlobalTheory.PairStep.exists_sec_separating_two_points_of_ample <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparateTwoPointsNefBig

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.NefBigSep

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {H N A B : LB X} {Z : Closeds X}

theorem deg_of_cls_eq (hZ : IsCompleteCurve k Z) (hH : IsAmpleLB H) (hN : N.IsLB) (hA : A.IsLB)
    (hB : B.IsLB) (a b : ℕ) (e : cls N hN = a • cls A hA + b • cls B hB) :
    interNumRed k Z ![N] = a * interNumRed k Z ![A] + b * interNumRed k Z ![B] := by
  rw [hZ.interNumRed_of_cls_eq_add hH hN (isLB_lbPow hA a) (isLB_lbPow hB b)
    (by rw [cls_lbPow hA, cls_lbPow hB, e]), hZ.interNumRed_lbPow hH hA,
    hZ.interNumRed_lbPow hH hB]

theorem exists_budget (ρ S c : ℚ) (a : ℕ) (hρ : 0 < ρ) (hS : S < ρ) (hS0 : 0 ≤ S) (hc : 0 < c) :
    ∃ q m' : ℕ, 0 < m' ∧ (q : ℚ) = ρ * m' ∧ a < q ∧ 1 / (m' : ℚ) ≤ c ∧ (m' : ℚ) * S < q - a := by
  have hd : (0 : ℚ) < ρ.den := by exact_mod_cast ρ.den_pos
  have hu : (0 : ℤ) ≤ ρ.num := (Rat.num_pos.2 hρ).le
  have hρ' : ((ρ.num.toNat : ℕ) : ℚ) = ρ * ρ.den := by
    rw [show ((ρ.num.toNat : ℕ) : ℚ) = ((ρ.num.toNat : ℤ) : ℚ) from rfl, Int.toNat_of_nonneg hu]
    exact (Rat.mul_den_eq_num ρ).symm
  have hgap : 0 < (ρ.den : ℚ) * (ρ - S) := mul_pos hd (sub_pos.2 hS)
  obtain ⟨t, ht⟩ := exists_nat_gt (max (1 / c) (a / ((ρ.den : ℚ) * (ρ - S))))
  have ht1 : 1 / c < t := lt_of_le_of_lt (le_max_left _ _) ht
  have ht2 : a / ((ρ.den : ℚ) * (ρ - S)) < t := lt_of_le_of_lt (le_max_right _ _) ht
  have htpos : (0 : ℚ) < t := lt_trans (by positivity) ht1
  have ht2' : (a : ℚ) < t * ((ρ.den : ℚ) * (ρ - S)) := by
    rw [div_lt_iff₀ hgap] at ht2; linarith
  refine ⟨ρ.num.toNat * t, ρ.den * t, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_pos ρ.den_pos (by exact_mod_cast htpos)
  · push_cast; rw [hρ']; ring
  · have : (a : ℚ) < ((ρ.num.toNat * t : ℕ) : ℚ) := by
      push_cast; rw [hρ']; nlinarith [mul_nonneg (mul_nonneg hd.le htpos.le) hS0]
    exact_mod_cast this
  · push_cast
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hc] at ht1
    have : (1 : ℚ) ≤ ρ.den := by exact_mod_cast ρ.den_pos
    nlinarith
  · push_cast; rw [hρ']; nlinarith

end GlobalTheory.NefBigSep

namespace GlobalTheory.NefBigSep

theorem separate_nef_big : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ρ : ℚ) (h : ℕ → ℚ) (x₁ x₂ : X), M.IsLB → IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsNef ℂ N → IsBig ℂ N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → ∑ e ∈ Finset.Icc 1 n, h e < ρ → 0 < ρ → ∃ s : M.Sec, (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s) := by
  intro hPr hNad hNef X _ _ _ p n hp hdim M Δ m G N ρ h x₁ x₂ hM hΔ hklt hm hG hNn hNb
    hcurve hx₁ hx₂ hne hh hz hsum hρ
  letI := algebraΓOfHom p
  obtain ⟨a, A, hA, E₀, ha, hAmp, hE₀, hcls⟩ :=
    GlobalTheory.T.exists_ample_add_effective_of_nef_big hNef X p hp N hNn.isLB hNn hNb
  obtain ⟨c, hc, hkltc⟩ := GlobalTheory.T.exists_pos_klt_add_smul_effective_divisor hPr X p n hp hdim Δ m G (qWeil E₀ 1) hm hG hklt
    ⟨1, E₀, one_pos, hE₀, rfl⟩
  have hS0 : 0 ≤ ∑ e ∈ Finset.Icc 1 n, h e := Finset.sum_nonneg fun e _ => (hh e).le
  obtain ⟨q, m', hm', hq, haq, hmc, hbud⟩ := exists_budget ρ _ c a hρ hsum hS0 hc
  have hNp := isLB_lbPow hNn.isLB (q - a)
  have hN'lb := isLB_tens hA hNp
  have hclsN' : cls _ hN'lb = cls A hA + (q - a) • cls N hNn.isLB := by
    rw [cls_tens hA hNp, cls_lbPow hNn.isLB]
  have hN'amp : IsAmpleLB (tens A (lbPow N (q - a))) :=
    IsAmpleLB.tens_of_isNef hNef ℂ X p hp A _ hAmp (hNn.pow hAmp _)
  have hqa : (0 : ℚ) < q - a := sub_pos.2 (by exact_mod_cast haq)
  have hqa' : (((q - a : ℕ) : ℚ)) = q - a := by rw [Nat.cast_sub haq.le]
  have hB : qWeil E₀ m' = (1 / (m' : ℚ)) • qWeil E₀ 1 := by
    funext z; simp [qWeil]; ring
  refine GlobalTheory.T.exists_section_separating_two_points_ample hPr hNad hNef X p n hp hdim M (Δ + qWeil E₀ m') (m * m') (m' • G + m • E₀)
    (tens A (lbPow N (q - a))) (1 / (m' : ℚ)) (fun e => h e / ((q : ℚ) - a)) x₁ x₂ hM
    (isEffQDiv_add_of_isQCart X p hp Δ _ hΔ ⟨m', E₀, hm', hE₀, rfl⟩) ?_ (Nat.mul_pos hm hm')
    (isLogCanonicalMultiple_add_qWeil X p n Δ m m' G E₀ hm hm' hG) hN'amp ?_ hx₁ hx₂ hne
    (fun e => div_pos (hh e) hqa) ?_ ?_
  · intro y
    rw [hB]
    exact (GlobalTheory.T.kltAt_and_lcAt_antitone_coeff X p n hp hdim Δ (qWeil E₀ 1) (1 / (m' : ℚ)) c y
      ⟨1, E₀, one_pos, hE₀, rfl⟩ hmc).1 (hkltc y)
  · intro C hC
    have h1 := hcurve C hC
    have dN' := deg_of_cls_eq hC hAmp hN'lb hA hNn.isLB 1 (q - a) (by rw [hclsN', one_nsmul])
    have dK := hC.interNumRed_of_cls_eq_add hAmp (isLB_lbPow hNn.isLB a) hA (isLB_toLB E₀)
      (by rw [cls_lbPow hNn.isLB, hcls])
    rw [hC.interNumRed_lbPow hAmp hNn.isLB] at dK
    have dG := deg_of_cls_eq hC hAmp (isLB_toLB (m' • G + m • E₀)) (isLB_toLB G) (isLB_toLB E₀)
      m' m (by rw [← toPic_apply, ← toPic_apply, ← toPic_apply, map_add (f := _), map_nsmul, map_nsmul])
    rw [h1, dN', dG]
    have dK' : (a : ℚ) * interNumRed ℂ C ![N] = interNumRed ℂ C ![A] + interNumRed ℂ C ![toLB E₀] := by
      exact_mod_cast dK
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have hm0' : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
    push_cast
    rw [hqa']
    field_simp
    linear_combination (m : ℚ) * dK' - (m : ℚ) * (interNumRed ℂ C ![N] : ℚ) * hq
  · intro z e hze he hdz
    have hmix := mixExp_interNumRed hNef ℂ X p hp N A (tens A (lbPow N (q - a))) hNn.isLB hA hN'lb
      (q - a) 1 (Closeds.closure {z}) e hNn hAmp.isNef (by rw [hclsN', one_nsmul, add_comm])
      (by rw [Closeds.coe_closure]; exact hdz)
    have key : ((q : ℚ) - a) ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)
        ≤ (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => tens A (lbPow N (q - a)) : ℤ) := by
      have := (Int.cast_le (R := ℚ)).2 hmix
      push_cast at this
      rwa [hqa'] at this
    have h0 := hz z e hze he hdz
    have e1 : h e ^ e * ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ) : ℚ) =
        (h e / ((q : ℚ) - a)) ^ e * (((q : ℚ) - a) ^ e *
          (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) := by
      rw [div_pow]; field_simp
    calc 2 * (e : ℚ) ^ e < _ := h0
      _ = _ := e1
      _ ≤ _ := mul_le_mul_of_nonneg_left key (pow_nonneg (div_pos (hh e) hqa).le _)
  · rw [← Finset.sum_div, div_lt_div_iff₀ hqa (by exact_mod_cast hm')]
    linarith

end GlobalTheory.NefBigSep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparateTwoPointsNefBigStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.separate_two_points_nef_big : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ρ : ℚ) (h : ℕ → ℚ) (x₁ x₂ : X), M.IsLB → IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsNef ℂ N → IsBig ℂ N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → ∑ e ∈ Finset.Icc 1 n, h e < ρ → 0 < ρ → ∃ s : M.Sec, (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s) := by
  first | exact @GlobalTheory.NefBigSep.separate_nef_big | exact GlobalTheory.NefBigSep.separate_nef_big | (intros; apply GlobalTheory.NefBigSep.separate_nef_big <;> assumption)
end
end
