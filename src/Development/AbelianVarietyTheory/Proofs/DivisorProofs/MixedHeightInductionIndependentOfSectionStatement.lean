module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecializesIsLocalization
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorAddEffective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionsNonvanishingFiniteSetStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveArakelovFormulaRhsTensorAdditiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveMixedHeightReciprocityTwoSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveMixedHeightTensorAdditiveStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorRationalSections

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt.Denom

variable {Y : Scheme.{0}} [IsIntegral Y]

theorem exists_sec_tens {L M : LB Y} (hL : L.IsLB) (hM : M.IsLB) {r : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) (u : M.Sec) (hu : genericPoint Y ∈ nonzeroLocus u)
    (hE : (divOfRatSec hL hr + divOfSec hM u hu).Eff) :
    ∃ (t : (tens L M).Sec) (ht : genericPoint Y ∈ nonzeroLocus t), ∀ i j, genericPoint Y ∈ L.U i →
      genericPoint Y ∈ M.U j → ratOfSec t ht (i, j) = r i * ratOfSec u hu j := by
  have P := (presents_divOfRatSec hL hr).tens (presents_divOfRatSec hM (isRatSec_ratOfSec u hu))
  obtain ⟨t, ht⟩ := P.exists_rat_eq (f := 1) (CartierDiv.mem_sections.2 fun x => hE x)
  have hη : genericPoint Y ∈ nonzeroLocus t :=
    (P.generatesAt_rat_iff t).1 (ht ▸ CartierDiv.generatesAt_genericPoint _ one_ne_zero)
  refine ⟨t, hη, fun i j hi hj => Units.ext ?_⟩
  have e := P.rat_mul t (i, j) ⟨hi, hj⟩
  rw [ht, one_mul] at e
  rw [val_ratOfSec (show genericPoint Y ∈ (tens L M).U (i, j) from ⟨hi, hj⟩), ← e]

theorem gen_mem_secPow {L : LB Y} (hL : L.IsLB) (t : L.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
    (m : ℕ) : genericPoint Y ∈ nonzeroLocus (Cartier.secPow t m) := by
  obtain ⟨i, hi⟩ := exists_chart hL (genericPoint Y)
  have hj : genericPoint Y ∈ (lbPow L m).U (fun _ => i) := (lbPow_U L m _).ge hi
  refine (mem_nonzeroLocus_iff _ _ hj).2 ((unitAt_fnOf_iff hj hj _).1 (unitAt_genericPoint ?_))
  show fnOf _ hj (resG Y _ (t.f i) ^ m) ≠ 0
  rw [map_pow, fnOf_resG]
  exact pow_ne_zero _ (fnOf_sec_ne_zero ht hi)

theorem divOfSec_secPow {L : LB Y} (hL : L.IsLB) (t : L.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
    (m : ℕ) (hm : genericPoint Y ∈ nonzeroLocus (Cartier.secPow t m)) :
    divOfSec (isLB_lbPow hL m) (Cartier.secPow t m) hm = m • divOfSec hL t ht := by
  refine CartierDiv.ext_of_isEqn fun x => ?_
  obtain ⟨i, hi⟩ := exists_chart hL x
  have hj : x ∈ (lbPow L m).U (fun _ => i) := (lbPow_U L m _).ge hi
  have e : ratOfSec (Cartier.secPow t m) hm (fun _ => i) = ratOfSec t ht i ^ m := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, val_ratOfSec (gen_mem hi), val_ratOfSec (gen_mem hj)]
    show fnOf _ (gen_mem hj) (resG Y _ (t.f i) ^ m) = _
    rw [map_pow, fnOf_resG]
  refine ⟨ratOfSec t ht i ^ m, ?_,
    ((presents_divOfRatSec hL (isRatSec_ratOfSec t ht)).isEqn i x hi).nsmul m⟩
  rw [← e]
  exact (presents_divOfRatSec (isLB_lbPow hL m) (isRatSec_ratOfSec _ hm)).isEqn _ x hj

theorem exists_open_regularAt {L : LB Y} (hL : L.IsLB) {r : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) :
    ∃ W : Y.Opens, genericPoint Y ∈ W ∧ ∀ x ∈ W, (divOfRatSec hL hr).RegularAt x 1 := by
  obtain ⟨i, hi⟩ := exists_chart hL (genericPoint Y)
  obtain ⟨U, hU, a, ha⟩ := (regAt_genericPoint (r i : Y.functionField)).exists_fnOf
  refine ⟨L.U i ⊓ U, ⟨hi, hU⟩, fun x hx => ?_⟩
  refine ((presents_divOfRatSec hL hr).isEqn i x hx.1).regularAt_iff.2 ?_
  rw [one_mul, ← ha]
  exact regAt_fnOf hx.2 _ a

end GlobalTheory.MixHt.Denom


open GlobalTheory.MixHt.Denom in
theorem GlobalTheory.MixHt.exists_common_denom : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y]
    (q : Y ⟶ Sp k), IsAmb q → ∀ (N : HermLB q) (r r' : N.B.ι → Y.functionFieldˣ), IsRatSec N.B r →
    IsRatSec N.B r' → ∃ (A : HermLB q) (u : A.B.Sec) (t t' : (N.tens A).B.Sec)
    (hu : genericPoint Y ∈ nonzeroLocus u) (ht : genericPoint Y ∈ nonzeroLocus t)
    (ht' : genericPoint Y ∈ nonzeroLocus t'), ∀ (i : N.B.ι) (j : A.B.ι), genericPoint Y ∈ N.B.U i →
    genericPoint Y ∈ A.B.U j → ratOfSec t ht (i, j) = r i * ratOfSec u hu j ∧
      ratOfSec t' ht' (i, j) = r' i * ratOfSec u hu j := by
  intro k _ Y _ q hq N r r' hr hr'
  obtain ⟨n₀, j, hj, hjq⟩ := hq.isProjOver
  let H₀ : HermLB (PSpace.str k n₀) :=
    .fs _ (isAmple_projective_O_one k n₀).isLB (ProjSpace.coord k n₀)
      (ProjSpace.iSup_nonzeroLocus_coord k n₀) (fun _ => 1) (fun _ => by simp)
      (fun _ => ⟨1, one_mem _, by rw [mul_one, Matrix.map_one _ (map_zero _) (map_one _)]⟩)
  let H : HermLB q := H₀.pull j hjq
  have hH : IsAmpleLB H.B := (isAmple_projective_O_one k n₀).pull_of_isClosedImmersion j
  haveI := hH.compactSpace
  obtain ⟨W, hW, hWr⟩ := exists_open_regularAt N.isLB hr
  obtain ⟨W', hW', hWr'⟩ := exists_open_regularAt N.isLB hr'
  obtain ⟨n, -, t, ht, hle, -⟩ :=
    hH.exists_affine_le (x := genericPoint Y) (U := W ⊓ W') ⟨hW, hW'⟩
  have hL := isLB_lbPow H.isLB n
  obtain ⟨N₁, h₁⟩ := EffDiff.eventually_eff_add_nsmul hL t ht _ fun x hx => hWr x (hle hx).1
  obtain ⟨N₂, h₂⟩ := EffDiff.eventually_eff_add_nsmul hL t ht _ fun x hx => hWr' x (hle hx).2
  have hu := gen_mem_secPow hL t ht (max N₁ N₂)
  have hD := divOfSec_secPow hL t ht (max N₁ N₂) hu
  obtain ⟨s, hs, e⟩ := exists_sec_tens N.isLB (isLB_lbPow hL _) hr (Cartier.secPow t (max N₁ N₂)) hu
    (by rw [hD]; exact h₁ _ (le_max_left _ _))
  obtain ⟨s', hs', e'⟩ := exists_sec_tens N.isLB (isLB_lbPow hL _) hr' (Cartier.secPow t (max N₁ N₂)) hu
    (by rw [hD]; exact h₂ _ (le_max_right _ _))
  exact ⟨(H.pow n).pow (max N₁ N₂), Cartier.secPow t (max N₁ N₂), s, s', hu, hs, hs',
    fun i j hi hj => ⟨e i j hi hj, e' i j hi hj⟩⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorRationalSectionsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.exists_common_denominator_rational_sections : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (N : HermLB q) (r r' : N.B.ι → Y.functionFieldˣ), IsRatSec N.B r → IsRatSec N.B r' → ∃ (A : HermLB q) (u : A.B.Sec) (t t' : (N.tens A).B.Sec) (hu : genericPoint Y ∈ nonzeroLocus u) (ht : genericPoint Y ∈ nonzeroLocus t) (ht' : genericPoint Y ∈ nonzeroLocus t'), ∀ (i : N.B.ι) (j : A.B.ι), genericPoint Y ∈ N.B.U i → genericPoint Y ∈ A.B.U j → ratOfSec t ht (i, j) = r i * ratOfSec u hu j ∧ ratOfSec t' ht' (i, j) = r' i * ratOfSec u hu j := by
  first | exact @GlobalTheory.MixHt.exists_common_denom | exact GlobalTheory.MixHt.exists_common_denom | (intros; apply GlobalTheory.MixHt.exists_common_denom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductionIndependentOfSection

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem recVal_indep_sec : ArchInteg → ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y]
    [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T,
    IsMix q (e + 1) T → ∀ (N : HermLB q) (L : Fin (e + 1) → HermLB q) (r : N.B.ι → Y.functionFieldˣ)
    (hr : IsRatSec N.B r) (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'),
    recVal (T (e + 1) L) L N hr = recVal (T (e + 1) L) L N hr' := by
  intro hI hR k _ Y _ _ q hq e hd T hT N L r hr r' hr'
  haveI : IsNoetherian Y := hq.isNoetherian
  have step1 : ∀ (P : HermLB q) (t t' : P.B.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
      (ht' : genericPoint Y ∈ nonzeroLocus t'),
      recVal (T (e + 1) L) L P (isRatSec_ratOfSec t ht) = recVal (T (e + 1) L) L P (isRatSec_ratOfSec t' ht') := by
    intro P t t' ht ht'
    have hS := (GlobalTheory.ZH.finite_notMem_coheight_le_one (nonzeroLocus t) ⟨_, ht⟩).union
      (GlobalTheory.ZH.finite_notMem_coheight_le_one (nonzeroLocus t') ⟨_, ht'⟩)
    obtain ⟨A, s, u, hs, hu⟩ := GlobalTheory.T.exists_tensor_sections_nonvanishing_finite_set k Y q hq (L 0) _ (hS.insert (genericPoint Y))
    have hgs : genericPoint Y ∈ nonzeroLocus s := hs (Set.mem_insert _ _)
    have hgu : genericPoint Y ∈ nonzeroLocus u := hu (Set.mem_insert _ _)
    have cs : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus t ∨ z ∈ nonzeroLocus s := fun z hz => by
      by_cases h : z ∈ nonzeroLocus t
      · exact Or.inl h
      · exact Or.inr (hs (Set.mem_insert_of_mem _ (Or.inl ⟨h, hz.le⟩)))
    have cs' : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus t' ∨ z ∈ nonzeroLocus s := fun z hz => by
      by_cases h : z ∈ nonzeroLocus t'
      · exact Or.inl h
      · exact Or.inr (hs (Set.mem_insert_of_mem _ (Or.inr ⟨h, hz.le⟩)))
    have cu : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus t ∨ z ∈ nonzeroLocus u := fun z hz => by
      by_cases h : z ∈ nonzeroLocus t
      · exact Or.inl h
      · exact Or.inr (hu (Set.mem_insert_of_mem _ (Or.inl ⟨h, hz.le⟩)))
    have cu' : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus t' ∨ z ∈ nonzeroLocus u := fun z hz => by
      by_cases h : z ∈ nonzeroLocus t'
      · exact Or.inl h
      · exact Or.inr (hu (Set.mem_insert_of_mem _ (Or.inr ⟨h, hz.le⟩)))
    have r1 := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT P ((L 0).tens A) (Fin.tail L) t s ht hgs cs
    have r1' := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT P ((L 0).tens A) (Fin.tail L) t' s ht' hgs cs'
    have r2 := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT P A (Fin.tail L) t u ht hgu cu
    have r2' := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT P A (Fin.tail L) t' u ht' hgu cu'
    have a1 := GlobalTheory.T.inductiveMixedHeight_tensor_additive hI k Y q hq e hd T hT P _ (isRatSec_ratOfSec t ht) (L 0) A (Fin.tail L)
    have a1' := GlobalTheory.T.inductiveMixedHeight_tensor_additive hI k Y q hq e hd T hT P _ (isRatSec_ratOfSec t' ht') (L 0) A (Fin.tail L)
    rw [← Fin.cons_self_tail L]
    linarith
  obtain ⟨A, u, t, t', hu, ht, ht', hrel⟩ := GlobalTheory.T.exists_common_denominator_rational_sections k Y q hq N r r' hr hr'
  have v1 := GlobalTheory.T.inductiveArakelovFormula_rhs_tensor_additive hI k Y q hq (e + 1) hd (T (e + 1) L) L N A r hr _ (isRatSec_ratOfSec u hu) _
    (isRatSec_ratOfSec t ht) fun i j hi hj => (hrel i j hi hj).1
  have v2 := GlobalTheory.T.inductiveArakelovFormula_rhs_tensor_additive hI k Y q hq (e + 1) hd (T (e + 1) L) L N A r' hr' _ (isRatSec_ratOfSec u hu) _
    (isRatSec_ratOfSec t' ht') fun i j hi hj => (hrel i j hi hj).2
  have s1 := step1 (N.tens A) t t' ht ht'
  linarith

end GlobalTheory.MixHt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductionIndependentOfSectionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.mixedHeightInduction_independent_of_section : ArchInteg → ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (N : HermLB q) (L : Fin (e + 1) → HermLB q) (r : N.B.ι → Y.functionFieldˣ) (hr : IsRatSec N.B r) (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'), recVal (T (e + 1) L) L N hr = recVal (T (e + 1) L) L N hr' := by
  first | exact @GlobalTheory.MixHt.recVal_indep_sec | exact GlobalTheory.MixHt.recVal_indep_sec | (intros; apply GlobalTheory.MixHt.recVal_indep_sec <;> assumption)
end
end
