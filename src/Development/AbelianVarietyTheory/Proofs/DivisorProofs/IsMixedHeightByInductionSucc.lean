module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArithStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbientStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveArakelovFormulaRhsTensorAdditiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionsNonvanishingFiniteSetStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveMixedHeightReciprocityTwoSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveMixedHeightTensorAdditiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductionIndependentOfSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductiveRhsSymmIsometryInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightRecursiveValueWellDefinedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightUniqueRestrictClosedSubschemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Mathlib.Algebra.Group.End
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.GroupTheory.Perm.Fin

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductionSymmetricFirstTwo

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.VSwap

theorem finite_coheight_one_mem_supp {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] [CompactSpace Z]
    (D : CartierDiv Z) : {z : Z | Order.coheight z = 1 ∧ z ∈ D.supp}.Finite := by
  classical
  have : IsNoetherian Z := {}
  obtain ⟨S, hS, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible D.supp.isClosed
  refine (hS.image fun T => if h : IsIrreducible T then h.genericPoint else genericPoint Z).subset
    fun z hz => ?_
  obtain ⟨T, hT, hzT⟩ := Set.mem_sUnion.1 (hU.le hz.2)
  refine ⟨T, hT, ?_⟩
  simp only [dif_pos (hi T hT)]
  have hg := (hi T hT).isGenericPoint_genericPoint (hc T hT)
  have h₁ : z ≤ (hi T hT).genericPoint := hg.specializes hzT
  have h₂ : (hi T hT).genericPoint < genericPoint Z := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
    have e' : _ = genericPoint Z := (Specializes.antisymm e (genericPoint_specializes _)).eq
    exact D.genericPoint_notMem_supp (e' ▸ hU.ge (Set.mem_sUnion.2 ⟨T, hT, hg.mem⟩))
  by_contra hne
  have h₃ := Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e => hne (Specializes.antisymm h₁ e).eq)
  have h₄ := Order.coheight_add_one_le h₂
  rw [hz.1] at h₃
  have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
  exact absurd h₅ (by decide)

section

variable (hI : ArchInteg) (hR : ArchRecip) {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y]
  [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hq : IsAmb q) {e : ℕ} (hd : topologicalKrullDim Y = (e + 1 + 1 : ℕ))
  {T : ∀ d : ℕ, (Fin d → HermLB q) → Y → ℝ} (hT : IsMix q (e + 1) T) (L : Fin e → HermLB q)


include hI hR hq hd hT in
theorem add_first (N M A : HermLB q) {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)
    {u : A.B.ι → Y.functionFieldˣ} (hu : IsRatSec A.B u) {t : (M.tens A).B.ι → Y.functionFieldˣ}
    (ht : IsRatSec (M.tens A).B t) :
    recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) (M.tens A) ht =
      recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr +
        recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) A hu := by
  have hp : IsRatSec (M.tens A).B (fun c : M.B.ι × A.B.ι => r c.1 * u c.2) := PtHtComb.isRatSec_tens hr hu
  rw [GlobalTheory.T.mixedHeightInduction_independent_of_section hI hR k Y q hq e hd T hT (M.tens A) (Fin.cons N L) t ht _ hp]
  exact GlobalTheory.T.inductiveArakelovFormula_rhs_tensor_additive hI k Y q hq (e + 1) hd (T (e + 1) (Fin.cons N L)) (Fin.cons N L) M A r hr u hu _ hp
    fun _ _ _ _ => rfl


include hI hR hq hd hT in
theorem swap_of_sec (M N : HermLB q) (t : N.B.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) {r' : N.B.ι → Y.functionFieldˣ} (hr' : IsRatSec N.B r') :
    recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr =
      recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N hr' := by
  have : IsNoetherian Y := hq.isNoetherian
  set S : Set Y := {genericPoint Y} ∪ {z | Order.coheight z = 1 ∧ z ∈ (divOfSec N.isLB t ht).supp} with hS
  have hfin : S.Finite := (Set.finite_singleton _).union (finite_coheight_one_mem_supp _)
  obtain ⟨B, s, v, hsS, hvS⟩ := GlobalTheory.T.exists_tensor_sections_nonvanishing_finite_set k Y q hq M S hfin
  have hs : genericPoint Y ∈ nonzeroLocus s := hsS (Set.mem_union_left _ rfl)
  have hv : genericPoint Y ∈ nonzeroLocus v := hvS (Set.mem_union_left _ rfl)
  have hcov : ∀ z : Y, Order.coheight z = 1 → z ∉ nonzeroLocus t → z ∈ S := fun z hz hzt =>
    Set.mem_union_right _ ⟨hz, by_contra fun h => hzt ((notMem_supp_divOfSec (hL := N.isLB) (s := t) (hs := ht)).1 h)⟩
  have R1 := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT (M.tens B) N L s t hs ht fun z hz =>
    (em (z ∈ nonzeroLocus t)).elim Or.inr fun h => Or.inl (hsS (hcov z hz h))
  have R2 := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT B N L v t hv ht fun z hz =>
    (em (z ∈ nonzeroLocus t)).elim Or.inr fun h => Or.inl (hvS (hcov z hz h))
  have A1 := add_first hI hR hq hd hT L N M B hr (isRatSec_ratOfSec v hv) (isRatSec_ratOfSec s hs)
  have A2 := GlobalTheory.T.inductiveMixedHeight_tensor_additive hI k Y q hq e hd T hT N (ratOfSec t ht) (isRatSec_ratOfSec t ht) M B L
  rw [GlobalTheory.T.mixedHeightInduction_independent_of_section hI hR k Y q hq e hd T hT N (Fin.cons M L) r' hr' _ (isRatSec_ratOfSec t ht)]
  linarith

end

theorem main : ArchInteg → ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y]
    (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T →
    ∀ (M N : HermLB q) (L : Fin e → HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r)
    (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'),
    recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr =
      recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N hr' := by
  intro hI hR k _ Y _ _ q hq e hd T hT M N L r hr r' hr'
  obtain ⟨A, s, u, hsS, huS⟩ := GlobalTheory.T.exists_tensor_sections_nonvanishing_finite_set k Y q hq N {genericPoint Y} (Set.finite_singleton _)
  have hs : genericPoint Y ∈ nonzeroLocus s := hsS rfl
  have hu : genericPoint Y ∈ nonzeroLocus u := huS rfl
  have hp := PtHtComb.isRatSec_tens hr' (isRatSec_ratOfSec u hu)
  have K1 := swap_of_sec hI hR hq hd hT L M (N.tens A) s hs hr hp
  have K2 := swap_of_sec hI hR hq hd hT L M A u hu hr (isRatSec_ratOfSec u hu)
  have A3 := GlobalTheory.T.inductiveMixedHeight_tensor_additive hI k Y q hq e hd T hT M r hr N A L
  have A4 := add_first hI hR hq hd hT L M N A hr' (isRatSec_ratOfSec u hu) hp
  linarith

end GlobalTheory.MixHt.VSwap
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductionSymmetricFirstTwoStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.mixedHeightInduction_symmetric_firstTwo : ArchInteg → ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (M N : HermLB q) (L : Fin e → HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r) (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'), recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr = recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N hr' := by
  first | exact @GlobalTheory.MixHt.VSwap.main | exact GlobalTheory.MixHt.VSwap.main | (intros; apply GlobalTheory.MixHt.VSwap.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermInvariantOfConsSwapAndTail

section

@[expose] public section

open Equiv

theorem GlobalTheory.perm_invariant_of_cons_swap :
  ∀ (α : Type 1) (n : ℕ) (F : (Fin (n + 2) → α) → ℝ), (∀ (a : α) (L : Fin (n + 1) → α) (e : Equiv.Perm (Fin (n + 1))), F (Fin.cons a fun i => L (e i)) = F (Fin.cons a L)) → (∀ (a b : α) (L : Fin n → α), F (Fin.cons a (Fin.cons b L : Fin (n + 1) → α)) = F (Fin.cons b (Fin.cons a L : Fin (n + 1) → α))) → ∀ (L : Fin (n + 2) → α) (e : Equiv.Perm (Fin (n + 2))), F (fun i => L (e i)) = F L := by
  intro α n F h1 h2
  let S : Subgroup (Equiv.Perm (Fin (n+2))) :=
    { carrier := {σ | ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L}
      mul_mem' := by
        intro σ τ hσ hτ
        have hσ' : ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L := hσ
        have hτ' : ∀ L : Fin (n+2) → α, F (fun i => L (τ i)) = F L := hτ
        show ∀ L : Fin (n+2) → α, F (fun i => L ((σ * τ) i)) = F L
        intro L
        calc F (fun i => L ((σ * τ) i)) = F (fun i => L (σ (τ i))) := rfl
          _ = F (fun j => L (σ j)) := hτ' (fun j => L (σ j))
          _ = F L := hσ' L
      one_mem' := by
        show ∀ L : Fin (n+2) → α, F (fun i => L ((1 : Equiv.Perm (Fin (n+2))) i)) = F L
        intro L; rfl
      inv_mem' := by
        intro σ hσ
        have hσ' : ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L := hσ
        show ∀ L : Fin (n+2) → α, F (fun i => L (σ⁻¹ i)) = F L
        intro L
        calc F (fun i => L (σ⁻¹ i)) = F (fun i => L (σ⁻¹ (σ i))) := (hσ' (fun j => L (σ⁻¹ j))).symm
          _ = F L := by simp }
  have memS : ∀ σ, σ ∈ S ↔ ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L := fun σ => Iff.rfl
  have hfix : ∀ e : Equiv.Perm (Fin (n+1)), Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) ∈ S := by
    intro e
    rw [memS]
    intro L
    have hc : (fun i => L (Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) i)) = Fin.cons (L 0) (fun i => Fin.tail L (e i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [Equiv.Perm.decomposeFin_symm_apply_succ, Fin.tail]
    rw [hc, h1 (L 0) (Fin.tail L) e, Fin.cons_self_tail]
  have hswap : Equiv.swap (0 : Fin (n+2)) 1 ∈ S := by
    rw [memS]
    intro L
    have e1 : L = Fin.cons (L 0) (Fin.cons (L 1) (fun i => L i.succ.succ) : Fin (n+1) → α) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun k => ?_) j
        · rfl
        · rfl
    have e2 : (fun i => L (Equiv.swap (0 : Fin (n+2)) 1 i)) = Fin.cons (L 1) (Fin.cons (L 0) (fun i => L i.succ.succ) : Fin (n+1) → α) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · refine Fin.cases ?_ (fun k => ?_) j
        · simp
        · have a1 : (k.succ.succ : Fin (n+2)) ≠ 0 := Fin.succ_ne_zero _
          have a2 : (k.succ.succ : Fin (n+2)) ≠ 1 := by
            intro h
            rw [← Fin.succ_zero_eq_one] at h
            exact Fin.succ_ne_zero _ (Fin.succ_injective _ h)
          simp [Equiv.swap_apply_of_ne_of_ne a1 a2]
    rw [e2, ← h2 (L 0) (L 1)]
    exact congrArg F e1.symm
  have hp : ∀ p : Fin (n+2), Equiv.swap (0 : Fin (n+2)) p ∈ S := by
    intro p
    refine Fin.cases ?_ (fun k => ?_) p
    · rw [Equiv.swap_self]; exact S.one_mem
    · have h0 : Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k) 0 = 0 := by simp
      have h1' : Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k) 1 = k.succ := by
        rw [← Fin.succ_zero_eq_one, Equiv.Perm.decomposeFin_symm_apply_succ]
        simp
      have hc := Equiv.swap_apply_apply (Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k)) 0 1
      rw [h0, h1'] at hc
      rw [hc]
      exact S.mul_mem (S.mul_mem (hfix _) hswap) (S.inv_mem (hfix _))
  have hdec : ∀ (p : Fin (n+2)) (e : Equiv.Perm (Fin (n+1))),
      Equiv.Perm.decomposeFin.symm (p, e) = Equiv.swap 0 p * Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) := by
    intro p e
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [Equiv.Perm.decomposeFin_symm_apply_succ]
  intro L e
  have he : e ∈ S := by
    rw [← Equiv.Perm.decomposeFin.symm_apply_apply e]
    rcases Equiv.Perm.decomposeFin e with ⟨p, e'⟩
    rw [hdec]
    exact S.mul_mem (hp p) (hfix e')
  exact (memS e).1 he L
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermInvariantOfConsSwapAndTailStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.perm_invariant_of_cons_swap_and_tail : ∀ (α : Type 1) (n : ℕ) (F : (Fin (n + 2) → α) → ℝ), (∀ (a : α) (L : Fin (n + 1) → α) (e : Equiv.Perm (Fin (n + 1))), F (Fin.cons a fun i => L (e i)) = F (Fin.cons a L)) → (∀ (a b : α) (L : Fin n → α), F (Fin.cons a (Fin.cons b L : Fin (n + 1) → α)) = F (Fin.cons b (Fin.cons a L : Fin (n + 1) → α))) → ∀ (L : Fin (n + 2) → α) (e : Equiv.Perm (Fin (n + 2))), F (fun i => L (e i)) = F L := by
  first | exact @GlobalTheory.perm_invariant_of_cons_swap | exact GlobalTheory.perm_invariant_of_cons_swap | (intros; apply GlobalTheory.perm_invariant_of_cons_swap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixedHeightByInductionSucc

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.Step

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

def extend (m : ℕ) (T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ) (V : (Fin (m + 1) → HermLB p) → X → ℝ) :
    ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ :=
  fun d L x => if h : d = m + 1 then V (fun a => L (Fin.cast h.symm a)) x else T d L x

theorem extend_of_ne {m : ℕ} {T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ} {V : (Fin (m + 1) → HermLB p) → X → ℝ}
    {d : ℕ} (h : d ≠ m + 1) (L : Fin d → HermLB p) (x : X) : extend m T V d L x = T d L x := dif_neg h

theorem extend_self {m : ℕ} {T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ} {V : (Fin (m + 1) → HermLB p) → X → ℝ}
    (L : Fin (m + 1) → HermLB p) (x : X) : extend m T V (m + 1) L x = V L x := by
  simp [extend]

theorem recVal_congr {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} {e : ℕ} {h h' : Y → ℝ}
    (H : ∀ z, Order.coheight z = 1 → h z = h' z) (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) : recVal h L M hr = recVal h' L M hr := by
  unfold recVal
  congr 1
  refine finsum_congr fun z => ?_
  by_cases hz : (M.div hr).mult z = 0
  · simp [hz]
  · rw [H z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)]

theorem isRatSec_tens_mul {Z : Scheme.{0}} [IsIntegral Z] {A B : LB Z} {r : A.ι → Z.functionFieldˣ}
    {s : B.ι → Z.functionFieldˣ} (hr : IsRatSec A r) (hs : IsRatSec B s) :
    IsRatSec (CechPic.tens A B) fun c : A.ι × B.ι => r c.1 * s c.2 := fun (c c' : A.ι × B.ι) h => by
  have h₁ : genericPoint Z ∈ A.U c.1 ⊓ A.U c'.1 := ⟨h.1.1, h.2.1⟩
  have h₂ : genericPoint Z ∈ B.U c.2 ⊓ B.U c'.2 := ⟨h.1.2, h.2.2⟩
  have e : fnOf _ h ((CechPic.tens A B).g c c' : Γ(Z, _)) =
      fnOf _ h₁ (A.g c.1 c'.1 : Γ(Z, _)) * fnOf _ h₂ (B.g c.2 c'.2 : Γ(Z, _)) := by
    change fnOf _ h ((res _ (A.g c.1 c'.1)).val * (res _ (B.g c.2 c'.2)).val) = _
    exact (map_mul (fnOf _ h) _ _).trans (congrArg₂ (· * ·) (fnOf_resG _ h _) (fnOf_resG _ h _))
  rw [Units.val_mul, Units.val_mul, hr c.1 c'.1 h₁, hs c.2 c'.2 h₂, e]
  ring

theorem isMix_succ : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∃ T, IsMix p (m + 1) T := by
  intro hI hR m hm k _ X p hp
  classical
  haveI : IsNoetherian X := hp.isNoetherian
  obtain ⟨T, hT⟩ := hm k X p hp
  choose v hv using GlobalTheory.T.mixedHeightRecursiveValue_well_defined hI hR m hm k X p hp T hT
  have hD := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hp
  have hdimi : ∀ (Y : Scheme.{0}) [IsIntegral Y] (i : Y ⟶ X) [IsClosedImmersion i] (d : ℕ),
      topologicalKrullDim Y = (d : ℕ) → HasDim (i (genericPoint Y)) d := fun Y _ i _ d h =>
    (hD.2.2.2.2.1 Y i (genericPoint Y) d).2 ((hD.2.2.2.2.2 Y d).2 h)
  have hcd : ∀ x : X, HasDim x (m + 1) → topologicalKrullDim (clo x) = ((m + 1 : ℕ) : WithBot ℕ∞) := fun x hx =>
    (hD.2.2.2.2.2 (clo x) (m + 1)).1
      ((hD.2.2.2.2.1 (clo x) (cloι x) (genericPoint (clo x)) (m + 1)).1 (by rw [cloι_genericPoint]; exact hx))
  have E : ∀ (x : X) (hx : HasDim x (m + 1)) (M : HermLB p) (L : Fin m → HermLB p)
      (M' : HermLB (cloι x ≫ p)) (L' : Fin m → HermLB (cloι x ≫ p)),
      (M.pull (cloι x) rfl).Isometric M' → (∀ a, ((L a).pull (cloι x) rfl).Isometric (L' a)) →
      ∀ (r : M'.B.ι → (clo x).functionFieldˣ) (hr : IsRatSec M'.B r)
        (TY : ∀ d : ℕ, (Fin d → HermLB (cloι x ≫ p)) → clo x → ℝ), IsMix (cloι x ≫ p) m TY →
      v x hx M L = recVal (TY m L') L' M' hr := by
    intro x hx M L M' L' hM hL r hr TY hTY
    rw [hv x hx M L (clo x) (cloι x ≫ p) (cloι x) rfl (cloι_genericPoint x) M' L' hM hL r hr]
    refine recVal_congr (fun z hz => ?_) L' M' hr
    have hz' : HasDim z m := ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k (clo x) (cloι x ≫ p) (hp.sub _) m (hcd x hx)).1 z).1 hz
    exact GlobalTheory.T.mixedHeight_unique_restrict_closedSubscheme k X (clo x) p (cloι x ≫ p) hp (cloι x) rfl m m T TY hT hTY m le_rfl le_rfl L L' hL z hz'
  let V : (Fin (m + 1) → HermLB p) → X → ℝ := fun L x =>
    if hx : HasDim x (m + 1) then v x hx (L 0) (Fin.tail L) else 0
  have hV : ∀ (L : Fin (m + 1) → HermLB p) (x : X) (hx : HasDim x (m + 1)),
      extend m T V (m + 1) L x = v x hx (L 0) (Fin.tail L) := fun L x hx => by
    rw [extend_self]
    exact dif_pos hx
  have hsym : ∀ (x : X) (hx : HasDim x (m + 1)) (L : Fin (m + 1) → HermLB p) (e : Equiv.Perm (Fin (m + 1))),
      v x hx (L (e 0)) (Fin.tail fun a => L (e a)) = v x hx (L 0) (Fin.tail L) := by
    intro x hx L e
    obtain ⟨TY, hTY⟩ := hm k (clo x) (cloι x ≫ p) (hp.sub (cloι x))
    have hq : IsAmb (cloι x ≫ p) := hp.sub (cloι x)
    have hdx := hcd x hx
    let F : (Fin (m + 1) → HermLB p) → ℝ := fun L => v x hx (L 0) (Fin.tail L)
    change F (fun a => L (e a)) = F L
    rcases m with _ | n
    · have : (fun a => L (e a)) = L := funext fun a => congrArg L (@Subsingleton.elim (Fin 1) _ _ _)
      rw [this]
    · refine GlobalTheory.T.perm_invariant_of_cons_swap_and_tail (HermLB p) n F (fun a L τ => ?_) (fun a b L => ?_) L e
      · simp only [F, Fin.cons_zero, Fin.tail_cons]
        obtain ⟨ra, hra⟩ := Cartier.exists_isRatSec (a.pull (cloι x) rfl).isLB
        rw [E x hx a (fun i => L (τ i)) (a.pull (cloι x) rfl) (fun i => (L (τ i)).pull (cloι x) rfl)
            (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) ra hra TY hTY,
          E x hx a L (a.pull (cloι x) rfl) (fun i => (L i).pull (cloι x) rfl)
            (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) ra hra TY hTY]
        exact (GlobalTheory.T.mixedHeight_inductive_rhs_symm_isometry_invariant hI k (clo x) (cloι x ≫ p) hq (n + 1) hdx TY hTY _ ra hra).2.1
          (fun i => (L i).pull (cloι x) rfl) τ
      · simp only [F, Fin.cons_zero, Fin.tail_cons]
        obtain ⟨ra, hra⟩ := Cartier.exists_isRatSec (a.pull (cloι x) rfl).isLB
        obtain ⟨rb, hrb⟩ := Cartier.exists_isRatSec (b.pull (cloι x) rfl).isLB
        have iso : ∀ (c : HermLB p) (j : Fin (n + 1)), ((Fin.cons c L : Fin (n + 1) → HermLB p) j).pull (cloι x) rfl |>.Isometric
            ((Fin.cons (c.pull (cloι x) rfl) (fun i => (L i).pull (cloι x) rfl) : Fin (n + 1) → HermLB (cloι x ≫ p)) j) := by
          intro c j
          refine Fin.cases ?_ (fun i => ?_) j <;> simp only [Fin.cons_zero, Fin.cons_succ] <;> exact HermLB.Isometric.refl _
        rw [E x hx a _ (a.pull (cloι x) rfl) _ (HermLB.Isometric.refl _) (iso b) ra hra TY hTY,
          E x hx b _ (b.pull (cloι x) rfl) _ (HermLB.Isometric.refl _) (iso a) rb hrb TY hTY]
        exact GlobalTheory.T.mixedHeightInduction_symmetric_firstTwo hI hR k (clo x) (cloι x ≫ p) hq n hdx TY hTY _ _ _ ra hra rb hrb
  refine ⟨extend m T V, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro d L M x hd hx hLM
    by_cases h : d = m + 1
    · subst h
      rw [hV _ _ hx, hV _ _ hx]
      obtain ⟨TY, hTY⟩ := hm k (clo x) (cloι x ≫ p) (hp.sub (cloι x))
      obtain ⟨r, hr⟩ := Cartier.exists_isRatSec ((L 0).pull (cloι x) rfl).isLB
      rw [E x hx (L 0) (Fin.tail L) ((L 0).pull (cloι x) rfl) (fun a => (Fin.tail L a).pull (cloι x) rfl)
          (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) r hr TY hTY,
        E x hx (M 0) (Fin.tail M) ((L 0).pull (cloι x) rfl) (fun a => (Fin.tail L a).pull (cloι x) rfl)
          ((hLM 0).symm.pull _ _) (fun a => (hLM a.succ).symm.pull _ _) r hr TY hTY]
    · rw [extend_of_ne h, extend_of_ne h]
      exact hT.iso d L M x (by omega) hx hLM
  · intro d L e x hd hx
    by_cases h : d = m + 1
    · subst h
      rw [hV _ _ hx, hV _ _ hx]
      exact hsym x hx L e
    · rw [extend_of_ne h, extend_of_ne h]
      exact hT.symm d L e x (by omega) hx
  · intro d A B L x hd hx
    by_cases h : d + 1 = m + 1
    · obtain rfl : d = m := by omega
      rw [hV _ _ hx, hV _ _ hx, hV _ _ hx]
      simp only [Fin.cons_zero, Fin.tail_cons]
      obtain ⟨TY, hTY⟩ := hm k (clo x) (cloι x ≫ p) (hp.sub (cloι x))
      obtain ⟨ra, hra⟩ := Cartier.exists_isRatSec (A.pull (cloι x) rfl).isLB
      obtain ⟨rb, hrb⟩ := Cartier.exists_isRatSec (B.pull (cloι x) rfl).isLB
      have ht := isRatSec_tens_mul hra hrb
      rw [E x hx (A.tens B) L ((A.pull (cloι x) rfl).tens (B.pull (cloι x) rfl)) (fun a => (L a).pull (cloι x) rfl)
          (HermLB.isometric_pull_tens A B _ _) (fun _ => HermLB.Isometric.refl _) _ ht TY hTY,
        E x hx A L (A.pull (cloι x) rfl) (fun a => (L a).pull (cloι x) rfl)
          (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) ra hra TY hTY,
        E x hx B L (B.pull (cloι x) rfl) (fun a => (L a).pull (cloι x) rfl)
          (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) rb hrb TY hTY]
      exact GlobalTheory.T.inductiveArakelovFormula_rhs_tensor_additive hI k (clo x) (cloι x ≫ p) (hp.sub _) d (hcd x hx) _ _ _ _ ra hra rb hrb _ ht
        fun _ _ _ _ => rfl
    · rw [extend_of_ne h, extend_of_ne h, extend_of_ne h]
      exact hT.add d A B L x (by omega) hx
  · intro L x hx
    rw [extend_of_ne (by omega)]
    exact hT.zero L x hx
  · intro Y _ _ q i _ hi e he hdim M L M' L' hM hL r hr
    have hfun : (fun z => extend m T V e L (i z)) = fun z => T e L (i z) :=
      funext fun z => extend_of_ne (by omega) L (i z)
    rw [hfun]
    by_cases h : e + 1 = m + 1
    · obtain rfl : e = m := by omega
      have hx := hdimi Y i (e + 1) hdim
      rw [hV _ _ hx]
      simp only [Fin.cons_zero, Fin.tail_cons]
      exact hv _ hx M L Y q i hi rfl M' L' hM hL r hr
    · rw [extend_of_ne h]
      exact hT.recur Y q i hi e (by omega) hdim M L M' L' hM hL r hr

end GlobalTheory.MixHt.Step
end
end
end
