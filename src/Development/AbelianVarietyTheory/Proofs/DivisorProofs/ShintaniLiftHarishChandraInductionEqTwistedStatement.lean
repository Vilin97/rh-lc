module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinConjInParStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeLiftClassFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperTwistedConjIffDefinedOverBaseStatement
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Basic.Complex.Basic
public import Mathlib.SetTheory.Cardinal.Finite
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateIntoAdjoinedAlgebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockParabolicSubgroupLeviProjection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EveryElementIsNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockParabolicSubgroupLeviProjectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTwistedNormGLDiagonalBlocksStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraInductionGLIsTwistedClassFunStatement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardComapMulFinsumEqFinsumFibres

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem fibre_count_comap_mul (G₀ G : Type) [Group G₀] [Group G] [Finite G₀] [Finite G]
    (ι : G₀ →* G) (H : Subgroup G) (T : G → ℂ)
    (hT : ∀ y, T y ≠ 0 → ∃ k p, p ∈ H ∧ y = ι k * p) :
    (Nat.card (H.comap ι) : ℂ) * ∑ᶠ y, T y = ∑ᶠ k : G₀, ∑ᶠ p : H, T (ι k * p) := by
  haveI : Fintype G₀ := Fintype.ofFinite G₀
  haveI : Fintype G := Fintype.ofFinite G
  have inner : ∀ k : G₀, ∑ᶠ p : H, T (ι k * p) =
      ∑ y : G, if (ι k)⁻¹ * y ∈ H then T y else 0 := by
    intro k
    rw [finsum_eq_sum_of_fintype]
    symm
    rw [← Equiv.sum_comp (Equiv.mulLeft (ι k))]
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype (Finset.univ.filter (fun x : G => x ∈ H)) (by simp)
      (fun x => T (ι k * x))
  have hcount : ∀ y, T y ≠ 0 →
      ∑ k : G₀, (if (ι k)⁻¹ * y ∈ H then (1 : ℂ) else 0) = Nat.card (H.comap ι) := by
    intro y hy
    obtain ⟨k₀, p₀, hp₀, rfl⟩ := hT y hy
    rw [← Equiv.sum_comp (Equiv.mulLeft k₀)]
    simp only [Equiv.coe_mulLeft, map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    have key : ∀ m : G₀, ((ι m)⁻¹ * p₀ ∈ H ↔ m ∈ H.comap ι) := by
      intro m
      rw [Subgroup.mem_comap, ← H.inv_mem_iff (x := ι m), H.mul_mem_cancel_right hp₀]
    simp only [key]
    rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp only [inner]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases hy : T y = 0
  · simp [hy]
  · rw [← hcount y hy, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    split_ifs <;> simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardComapMulFinsumEqFinsumFibresStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.card_comap_mul_finsum_eq_finsum_fibres : ∀ (G₀ G : Type) [Group G₀] [Group G] [Finite G₀] [Finite G] (ι : G₀ →* G) (H : Subgroup G) (T : G → ℂ), (∀ y, T y ≠ 0 → ∃ k p, p ∈ H ∧ y = ι k * p) → (Nat.card (H.comap ι) : ℂ) * ∑ᶠ y, T y = ∑ᶠ k : G₀, ∑ᶠ p : H, T (ι k * p) := by
  first | (exact @GlobalTheory.fibre_count_comap_mul) | (exact GlobalTheory.fibre_count_comap_mul) | (intros; apply GlobalTheory.fibre_count_comap_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlocksTwistedConjBlockUpperTriangular

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.BlocksTwist

theorem toG_map {F : Type} [Field F] (t : F →+* F) {m : ℕ} (M : Matrix (Fin m) (Fin m) F) (h : IsUnit M) :
    toG (M.map t) = gal t m (toG M) := by
  have h' : IsUnit (M.map t) := by simpa using h.map (t.mapMatrix)
  unfold toG
  rw [dite_eq_left h', dite_eq_left h]
  ext i j
  simp [gal]

theorem coe_gal {F : Type} [Field F] (t : F →+* F) (n : ℕ) (p : GL (Fin n) F) :
    ((gal t n p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = (p : Matrix (Fin n) (Fin n) F).map t := by
  simp [gal]

theorem ent_map {F : Type} [Field F] (t : F →+* F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : ℕ) :
    ent (M.map t) i j = t (ent M i j) := by
  unfold ent
  split_ifs <;> simp

theorem tl_map {F : Type} [Field F] (t : F →+* F) (a : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    tl a (M.map t) = (tl a M).map t := by
  ext i j; simp [tl, ent_map]

theorem br_map {F : Type} [Field F] (t : F →+* F) (a b : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    br a b (M.map t) = (br a b M).map t := by
  ext i j; simp [br, ent_map]

theorem inPar_gal {F : Type} [Field F] (t : F →+* F) (a : ℕ) {n : ℕ} (p : GL (Fin n) F) (hp : InPar a p) :
    InPar a (gal t n p) := by
  intro i j hj hi
  rw [coe_gal]
  simp [hp i j hj hi]

theorem blocks_twist : ∀ (F : Type) [Field F] (t : F →+* F) (a b n : ℕ), n = a + b → ∀ (p x : GL (Fin n) F), InPar a p → InPar a x → tlG a (p⁻¹ * x * gal t n p) = (tlG a p)⁻¹ * tlG a x * gal t a (tlG a p) ∧ brG a b (p⁻¹ * x * gal t n p) = (brG a b p)⁻¹ * brG a b x * gal t b (brG a b p) := by
  intro F _ t a b n hn p x hp hx
  obtain ⟨H, π, hH, -, hπ, -, -⟩ := BlockPar.block_par F a b n hn
  let p' : H := ⟨p, (hH p).2 hp⟩
  let x' : H := ⟨x, (hH x).2 hx⟩
  let g' : H := ⟨gal t n p, (hH _).2 (inPar_gal t a p hp)⟩
  have key : π (p'⁻¹ * x' * g') = (π p')⁻¹ * π x' * π g' := by simp only [map_mul, map_inv]
  rw [hπ, hπ, hπ, hπ] at key
  have e : ((p'⁻¹ * x' * g' : H) : GL (Fin n) F) = p⁻¹ * x * gal t n p := rfl
  rw [e] at key
  have htl : tlG a (gal t n p) = gal t a (tlG a p) := by
    subst hn
    unfold tlG
    rw [coe_gal, tl_map, toG_map _ _ (BlockPar.units_of_par p hp).1]
  have hbr : brG a b (gal t n p) = gal t b (brG a b p) := by
    subst hn
    unfold brG
    rw [coe_gal, br_map, toG_map _ _ (BlockPar.units_of_par p hp).2]
  simp only [Prod.ext_iff, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv] at key
  rw [← htl, ← hbr]
  exact key

end GlobalTheory.Shin.BlocksTwist
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlocksTwistedConjBlockUpperTriangularStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.diagonalBlocks_twistedConj_blockUpperTriangular : ∀ (F : Type) [Field F] (t : F →+* F) (a b n : ℕ), n = a + b → ∀ (p x : GL (Fin n) F), InPar a p → InPar a x → tlG a (p⁻¹ * x * gal t n p) = (tlG a p)⁻¹ * tlG a x * gal t a (tlG a p) ∧ brG a b (p⁻¹ * x * gal t n p) = (brG a b p)⁻¹ * brG a b x * gal t b (brG a b p) := by
  first | (exact @GlobalTheory.Shin.BlocksTwist.blocks_twist) | (exact GlobalTheory.Shin.BlocksTwist.blocks_twist) | (intros; apply GlobalTheory.Shin.BlocksTwist.blocks_twist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftHarishChandraInductionEqTwisted

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.LiftHc

theorem galAct_incl {F F' : Type} [Field F] [Field F'] [Algebra F F'] (n : ℕ) (t : F' ≃ₐ[F] F')
    (x : GL (Fin n) F) : galAct F F' n t (incl F F' n x) = incl F F' n x := by
  ext i j; simp [galAct_apply, gal, incl]

theorem inPar_incl {F F' : Type} [Field F] [Field F'] [Algebra F F'] (a n : ℕ) (x : GL (Fin n) F) :
    InPar a (incl F F' n x) ↔ InPar a x := by
  simp [InPar, incl, gal]

theorem inPar_gal {F : Type} [Field F] (t : F →+* F) (a n : ℕ) (x : GL (Fin n) F) (hx : InPar a x) :
    InPar a (gal t n x) := by
  intro i j hj hi; simp [gal, hx i j hj hi]

theorem gal_id {F : Type} [Field F] (n : ℕ) (x : GL (Fin n) F) : gal (RingHom.id F) n x = x := by
  ext i j; simp [gal]

theorem nrm_conj_incl {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (δ : GL (Fin n) F') (y₀ : GL (Fin n) F) :
    nrm s ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) = (incl F F' n y₀)⁻¹ * nrm s δ * incl F F' n y₀ := by
  unfold nrm nrmG
  set c := incl F F' n y₀
  set L := List.range (Module.finrank F F')
  have h : ∀ i : ℕ, galAct F F' n (s ^ i) (c⁻¹ * δ * c) =
      MulAut.conj c⁻¹ (galAct F F' n (s ^ i) δ) := by
    intro i
    rw [map_mul, map_mul, map_inv, galAct_incl, MulAut.conj_apply, inv_inv]
  simp only [h]
  have e := map_list_prod (MulAut.conj c⁻¹) (L.map fun i => galAct F F' n (s ^ i) δ)
  rw [List.map_map] at e
  rw [show (fun i => MulAut.conj c⁻¹ (galAct F F' n (s ^ i) δ)) =
    (⇑(MulAut.conj c⁻¹) ∘ fun i => galAct F F' n (s ^ i) δ) from rfl, ← e, MulAut.conj_apply, inv_inv]

theorem count {G₀ G : Type} [Group G₀] [Group G] [Finite G₀] [Finite G] (ι : G₀ →* G)
    (H : Subgroup G) (T : G → ℂ) (hT : ∀ y, T y ≠ 0 → ∃ k p, p ∈ H ∧ y = ι k * p) :
    (Nat.card (H.comap ι) : ℂ) * ∑ᶠ y, T y = ∑ᶠ k : G₀, ∑ᶠ p : H, T (ι k * p) :=
  GlobalTheory.T.card_comap_mul_finsum_eq_finsum_fibres G₀ G ι H T hT

theorem blocks_twist {F : Type} [Field F] (t : F →+* F) (a b n : ℕ) (hn : n = a + b)
    (p x : GL (Fin n) F) (hp : InPar a p) (hx : InPar a x) :
    tlG a (p⁻¹ * x * gal t n p) = (tlG a p)⁻¹ * tlG a x * gal t a (tlG a p) ∧
    brG a b (p⁻¹ * x * gal t n p) = (brG a b p)⁻¹ * brG a b x * gal t b (brG a b p) :=
  GlobalTheory.T.diagonalBlocks_twistedConj_blockUpperTriangular F t a b n hn p x hp hx

theorem inPar_conj_adjoin {F F' : Type} [Field F] [Field F'] [Algebra F F'] (a n : ℕ)
    (γ y₀ : GL (Fin n) F) (δ : GL (Fin n) F')
    (hA : (δ : Matrix (Fin n) (Fin n) F') ∈
      Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')})
    (hP : InPar a (y₀⁻¹ * γ * y₀)) : InPar a ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) :=
  GlobalTheory.T.inPar_conj_of_mem_adjoin_incl_of_inPar_conj F F' a n γ y₀ δ hA hP

theorem term (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F')
    (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (a b n : ℕ) (hn : n = a + b)
    (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (hα : IsCl α) (hβ : IsCl β)
    (γ : GL (Fin n) F) (δ : GL (Fin n) F')
    (hA : (δ : Matrix (Fin n) (Fin n) F') ∈
      Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')})
    (hN : nrm s δ = incl F F' n γ) (y₀ : GL (Fin n) F) (p : GL (Fin n) F') (hp : InPar a p) :
    (if InPar a ((incl F F' n y₀ * p)⁻¹ * δ * gal (s : F' →+* F') n (incl F F' n y₀ * p)) then
      shLift s α (tlG a ((incl F F' n y₀ * p)⁻¹ * δ * gal (s : F' →+* F') n (incl F F' n y₀ * p))) *
      shLift s β (brG a b ((incl F F' n y₀ * p)⁻¹ * δ * gal (s : F' →+* F') n (incl F F' n y₀ * p)))
      else 0) =
    (if InPar a (y₀⁻¹ * γ * y₀) then α (tlG a (y₀⁻¹ * γ * y₀)) * β (brG a b (y₀⁻¹ * γ * y₀)) else 0) := by
  have hle : a ≤ n := by omega
  obtain ⟨H, π, hH, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F' a b n hn
  obtain ⟨H₀, π₀, hH₀, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b n hn
  set c := incl F F' n y₀ with hc
  set δ₁ := c⁻¹ * δ * c with hδ₁def
  have hgc : gal (s : F' →+* F') n c = c := galAct_incl n s y₀
  have key : (c * p)⁻¹ * δ * gal (s : F' →+* F') n (c * p) = p⁻¹ * δ₁ * gal (s : F' →+* F') n p := by
    rw [map_mul, hgc, hδ₁def]; group
  by_cases h1 : InPar a (y₀⁻¹ * γ * y₀)
  · rw [key]
    have hδ₁ : InPar a δ₁ := inPar_conj_adjoin a n γ y₀ δ hA h1
    have hin : InPar a (p⁻¹ * δ₁ * gal (s : F' →+* F') n p) := by
      rw [← hH]
      exact H.mul_mem (H.mul_mem (H.inv_mem ((hH p).2 hp)) ((hH _).2 hδ₁))
        ((hH _).2 (inPar_gal _ a n p hp))
    rw [if_pos hin, if_pos h1]
    obtain ⟨et, eb⟩ := blocks_twist (s : F' →+* F') a b n hn p δ₁ hp hδ₁
    have hN₁ : nrm s δ₁ = incl F F' n (y₀⁻¹ * γ * y₀) := by
      rw [hδ₁def, nrm_conj_incl, hN, map_mul, map_mul, map_inv]
    obtain ⟨nt, nb⟩ := GlobalTheory.T.galoisTwistedNormGL_diagonal_blocks F F' s hs a b n hn _ δ₁ h1 hδ₁ hN₁
    have lα := GlobalTheory.T.base_change_lift_class_function F F' s hs a α hα
    have lβ := GlobalTheory.T.base_change_lift_class_function F F' s hs b β hβ
    rw [et, eb]
    have eα := lα.2 (tlG a δ₁) (tlG a p)
    have eβ := lβ.2 (brG a b δ₁) (brG a b p)
    rw [galAct_apply] at eα eβ
    rw [eα, eβ, lα.1 _ _ (by unfold IsNorm; rw [nt]), lβ.1 _ _ (by unfold IsNorm; rw [nb])]
  · rw [if_neg h1, if_neg]
    intro hin
    obtain ⟨y₁, p₁, hp₁, e, hγ₁⟩ := (GlobalTheory.T.blockUpper_twistedConj_iff_defined_over_base F F' s hs a n hle γ δ (c * p) hA hN).1 hin
    have hh : incl F F' n (y₁⁻¹ * y₀) = p₁ * p⁻¹ := by
      rw [map_mul, map_inv, ← hc, show c = incl F F' n y₁ * p₁ * p⁻¹ by rw [← e]; group]
      group
    have hP : InPar a (y₁⁻¹ * y₀) := by
      rw [← inPar_incl (F' := F'), hh, ← hH]
      exact H.mul_mem ((hH _).2 hp₁) (H.inv_mem ((hH _).2 hp))
    apply h1
    have : y₀⁻¹ * γ * y₀ = (y₁⁻¹ * y₀)⁻¹ * (y₁⁻¹ * γ * y₁) * (y₁⁻¹ * y₀) := by group
    rw [this, ← hH₀]
    exact H₀.mul_mem (H₀.mul_mem (H₀.inv_mem ((hH₀ _).2 hP)) ((hH₀ _).2 hγ₁)) ((hH₀ _).2 hP)

theorem pointwise (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F')
    (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (a b n : ℕ) (hn : n = a + b)
    (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (hα : IsCl α) (hβ : IsCl β)
    (γ : GL (Fin n) F) (δ : GL (Fin n) F')
    (hA : (δ : Matrix (Fin n) (Fin n) F') ∈
      Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')})
    (hN : nrm s δ = incl F F' n γ) :
    hcTw (s : F' →+* F') a b (shLift s α) (shLift s β) n δ = hc a b α β n γ := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  obtain ⟨H, -, hH, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F' a b n hn
  set T : GL (Fin n) F' → ℂ := fun y => if InPar a (y⁻¹ * δ * gal (s : F' →+* F') n y) then
      shLift s α (tlG a (y⁻¹ * δ * gal (s : F' →+* F') n y)) *
      shLift s β (brG a b (y⁻¹ * δ * gal (s : F' →+* F') n y)) else 0 with hTdef
  set c₀ : GL (Fin n) F → ℂ := fun y₀ => if InPar a (y₀⁻¹ * γ * y₀) then
      α (tlG a (y₀⁻¹ * γ * y₀)) * β (brG a b (y₀⁻¹ * γ * y₀)) else 0 with hc₀
  have hsupp : ∀ y, T y ≠ 0 → ∃ k p, p ∈ H ∧ y = incl F F' n k * p := by
    intro y hy
    have hin : InPar a (y⁻¹ * δ * gal (s : F' →+* F') n y) := by
      by_contra h; exact hy (if_neg h)
    obtain ⟨k, p, hp, e, -⟩ := (GlobalTheory.T.blockUpper_twistedConj_iff_defined_over_base F F' s hs a n (by omega) γ δ y hA hN).1 hin
    exact ⟨k, p, (hH p).2 hp, e⟩
  have hcnt := count (incl F F' n) H T hsupp
  have hterm : ∀ k (p : H), T (incl F F' n k * p) = c₀ k := fun k p =>
    term F F' s hs a b n hn α β hα hβ γ δ hA hN k p ((hH p).1 p.2)
  simp only [hterm] at hcnt
  have e1 : Nat.card (H.comap (incl F F' n)) = Nat.card {p : GL (Fin n) F // InPar a p} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [Subgroup.mem_comap, hH, inPar_incl])
  have e2 : Nat.card H = Nat.card {p : GL (Fin n) F' // InPar a p} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => hH x)
  have hpos1 : (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ) ≠ 0 := by
    rw [← e1]; exact_mod_cast (Nat.card_pos (α := H.comap (incl F F' n))).ne'
  have hpos2 : (Nat.card {p : GL (Fin n) F' // InPar a p} : ℂ) ≠ 0 := by
    rw [← e2]; exact_mod_cast (Nat.card_pos (α := H)).ne'
  haveI := Fintype.ofFinite H
  have hconst : ∀ k, ∑ᶠ _p : H, c₀ k = (Nat.card H : ℂ) * c₀ k := by
    intro k; rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul]
  simp only [hconst] at hcnt
  rw [← mul_finsum] at hcnt
  have hhc : hc a b α β n γ = (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹ * ∑ᶠ y₀, c₀ y₀ := by
    simp only [hc, hcTw, gal_id, hc₀]
  rw [hhc, e1, e2] at *
  unfold hcTw
  rw [← hTdef]
  field_simp
  linear_combination hcnt

end GlobalTheory.Shin.LiftHc

theorem GlobalTheory.Shin.shLift_hc_eq_hcTw : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsCl α → IsCl β → shLift s (hc a b α β n) = hcTw (s : F' →+* F') a b (shLift s α) (shLift s β) n := by
  intro F F' _ _ _ _ s hs a b n hn α β hα hβ
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  funext δ
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.every_element_is_norm F F' s hs n δ
  obtain ⟨y, hyA, hyN⟩ := GlobalTheory.T.conjugate_into_adjoined_algebra F F' s hs n δ γ hγ
  have hcl := (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) a b n α β).2.1
  have hL := (GlobalTheory.T.base_change_lift_class_function F F' s hs n _ hcl).2 δ y
  have hR := (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F' (s : F' →+* F') a b n (shLift s α) (shLift s β)).1 δ y
  rw [← hL, ← hR, (GlobalTheory.T.base_change_lift_class_function F F' s hs n _ hcl).1 _ γ (by unfold IsNorm; rw [hyN])]
  exact (GlobalTheory.Shin.LiftHc.pointwise F F' s hs a b n hn α β hα hβ γ _ hyA hyN).symm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftHarishChandraInductionEqTwistedStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.shintaniLift_harishChandraInduction_eq_twisted : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsCl α → IsCl β → shLift s (hc a b α β n) = hcTw (s : F' →+* F') a b (shLift s α) (shLift s β) n := by
  first | (exact @GlobalTheory.Shin.shLift_hc_eq_hcTw) | (exact GlobalTheory.Shin.shLift_hc_eq_hcTw) | (intros; apply GlobalTheory.Shin.shLift_hc_eq_hcTw  <;> assumption)
end
end
