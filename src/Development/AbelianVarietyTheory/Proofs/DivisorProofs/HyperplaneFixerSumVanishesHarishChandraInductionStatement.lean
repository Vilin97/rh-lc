module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterCosetSumEqZeroOfSubgroupSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockParabolicSubgroupLeviProjectionStatement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMemEq

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.Shin.FreeHc

variable {F : Type} [Field F]

def fixSet {m : ℕ} (f : Fin m → F) : Set (GL (Fin m) F) :=
  {x | ∀ w : Fin m → F, f ⬝ᵥ w = 0 → (x : Matrix (Fin m) (Fin m) F) *ᵥ w = w}

def fixSub {m : ℕ} (f : Fin m → F) : Subgroup (GL (Fin m) F) where
  carrier := fixSet f
  one_mem' := by intro w _; simp
  mul_mem' := by
    intro x y hx hy w hw
    rw [Units.val_mul, ← mulVec_mulVec, hy w hw, hx w hw]
  inv_mem' := by
    intro x hx w hw
    calc ((x⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ w
        = ((x⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ ((x : Matrix (Fin m) (Fin m) F) *ᵥ w) := by rw [hx w hw]
      _ = w := by rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem isChar_conj {G : Type} [Group G] {χ : G → ℂ} (h : IsChar ℂ ℂ χ) (x y : G) :
    χ (y⁻¹ * x * y) = χ x := by
  obtain ⟨n, ρ, hρ⟩ := h
  rw [hρ, hρ]
  congr 1
  simpa using ρ.char_conj x y⁻¹

theorem finsum_mem_eq {α : Type} [Fintype α] (s : Set α) (g : α → ℂ) :
    ∑ᶠ x ∈ s, g x = ∑ x, if x ∈ s then g x else 0 := by
  rw [finsum_mem_def, finsum_eq_sum_of_fintype]
  simp [Set.indicator_apply]

def eLast (m : ℕ) (hm : 0 < m) : Fin m → F := Pi.single (⟨m - 1, by omega⟩ : Fin m) 1

theorem vmv_mulVec {m : ℕ} (u v w : Fin m → F) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec, of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem key {m : ℕ} (f w₀ : Fin m → F) (hw : f ⬝ᵥ w₀ = 1) (x : GL (Fin m) F) (hx : x ∈ fixSet f) :
    (x : Matrix (Fin m) (Fin m) F) = 1 + vecMulVec ((x : Matrix (Fin m) (Fin m) F) *ᵥ w₀ - w₀) f := by
  have h : ∀ w, (x : Matrix (Fin m) (Fin m) F) *ᵥ w =
      (1 + vecMulVec ((x : Matrix (Fin m) (Fin m) F) *ᵥ w₀ - w₀) f) *ᵥ w := by
    intro w
    have hw' : f ⬝ᵥ (w - (f ⬝ᵥ w) • w₀) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, hw, smul_eq_mul, mul_one, sub_self]
    have h1 := hx _ hw'
    rw [add_mulVec, one_mulVec, vmv_mulVec, smul_sub]
    have : w = (w - (f ⬝ᵥ w) • w₀) + (f ⬝ᵥ w) • w₀ := by abel
    conv_lhs => rw [this]
    rw [mulVec_add, h1, mulVec_smul]
    abel
  ext i j
  have := congr_fun (h (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

theorem conj_mem {m : ℕ} (f : Fin m → F) (z x : GL (Fin m) F) :
    z⁻¹ * x * z ∈ fixSet (f ᵥ* (z : Matrix (Fin m) (Fin m) F)) ↔ x ∈ fixSet f := by
  have hzz : (z : Matrix (Fin m) (Fin m) F) * ((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hzz' : ((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * (z : Matrix (Fin m) (Fin m) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  constructor
  · intro h w hw
    have hw' : (f ᵥ* (z : Matrix (Fin m) (Fin m) F)) ⬝ᵥ (((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ w) = 0 := by
      rw [← dotProduct_mulVec, mulVec_mulVec, hzz, one_mulVec, hw]
    have := h _ hw'
    have hzw : (z : Matrix (Fin m) (Fin m) F) *ᵥ (((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ w) = w := by
      rw [mulVec_mulVec, hzz, one_mulVec]
    simp only [Units.val_mul] at this
    rw [← mulVec_mulVec, ← mulVec_mulVec, hzw] at this
    have hzv : ∀ v, (z : Matrix (Fin m) (Fin m) F) *ᵥ (((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ v) = v := by
      intro v; rw [mulVec_mulVec, hzz, one_mulVec]
    have := congrArg (fun v => (z : Matrix (Fin m) (Fin m) F) *ᵥ v) this
    simpa only [hzv] using this
  · intro h w hw
    rw [← dotProduct_mulVec] at hw
    simp only [Units.val_mul]
    rw [← mulVec_mulVec, ← mulVec_mulVec, h _ hw, mulVec_mulVec, hzz', one_mulVec]

theorem sum_conj {m : ℕ} [Fintype (GL (Fin m) F)] (f : Fin m → F) (z : GL (Fin m) F) (φ : GL (Fin m) F → ℂ) :
    (∑ x, if x ∈ fixSet f then φ (z⁻¹ * x * z) else 0) =
      ∑ g, if g ∈ fixSet (f ᵥ* (z : Matrix (Fin m) (Fin m) F)) then φ g else 0 := by
  refine Fintype.sum_equiv (MulAut.conj z⁻¹).toEquiv _ _ fun x => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
  rw [conj_mem]

end GlobalTheory.Shin.FreeHc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneFixerSumVanishesHarishChandraInduction

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.Shin.FreeHc

variable {F : Type} [Field F]

theorem avg {G H : Type} [Group G] [Fintype G] [Fintype H] (S : Subgroup G) (T : Set H) (hT : T.Nonempty)
    (ψ : H → G) (hψ : ∀ u ∈ T, ψ u ∈ S) (φ : G → ℂ)
    (h : ∀ g ∈ S, (∑ u, if u ∈ T then φ (g * ψ u) else 0) = 0) :
    (∑ g, if g ∈ S then φ g else 0) = 0 := by
  have h1 : ∀ u ∈ T, (∑ g, if g ∈ S then φ (g * ψ u) else 0) = ∑ g, if g ∈ S then φ g else 0 :=
    fun u hu => Fintype.sum_equiv (Equiv.mulRight (ψ u)) _ _ (fun g => by
      simp [Subgroup.mul_mem_cancel_right S (hψ u hu)])
  have h2 : (∑ u, if u ∈ T then (∑ g, if g ∈ S then φ g else 0) else 0) = 0 := by
    calc _ = ∑ u, ∑ g, (if u ∈ T then (if g ∈ S then φ (g * ψ u) else 0) else 0) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            by_cases hu : u ∈ T
            · simp only [hu, if_true]; exact (h1 u hu).symm
            · simp [hu]
      _ = ∑ g, ∑ u, (if u ∈ T then (if g ∈ S then φ (g * ψ u) else 0) else 0) := Finset.sum_comm
      _ = 0 := by
            refine Finset.sum_eq_zero fun g _ => ?_
            by_cases hg : g ∈ S
            · simpa [hg] using h g hg
            · simp [hg]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at h2
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exfalso
    obtain ⟨u, hu⟩ := hT
    have : (Finset.univ.filter (· ∈ T)).card ≠ 0 :=
      Finset.card_ne_zero.2 ⟨u, by simp [hu]⟩
    exact this (by exact_mod_cast h3)
  · exact h3

theorem sub_sum {G : Type} [Group G] [Fintype G] (H : Subgroup G) (χ : G → ℂ) :
    ∑ᶠ u : H, χ u = ∑ g, if g ∈ H then χ g else 0 := by
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) χ).symm

theorem hyp_eq {m : ℕ} (hm : 0 < m) :
    {x : GL (Fin m) F | ∀ i j : Fin m, (j : ℕ) + 1 < m →
      (x : Matrix (Fin m) (Fin m) F) i j = (1 : Matrix (Fin m) (Fin m) F) i j} = fixSet (eLast m hm) := by
  ext x
  simp only [Set.mem_ofPred_eq, fixSet, eLast, single_dotProduct, one_mul]
  constructor
  · intro h w hw
    ext i
    simp only [mulVec, dotProduct]
    rw [show w i = ∑ j, (1 : Matrix (Fin m) (Fin m) F) i j * w j by simp [Matrix.one_apply]]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : (j : ℕ) + 1 < m
    · rw [h i j hj]
    · have : j = ⟨m - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [this, hw]
      simp
  · intro h i j hj
    have hne : (⟨m - 1, by omega⟩ : Fin m) ≠ j := by
      intro h'; rw [← h'] at hj; simp at hj; omega
    have := congrFun (h (Pi.single j 1) (by rw [Pi.single_eq_of_ne hne])) i
    simpa [mulVec_single_one, Matrix.one_apply, Pi.single_apply] using this

theorem exists_row {m : ℕ} (hm : 0 < m) (f : Fin m → F) (hf : f ≠ 0) :
    ∃ z : GL (Fin m) F, eLast m hm ᵥ* (z : Matrix (Fin m) (Fin m) F) = f := by
  have he : eLast (F := F) m hm ≠ 0 := by
    intro h
    have := congrFun h ⟨m - 1, by omega⟩
    simp [eLast] at this
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.toSpanNonzeroSingleton F (Fin m → F) (eLast m hm) he).symm.trans
      (LinearEquiv.toSpanNonzeroSingleton F (Fin m → F) f hf))
  have h1 := hg ⟨eLast m hm, Submodule.mem_span_singleton_self _⟩
  rw [← LinearEquiv.toSpanNonzeroSingleton_one F (Fin m → F) (eLast m hm) he, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.toSpanNonzeroSingleton_one,
    LinearEquiv.toSpanNonzeroSingleton_one] at h1
  set M := LinearMap.toMatrix' g.toLinearMap with hM
  set N := LinearMap.toMatrix' g.symm.toLinearMap with hN
  have hMN : M * N = 1 := by rw [hM, hN, ← LinearMap.toMatrix'_comp]; simp
  have hNM : N * M = 1 := by rw [hM, hN, ← LinearMap.toMatrix'_comp]; simp
  refine ⟨⟨Mᵀ, Nᵀ, by rw [← transpose_mul, hNM, transpose_one], by rw [← transpose_mul, hMN, transpose_one]⟩, ?_⟩
  show eLast m hm ᵥ* Mᵀ = f
  rw [vecMul_transpose, hM, LinearMap.toMatrix'_mulVec]
  exact h1.symm

theorem transfer {m : ℕ} [Fintype (GL (Fin m) F)] (Y : GL (Fin m) F → ℂ) (hY : ∀ x y, Y (y⁻¹ * x * y) = Y x)
    (hfree : HFree Y) (f : Fin m → F) (hf : f ≠ 0) : (∑ x, if x ∈ fixSet f then Y x else 0) = 0 := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; exact absurd (_root_.funext fun (i : Fin 0) => Fin.elim0 i) hf
    · exact h
  obtain ⟨z, hz⟩ := exists_row hm f hf
  rw [← hz, ← sum_conj (eLast m hm) z Y]
  simp only [hY]
  rw [← finsum_mem_eq, ← hyp_eq hm]
  exact hfree hm

theorem detOne {m : ℕ} (u v : Fin m → F) : (1 + vecMulVec u v).det = 1 + v ⬝ᵥ u := by
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]

theorem toG_val {m : ℕ} (u : GL (Fin m) F) : toG (u : Matrix (Fin m) (Fin m) F) = u := by
  unfold toG
  rw [dite_eq_left u.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

theorem toG_coe {m : ℕ} (M : Matrix (Fin m) (Fin m) F) (h : IsUnit M) : ((toG M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = M := by
  unfold toG
  rw [dite_eq_left h]
  exact IsUnit.unit_spec _

theorem ent_castAdd {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) F) (i j : Fin a) :
    ent M (i : ℕ) (j : ℕ) = M (Fin.castAdd b i) (Fin.castAdd b j) := by
  unfold ent
  rw [dite_eq_left ⟨by omega, by omega⟩]
  rfl

theorem ent_natAdd {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) F) (i j : Fin b) :
    ent M (a + (i : ℕ)) (a + (j : ℕ)) = M (Fin.natAdd a i) (Fin.natAdd a j) := by
  unfold ent
  rw [dite_eq_left ⟨by omega, by omega⟩]
  rfl

theorem exists_dot_one {m : ℕ} (f : Fin m → F) (hf : f ≠ 0) : ∃ w₀ : Fin m → F, f ⬝ᵥ w₀ = 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hf
  refine ⟨Pi.single i (f i)⁻¹, ?_⟩
  rw [dotProduct_single]
  exact mul_inv_cancel₀ hi

theorem sec1 (a b : ℕ) (f : Fin (a + b) → F) (hf : (fun i => f (Fin.castAdd b i)) ≠ 0) :
    ∃ ψ : GL (Fin a) F → GL (Fin (a + b)) F, ∀ u ∈ fixSet (fun i => f (Fin.castAdd b i)),
      ψ u ∈ fixSet f ∧ InPar a (ψ u) ∧ tlG a (ψ u) = u ∧ brG a b (ψ u) = 1 := by
  set fa : Fin a → F := fun i => f (Fin.castAdd b i) with hfa
  obtain ⟨w₀, hw₀⟩ := exists_dot_one fa hf
  let vt : GL (Fin a) F → Fin (a + b) → F := fun u =>
    Fin.append ((u : Matrix (Fin a) (Fin a) F) *ᵥ w₀ - w₀) (0 : Fin b → F)
  refine ⟨fun u => toG (1 + vecMulVec (vt u) f), fun u hu => ?_⟩
  have hkey := key fa w₀ hw₀ u hu
  have hdot : f ⬝ᵥ vt u = fa ⬝ᵥ ((u : Matrix (Fin a) (Fin a) F) *ᵥ w₀ - w₀) := by
    simp [vt, dotProduct, Fin.sum_univ_add, hfa]
  have hunit : IsUnit (1 + vecMulVec (vt u) f) := by
    rw [Matrix.isUnit_iff_isUnit_det, detOne, hdot, ← detOne, ← hkey]
    exact Matrix.isUnits_det_units u
  have hc := toG_coe _ hunit
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    rw [hc, add_mulVec, one_mulVec, vmv_mulVec, hw, zero_smul, add_zero]
  · intro i j hj hi
    obtain ⟨k, rfl⟩ : ∃ k : Fin b, i = Fin.natAdd a k := ⟨⟨i - a, by omega⟩, Fin.ext (by simp; omega)⟩
    have hne : Fin.natAdd a k ≠ j := fun h => by rw [← h] at hj; simp at hj
    rw [hc]
    simp [vt, vecMulVec, Matrix.one_apply, hne]
  · unfold tlG
    conv_rhs => rw [← toG_val u]
    congr 1
    ext i j
    unfold tl
    rw [ent_castAdd, hc]
    conv_rhs => rw [hkey]
    simp [vt, vecMulVec, Matrix.one_apply, hfa]
  · unfold brG
    rw [← toG_val (1 : GL (Fin b) F)]
    congr 1
    ext i j
    unfold br
    rw [ent_natAdd, hc]
    simp [vt, vecMulVec, Matrix.one_apply]

theorem sec2 (a b : ℕ) (f : Fin (a + b) → F) (h0 : (fun i => f (Fin.castAdd b i)) = 0)
    (hf : (fun j => f (Fin.natAdd a j)) ≠ 0) :
    ∃ ψ : GL (Fin b) F → GL (Fin (a + b)) F, ∀ u ∈ fixSet (fun j => f (Fin.natAdd a j)),
      ψ u ∈ fixSet f ∧ InPar a (ψ u) ∧ tlG a (ψ u) = 1 ∧ brG a b (ψ u) = u := by
  set fb : Fin b → F := fun j => f (Fin.natAdd a j) with hfb
  have h0' : ∀ i, f (Fin.castAdd b i) = 0 := fun i => congrFun h0 i
  obtain ⟨w₀, hw₀⟩ := exists_dot_one fb hf
  let vt : GL (Fin b) F → Fin (a + b) → F := fun u =>
    Fin.append (0 : Fin a → F) ((u : Matrix (Fin b) (Fin b) F) *ᵥ w₀ - w₀)
  refine ⟨fun u => toG (1 + vecMulVec (vt u) f), fun u hu => ?_⟩
  have hkey := key fb w₀ hw₀ u hu
  have hdot : f ⬝ᵥ vt u = fb ⬝ᵥ ((u : Matrix (Fin b) (Fin b) F) *ᵥ w₀ - w₀) := by
    simp [vt, dotProduct, Fin.sum_univ_add, hfb]
  have hunit : IsUnit (1 + vecMulVec (vt u) f) := by
    rw [Matrix.isUnit_iff_isUnit_det, detOne, hdot, ← detOne, ← hkey]
    exact Matrix.isUnits_det_units u
  have hc := toG_coe _ hunit
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    rw [hc, add_mulVec, one_mulVec, vmv_mulVec, hw, zero_smul, add_zero]
  · intro i j hj hi
    obtain ⟨k, rfl⟩ : ∃ k : Fin b, i = Fin.natAdd a k := ⟨⟨i - a, by omega⟩, Fin.ext (by simp; omega)⟩
    obtain ⟨l, rfl⟩ : ∃ l : Fin a, j = Fin.castAdd b l := ⟨⟨j, hj⟩, Fin.ext (by simp)⟩
    have hne : Fin.natAdd a k ≠ Fin.castAdd b l := fun h => by
      have := congrArg Fin.val h; simp at this; omega
    rw [hc]
    simp [vecMulVec, Matrix.one_apply, hne, h0']
  · unfold tlG
    rw [← toG_val (1 : GL (Fin a) F)]
    congr 1
    ext i j
    unfold tl
    rw [ent_castAdd, hc]
    simp [vt, vecMulVec, Matrix.one_apply]
  · unfold brG
    conv_rhs => rw [← toG_val u]
    congr 1
    ext i j
    unfold br
    rw [ent_natAdd, hc]
    conv_rhs => rw [hkey]
    simp [vt, vecMulVec, Matrix.one_apply, hfb]

theorem coset_zero {m : ℕ} [Finite F] [Fintype (GL (Fin m) F)] (Y : GL (Fin m) F → ℂ) (hY : IsChar ℂ ℂ Y)
    (hfree : HFree Y) (f : Fin m → F) (hf : f ≠ 0) (c : GL (Fin m) F) :
    (∑ u, if u ∈ fixSet f then Y (c * u) else 0) = 0 := by
  have h0 := transfer Y (fun x y => isChar_conj hY x y) hfree f hf
  have h1 : ∑ᶠ u : fixSub f, Y u = 0 := by
    rw [sub_sum]; exact h0
  have h2 := char_coset_sum_eq_zero (GL (Fin m) F) Y hY (fixSub f) h1 c
  rw [sub_sum (fixSub f) (fun u => Y (c * u))] at h2
  exact h2

theorem core [Finite F] (a b : ℕ) [Fintype (GL (Fin (a + b)) F)] (A : GL (Fin a) F → ℂ) (B : GL (Fin b) F → ℂ)
    (hA : IsChar ℂ ℂ A) (hB : IsChar ℂ ℂ B) (hfA : HFree A) (hfB : HFree B) (f : Fin (a + b) → F) (hf : f ≠ 0) :
    (∑ g, if g ∈ fixSet f then
      (if InPar a g then A (tlG a g) * B (brG a b g) else 0) else 0) = 0 := by
  obtain ⟨P, π, hmem, -, hπ, -, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b (a + b) rfl
  have hmul : ∀ p q : GL (Fin (a + b)) F, InPar a p → InPar a q →
      InPar a (p * q) ∧ tlG a (p * q) = tlG a p * tlG a q ∧ brG a b (p * q) = brG a b p * brG a b q := by
    intro p q hp hq
    have hp' := (hmem p).2 hp
    have hq' := (hmem q).2 hq
    have h := map_mul π ⟨p, hp'⟩ ⟨q, hq'⟩
    rw [hπ, hπ, hπ] at h
    refine ⟨(hmem _).1 (P.mul_mem hp' hq'), ?_, ?_⟩
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have hnot : ∀ p q : GL (Fin (a + b)) F, ¬ InPar a p → InPar a q → ¬ InPar a (p * q) := by
    intro p q hp hq hpq
    apply hp
    have := P.mul_mem ((hmem _).2 hpq) (P.inv_mem ((hmem _).2 hq))
    rw [mul_inv_cancel_right] at this
    exact (hmem _).1 this
  have hS : ∀ g, g ∈ fixSub f ↔ g ∈ fixSet f := fun _ => Iff.rfl
  simp_rw [← hS]
  by_cases h0 : (fun i => f (Fin.castAdd b i)) = 0
  · have hf2 : (fun j => f (Fin.natAdd a j)) ≠ 0 := by
      intro h2
      apply hf
      funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · exact congrFun h0 i
      · exact congrFun h2 j
    obtain ⟨ψ, hψ⟩ := sec2 a b f h0 hf2
    haveI : Fintype (GL (Fin b) F) := Fintype.ofFinite _
    refine avg (fixSub f) (fixSet fun j => f (Fin.natAdd a j)) ⟨1, (fixSub _).one_mem⟩ ψ
      (fun u hu => (hψ u hu).1) _ fun g hg => ?_
    by_cases hpg : InPar a g
    · have : ∀ u, (if u ∈ fixSet (fun j => f (Fin.natAdd a j)) then
          (if InPar a (g * ψ u) then A (tlG a (g * ψ u)) * B (brG a b (g * ψ u)) else 0) else 0) =
          A (tlG a g) * (if u ∈ fixSet (fun j => f (Fin.natAdd a j)) then B (brG a b g * u) else 0) := by
        intro u
        by_cases hu : u ∈ fixSet (fun j => f (Fin.natAdd a j))
        · obtain ⟨-, hp, ht, hb⟩ := hψ u hu
          obtain ⟨h1, h2, h3⟩ := hmul g (ψ u) hpg hp
          simp [hu, h1, h2, h3, ht, hb]
        · simp [hu]
      rw [Finset.sum_congr rfl fun u _ => this u, ← Finset.mul_sum, coset_zero B hB hfB _ hf2, mul_zero]
    · refine Finset.sum_eq_zero fun u _ => ?_
      by_cases hu : u ∈ fixSet (fun j => f (Fin.natAdd a j))
      · simp [hu, hnot g (ψ u) hpg (hψ u hu).2.1]
      · simp [hu]
  · obtain ⟨ψ, hψ⟩ := sec1 a b f h0
    haveI : Fintype (GL (Fin a) F) := Fintype.ofFinite _
    refine avg (fixSub f) (fixSet fun i => f (Fin.castAdd b i)) ⟨1, (fixSub _).one_mem⟩ ψ
      (fun u hu => (hψ u hu).1) _ fun g hg => ?_
    by_cases hpg : InPar a g
    · have : ∀ u, (if u ∈ fixSet (fun i => f (Fin.castAdd b i)) then
          (if InPar a (g * ψ u) then A (tlG a (g * ψ u)) * B (brG a b (g * ψ u)) else 0) else 0) =
          B (brG a b g) * (if u ∈ fixSet (fun i => f (Fin.castAdd b i)) then A (tlG a g * u) else 0) := by
        intro u
        by_cases hu : u ∈ fixSet (fun i => f (Fin.castAdd b i))
        · obtain ⟨-, hp, ht, hb⟩ := hψ u hu
          obtain ⟨h1, h2, h3⟩ := hmul g (ψ u) hpg hp
          simp [hu, h1, h2, h3, ht, hb, mul_comm]
        · simp [hu]
      rw [Finset.sum_congr rfl fun u _ => this u, ← Finset.mul_sum, coset_zero A hA hfA _ h0, mul_zero]
    · refine Finset.sum_eq_zero fun u _ => ?_
      by_cases hu : u ∈ fixSet (fun i => f (Fin.castAdd b i))
      · simp [hu, hnot g (ψ u) hpg (hψ u hu).2.1]
      · simp [hu]

theorem hfree_hc : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (A : GL (Fin a) F → ℂ)
    (B : GL (Fin b) F → ℂ), IsChar ℂ ℂ A → IsChar ℂ ℂ B → HFree A → HFree B → HFree (hc a b A B n) := by
  intro F _ _ a b n hn A B hA hB hfA hfB
  subst hn
  intro hpos
  haveI : Fintype (GL (Fin (a + b)) F) := Fintype.ofFinite _
  rw [hyp_eq hpos, finsum_mem_eq]
  have hgal : ∀ y : GL (Fin (a + b)) F, gal (RingHom.id F) (a + b) y = y := fun y => by
    ext; simp [gal]
  simp only [hc, hcTw, hgal, finsum_eq_sum_of_fintype]
  have : ∀ x : GL (Fin (a + b)) F, (if x ∈ fixSet (eLast (a + b) hpos) then
      (Nat.card {p : GL (Fin (a + b)) F // InPar a p} : ℂ)⁻¹ * ∑ y : GL (Fin (a + b)) F,
        (if InPar a (y⁻¹ * x * y) then A (tlG a (y⁻¹ * x * y)) * B (brG a b (y⁻¹ * x * y)) else 0) else 0) =
      (Nat.card {p : GL (Fin (a + b)) F // InPar a p} : ℂ)⁻¹ * ∑ y : GL (Fin (a + b)) F,
        (if x ∈ fixSet (eLast (a + b) hpos) then
          (if InPar a (y⁻¹ * x * y) then A (tlG a (y⁻¹ * x * y)) * B (brG a b (y⁻¹ * x * y)) else 0) else 0) := by
    intro x
    by_cases hx : x ∈ fixSet (eLast (a + b) hpos) <;> simp [hx]
  rw [Finset.sum_congr rfl fun x _ => this x, ← Finset.mul_sum, Finset.sum_comm]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun y _ => ?_)
  rw [sum_conj (eLast (a + b) hpos) y
    (fun g => if InPar a g then A (tlG a g) * B (brG a b g) else 0)]
  refine core a b A B hA hB hfA hfB _ ?_
  intro h
  have h2 := congrArg (fun v => v ᵥ* ((y⁻¹ : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F)) h
  simp only [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one, zero_vecMul] at h2
  have h3 := congrFun h2 ⟨a + b - 1, by omega⟩
  simp [eLast] at h3

end GlobalTheory.Shin.FreeHc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneFixerSumVanishesHarishChandraInductionStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.hyperplaneFixerSumVanishes_harishChandraInduction : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (A : GL (Fin a) F → ℂ) (B : GL (Fin b) F → ℂ), IsChar ℂ ℂ A → IsChar ℂ ℂ B → HFree A → HFree B → HFree (hc a b A B n) := by
  first | (exact @GlobalTheory.Shin.FreeHc.hfree_hc) | (exact GlobalTheory.Shin.FreeHc.hfree_hc) | (intros; apply GlobalTheory.Shin.FreeHc.hfree_hc  <;> assumption)
end
end
