module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CayleyHamilton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralLinearFormPiMatrixEqSumTraceStatement
public import Mathlib.LinearAlgebra.Matrix.Trace
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
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLinearExtension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Idempotents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAndIsSemisimpleRingOfNoNilIdealsBoundedIde
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PseudoCharacterApplyIdempotentNatLeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PseudoCharacterEqZeroOfIsNilpotentStatement
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgHomTraceEqSumMultTrace

section

@[expose] public section

namespace GlobalTheory

open Matrix

noncomputable def blockDiagMultAlgHom (k : Type) [Field k] (N : ℕ) (n m : Fin N → ℕ) :
    (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₐ[k]
      Matrix (Σ j : (Σ i, Fin (m i)), Fin (n j.1)) (Σ j : (Σ i, Fin (m i)), Fin (n j.1)) k where
  toFun x := blockDiagonal' (fun j : (Σ i, Fin (m i)) => x j.1)
  map_one' := by
    show blockDiagonal' (fun j : (Σ i, Fin (m i)) => (1 : Matrix (Fin (n j.1)) (Fin (n j.1)) k)) = 1
    exact blockDiagonal'_one
  map_mul' x y := by
    simp only [Pi.mul_apply]
    exact blockDiagonal'_mul _ _
  map_zero' := by
    show blockDiagonal' (fun j : (Σ i, Fin (m i)) => (0 : Matrix (Fin (n j.1)) (Fin (n j.1)) k)) = 0
    exact blockDiagonal'_zero
  map_add' x y := by
    simp only [Pi.add_apply]
    exact (blockDiagonal'_add _ _)
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    simp only [Pi.smul_apply, Pi.one_apply]
    rw [show (fun j : (Σ i, Fin (m i)) => r • (1 : Matrix (Fin (n j.1)) (Fin (n j.1)) k))
        = r • (fun j => 1) from rfl, blockDiagonal'_smul]
    congr 1
    exact blockDiagonal'_one

theorem blockDiagMultAlgHom_trace (k : Type) [Field k] (N : ℕ) (n m : Fin N → ℕ)
    (x : Π i, Matrix (Fin (n i)) (Fin (n i)) k) :
    (blockDiagMultAlgHom k N n m x).trace = ∑ i, (m i : k) * (x i).trace := by
  show (blockDiagonal' (fun j : (Σ i, Fin (m i)) => x j.1)).trace = _
  rw [trace_blockDiagonal', Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ∑ _y : Fin (m i), (x i).trace = _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem exists_algHom_trace_eq_sum_mult_trace : ∀ (k : Type) [Field k] (N : ℕ) (n m : Fin N → ℕ) (d : ℕ),
    ∑ i, m i * n i = d → ∃ ρ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₐ[k] Matrix (Fin d) (Fin d) k,
      ∀ x, (ρ x).trace = ∑ i, (m i : k) * (x i).trace := by
  intro k _ N n m d hd
  have hcard : Fintype.card (Σ j : (Σ i, Fin (m i)), Fin (n j.1)) = d := by
    rw [Fintype.card_sigma, Fintype.sum_sigma, ← hd]
    simp [mul_comm]
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨(reindexAlgEquiv k k e).toAlgHom.comp (blockDiagMultAlgHom k N n m), fun x => ?_⟩
  rw [← blockDiagMultAlgHom_trace]
  show (reindex e e (blockDiagMultAlgHom k N n m x)).trace = _
  simp only [reindex_apply, trace, diag, submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => blockDiagMultAlgHom k N n m x i i)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgHomTraceEqSumMultTraceStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_algHom_trace_eq_sum_mul_trace : ∀ (k : Type) [Field k] (N : ℕ) (n m : Fin N → ℕ) (d : ℕ), ∑ i, m i * n i = d → ∃ ρ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₐ[k] Matrix (Fin d) (Fin d) k, ∀ x, (ρ x).trace = ∑ i, (m i : k) * (x i).trace := by
  first | exact @GlobalTheory.exists_algHom_trace_eq_sum_mult_trace | exact GlobalTheory.exists_algHom_trace_eq_sum_mult_trace | (intros; apply GlobalTheory.exists_algHom_trace_eq_sum_mult_trace <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAndIsSemisimpleRingOfNoNilIdealsBoundedIdeStatement

section

@[expose] public section

open Formalism.MainNotions.N GlobalTheory.PsChar

theorem _root_.GlobalTheory.T.finite_and_isSemisimpleRing_of_no_nil_ideals_bounded_idempotents : ∀ (k R : Type) [Field k] [IsAlgClosed k] [Ring R] [Algebra k R] (d : ℕ), (∀ x : R, IsIntegral k x) → (∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0) → (∀ (m : ℕ) (e : Fin m → R), OrthogonalIdempotents e → (∀ i, e i ≠ 0) → m ≤ d) → Module.Finite k R ∧ IsSemisimpleRing R := by
  first | exact @GlobalTheory.AlgRing.finite_and_isSemisimpleRing | exact GlobalTheory.AlgRing.finite_and_isSemisimpleRing | (intros; apply GlobalTheory.AlgRing.finite_and_isSemisimpleRing <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemisimpleRepOfIsSemisimpleRingRange

section

@[expose] public section

open Formalism.MainNotions.N

namespace GlobalTheory

theorem isSSRep_of_isSemisimpleRing_range :
    ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin d) (Fin d) k),
      IsSemisimpleRing ρ.range → IsSSRep ((ρ.toMonoidHom.comp (MonoidAlgebra.of k Γ)).toHomUnits) := by
  intro Γ k _ _ d ρ hss W hW

  have hB : ∀ x : MonoidAlgebra k Γ, ∀ v ∈ W, (ρ x).mulVec v ∈ W := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g => intro v hv; exact hW g v hv
    | add x y hx hy =>
      intro v hv; rw [map_add (f := _), Matrix.add_mulVec]; exact W.add_mem (hx v hv) (hy v hv)
    | smul c x hx =>
      intro v hv; rw [map_smul, Matrix.smul_mulVec]; exact W.smul_mem c (hx v hv)
  let WB : Submodule ρ.range (Fin d → k) :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := by
        rintro ⟨b, x, rfl⟩ v hv
        exact hB x v hv }
  have hWB : WB.restrictScalars k = W := by ext v; rfl
  obtain ⟨WB', hc⟩ := exists_isCompl WB
  refine ⟨WB'.restrictScalars k, ?_, ?_⟩
  · intro g v hv
    have hmem : ρ (MonoidAlgebra.of k Γ g) ∈ ρ.range := ⟨_, rfl⟩
    exact WB'.smul_mem ⟨_, hmem⟩ hv
  · rw [← hWB]
    exact hc.map (Submodule.restrictScalarsLatticeHom k ρ.range (Fin d → k))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemisimpleRepOfIsSemisimpleRingRangeStatement

section

@[expose] public section

open Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.isSemisimpleRep_of_isSemisimpleRing_range : ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin d) (Fin d) k), IsSemisimpleRing ρ.range → IsSSRep ((ρ.toMonoidHom.comp (MonoidAlgebra.of k Γ)).toHomUnits) := by
  first | exact @GlobalTheory.isSSRep_of_isSemisimpleRing_range | exact GlobalTheory.isSSRep_of_isSemisimpleRing_range | (intros; apply GlobalTheory.isSSRep_of_isSemisimpleRing_range <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple

section

@[expose] public section

open Formalism.MainNotions.N GlobalTheory.PsChar

namespace GlobalTheory.PsChar

theorem finite_semisimple (k R : Type) [Field k] [CharZero k] [IsAlgClosed k] [Ring R] [Algebra k R]
    (d : ℕ) (T : R →ₗ[k] k) (h : IsPsChar d (fun x => T x))
    (hnd : ∀ x, (∀ y, T (x * y) = 0) → x = 0) :
    Module.Finite k R ∧ IsSemisimpleRing R := by
  refine GlobalTheory.T.finite_and_isSemisimpleRing_of_no_nil_ideals_bounded_idempotents k R d (fun x => ?_) (fun x hx => ?_) (fun m e he hne => ?_)
  · obtain ⟨p, hp, -, hT⟩ := cayleyHamilton k R d T h x
    exact ⟨p, hp, hnd _ hT⟩
  · refine hnd x fun y => ?_
    rw [show T (x * y) = T (y * x) from h.comm x y]
    exact GlobalTheory.T.pseudoCharacter_eq_zero_of_isNilpotent k R d T h _ (hx y)
  · have hv : ∀ i, ∃ a : ℕ, 1 ≤ a ∧ T (e i) = a := fun i => by
      obtain ⟨⟨a, -, ha⟩, h0⟩ := GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le k R d T h (e i) (he.idem i)
      refine ⟨a, Nat.one_le_iff_ne_zero.2 fun h' => hne i (hnd _ (h0 ?_)), ha⟩
      rw [ha, h', Nat.cast_zero]
    choose a ha1 ha using hv
    obtain ⟨⟨s, hs, hsT⟩, -⟩ := GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le k R d T h (∑ i, e i) he.isIdempotentElem_sum
    have h1 : ((∑ i, a i : ℕ) : k) = s := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hsT, map_sum]; push_cast; exact Finset.sum_congr rfl fun i _ => (ha i).symm
    have h2 : ∑ i, a i = s := by exact_mod_cast h1
    calc m = ∑ _i : Fin m, 1 := by simp
      _ ≤ ∑ i, a i := Finset.sum_le_sum fun i _ => ha1 i
      _ = s := h2
      _ ≤ d := hs

def traceKer {k A : Type} [Field k] [Ring A] [Algebra k A] (T : A →ₗ[k] k)
    (hc : ∀ x y, T (x * y) = T (y * x)) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' {x | ∀ y, T (x * y) = 0} (by simp)
    (fun {x y} hx hy z => by simp only [Set.mem_setOf_eq] at hx hy; simp [add_mul, hx z, hy z])
    (fun {x} hx z => by simp only [Set.mem_setOf_eq] at hx; simp [neg_mul, hx z])
    (fun {x y} hy z => by
      simp only [Set.mem_setOf_eq] at hy
      rw [mul_assoc, hc, mul_assoc, hy])
    (fun {x y} hx z => by simp only [Set.mem_setOf_eq] at hx; rw [mul_assoc, hx])

theorem mem_traceKer {k A : Type} [Field k] [Ring A] [Algebra k A] (T : A →ₗ[k] k)
    (hc : ∀ x y, T (x * y) = T (y * x)) (x : A) : x ∈ traceKer T hc ↔ ∀ y, T (x * y) = 0 :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ x

theorem exists_descend {k A B : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup B]
    [Module k B] (f : A →ₗ[k] B) (hf : Function.Surjective f) (T : A →ₗ[k] k)
    (h : ∀ a, f a = 0 → T a = 0) : ∃ S : B →ₗ[k] k, ∀ a, S (f a) = T a := by
  refine ⟨(LinearMap.ker f).liftQ T (fun a ha => h a ha) ∘ₗ (f.quotKerEquivOfSurjective hf).symm.toLinearMap,
    fun a => ?_⟩
  have : (f.quotKerEquivOfSurjective hf).symm (f a) = Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this]
  exact Submodule.liftQ_apply _ _ _

theorem exists_ssRep (Γ k : Type) [Group Γ] [Field k] [CharZero k] [IsAlgClosed k] (d : ℕ)
    (T : Γ → k) (hT : IsPsChar d T) :
    ∃ r : Γ →* GL (Fin d) k, IsSSRep r ∧
      ∀ g, ((r g : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).trace = T g := by
  obtain ⟨T', hT'g, hT'⟩ := exists_linear_extension Γ k d T hT
  have hc : ∀ x y, T' (x * y) = T' (y * x) := hT'.comm
  let I := traceKer T' hc
  let f : MonoidAlgebra k Γ →ₐ[k] I.ringCon.Quotient := RingCon.mkₐ k I.ringCon
  have hf : Function.Surjective f := fun y => Quotient.inductionOn' y fun x => ⟨x, rfl⟩
  have hk : ∀ x, f x = 0 ↔ x ∈ I := fun x => by
    rw [TwoSidedIdeal.mem_iff, ← RingCon.eq]
    rfl
  obtain ⟨S, hS⟩ := exists_descend f.toLinearMap hf T' fun a ha => by
    simpa using (mem_traceKer T' hc a).1 ((hk a).1 ha) 1
  have hS1 : ∀ a, S (f a) = T' a := hS
  have hS' : IsPsChar d (fun x => S x) := by
    refine ⟨?_, ?_, ?_⟩
    · show S 1 = d
      rw [← map_one f, hS1]; exact hT'.one
    · intro x y
      obtain ⟨a, rfl⟩ := hf x
      obtain ⟨b, rfl⟩ := hf y
      show S (f a * f b) = S (f b * f a)
      rw [← map_mul, ← map_mul, hS1, hS1]; exact hc a b
    · intro x
      choose a ha using fun i => hf (x i)
      have hx : x = fun i => (f : MonoidAlgebra k Γ →* I.ringCon.Quotient) (a i) := funext fun i => (ha i).symm
      rw [hx, alt_comp_monoidHom]
      have he : (fun g => S ((f : MonoidAlgebra k Γ →* I.ringCon.Quotient) g)) = fun g => T' g :=
        funext fun g => hS1 g
      rw [he]; exact hT'.alt_eq_zero a
  have hnd : ∀ x, (∀ y, S (x * y) = 0) → x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := hf x
    refine (hk a).2 ((mem_traceKer T' hc a).2 fun b => ?_)
    rw [← hS1, map_mul]; exact hx (f b)
  obtain ⟨hfin, hss⟩ := finite_semisimple k _ d S hS' hnd
  obtain ⟨N, n, hn, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k I.ringCon.Quotient
  let τ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₗ[k] k := S ∘ₗ e.symm.toLinearMap
  have hτ : ∀ x, τ x = S (e.symm x) := fun x => rfl
  obtain ⟨c, hcτ⟩ := GlobalTheory.T.exists_eq_sum_trace_of_trace_like_pi_matrix k N n τ fun x y => by
    rw [hτ, hτ, map_mul e.symm, map_mul e.symm]; exact hS'.comm _ _
  have hcn : ∀ i, ∃ m : ℕ, c i = m := by
    intro i
    haveI := hn i
    let E : Π j, Matrix (Fin (n j)) (Fin (n j)) k := Pi.single i (Matrix.single 0 0 1)
    have hE : IsIdempotentElem E := by
      unfold IsIdempotentElem
      ext1 j
      by_cases hj : j = i
      · subst hj; simp [E, Matrix.single_mul_single_same]
      · simp [E, hj]
    have hτE : τ E = c i := by
      rw [hcτ, Finset.sum_eq_single i]
      · simp [E, Matrix.trace_single_eq_same]
      · intro j _ hj; simp [E, hj]
      · simp
    obtain ⟨⟨m, -, hm⟩, -⟩ := GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le k _ d S hS' (e.symm E) (hE.map e.symm)
    exact ⟨m, hτE.symm.trans hm⟩
  choose m hm using hcn
  have hsum : ∑ i, m i * n i = d := by
    have h1 : τ 1 = d := by rw [hτ, map_one]; exact hS'.one
    rw [hcτ] at h1
    simp only [Pi.one_apply, Matrix.trace_one, Fintype.card_fin, hm] at h1
    exact_mod_cast h1
  obtain ⟨ρ₀, hρ₀⟩ := GlobalTheory.T.exists_algHom_trace_eq_sum_mul_trace k N n m d hsum
  let g : I.ringCon.Quotient →ₐ[k] Matrix (Fin d) (Fin d) k := ρ₀.comp e.toAlgHom
  let ρ : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin d) (Fin d) k := g.comp f
  have htr : ∀ a, (ρ a).trace = T' a := fun a => by
    show (ρ₀ (e (f a))).trace = _
    rw [hρ₀, ← hS1, ← e.symm_apply_apply (f a), ← hτ, hcτ]
    simp [hm]
  have hrange : IsSemisimpleRing ρ.range := by
    have : ρ.range = g.range := by
      rw [AlgHom.range_comp, (AlgHom.range_eq_top f).2 hf, Algebra.map_top]
    rw [this]
    exact RingHom.isSemisimpleRing_of_surjective g.rangeRestrict.toRingHom
      (AlgHom.rangeRestrict_surjective _)
  refine ⟨(ρ.toMonoidHom.comp (MonoidAlgebra.of k Γ)).toHomUnits, GlobalTheory.T.isSemisimpleRep_of_isSemisimpleRing_range Γ k d ρ hrange,
    fun x => ?_⟩
  show (ρ (MonoidAlgebra.of k Γ x)).trace = T x
  rw [htr, hT'g]

end GlobalTheory.PsChar
end
end
