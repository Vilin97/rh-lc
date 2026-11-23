module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorCompactWithinNhdsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComapMulVecCompactOpenStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetSumTranslateInvariantStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactOpenSubgroupMemStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteCosetRepresentativesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGLVecMulEqLastBasisStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSemidefiniteNullRadicalStatement
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Topology.Algebra.Group.Defs
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
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenAdditiveCharacterKernel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenCharacterAnnihilatorStatement
public import Mathlib.GroupTheory.Index
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexOpenCompactNeZero
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupAddSubgroup

section

@[expose] public section

open Matrix
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.Topology

theorem isCompact_addSubgroup_sup : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A B : AddSubgroup X), IsCompact (A : Set X) → IsCompact (B : Set X) → IsCompact ((A ⊔ B : AddSubgroup X) : Set X) := by
  intro X _ _ _ A B hA hB
  have h : ((A ⊔ B : AddSubgroup X) : Set X) = (A : Set X) + (B : Set X) := by
    ext x
    simp only [SetLike.mem_coe, AddSubgroup.mem_sup, Set.mem_add]
  rw [h]
  exact hA.add hB

end GlobalTheory.CompanionTheory.Topology
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupAddSubgroupStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.isCompact_sup_addSubgroup : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A B : AddSubgroup X), IsCompact (A : Set X) → IsCompact (B : Set X) → IsCompact ((A ⊔ B : AddSubgroup X) : Set X) := by
  first | exact @GlobalTheory.CompanionTheory.Topology.isCompact_addSubgroup_sup | exact GlobalTheory.CompanionTheory.Topology.isCompact_addSubgroup_sup | (intros; apply GlobalTheory.CompanionTheory.Topology.isCompact_addSubgroup_sup <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenAdditiveCharacterKernelStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.isOpen_additive_character_kernel : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → IsOpen {x : k | ψ x = 1} := by
  first | exact @GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker | exact GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker | (intros; apply GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexOpenCompactNeZeroStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.relIndex_open_compact_ne_zero : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A H : AddSubgroup X), IsCompact (A : Set X) → IsOpen (H : Set X) → H ≤ A → H.relIndex A ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen | exact GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen | (intros; apply GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SesquilinearEqZeroOfDiagZero

section

@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.Sesquilinear

theorem eq_zero_of_diag_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (h : ∀ v, B v v = 0) : B = 0 := by
  ext v w
  have h1 := h (v + w)
  have h2 := h (v + Complex.I • w)
  simp only [map_add (f := _), LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    h v, h w, smul_eq_mul, zero_add, add_zero, Complex.conj_I, RingHom.id_apply,
    mul_zero] at h1 h2
  have h3 : B v w = B w v := by
    have : Complex.I * (B w v - B v w) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h4 | h4
    · exact absurd h4 Complex.I_ne_zero
    · exact (sub_eq_zero.mp h4).symm
  have h5 : (2 : ℂ) * B v w = 0 := by linear_combination h1 + h3
  simpa using h5

end GlobalTheory.CompanionTheory.Sesquilinear
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SesquilinearEqZeroOfDiagZeroStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.sesquilinear_eq_zero_of_diag_zero : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v, B v v = 0) → B = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero | exact GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.IsotropicAtoms.ChartRestriction

section

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.Form.U.Atom

section Transversal

variable {X : Type} [AddCommGroup X]

theorem sum_transversal_add {M : Type} [AddCommMonoid M] {A H : AddSubgroup X} (hHA : H ≤ A) {T : Finset X}
    (hT : ∀ t ∈ T, t ∈ A) (hTr : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) (F : X → M)
    (hF : ∀ a, ∀ h ∈ H, F (a + h) = F a) {a : X} (ha : a ∈ A) :
    ∑ t ∈ T, F (t + a) = ∑ t ∈ T, F t :=
  GlobalTheory.T.coset_sum_translate_invariant hHA hT hTr F hF ha

theorem card_smul_sum_eq {M : Type} [AddCommGroup M] [Module ℂ M] {A H H' : AddSubgroup X} (hH : H ≤ A) (hH' : H' ≤ A)
    {T T' : Finset X} (hT : ∀ t ∈ T, t ∈ A) (hTr : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (hT' : ∀ t ∈ T', t ∈ A) (hTr' : ∀ a ∈ A, ∃! t, t ∈ T' ∧ a - t ∈ H') (F : X → M)
    (hF : ∀ a, ∀ h ∈ H, F (a + h) = F a) (hF' : ∀ a, ∀ h ∈ H', F (a + h) = F a) :
    (T'.card : ℂ) • ∑ t ∈ T, F t = (T.card : ℂ) • ∑ t ∈ T', F t := by
  have h1 : ∀ s ∈ T', ∑ t ∈ T, F (t + s) = ∑ t ∈ T, F t := fun s hs =>
    sum_transversal_add hH hT hTr F hF (hT' s hs)
  have h2 : ∀ t ∈ T, ∑ s ∈ T', F (s + t) = ∑ s ∈ T', F s := fun t ht =>
    sum_transversal_add hH' hT' hTr' F hF' (hT t ht)
  have e1 : ∑ s ∈ T', ∑ t ∈ T, F (t + s) = T'.card • ∑ t ∈ T, F t := by
    rw [Finset.sum_congr rfl h1, Finset.sum_const]
  have e2 : ∑ t ∈ T, ∑ s ∈ T', F (s + t) = T.card • ∑ s ∈ T', F s := by
    rw [Finset.sum_congr rfl h2, Finset.sum_const]
  have e3 : ∑ s ∈ T', ∑ t ∈ T, F (t + s) = ∑ t ∈ T, ∑ s ∈ T', F (s + t) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [add_comm]
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← e1, ← e2, e3]

theorem sum_transversal_char {A H : AddSubgroup X} (hHA : H ≤ A) {T : Finset X}
    (hT : ∀ t ∈ T, t ∈ A) (hTr : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) (χ : X → ℂ)
    (hχ : ∀ a b, χ (a + b) = χ a * χ b) (hH : ∀ h ∈ H, χ h = 1) {a : X} (ha : a ∈ A) (hne : χ a ≠ 1) :
    ∑ t ∈ T, χ t = 0 := by
  have key := sum_transversal_add hHA hT hTr χ (fun b h hh => by rw [hχ, hH h hh, mul_one]) ha
  simp only [hχ] at key
  rw [← Finset.sum_mul] at key
  have h0 : (∑ t ∈ T, χ t) * (χ a - 1) = 0 := by rw [mul_sub, mul_one, key, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hne

theorem transversal_nonempty {A H : AddSubgroup X} {T : Finset X} (hTr : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) :
    T.Nonempty := by
  obtain ⟨t, ⟨ht, -⟩, -⟩ := hTr 0 A.zero_mem
  exact ⟨t, ht⟩

variable [TopologicalSpace X] [IsTopologicalAddGroup X]

theorem exists_transversal (A H : AddSubgroup X) (hA : IsCompact (A : Set X)) (hH : IsOpen (H : Set X)) (hHA : H ≤ A) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H :=
  GlobalTheory.T.exists_finite_coset_representatives A H hA hH hHA

theorem isCompact_sup (A B : AddSubgroup X) (hA : IsCompact (A : Set X)) (hB : IsCompact (B : Set X)) :
    IsCompact ((A ⊔ B : AddSubgroup X) : Set X) :=
  GlobalTheory.T.isCompact_sup_addSubgroup A B hA hB

theorem relIndex_ne_zero' (A H : AddSubgroup X) (hA : IsCompact (A : Set X)) (hH : IsOpen (H : Set X)) (hHA : H ≤ A) :
    H.relIndex A ≠ 0 :=
  GlobalTheory.T.relIndex_open_compact_ne_zero A H hA hH hHA

end Transversal

section Forms

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem apply_eq_zero_of_isotropic (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hB' : ∀ v, 0 ≤ (B v v).re) (x : V) (hx : (B x x).re = 0) (w : V) : B x w = 0 :=
  GlobalTheory.T.hermitian_semidefinite_null_radical B hB hB' x hx w

theorem eq_zero_of_diag (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : ∀ v, B v v = 0) : B = 0 :=
  GlobalTheory.T.sesquilinear_eq_zero_of_diag_zero B hB

end Forms

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_ker_char (ψ : AddChar k Circle) (hψ : Continuous ψ) : IsOpen {x : k | ψ x = 1} :=
  GlobalTheory.T.isOpen_additive_character_kernel ψ hψ

theorem exists_lat_mem (n : ℕ) (x : Fin n → k) :
    ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧ x ∈ A :=
  GlobalTheory.T.exists_compact_open_subgroup_mem n x

theorem isOpen_ann (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) (A : AddSubgroup (Fin n → k))
    (hA : IsCompact (A : Set (Fin n → k))) : IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} :=
  GlobalTheory.T.isOpen_character_annihilator ψ hψ n A hA

theorem exists_small_ann (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (n : ℕ) (S : Set (Fin n → k))
    (hS : S ∈ nhds (0 : Fin n → k)) : ∃ Ξ : AddSubgroup (Fin n → k), IsCompact (Ξ : Set (Fin n → k)) ∧
      ∀ t : Fin n → k, (∀ ξ ∈ Ξ, ψ (ξ ⬝ᵥ t) = 1) → t ∈ S :=
  GlobalTheory.T.annihilator_compact_within_nhds ψ hψ hψ1 n S hS

theorem comap_lat (n : ℕ) (g : Matrix (Fin n) (Fin n) k) (hg : IsUnit g) (A : AddSubgroup (Fin n → k))
    (hA : IsCompact (A : Set (Fin n → k))) (hA' : IsOpen (A : Set (Fin n → k))) :
    IsCompact ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) ∧
      IsOpen ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) :=
  GlobalTheory.T.isCompact_isOpen_comap_mulVecLin n g hg A hA hA'

end Local

theorem exists_GL_vecMul {k : Type} [Field k] (n : ℕ) (ξ : Fin (n + 1) → k) (hξ : ξ ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k, Matrix.vecMul ξ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = Pi.single (Fin.last n) 1 :=
  GlobalTheory.T.exists_GL_vecMul_eq_last_basis n ξ hξ

end PositivityTheory.RgUd.Form.U.Atom
end
end
end
