module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Free
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Topology
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

-- Source module: GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Lattice

section

@[expose] public section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct

noncomputable section

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {R : Type*} [CommRing R] [Algebra K R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

theorem repr_one_tmul (e : E) (m : κ) :
    (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ e) m = algebraMap K R (b.repr e m) := by
  rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]

theorem repr_mul (z w : R ⊗[K] E) (m : κ) :
    (Algebra.TensorProduct.basis R b).repr (z * w) m =
      ∑ k, ∑ l, (Algebra.TensorProduct.basis R b).repr z k *
        (Algebra.TensorProduct.basis R b).repr w l * algebraMap K R (b.repr (b k * b l) m) := by
  set B := Algebra.TensorProduct.basis R b
  conv_lhs => rw [← B.sum_repr z, ← B.sum_repr w]

  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, B,
  Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_sum,
  map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
  repr_one_tmul]
  exact Finset.sum_comm


variable (ι R) in
def stdLattice (O : Subring R) : Set (ι → R ⊗[K] E) :=
  {x | ∀ i k, (Algebra.TensorProduct.basis R b).repr (x i) k ∈ O}


variable {H b}


variable (b) in
def IsAdapted (O : Subring R) : Prop :=
  (∀ k, algebraMap K R (b.repr 1 k) ∈ O) ∧ ∀ k l m, algebraMap K R (b.repr (b k * b l) m) ∈ O

end

end GroundTheory.Automorphic
end
end

-- Source module: GroundTheory.AutomorphicForms.AdelicUnitaryGroups.LatticeCompact

section

@[expose] public section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct Topology

noncomputable section

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable (R : Type*) [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

def vecCoordsHomeomorph : (ι → R ⊗[K] E) ≃ₜ (ι → κ → R) :=
  Homeomorph.piCongrRight fun _ => tensorCoordsHomeomorph R b

theorem stdLattice_eq_preimage (O : Subring R) :
    stdLattice ι R b O = vecCoordsHomeomorph R b ⁻¹'
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (O : Set R) := by
  ext x
  simp only [stdLattice, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
    true_implies, SetLike.mem_coe]
  rfl

theorem isOpen_stdLattice {O : Subring R} (hO : IsOpen (O : Set R)) :
    IsOpen (stdLattice ι R b O) := by
  rw [stdLattice_eq_preimage]
  exact (vecCoordsHomeomorph R b).continuous.isOpen_preimage _
    (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hO)

theorem isCompact_stdLattice {O : Subring R} (hO : IsCompact (O : Set R)) :
    IsCompact (stdLattice ι R b O) := by
  rw [stdLattice_eq_preimage]
  exact (vecCoordsHomeomorph R b).isCompact_preimage.2
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hO)

theorem continuous_unitaryMat_mulVec :
    Continuous fun p : unitaryPoints K E H R × (ι → R ⊗[K] E) => unitaryMat p.1 *ᵥ p.2 := by
  have h1 : Continuous fun p : unitaryPoints K E H R × (ι → R ⊗[K] E) => unitaryMat p.1 :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_fst
  exact h1.matrix_mulVec continuous_snd

section NumberField

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K] {E : Type*} [CommRing E] [Algebra K E]
  [Algebra.IsQuadraticExtension K E] {H : Matrix ι ι E} (b : Basis κ K E)
  (v : HeightOneSpectrum (𝓞 K))

end NumberField

end

end GroundTheory.Automorphic
end
end
