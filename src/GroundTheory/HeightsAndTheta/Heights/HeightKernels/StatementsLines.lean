module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder

noncomputable section

def stdLattice (K : Type*) [Field K] (k : ℕ) : Submodule (𝓞 K) (Fin k → K) :=
  Submodule.span (𝓞 K) (Set.range fun j : Fin k => (Pi.single j 1 : Fin k → K))

def stdSumBasis (K : Type*) [Field K] (m k : ℕ) : Module.Basis (Fin m ⊕ Fin k) K (Fin (m + k) → K) :=
  (Pi.basisFun K (Fin (m + k))).reindex finSumFinEquiv.symm

def LinesLatticeBasis.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (ι : Type) [Fintype ι],
    Fintype.card ι = Module.finrank ℚ V → ∀ M : Submodule ℤ V, Submodule.IsLattice ℚ M →
      ∃ b : Module.Basis ι ℚ V, M = Submodule.span ℤ (Set.range b)

def LinesGenIndexDet.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (ι : Type) [Fintype ι]
    [DecidableEq ι] (bA bB : Module.Basis ι ℚ V) (A B : AddSubgroup V),
    A = AddSubgroup.closure (Set.range bA) → B = AddSubgroup.closure (Set.range bB) →
      genIndex A B = |((bA.det bB : ℚ) : ℝ)|

def LinesIsLattice.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (M : Submodule (𝓞 K) (ι → K)),
    (M.restrictScalars ℤ).FG → Submodule.span K (M : Set (ι → K)) = ⊤ →
      Submodule.IsLattice ℚ (M.restrictScalars ℤ)

def LinesGenIndexTrans.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (A B C : Submodule ℤ V),
    Submodule.IsLattice ℚ A → Submodule.IsLattice ℚ B → Submodule.IsLattice ℚ C →
      0 < genIndex A.toAddSubgroup B.toAddSubgroup ∧
        genIndex A.toAddSubgroup B.toAddSubgroup * genIndex B.toAddSubgroup C.toAddSubgroup =
          genIndex A.toAddSubgroup C.toAddSubgroup

def LinesIdealLatticeFG.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K),
    (∀ x, a x ≠ 0) →
      (idealLattice a).FG ∧ Submodule.span K (idealLattice a : Set (Fin n → K)) = ⊤

theorem stdSumBasis_inl (K : Type*) [Field K] (m k : ℕ) (i : Fin m) :
    stdSumBasis K m k (Sum.inl i) = Pi.single (Fin.castAdd k i) 1 := by
  simp [stdSumBasis]

theorem stdSumBasis_inr (K : Type*) [Field K] (m k : ℕ) (j : Fin k) :
    stdSumBasis K m k (Sum.inr j) = Pi.single (Fin.natAdd m j) 1 := by
  simp [stdSumBasis]

theorem stdSumBasis_elim (K : Type*) [Field K] (m k : ℕ) :
    Sum.elim (fun i => stdSumBasis K m k (Sum.inl i)) (fun j => stdSumBasis K m k (Sum.inr j)) =
      ⇑(stdSumBasis K m k) := by
  funext x; cases x <;> rfl

theorem stdLattice_isLattice_example :
    Submodule.IsLattice ℚ ((stdLattice ℚ 1).restrictScalars ℤ) :=
  Submodule.IsLattice.of_fg ℚ ((Submodule.fg_span (Set.finite_range _)).restrictScalars)

end

end GroundTheory.Heights₂.Heights
