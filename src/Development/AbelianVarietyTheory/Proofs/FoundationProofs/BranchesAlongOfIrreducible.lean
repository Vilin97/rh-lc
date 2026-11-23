module

public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroMapEqZeroOfWeightNe
public import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCassemLemmas
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankLeFinrankDirectSumBelow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InitMinorNeZeroOfStrictMono
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwiningGlOfUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankIntertwiningMapDirectSum

section

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.IntertwinerSum

open Representation

variable {k G ι U W : Type} [Field k] [Group G] [Fintype ι] {V : ι → Type}
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [AddCommGroup U] [Module k U]
  [AddCommGroup W] [Module k W]

theorem finite_intertwiningMap [FiniteDimensional k U] [FiniteDimensional k W]
    (τ : Representation k G U) (σ : Representation k G W) :
    FiniteDimensional k (τ.IntertwiningMap σ) :=
  FiniteDimensional.of_injective
    ({ toFun := fun f => f.toLinearMap
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : τ.IntertwiningMap σ →ₗ[k] (U →ₗ[k] W))
    (IntertwiningMap.toLinearMap_injective τ σ)

theorem equivs_of_biproduct (ρ : ∀ i, Representation k G (V i)) (τ : Representation k G U)
    (σ : Representation k G W) (p : ∀ i, σ.IntertwiningMap (ρ i))
    (j : ∀ i, (ρ i).IntertwiningMap σ) (hsum : ∀ w, ∑ i, j i (p i w) = w)
    (hdiag : ∀ i x, p i (j i x) = x) (hoff : ∀ i i', i' ≠ i → ∀ x, p i (j i' x) = 0) :
    Nonempty (τ.IntertwiningMap σ ≃ₗ[k] ∀ i, τ.IntertwiningMap (ρ i)) ∧
      Nonempty (σ.IntertwiningMap τ ≃ₗ[k] ∀ i, (ρ i).IntertwiningMap τ) := by
  classical
  refine ⟨⟨{ toFun := fun f i => (p i).comp f
             map_add' := fun f g => ?_
             map_smul' := fun c f => ?_
             invFun := fun f => ∑ i, (j i).comp (f i)
             left_inv := fun f => ?_
             right_inv := fun f => ?_ }⟩,
          ⟨{ toFun := fun f i => f.comp (j i)
             map_add' := fun f g => rfl
             map_smul' := fun c f => rfl
             invFun := fun f => ∑ i, (f i).comp (p i)
             left_inv := fun f => ?_
             right_inv := fun f => ?_ }⟩⟩
  · funext i
    exact DFunLike.ext _ _ fun u => map_add (p i) (f u) (g u)
  · funext i
    exact DFunLike.ext _ _ fun u => map_smul (p i) c (f u)
  · refine DFunLike.ext _ _ fun u => ?_
    rw [IntertwiningMap.sum_apply]
    exact hsum (f u)
  · funext i
    refine DFunLike.ext _ _ fun u => ?_

    rw [IntertwiningMap.comp_apply, IntertwiningMap.sum_apply, map_sum]
    simp only [IntertwiningMap.comp_apply]
    rw [Finset.sum_eq_single i (fun i' _ h => hoff i i' h _) (by simp)]
    exact hdiag i _
  · refine DFunLike.ext _ _ fun w => ?_
    rw [IntertwiningMap.sum_apply]
    simp only [IntertwiningMap.comp_apply]

    rw [← map_sum, hsum]
  · funext i
    refine DFunLike.ext _ _ fun x => ?_
    rw [IntertwiningMap.comp_apply, IntertwiningMap.sum_apply]
    simp only [IntertwiningMap.comp_apply]
    rw [Finset.sum_eq_single i (fun i' _ h => by rw [hoff i' i h.symm, map_zero]) (by simp), hdiag]

theorem finrank_intertwiningMap_directSum :
    ∀ (k G ι U W : Type) [Field k] [Group G] [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] [AddCommGroup U] [Module k U] [FiniteDimensional k U] [AddCommGroup W] [Module k W] (ρ : ∀ i, Representation k G (V i)) (τ : Representation k G U) (σ : Representation k G W), Nonempty ((Representation.directSum ρ).Equiv σ) → Module.finrank k (τ.IntertwiningMap σ) = ∑ i, Module.finrank k (τ.IntertwiningMap (ρ i)) ∧ Module.finrank k (σ.IntertwiningMap τ) = ∑ i, Module.finrank k ((ρ i).IntertwiningMap τ) := by
  intro k G ι U W _ _ _ V _ _ _ _ _ _ _ _ ρ τ σ ⟨e⟩
  classical
  let p₀ : ∀ i, (Representation.directSum ρ).IntertwiningMap (ρ i) := fun i =>
    { toLinearMap := DirectSum.component k ι V i
      isIntertwining' := fun g => by
        refine LinearMap.ext fun x => ?_
        rfl }
  let j₀ : ∀ i, (ρ i).IntertwiningMap (Representation.directSum ρ) := fun i =>
    { toLinearMap := DirectSum.lof k ι V i
      isIntertwining' := fun g => by
        refine LinearMap.ext fun x => ?_
        simp [Representation.directSum] }
  have hse : ∀ x, e.symm.toIntertwiningMap (e.toIntertwiningMap x) = x :=
    fun x => e.toLinearEquiv.symm_apply_apply x
  have hes : ∀ x, e.toIntertwiningMap (e.symm.toIntertwiningMap x) = x :=
    fun x => e.toLinearEquiv.apply_symm_apply x
  obtain ⟨⟨a⟩, ⟨b⟩⟩ := equivs_of_biproduct ρ τ σ
    (fun i => (p₀ i).comp e.symm.toIntertwiningMap) (fun i => e.toIntertwiningMap.comp (j₀ i))
    (fun w => by
      simp only [IntertwiningMap.comp_apply]

      rw [← map_sum]
      have : ∀ x : ⨁ i, V i, ∑ i, j₀ i (p₀ i x) = x := fun x => DirectSum.sum_univ_of x
      rw [this, hes])
    (fun i x => by
      simp only [IntertwiningMap.comp_apply]
      rw [hse]
      exact DirectSum.component.lof_self k i x)
    (fun i i' h x => by
      simp only [IntertwiningMap.comp_apply]
      rw [hse]
      exact DirectSum.of_eq_of_ne i' i x h.symm)
  have := fun i => finite_intertwiningMap τ (ρ i)
  have := fun i => finite_intertwiningMap (ρ i) τ
  exact ⟨a.finrank_eq.trans (Module.finrank_pi_fintype k), b.finrank_eq.trans (Module.finrank_pi_fintype k)⟩

end GlobalTheory.IntertwinerSum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.BranchesAlongOfIrreducible

section

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem branchesAlong_of_irreducible {H : Type} [Group H] {n N : ℕ} (ι : H →* GL (Fin n) ℂ) (h : n + 1 = N) (lam : DomWeight N)
    (hirr : ∀ mu : DomWeight n, (smallRep ι mu).IsIrreducible)
    (hz : ∀ mu nu : DomWeight n, mu ≠ nu → ∀ φ : (smallRep ι mu).IntertwiningMap (smallRep ι nu), φ = 0) :
    BranchesAlong ι h lam := by
  classical
  have iso : Nonempty ((sumRep ι h lam).Equiv (resRep ι h lam)) := by
    refine GlobalTheory.nonempty_directSum_equiv_of_finrank_le ℂ H (Below h lam) _ (fun mu => nablaSq ℂ n mu.1) (fun mu => smallRep ι mu.1) _
      (fun mu => hirr mu.1) (fun i j hij => hz i.1 j.1 fun e => hij (Subtype.ext e)) (fun mu => ?_) (GlobalTheory.Branching.finrank_le_finrank_directSum_below n N h lam)
    obtain ⟨φ, hφ⟩ := GlobalTheory.Branching.exists_intertwining_ne_zero n N h lam mu.1 mu.2
    refine ⟨⟨φ.toLinearMap, fun y => φ.isIntertwining' (ι y)⟩, fun e => hφ ?_⟩
    have e' := congrArg Representation.IntertwiningMap.toLinearMap e
    exact Representation.IntertwiningMap.ext e'
  refine ⟨iso, fun mu => ?_⟩
  letI : Fintype (Below h lam) := Fintype.ofFinite _
  have hm := (GlobalTheory.IntertwinerSum.finrank_intertwiningMap_directSum ℂ H (Below h lam) _ _ (fun mu => nablaSq ℂ n mu.1) (fun mu => smallRep ι mu.1)
    (smallRep ι mu) (resRep ι h lam) iso).1
  have h0 : ∀ nu : DomWeight n, mu ≠ nu →
      Module.finrank ℂ ((smallRep ι mu).IntertwiningMap (smallRep ι nu)) = 0 := fun nu hne => by
    have : Subsingleton ((smallRep ι mu).IntertwiningMap (smallRep ι nu)) :=
      ⟨fun a b => (hz mu nu hne a).trans (hz mu nu hne b).symm⟩
    exact Module.finrank_zero_of_subsingleton
  refine ⟨fun hI => ?_, fun hI => ?_⟩
  · unfold mult
    rw [hm, Finset.sum_eq_single (⟨mu, hI⟩ : Below h lam)]
    · have := hirr mu
      exact Representation.IsIrreducible.finrank_intertwiningMap_self _
    · intro b _ hb
      exact h0 b.1 fun e => hb (Subtype.ext e.symm)
    · simp
  · unfold mult
    rw [hm]
    exact Finset.sum_eq_zero fun b _ => h0 b.1 fun e => hI (e ▸ b.2)

theorem intertwining_unitary_eq_zero (n : ℕ) (mu nu : DomWeight n) (hne : mu ≠ nu)
    (φ : (smallRep (unitaryIncl n) mu).IntertwiningMap (smallRep (unitaryIncl n) nu)) : φ = 0 := by
  have := GlobalTheory.Branching.isIrreducible_smallRep_unitary n mu
  obtain ⟨f, hf, h0⟩ := GlobalTheory.Branching.exists_ne_zero_map_eq_zero_of_weight_ne n mu nu hne
    ⟨φ.toLinearMap, fun g => LinearMap.ext fun f => GlobalTheory.Branching.intertwining_gl_of_unitary n mu nu φ g f⟩
  refine (Representation.IsIrreducible.injective_or_eq_zero φ).resolve_left fun hi => hf (hi ?_)
  rw [map_zero]; exact h0

theorem isIrreducible_smallRep_id (n : ℕ) (mu : DomWeight n) : (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu).IsIrreducible := by
  have hU := GlobalTheory.Branching.isIrreducible_smallRep_unitary n mu
  let r : Subrepresentation (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu) → Subrepresentation (smallRep (unitaryIncl n) mu) :=
    fun S => ⟨S.toSubmodule, fun u _ hv => S.apply_mem_toSubmodule (unitaryIncl n u) hv⟩
  have hnt : Nontrivial (Subrepresentation (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu)) :=
    ⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun S => ?_⟩
  rcases eq_bot_or_eq_top (r S) with e | e
  · have e' := congrArg Subrepresentation.toSubmodule e
    exact Or.inl (Subrepresentation.ext e')
  · have e' := congrArg Subrepresentation.toSubmodule e
    exact Or.inr (Subrepresentation.ext e')

theorem intertwining_id_eq_zero (n : ℕ) (mu nu : DomWeight n) (hne : mu ≠ nu)
    (φ : (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu).IntertwiningMap (smallRep (MonoidHom.id (GL (Fin n) ℂ)) nu)) :
    φ = 0 := by
  have := intertwining_unitary_eq_zero n mu nu hne ⟨φ.toLinearMap, fun u => φ.isIntertwining' (unitaryIncl n u)⟩
  have e' := congrArg Representation.IntertwiningMap.toLinearMap this
  exact Representation.IntertwiningMap.ext e'

theorem branchesAlong_all (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) :
    BranchesAlong (MonoidHom.id (GL (Fin n) ℂ)) h lam ∧ BranchesAlong (unitaryIncl n) h lam :=
  ⟨branchesAlong_of_irreducible _ h lam (isIrreducible_smallRep_id n) (intertwining_id_eq_zero n),
    branchesAlong_of_irreducible _ h lam (isIrreducible_smallRep_unitary n) (intertwining_unitary_eq_zero n)⟩

theorem comult_of_irreducible {H : Type} [Group H] {n N : ℕ} (ι : H →* GL (Fin n) ℂ) (h : n + 1 = N)
    (lam : DomWeight N) (hirr : ∀ mu : DomWeight n, (smallRep ι mu).IsIrreducible)
    (hz : ∀ mu nu : DomWeight n, mu ≠ nu → ∀ φ : (smallRep ι mu).IntertwiningMap (smallRep ι nu), φ = 0)
    (mu : DomWeight n) :
    (Interlace h lam mu → Module.finrank ℂ ((resRep ι h lam).IntertwiningMap (smallRep ι mu)) = 1) ∧
      (¬ Interlace h lam mu → Module.finrank ℂ ((resRep ι h lam).IntertwiningMap (smallRep ι mu)) = 0) := by
  classical
  have iso := (branchesAlong_of_irreducible ι h lam hirr hz).1
  letI : Fintype (Below h lam) := Fintype.ofFinite _
  have hm := (GlobalTheory.IntertwinerSum.finrank_intertwiningMap_directSum ℂ H (Below h lam) _ _ (fun mu => nablaSq ℂ n mu.1) (fun mu => smallRep ι mu.1)
    (smallRep ι mu) (resRep ι h lam) iso).2
  have h0 : ∀ nu : DomWeight n, nu ≠ mu →
      Module.finrank ℂ ((smallRep ι nu).IntertwiningMap (smallRep ι mu)) = 0 := fun nu hne => by
    have : Subsingleton ((smallRep ι nu).IntertwiningMap (smallRep ι mu)) :=
      ⟨fun a b => (hz nu mu hne a).trans (hz nu mu hne b).symm⟩
    exact Module.finrank_zero_of_subsingleton
  refine ⟨fun hI => ?_, fun hI => ?_⟩
  · rw [hm, Finset.sum_eq_single (⟨mu, hI⟩ : Below h lam)]
    · have := hirr mu
      exact Representation.IsIrreducible.finrank_intertwiningMap_self _
    · intro b _ hb
      exact h0 b.1 fun e => hb (Subtype.ext e)
    · simp
  · rw [hm]
    exact Finset.sum_eq_zero fun b _ => h0 b.1 fun e => hI (e ▸ b.2)

theorem comult_id (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) :
    (Interlace h lam mu → Module.finrank ℂ ((resRep (MonoidHom.id (GL (Fin n) ℂ)) h lam).IntertwiningMap
        (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu)) = 1) ∧
      (¬ Interlace h lam mu → Module.finrank ℂ ((resRep (MonoidHom.id (GL (Fin n) ℂ)) h lam).IntertwiningMap
        (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu)) = 0) :=
  comult_of_irreducible _ h lam (isIrreducible_smallRep_id n) (intertwining_id_eq_zero n) mu

theorem comult_unitary (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) :
    (Interlace h lam mu → Module.finrank ℂ ((resRep (unitaryIncl n) h lam).IntertwiningMap
        (smallRep (unitaryIncl n) mu)) = 1) ∧
      (¬ Interlace h lam mu → Module.finrank ℂ ((resRep (unitaryIncl n) h lam).IntertwiningMap
        (smallRep (unitaryIncl n) mu)) = 0) :=
  comult_of_irreducible _ h lam (isIrreducible_smallRep_unitary n) (intertwining_unitary_eq_zero n) mu

end GlobalTheory.Branching

namespace GlobalTheory.Published

theorem weylBranching_holds : WeylBranching := fun n N h _ lam => GlobalTheory.Branching.branchesAlong_all n N h lam

end GlobalTheory.Published
end
end
