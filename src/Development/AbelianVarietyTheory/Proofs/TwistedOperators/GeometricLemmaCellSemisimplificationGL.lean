module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdditiveFamilyFunctionDeterminedConstituentsStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultNormalisedInductionExactStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedInductionProductParabolicPiTensor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducibleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PiExteriorTensorFlattenedIndexEquivNested
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiTensorSmoothRepsExactEachFactorStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelativeJacquetFunctorPiTensorEquivStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorProductDeterminesFactorClassesStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLeviStatement

section

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_equiv_piExteriorTensor_blockLevi : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (τ : GlobalTheory.SmGL.IrrRep (GlobalTheory.SmGL.Levi k c)), ∃ s : ∀ j, GlobalTheory.SmGL.IrrRep (GL (c j) k), Nonempty (τ.ρ.Equiv (GlobalTheory.SmGL.piTensor fun j => (s j).ρ)) := by
  first | exact @GlobalTheory.LeviFactor.exists_equiv_piTensor_levi | exact GlobalTheory.LeviFactor.exists_equiv_piTensor_levi | (intros; apply GlobalTheory.LeviFactor.exists_equiv_piTensor_levi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedInductionProductParabolicPiTensorStatement

section

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.normalised_induction_product_parabolic_piTensor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] [LinearOrder β] (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) (Z : α → Type) [∀ i, AddCommGroup (Z i)] [∀ i, Module ℂ (Z i)] (σ : ∀ i, Representation ℂ (GlobalTheory.SmGL.Levi k (c i)) (Z i)), (∀ i, GlobalTheory.PRep.IsSmooth (σ i)) → Nonempty ((GlobalTheory.SmGL.relInd f (GlobalTheory.SmGL.piTensor σ)).Equiv (GlobalTheory.SmGL.piTensor fun i => GlobalTheory.SmGL.parInd (f i) (σ i))) := by
  first | exact @GlobalTheory.SmGL.IndTensor.relInd_piTensor | exact GlobalTheory.SmGL.IndTensor.relInd_piTensor | (intros; apply GlobalTheory.SmGL.IndTensor.relInd_piTensor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiTensorDoublyIndexedSwapBlocksEquiv

section

@[expose] public section

open scoped TensorProduct

noncomputable section

open PiTensorProduct GlobalTheory.PRep GlobalTheory.JacStages

namespace GlobalTheory.SmGL

section SwapTensor

def sigmaPairSwap (α β : Type) : (Σ _ : α, β) ≃ (Σ _ : β, α) where
  toFun p := ⟨p.2, p.1⟩
  invFun q := ⟨q.2, q.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {α β : Type} [Finite α] [Finite β]
  (Y : α → β → Type) [∀ i j, AddCommGroup (Y i j)] [∀ i j, Module ℂ (Y i j)]

theorem exists_pairCurry : ∃ e : (⨂[ℂ] p : (Σ _ : α, β), Y p.1 p.2) ≃ₗ[ℂ] ⨂[ℂ] i, ⨂[ℂ] j, Y i j,
    ∀ x : ∀ p : (Σ _ : α, β), Y p.1 p.2, e (tprod ℂ x) = tprod ℂ fun i => tprod ℂ fun j => x ⟨i, j⟩ := by
  classical
  exact ⟨sigmaCurry (fun p : (Σ _ : α, β) => Y p.1 p.2),
    sigmaCurry_tprod (fun p : (Σ _ : α, β) => Y p.1 p.2)⟩


omit [Finite α] [Finite β] in
theorem exists_pairSwap :
    ∃ e : (⨂[ℂ] p : (Σ _ : α, β), Y p.1 p.2) ≃ₗ[ℂ] ⨂[ℂ] q : (Σ _ : β, α), Y q.2 q.1,
    ∀ x : ∀ p : (Σ _ : α, β), Y p.1 p.2,
      e (tprod ℂ x) = tprod ℂ fun q : (Σ _ : β, α) => x ⟨q.2, q.1⟩ :=
  ⟨reindex ℂ (fun p : (Σ _ : α, β) => Y p.1 p.2) (sigmaPairSwap α β),
    fun x => reindex_tprod (sigmaPairSwap α β) x⟩

theorem exists_pairCurrySwap : ∃ e : (⨂[ℂ] p : (Σ _ : α, β), Y p.1 p.2) ≃ₗ[ℂ] ⨂[ℂ] j, ⨂[ℂ] i, Y i j,
    ∀ x : ∀ p : (Σ _ : α, β), Y p.1 p.2, e (tprod ℂ x) = tprod ℂ fun j => tprod ℂ fun i => x ⟨i, j⟩ := by
  obtain ⟨e₁, h₁⟩ := exists_pairSwap Y
  obtain ⟨e₂, h₂⟩ := exists_pairCurry (fun j i => Y i j)
  refine ⟨e₁.trans e₂, fun x => ?_⟩
  rw [LinearEquiv.trans_apply, h₁]
  exact h₂ _

end SwapTensor

theorem piTensor_swapBlocks_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] (c : α → β → Type)
    [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (Y : α → β → Type) [∀ i j, AddCommGroup (Y i j)]
    [∀ i j, Module ℂ (Y i j)] (σ : ∀ i j, Representation ℂ (GL (c i j) k) (Y i j)),
    Nonempty (Representation.Equiv
      ((GlobalTheory.SmGL.piTensor fun i => GlobalTheory.SmGL.piTensor fun j => σ i j).comp (GlobalTheory.SmGL.swapBlocks k c))
      (GlobalTheory.SmGL.piTensor fun j => GlobalTheory.SmGL.piTensor fun i => σ i j)) := by
  intro k _ _ _ _ α β _ _ c _ _ Y _ _ σ
  obtain ⟨e₁, h₁⟩ := exists_pairCurry Y
  obtain ⟨e₂, h₂⟩ := exists_pairCurrySwap Y
  refine ⟨Representation.Equiv.mk (e₁.symm.trans e₂) fun g => ?_⟩
  have key : ∀ w : ⨂[ℂ] p : (Σ _ : α, β), Y p.1 p.2,
      e₂ (e₁.symm ((piTensor fun i => piTensor fun j => σ i j) (swapBlocks k c g) (e₁ w))) =
        (piTensor fun j => piTensor fun i => σ i j) g (e₂ w) := by
    intro w
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      have h : (piTensor fun i => piTensor fun j => σ i j) (swapBlocks k c g) (e₁ (tprod ℂ x)) =
          e₁ (tprod ℂ fun p : (Σ _ : α, β) => σ p.1 p.2 (g p.2 p.1) (x p)) := by
        rw [h₁, h₁, piTensor_tprod]
        congr 1
        funext i
        exact piTensor_tprod (fun j => σ i j) _ _
      have h' : (piTensor fun j => piTensor fun i => σ i j) g (e₂ (tprod ℂ x)) =
          e₂ (tprod ℂ fun p : (Σ _ : α, β) => σ p.1 p.2 (g p.2 p.1) (x p)) := by
        rw [h₂, h₂, piTensor_tprod]
        congr 1
        funext j
        exact piTensor_tprod (fun i => σ i j) _ _
      rw [map_smul, map_smul, map_smul, map_smul, map_smul, map_smul, h, h', LinearEquiv.symm_apply_apply]
    | add w w' hw hw' =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hw, hw']
  refine LinearMap.ext fun v => ?_
  obtain ⟨w, rfl⟩ := e₁.surjective v
  have h := key w
  rw [← e₁.symm_apply_apply w, e₁.apply_symm_apply] at h
  exact h

end GlobalTheory.SmGL
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiTensorDoublyIndexedSwapBlocksEquivStatement

section

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.piTensor_doubly_indexed_swap_blocks_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (Y : α → β → Type) [∀ i j, AddCommGroup (Y i j)] [∀ i j, Module ℂ (Y i j)] (σ : ∀ i j, Representation ℂ (GL (c i j) k) (Y i j)), Nonempty (Representation.Equiv ((GlobalTheory.SmGL.piTensor fun i => GlobalTheory.SmGL.piTensor fun j => σ i j).comp (GlobalTheory.SmGL.swapBlocks k c)) (GlobalTheory.SmGL.piTensor fun j => GlobalTheory.SmGL.piTensor fun i => σ i j)) := by
  first | exact @GlobalTheory.SmGL.piTensor_swapBlocks_equiv | exact GlobalTheory.SmGL.piTensor_swapBlocks_equiv | (intros; apply GlobalTheory.SmGL.piTensor_swapBlocks_equiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaCellSemisimplificationGL

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JHMult
open scoped TensorProduct

namespace GlobalTheory.SmGL.CellSemis

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def relIndEquiv {α β : Type} [Fintype α] [Fintype β] [LinearOrder β] {m : α → Type}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {c : α → β → Type} [∀ i j, Fintype (c i j)]
    [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) {V W : Type} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (∀ i, Levi k (c i)) V}
    {σ : Representation ℂ (∀ i, Levi k (c i)) W} (φ : ρ.Equiv σ) : (relInd f ρ).Equiv (relInd f σ) :=
  GlobalTheory.LocGL.equivOfBijective (smIndMap (compMap (twistMap φ.toIntertwiningMap _) _))
    (Function.bijective_iff_has_inverse.2
      ⟨smIndMap (compMap (twistMap φ.symm.toIntertwiningMap _) _),
        fun F => Subtype.ext (Subtype.ext (funext fun x => φ.symm_apply_apply (F.1.1 x))),
        fun F => Subtype.ext (Subtype.ext (funext fun x => φ.apply_symm_apply (F.1.1 x)))⟩)

theorem jhMult_relInd_of_subsingleton {α β : Type} [Fintype α] [Fintype β] [LinearOrder β]
    {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {c : α → β → Type}
    [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) {V : Type}
    [AddCommGroup V] [Module ℂ V] [Subsingleton V] (ρ : Representation ℂ (∀ i, Levi k (c i)) V)
    {Y : Type} [AddCommGroup Y] [Module ℂ Y] {τ : Representation ℂ (Levi k m) Y}
    (hτ : τ.IsIrreducible) : jhMult τ (relInd f ρ) = 0 := by
  haveI : Subsingleton (smoothPart (ind (relParab k f) ((twist ρ (relDeltaHalf k c)).comp (relProj k f)))) :=
    ⟨fun a b => Subtype.ext (Subtype.ext (funext fun _ => Subsingleton.elim _ _))⟩
  exact jhMult_of_subsingleton hτ _

theorem subsingleton_piTensor {α : Type} [Fintype α] [DecidableEq α] {X : α → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (i : α) [Subsingleton (X i)] :
    Subsingleton (⨂[ℂ] a, X a) := by
  have h : ∀ z : ⨂[ℂ] a, X a, z = 0 := fun z => by
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      rw [(PiTensorProduct.tprod ℂ).map_coord_zero i (Subsingleton.elim _ _), smul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y => (h x).trans (h y).symm⟩

end GlobalTheory.SmGL.CellSemis

open GlobalTheory.SmGL.CellSemis in
theorem GlobalTheory.SmGL.CellSemis.cellSemisimplification : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.CellSemisimplification k := by
  intro hBZ k _ _ _ _ α β _ _ _ _ m _ _ m' _ _ c _ _ f g X _ _ ρ hρ hl
  classical
  let A : ∀ i, SmRep (Levi k (c i)) := fun i => ⟨_, jac (f i) (ρ i), isSmooth_jac (f i) (hρ i)⟩
  have hA : ∀ i, HasFiniteLength (A i).ρ := fun i =>
    (hBZ k).2.1 β (m i) (c i) (f i) (X i) (ρ i) (hρ i) (hl i)
  let Φ : IrrRep (Levi k m') → (∀ i, SmRep (Levi k (c i))) → ℕ∞ := fun τ B =>
    jhMult τ.ρ (relInd (c := fun j i => c i j) g ((piTensor fun i => (B i).ρ).comp (swapBlocks k c)))
  have hswap : Continuous (swapBlocks k c) := by
    show Continuous fun g : (∀ j, Levi k fun i => c i j) => fun i j => g j i
    exact continuous_pi fun i => continuous_pi fun j => (continuous_apply i).comp (continuous_apply j)
  have hzero : ∀ τ (B : ∀ i, SmRep (Levi k (c i))) (i : α), Subsingleton (B i).V → Φ τ B = 0 := by
    intro τ B i hi
    haveI := subsingleton_piTensor (X := fun a => (B a).V) i
    exact jhMult_relInd_of_subsingleton _ _ τ.irr
  have hexact : ∀ τ (B : ∀ i, SmRep (Levi k (c i))) (i : α) (C C₁ C₂ : SmRep (Levi k (c i)))
      (ι : C₁.ρ.IntertwiningMap C.ρ) (p : C.ρ.IntertwiningMap C₂.ρ), Function.Injective ι →
      Function.Surjective p → (∀ u, p (ι u) = 0) → (∀ v, p v = 0 → ∃ u, ι u = v) →
      Φ τ (Function.update B i C) = Φ τ (Function.update B i C₁) + Φ τ (Function.update B i C₂) := by
    intro τ B i C C₁ C₂ ι p h1 h2 h3 h4
    obtain ⟨ι', p', h1', h2', h3', h4'⟩ := GlobalTheory.T.piTensor_smooth_reps_exact_each_factor α (fun i => Levi k (c i)) B i C C₁ C₂ ι p h1 h2 h3 h4
    exact GlobalTheory.T.jordanHolder_mult_normalised_induction_exact k β α m' (fun j i => c i j) g _ _ _ _ _ _ (compMap ι' _) (compMap p' _) h1' h2' h3' h4'
      (isSmooth_comp (isSmooth_piTensor fun a => (Function.update B i C a).smooth) _ hswap) _ τ.ρ τ.irr
  let T' : Finset (∀ i, IrrCl (Levi k (c i))) :=
    Fintype.piFinset fun i => (finite_constituents (hA i)).toFinset
  have hT' : ∀ t ∉ T', ∃ i, jhMult (t i).rep.ρ (A i).ρ = 0 := by
    intro t ht
    rw [Fintype.mem_piFinset] at ht
    push_neg at ht
    obtain ⟨i, hi⟩ := ht
    exact ⟨i, by simpa using hi⟩
  let P : ∀ i, (∀ j, IrrCl (GL (c i j) k)) → IrrRep (Levi k (c i)) := fun i s =>
    ⟨_, piTensor fun j => (s j).rep.ρ, isSmooth_piTensor fun j => (s j).rep.smooth,
      GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k β (c i) fun j => (s j).rep⟩
  let Θ : (∀ i j, IrrCl (GL (c i j) k)) → ∀ i, IrrCl (Levi k (c i)) := fun s i => (P i (s i)).cl
  have hΘi : Function.Injective Θ := by
    intro s s' h
    funext i j
    have h2 := GlobalTheory.T.tensor_product_determines_factor_classes β (fun j => GL (c i j) k) (fun j => (s i j).rep) (fun j => (s' i j).rep)
      (IrrRep.cl_eq_iff.1 (congrFun h i)) j
    rwa [IrrCl.cl_rep, IrrCl.cl_rep] at h2
  have hΘs : Function.Surjective Θ := by
    intro t
    choose s hs using fun i => GlobalTheory.T.exists_equiv_piExteriorTensor_blockLevi hBZ k β (c i) (t i).rep
    refine ⟨fun i j => (s i j).cl, funext fun i => ?_⟩
    rw [← (t i).cl_rep]
    exact IrrRep.cl_eq_iff.2 ⟨(GlobalTheory.LocGL.piTensorEquiv fun j => (s i j).nonempty_equiv_rep.some).trans
      (hs i).some.symm⟩
  refine ⟨T'.preimage Θ hΘi.injOn, fun s hs => ?_, fun τ => ?_⟩
  · rw [Finset.mem_preimage] at hs
    obtain ⟨i, hi⟩ := hT' _ hs
    exact ⟨i, (jhMult_congr_left (P i (s i)).nonempty_equiv_rep.some.symm _).trans hi⟩
  · have hLHS : jhMult τ.ρ (cellFunctor f g (piTensor ρ)) = Φ τ A :=
      jhMult_congr_right _ (relIndEquiv g (GlobalTheory.LocGL.compEquiv (GlobalTheory.T.relative_jacquet_functor_piTensor_equiv k α β m c f X ρ).some (swapBlocks k c)))
    rw [hLHS, GlobalTheory.T.additive_family_function_determined_constituents α (fun i => Levi k (c i)) (Φ τ) (hzero τ) (hexact τ) A hA T' hT',
      ← Finset.sum_preimage Θ T' hΘi.injOn _ (fun t _ ht => absurd (hΘs t) ht)]
    refine Finset.sum_congr rfl fun s _ => ?_
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ =>
      jhMult_congr_left (P i (s i)).nonempty_equiv_rep.some _) (jhMult_congr_right _ ?_)
    exact (relIndEquiv g ((GlobalTheory.LocGL.compEquiv (GlobalTheory.LocGL.piTensorEquiv fun i =>
      (P i (s i)).nonempty_equiv_rep.some) (swapBlocks k c)).trans
        (GlobalTheory.T.piTensor_doubly_indexed_swap_blocks_equiv k α β c (fun i j => (s i j).rep.V) (fun i j => (s i j).rep.ρ)).some)).trans
      (GlobalTheory.T.normalised_induction_product_parabolic_piTensor k β α m' (fun j i => c i j) g (fun j => ⨂[ℂ] i, (s i j).rep.V)
        (fun j => piTensor fun i => (s i j).rep.ρ) (fun j => isSmooth_piTensor fun i => (s i j).rep.smooth)).some
end
end
end
