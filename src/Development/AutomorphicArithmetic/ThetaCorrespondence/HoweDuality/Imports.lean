module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorEqTopOrLeKerFiniteLengthModules
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.PartStable
public import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.RadFin
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.PartStable

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorEqTopOrLeKerFiniteLengthModulesStatement

section

@[expose] public section

open scoped TensorProduct


theorem _root_.GlobalTheory.T.tensor_eq_top_or_le_ker_finiteLength_modules : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ P₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup P₀] [Module ℂ P₀]
    {M P : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i)))
    (Rel₀ : Submodule ℂ M₀) (Rel : ∀ i, Submodule ℂ (M i)) (p₀ : M₀ →ₗ[ℂ] P₀) (p : ∀ i, M i →ₗ[ℂ] P i),
    Module.rank ℂ M₀ ≤ Cardinal.aleph0 → (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) →
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M₀), StrictMono N →
        (∀ j, Rel₀ ≤ N j ∧ ∀ g ∈ Op₀, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → (∀ g ∈ Op₀, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker p₀) →
    Rel₀ ≤ LinearMap.ker p₀ → (∀ g ∈ Op₀, ∀ x ∈ LinearMap.ker p₀, g x ∈ LinearMap.ker p₀) →
    (∀ i, ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (M i)), StrictMono N →
        (∀ j, Rel i ≤ N j ∧ ∀ g ∈ Op i, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ i, ∀ N : Submodule ℂ (M i), Rel i ≤ N → (∀ g ∈ Op i, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker (p i)) →
    (∀ i, Rel i ≤ LinearMap.ker (p i)) → (∀ i, ∀ g ∈ Op i, ∀ x ∈ LinearMap.ker (p i), g x ∈ LinearMap.ker (p i)) →
    ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N) →
      (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j), x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) →
      (∀ g ∈ Op₀, ∀ t ∈ N, TensorProduct.map g LinearMap.id t ∈ N) →
      (∀ i, ∀ g ∈ Op i, ∀ t ∈ N, TensorProduct.map LinearMap.id
        (PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g)) t ∈ N) →
      N = ⊤ ∨ N ≤ LinearMap.ker (TensorProduct.map p₀ (PiTensorProduct.map p)) := by
  first | exact @GlobalTheory.TensHead.tensor_eq_top_or_le_ker_map | exact GlobalTheory.TensHead.tensor_eq_top_or_le_ker_map | (intros; apply GlobalTheory.TensHead.tensor_eq_top_or_le_ker_map <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.Nak

section

@[expose] public section

open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

theorem UpperTheory.Lit.HoweDuality.nak :
    ∀ {M T R : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup T] [Module ℂ T] (j : R → M →ₗ[ℂ] T) (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) (N : Submodule ℂ T), (⨆ r, LinearMap.range (j r)) = ⊤ → (∀ g ∈ Op, ∃ Φ : Module.End ℂ T, (∀ r x, Φ (j r x) = j r (g x)) ∧ ∀ t ∈ N, Φ t ∈ N) → (∀ r, ∀ x ∈ Rel, j r x ∈ N) → RadFin Op Rel K → N ⊔ (⨆ r, K.map (j r)) = ⊤ → N = ⊤ := by
  intro M T R _ _ _ _ j Op Rel K N hspan hOp hRel hRad hsup
  classical
  have h1 : ∀ e ∈ Algebra.adjoin ℂ Op,
      ∃ Φ : Module.End ℂ T, (∀ r x, Φ (j r x) = j r (e x)) ∧ ∀ t ∈ N, Φ t ∈ N := by
    intro e he
    induction he using Algebra.adjoin_induction with
    | mem g hg => exact hOp g hg
    | algebraMap c =>
      refine ⟨c • (1 : Module.End ℂ T), fun r x => ?_, fun t ht => ?_⟩
      · simp [Algebra.algebraMap_eq_smul_one]
      · simpa using N.smul_mem c ht
    | add a b _ _ ha hb =>
      obtain ⟨A, hA, hAN⟩ := ha
      obtain ⟨B, hB, hBN⟩ := hb
      refine ⟨A + B, fun r x => ?_, fun t ht => ?_⟩
      · simp [hA, hB]
      · simpa using N.add_mem (hAN t ht) (hBN t ht)
    | mul a b _ _ ha hb =>
      obtain ⟨A, hA, hAN⟩ := ha
      obtain ⟨B, hB, hBN⟩ := hb
      refine ⟨A * B, fun r x => ?_, fun t ht => ?_⟩
      · simp [hA, hB]
      · simpa using hAN _ (hBN t ht)
  have h2 : ∀ u ∈ (⨆ r, K.map (j r)), ∃ S : Finset M, (∀ k ∈ S, k ∈ K) ∧
      ∀ (e : Module.End ℂ M) (Φ : Module.End ℂ T), (∀ r x, Φ (j r x) = j r (e x)) →
        (∀ k ∈ S, e k ∈ Rel) → Φ u ∈ N := by
    intro u hu
    induction hu using Submodule.iSup_induction' with
    | mem r x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      refine ⟨{k}, by simpa using hk, fun e Φ hΦ hS => ?_⟩
      rw [hΦ]
      exact hRel r _ (hS k (Finset.mem_singleton_self k))
    | zero => exact ⟨∅, by simp, fun e Φ _ _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨S, hS, hS'⟩ := hx
      obtain ⟨S2, hS2, hS2'⟩ := hy
      refine ⟨S ∪ S2, fun k hk => ?_, fun e Φ hΦ h => ?_⟩
      · rcases Finset.mem_union.1 hk with h | h
        · exact hS k h
        · exact hS2 k h
      · rw [map_add (f := _)]
        exact N.add_mem (hS' e Φ hΦ fun k hk => h k (Finset.mem_union_left _ hk))
          (hS2' e Φ hΦ fun k hk => h k (Finset.mem_union_right _ hk))
  obtain ⟨s, hGen, hs⟩ := hRad
  have h3 : ∀ r, j r s ∈ N := by
    intro r
    have hm : j r s ∈ N ⊔ (⨆ r, K.map (j r)) := by rw [hsup]; trivial
    obtain ⟨n, hn, u, hu, hnu⟩ := Submodule.mem_sup.1 hm
    obtain ⟨S, hSK, hS⟩ := h2 u hu
    obtain ⟨e, he, hes, heS⟩ := hs S hSK
    obtain ⟨Φ, hΦ, hΦN⟩ := h1 e he
    have : j r s = Φ n + Φ u := by rw [← map_add (f := _), hnu, hΦ, hes]
    rw [this]
    exact N.add_mem (hΦN n hn) (hS e Φ hΦ heS)
  have h4 : ∀ r, N.comap (j r) = ⊤ := by
    intro r
    refine hGen _ (fun x hx => hRel r x hx) (fun g hg x hx => ?_) (h3 r)
    obtain ⟨Φ, hΦ, hΦN⟩ := hOp g hg
    show j r (g x) ∈ N
    rw [← hΦ]
    exact hΦN _ hx
  rw [eq_top_iff, ← hspan]
  refine iSup_le fun r => ?_
  rintro _ ⟨x, rfl⟩
  have : x ∈ N.comap (j r) := by rw [h4 r]; trivial
  exact this
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.SlotBasic

section

@[expose] public section

open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

theorem UpperTheory.Lit.HoweDuality.slotFacts :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (i : ι), (⨆ r : M₀ × (∀ j, M j), LinearMap.range (intersection_update_fsHerm_neg_one i r)) = ⊤ ∧ ∀ (g : Module.End ℂ (M i)) (r : M₀ × (∀ j, M j)) (x : M i), factorOp i g (intersection_update_fsHerm_neg_one i r x) = intersection_update_fsHerm_neg_one i r (g x) := by
  intro ι _ _ M₀ _ _ M _ _ i
  refine ⟨?_, ?_⟩
  · rw [Submodule.eq_top_iff']
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add a b ha hb => exact Submodule.add_mem _ ha hb
    | tmul x₀ w =>
      induction w using PiTensorProduct.induction_on with
      | smul_tprod c y =>
        rw [TensorProduct.tmul_smul]
        refine Submodule.smul_mem _ c ?_
        refine Submodule.mem_iSup_of_mem (x₀, y) ⟨y i, ?_⟩
        rw [position_apply]
        simp only [Function.update_eq_self]
      | add a b ha hb =>
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ ha hb
  · intro g r x
    rw [position_apply, position_apply, factorOp, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
    congr 2
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [Function.update_of_ne h]
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.NakAll

section

@[expose] public section

open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

theorem UpperTheory.Lit.HoweDuality.nakAll :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (Op : ∀ i, Set (Module.End ℂ (M i))) (Rel K : ∀ i, Submodule ℂ (M i)), (∀ i, Stable (Op i) (Rel i)) → (∀ i, Stable (Op i) (K i)) → (∀ i, Rad (Op i) (Rel i) (K i)) → ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)), (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j), x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) → (∀ i, ∀ g ∈ Op i, ∀ t ∈ N, TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g)) t ∈ N) → N ⊔ (⨆ i, part M₀ i (K i)) = ⊤ → N = ⊤ := by
  intro ι _ _ M₀ _ _ M _ _ Op Rel K hRel hK hRad N hN hOp hsup
  have key : ∀ S : Finset ι, N ⊔ (⨆ i ∈ S, part M₀ i (K i)) = ⊤ → N = ⊤ := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro h; simpa using h
    | insert i S hi ih =>
      intro h
      apply ih
      refine UpperTheory.Lit.HoweDuality.nak (fun r : M₀ × (∀ j, M j) => intersection_update_fsHerm_neg_one i r) (Op i) (Rel i) (K i) _
        (UpperTheory.Lit.HoweDuality.slotFacts i).1 (fun g hg => ⟨factorOp i g, (UpperTheory.Lit.HoweDuality.slotFacts i).2 g, ?_⟩)
        (fun r x hx => Submodule.mem_sup_left (hN i x hx r.1 r.2))
        (UpperTheory.Lit.HoweDuality.radFin _ _ _ (hRel i) (hK i) (hRad i)) ?_
      · have hle : N ⊔ (⨆ l ∈ S, part M₀ l (K l)) ≤
            (N ⊔ (⨆ l ∈ S, part M₀ l (K l))).comap (factorOp i g) := by
          refine sup_le (fun t ht => Submodule.mem_sup_left (hOp i g hg t ht))
            (iSup₂_le fun l hl t ht => Submodule.mem_sup_right ?_)
          have hne : i ≠ l := fun e => hi (e ▸ hl)
          exact (le_iSup₂ (f := fun l (_ : l ∈ S) => part M₀ l (K l)) l hl)
            ((UpperTheory.Lit.HoweDuality.partStable l (K l)).2.2 i hne g t ht)
        exact fun t ht => hle ht
      · rw [Finset.iSup_insert, sup_comm (part M₀ i (K i)), ← sup_assoc] at h
        exact h
  apply key Finset.univ
  simpa using hsup
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.Imports

section

@[expose] public section

open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

theorem UpperTheory.Lit.HoweDuality.tens :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ P₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup P₀] [Module ℂ P₀] {M P : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i))) (Rel₀ : Submodule ℂ M₀) (Rel : ∀ i, Submodule ℂ (M i)) (p₀ : M₀ →ₗ[ℂ] P₀) (p : ∀ i, M i →ₗ[ℂ] P i), Module.rank ℂ M₀ ≤ Cardinal.aleph0 → (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) → (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M₀), StrictMono N → (∀ j, Rel₀ ≤ N j ∧ ∀ g ∈ Op₀, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) → (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → (∀ g ∈ Op₀, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker p₀) → Rel₀ ≤ LinearMap.ker p₀ → (∀ g ∈ Op₀, ∀ x ∈ LinearMap.ker p₀, g x ∈ LinearMap.ker p₀) → (∀ i, Stable (Op i) (Rel i)) → (∀ i, Stable (Op i) (LinearMap.ker (p i))) → (∀ i, Rad (Op i) (Rel i) (LinearMap.ker (p i))) → (∀ i, ∀ N : Submodule ℂ (M i), LinearMap.ker (p i) ≤ N → Stable (Op i) N → N ≠ ⊤ → N ≤ LinearMap.ker (p i)) → ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)), (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N) → (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j), x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) → (∀ g ∈ Op₀, ∀ t ∈ N, TensorProduct.map g LinearMap.id t ∈ N) → (∀ i, ∀ g ∈ Op i, ∀ t ∈ N, TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g)) t ∈ N) → N = ⊤ ∨ N ≤ LinearMap.ker (TensorProduct.map p₀ (PiTensorProduct.map p)) := by
  intro ι _ _ M₀ P₀ _ _ _ _ M P _ _ _ _ Op₀ Op Rel₀ Rel p₀ p hr₀ hr hL₀ hmax₀ hRel₀ hker₀ hRel hK hRad
    hmax N hN₀ hN hOp₀ hOp
  have stab : ∀ Φ : Module.End ℂ (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)), (∀ t ∈ N, Φ t ∈ N) →
      (∀ l, ∀ t ∈ part M₀ l (LinearMap.ker (p l)), Φ t ∈ part M₀ l (LinearMap.ker (p l))) →
      ∀ t ∈ N ⊔ (⨆ l, part M₀ l (LinearMap.ker (p l))),
        Φ t ∈ N ⊔ (⨆ l, part M₀ l (LinearMap.ker (p l))) := by
    intro Φ h1 h2
    have hle : N ⊔ (⨆ l, part M₀ l (LinearMap.ker (p l))) ≤
        (N ⊔ (⨆ l, part M₀ l (LinearMap.ker (p l)))).comap Φ :=
      sup_le (fun t ht => Submodule.mem_sup_left (h1 t ht))
        (iSup_le fun l t ht => Submodule.mem_sup_right
          ((le_iSup (fun l => part M₀ l (LinearMap.ker (p l))) l) (h2 l t ht)))
    exact fun t ht => hle ht
  have key := GlobalTheory.T.tensor_eq_top_or_le_ker_finiteLength_modules Op₀ Op Rel₀ (fun i => LinearMap.ker (p i)) p₀ p hr₀ hr hL₀ hmax₀ hRel₀ hker₀
    (fun i => ⟨2, fun m C hC h => ?_⟩) hmax (fun i => le_rfl) hK
    (N ⊔ (⨆ l, part M₀ l (LinearMap.ker (p l))))
    (fun x hx y => Submodule.mem_sup_left (hN₀ x hx y))
    (fun i x hx x₀ y => Submodule.mem_sup_right
      ((le_iSup (fun l => part M₀ l (LinearMap.ker (p l))) i)
        ((le_iSup (fun r : M₀ × ∀ j, M j => (LinearMap.ker (p i)).map (intersection_update_fsHerm_neg_one i r)) (x₀, y))
          (Submodule.mem_map_of_mem hx))))
    (fun g hg => stab _ (hOp₀ g hg) fun l => (partStable l _).1 g)
    (fun i g hg => stab (factorOp i g) (hOp i g hg) fun l => ?_)
  · rcases key with h | h
    · exact Or.inl (nakAll Op Rel (fun i => LinearMap.ker (p i)) hRel hK hRad N hN hOp h)
    · exact Or.inr (le_sup_left.trans h)
  · by_contra hm
    have hm : 2 < m := not_le.1 hm
    have h01 : C ⟨0, by omega⟩ < C ⟨1, by omega⟩ := hC (by simp [Fin.lt_def])
    have h12 : C ⟨1, by omega⟩ < C ⟨2, hm⟩ := hC (by simp [Fin.lt_def])
    have h1 := hmax i _ (h ⟨1, by omega⟩).1 (h ⟨1, by omega⟩).2 h12.ne_top
    exact absurd (h01.trans_le (h1.trans (h ⟨0, by omega⟩).1)) (lt_irrefl _)
  · by_cases hl : i = l
    · subst hl
      exact (partStable i _).2.1 g (hK i g hg)
    · exact (partStable l _).2.2 i hl g
end
end
