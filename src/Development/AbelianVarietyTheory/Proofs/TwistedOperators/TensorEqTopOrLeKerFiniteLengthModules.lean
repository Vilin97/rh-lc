module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqTopOfPureTensorsOfFactorGenerators
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OperatorStablePiTensorPureKernelSpanStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiTensorMaximalStableContainsSlotKernelStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOverStableSubmodulePiTensorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOverStableSubmoduleTensorPureKernelSpanStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorMaximalStableContainsLeftKernelStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqTopOfPureTensorsOfFactorGeneratorsStatement

section

@[expose] public section

open scoped TensorProduct


theorem _root_.GlobalTheory.T.eq_top_of_pure_tensors_of_factor_generators : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
    {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i)))
    (Rel₀ : Submodule ℂ M₀) (Rel : ∀ i, Submodule ℂ (M i)) (F₀ : Finset M₀) (F : ∀ i, Finset (M i)),
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → GlobalTheory.TensHead.Stab Op₀ N → (↑F₀ : Set M₀) ⊆ ↑N → N = ⊤) →
    (∀ i, ∀ N : Submodule ℂ (M i), Rel i ≤ N → GlobalTheory.TensHead.Stab (Op i) N →
      (↑(F i) : Set (M i)) ⊆ ↑N → N = ⊤) →
    ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N) →
      (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) →
      GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ (GlobalTheory.TensHead.piOps Op)) N →
      (∀ x₀ ∈ F₀, ∀ y : ∀ i, M i, (∀ i, y i ∈ F i) → x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y ∈ N) →
      N = ⊤ := by
  first | exact @GlobalTheory.TensHead.eq_top_of_pure_generators | exact GlobalTheory.TensHead.eq_top_of_pure_generators | (intros; apply GlobalTheory.TensHead.eq_top_of_pure_generators <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetGeneratingOperatorStableBounded

section

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory.StabGen

open GlobalTheory.TensHead

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def stabClosure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) : Submodule ℂ M :=
  sInf {N | Rel ≤ N ∧ Stab Op N ∧ S ⊆ N}

theorem rel_le_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    Rel ≤ stabClosure Op Rel S :=
  le_sInf fun _ hN => hN.1

theorem subset_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    S ⊆ stabClosure Op Rel S := fun _ hx =>
  Submodule.mem_sInf.2 fun _ hN => hN.2.2 hx

theorem stab_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    Stab Op (stabClosure Op Rel S) := by
  intro g hg x hx
  rw [stabClosure, Submodule.mem_sInf] at hx ⊢
  intro N hN
  exact hN.2.1 g hg x (hx N hN)

theorem closure_le {Op : Set (Module.End ℂ M)} {Rel N : Submodule ℂ M} {S : Set M}
    (h1 : Rel ≤ N) (h2 : Stab Op N) (h3 : S ⊆ N) : stabClosure Op Rel S ≤ N :=
  sInf_le ⟨h1, h2, h3⟩

theorem closure_mono {Op : Set (Module.End ℂ M)} {Rel : Submodule ℂ M} {S T : Set M}
    (h : S ⊆ T) : stabClosure Op Rel S ≤ stabClosure Op Rel T :=
  closure_le (rel_le_closure Op Rel T) (stab_closure Op Rel T)
    (h.trans (subset_closure Op Rel T))

noncomputable def chainSet [DecidableEq M] (pick : Finset M → M) : ℕ → Finset M
  | 0 => ∅
  | n + 1 => insert (pick (chainSet pick n)) (chainSet pick n)

theorem exists_finset_generating (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M)
    (hL : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) :
    ∃ F : Finset M, ∀ N : Submodule ℂ M, Rel ≤ N → GlobalTheory.TensHead.Stab Op N →
      (↑F : Set M) ⊆ ↑N → N = ⊤ := by
  classical
  obtain ⟨L, hL⟩ := hL
  by_contra hne
  push_neg at hne
  have hx : ∀ F : Finset M, ∃ x, x ∉ stabClosure Op Rel (F : Set M) := by
    intro F
    obtain ⟨N, h1, h2, h3, h4⟩ := hne F
    by_contra h
    push_neg at h
    exact h4 (eq_top_iff.2 fun x _ => closure_le h1 h2 h3 (h x))
  choose pick hpick using hx
  have hD : StrictMono fun n => stabClosure Op Rel (↑(chainSet pick n) : Set M) := by
    refine strictMono_nat_of_lt_succ fun n => lt_of_le_of_ne ?_ ?_
    · exact closure_mono (Finset.coe_subset.2 (Finset.subset_insert _ _))
    · intro h
      apply hpick (chainSet pick n)
      have hmem : pick (chainSet pick n) ∈ stabClosure Op Rel (↑(chainSet pick (n + 1)) : Set M) :=
        subset_closure Op Rel _ (by simp [chainSet])
      rw [← h] at hmem
      exact hmem
  have := hL (L + 1) (fun j => stabClosure Op Rel (↑(chainSet pick j) : Set M))
    (fun a b hab => hD hab) (fun j => ⟨rel_le_closure _ _ _, stab_closure _ _ _⟩)
  omega

end GlobalTheory.StabGen
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetGeneratingOperatorStableBoundedStatement

section

@[expose] public section

open scoped TensorProduct


theorem _root_.GlobalTheory.T.exists_finset_generating_operator_stable_bounded : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    ∃ F : Finset M, ∀ N : Submodule ℂ M, Rel ≤ N → GlobalTheory.TensHead.Stab Op N → (↑F : Set M) ⊆ ↑N → N = ⊤ := by
  first | exact @GlobalTheory.StabGen.exists_finset_generating | exact GlobalTheory.StabGen.exists_finset_generating | (intros; apply GlobalTheory.StabGen.exists_finset_generating <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMaximalOperatorStableOfFinsetGenerating

section

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory.TensHead

theorem exists_maximal_stab_of_finset {V : Type} [AddCommGroup V] [Module ℂ V]
    (G : Set (Module.End ℂ V)) (R : Submodule ℂ V) (F : Finset V)
    (hF : ∀ N : Submodule ℂ V, R ≤ N → Stab G N → (↑F : Set V) ⊆ ↑N → N = ⊤) :
    ∀ N : Submodule ℂ V, R ≤ N → Stab G N → N ≠ ⊤ →
      ∃ N' : Submodule ℂ V, N ≤ N' ∧ Stab G N' ∧ N' ≠ ⊤ ∧
        ∀ U : Submodule ℂ V, Stab G U → N' ≤ U → U = N' ∨ U = ⊤ := by
  intro N hRN hN hNtop
  let s : Set (Submodule ℂ V) := {U | R ≤ U ∧ Stab G U ∧ ¬ (↑F : Set V) ⊆ ↑U}
  have hcomp := (isCompactElement_iff_le_of_directed_sSup_le _).1
    (Submodule.finset_span_isCompactElement (R := ℂ) F)
  have hNs : N ∈ s := ⟨hRN, hN, fun h => hNtop (hF N hRN hN h)⟩
  obtain ⟨M, hNM, hM⟩ := zorn_le_nonempty₀ s (by
    intro c hcs hc y hy
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨le_trans (hcs hy).1 (le_sSup hy), ?_, ?_⟩, fun z hz => le_sSup hz⟩
    · intro g hg x hx
      obtain ⟨U, hU, hxU⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hx
      exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨U, hU, (hcs hU).2.1 g hg x hxU⟩
    · intro hFc
      have hspan : Submodule.span ℂ (↑F : Set V) ≤ sSup c := Submodule.span_le.2 hFc
      obtain ⟨U, hU, hle⟩ := hcomp c hne hdir hspan
      exact (hcs hU).2.2 (Submodule.span_le.1 hle)) N hNs
  refine ⟨M, hNM, hM.prop.2.1, fun h => hM.prop.2.2 (by rw [h]; exact fun _ _ => trivial), ?_⟩
  intro U hU hMU
  by_cases hFU : (↑F : Set V) ⊆ ↑U
  · exact Or.inr (hF U (le_trans hM.prop.1 hMU) hU hFU)
  · exact Or.inl (le_antisymm (hM.2 ⟨le_trans hM.prop.1 hMU, hU, hFU⟩ hMU) hMU)

end GlobalTheory.TensHead
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMaximalOperatorStableOfFinsetGeneratingStatement

section

@[expose] public section

open scoped TensorProduct


theorem _root_.GlobalTheory.T.exists_maximal_operatorStable_of_finset_generating : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V)) (R : Submodule ℂ V)
    (F : Finset V),
    (∀ N : Submodule ℂ V, R ≤ N → GlobalTheory.TensHead.Stab G N → (↑F : Set V) ⊆ ↑N → N = ⊤) →
    ∀ N : Submodule ℂ V, R ≤ N → GlobalTheory.TensHead.Stab G N → N ≠ ⊤ →
      ∃ N' : Submodule ℂ V, N ≤ N' ∧ GlobalTheory.TensHead.Stab G N' ∧ N' ≠ ⊤ ∧
        ∀ U : Submodule ℂ V, GlobalTheory.TensHead.Stab G U → N' ≤ U → U = N' ∨ U = ⊤ := by
  first | exact @GlobalTheory.TensHead.exists_maximal_stab_of_finset | exact GlobalTheory.TensHead.exists_maximal_stab_of_finset | (intros; apply GlobalTheory.TensHead.exists_maximal_stab_of_finset <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorEqTopOrLeKerFiniteLengthModules

section

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory.TensHead

theorem tensor_eq_top_or_le_ker_map : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ P₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup P₀] [Module ℂ P₀]
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
  intro ι _ _ M₀ P₀ _ _ _ _ M P _ _ _ _ Op₀ Op Rel₀ Rel p₀ p hr₀ hr hL₀ hloc₀ hRel₀ hK₀ hL hloc hRel hK
    N hN₀ hNi hS₀ hSi
  classical
  have hS : Stab (tensOps Op₀ (piOps Op)) N := by
    rintro f (⟨g, hg, rfl⟩ | ⟨h, ⟨i, g, hg, rfl⟩, rfl⟩) t ht
    · exact hS₀ g hg t ht
    · exact hSi i g hg t ht
  by_cases h0 : LinearMap.ker p₀ = ⊤
  · right
    intro t _
    have : p₀ = 0 := LinearMap.ker_eq_top.mp h0
    rw [LinearMap.mem_ker, this, TensorProduct.map_zero_left, LinearMap.zero_apply]
  by_cases hi : ∃ i, LinearMap.ker (p i) = ⊤
  · right
    obtain ⟨i, hi⟩ := hi
    have hpi : p i = 0 := LinearMap.ker_eq_top.mp hi
    have hmap : PiTensorProduct.map p = 0 := by
      ext y
      simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod,
        LinearMap.zero_apply]
      exact MultilinearMap.map_coord_zero _ i (by simp [hpi])
    intro t _
    rw [LinearMap.mem_ker, hmap, TensorProduct.map_zero_right, LinearMap.zero_apply]
  push_neg at hi
  by_cases hN : N = ⊤
  · exact Or.inl hN
  have hSimple₀ : SimpleOver Op₀ (LinearMap.ker p₀) := fun U hU hKU => by
    by_cases hUt : U = ⊤
    · exact Or.inr hUt
    exact Or.inl (le_antisymm (hloc₀ U (hRel₀.trans hKU) hU hUt) hKU)
  have hSimple : ∀ i, SimpleOver (Op i) (LinearMap.ker (p i)) := fun i U hU hKU => by
    by_cases hUt : U = ⊤
    · exact Or.inr hUt
    exact Or.inl (le_antisymm (hloc i U ((hRel i).trans hKU) hU hUt) hKU)
  obtain ⟨F₀, hF₀⟩ := GlobalTheory.T.exists_finset_generating_operator_stable_bounded Op₀ Rel₀ hL₀
  choose F hF using fun i => GlobalTheory.T.exists_finset_generating_operator_stable_bounded (Op i) (Rel i) (hL i)
  let G : Finset (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)) :=
    (F₀ ×ˢ Fintype.piFinset F).image (fun q => q.1 ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ q.2)
  have hgen : ∀ U, N ≤ U → Stab (tensOps Op₀ (piOps Op)) U → (↑G : Set (M₀ ⊗[ℂ] (⨂[ℂ] i, M i))) ⊆ (U : Set (M₀ ⊗[ℂ] (⨂[ℂ] i, M i))) → U = ⊤ := by
    intro U hNU hU hGU
    refine GlobalTheory.T.eq_top_of_pure_tensors_of_factor_generators Op₀ Op Rel₀ Rel F₀ F hF₀ hF U (fun x hx y => hNU (hN₀ x hx y))
      (fun i x hx x₀ y => hNU (hNi i x hx x₀ y)) hU ?_
    intro x₀ hx₀ y hy
    apply hGU
    simp only [G, Finset.coe_image]
    exact ⟨(x₀, y), by simp [hx₀, Fintype.mem_piFinset, hy], rfl⟩
  obtain ⟨N', hNN', hS', hN'top, hmax⟩ := GlobalTheory.T.exists_maximal_operatorStable_of_finset_generating _ N G hgen N le_rfl hS hN
  have h0' := GlobalTheory.T.tensor_maximalStable_contains_leftKernel Op₀ (piOps Op) Rel₀ (LinearMap.ker p₀) hL₀ hloc₀ h0 hK₀ N'
    (fun x hx y => hNN' (hN₀ x hx y)) hS' hmax
  have hi' : ∀ i, ∀ x ∈ LinearMap.ker (p i), ∀ (x₀ : M₀) (y : ∀ j, M j),
      x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N' := fun i =>
    GlobalTheory.T.piTensor_maximalStable_contains_positionKernel Op₀ Op i (Rel i) (LinearMap.ker (p i)) (hL i) (hloc i) (hi i) (hK i) N'
      (fun x hx x₀ y => hNN' (hNi i x hx x₀ y)) hS' hmax
  have hKT : tensKer (LinearMap.ker p₀) (piKer fun i => LinearMap.ker (p i)) ≤ N' := by
    rw [tensKer, Submodule.span_le]
    rintro t ⟨x, y, hxy | hxy, rfl⟩
    · exact h0' x hxy y
    · refine Submodule.span_induction (p := fun y _ => x ⊗ₜ[ℂ] y ∈ N') ?_ ?_ ?_ ?_ hxy
      · rintro _ ⟨z, ⟨i, hzi⟩, rfl⟩
        have := hi' i (z i) hzi x z
        rwa [Function.update_eq_self] at this
      · simp
      · intro a b _ _ ha hb
        rw [TensorProduct.tmul_add]
        exact N'.add_mem ha hb
      · intro c a _ ha
        rw [TensorProduct.tmul_smul]
        exact N'.smul_mem c ha
  have hPi := GlobalTheory.T.simpleOverStableSubmodule_piTensor Op (fun i => LinearMap.ker (p i)) hr hK hSimple
  have hT := GlobalTheory.T.simpleOverStableSubmodule_tensorPureKernelSpan Op₀ (piOps Op) (LinearMap.ker p₀) (piKer fun i => LinearMap.ker (p i)) hr₀ hK₀
    (GlobalTheory.T.operatorStable_piTensorPureKernelSpan Op _ hK) hSimple₀ hPi
  rcases hT N' hS' hKT with h | h
  · right
    rw [h] at hNN'
    refine hNN'.trans ?_
    have hle : piKer (fun i => LinearMap.ker (p i)) ≤ LinearMap.ker (PiTensorProduct.map p) := by
      rw [piKer, Submodule.span_le]
      rintro _ ⟨z, ⟨i, hzi⟩, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, PiTensorProduct.map_tprod]
      exact MultilinearMap.map_coord_zero _ i (LinearMap.mem_ker.mp hzi)
    rw [tensKer, Submodule.span_le]
    rintro t ⟨x, y, hxy | hxy, rfl⟩
    · simp [TensorProduct.map_tmul, LinearMap.mem_ker.mp hxy]
    · simp [TensorProduct.map_tmul, LinearMap.mem_ker.mp (hle hxy)]
  · exact absurd h hN'top

end GlobalTheory.TensHead
end
end
