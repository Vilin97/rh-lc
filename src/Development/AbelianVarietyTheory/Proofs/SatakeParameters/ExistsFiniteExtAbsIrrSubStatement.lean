module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndSpannedByRepMatricesOfScalarExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapMulVecMemOfMemSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbittAlg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubrepIsoSummandOfIsInternalStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleMatrixRepIsInternalIrreducible
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndSpannedOfIsIrrSubOfIsAlgClosed

section

@[expose] public section

open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

namespace GlobalTheory.SplitField

theorem endSpanned_of_isIrrSub_of_isAlgClosed :
    ∀ {Γ E : Type} [Group Γ] [Field E] [IsAlgClosed E] {a : ℕ} (σ : Γ →* GL (Fin a) E)
      (U : Submodule E (Fin a → E)), IsIrrSub σ U → EndSpanned σ U := by
  intro Γ E _ _ _ a σ U h
  classical
  have hinv : ∀ g, ∀ v ∈ U, (Matrix.toLin' ((σ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)) v ∈ U :=
    fun g v hv => by rw [Matrix.toLin'_apply]; exact h.2.1 g v hv
  let r : Representation E Γ U :=
    { toFun := fun g => (Matrix.toLin' ((σ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)).restrict (hinv g)
      map_one' := by
        ext v i
        simp [LinearMap.restrict_apply]
      map_mul' := fun g g' => by
        ext v i
        simp [LinearMap.restrict_apply, Matrix.mulVec_mulVec] }
  have hr : ∀ g (v : U), ((r g v : U) : Fin a → E) = ((σ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E).mulVec v :=
    fun g v => by simp [r, LinearMap.restrict_apply]
  have hirr : r.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation r) := by
      refine ⟨⊥, ⊤, fun hbt => h.1 ?_⟩
      have h2 := congrArg Subrepresentation.toSubmodule hbt
      change (⊥ : Submodule E U) = ⊤ at h2
      rw [eq_bot_iff]
      intro v hv
      have : (⟨v, hv⟩ : U) ∈ (⊥ : Submodule E U) := by rw [h2]; trivial
      rw [Submodule.mem_bot] at this
      simpa using congrArg Subtype.val this
    refine ⟨fun W => ?_⟩
    have hle : W.toSubmodule.map U.subtype ≤ U := by
      rintro _ ⟨v, _, rfl⟩; exact v.2
    have hinvW : IsInv σ (W.toSubmodule.map U.subtype) := by
      rintro g _ ⟨v, hv, rfl⟩
      refine ⟨r g v, W.apply_mem_toSubmodule g hv, ?_⟩
      simp [hr]
    rcases h.2.2 _ hle hinvW with h1 | h1
    · left
      refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun v hv => ?_)
      have : (v : Fin a → E) ∈ W.toSubmodule.map U.subtype := ⟨v, hv, rfl⟩
      rw [h1, Submodule.mem_bot] at this
      show v ∈ (⊥ : Submodule E U)
      rw [Submodule.mem_bot]; exact Subtype.ext this
    · right
      refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun v _ => ?_)
      have : (v : Fin a → E) ∈ W.toSubmodule.map U.subtype := by rw [h1]; exact v.2
      obtain ⟨w, hw, hwv⟩ := this
      rwa [show w = v from Subtype.ext hwv] at hw
  have hs := GlobalTheory.BurnsideField.span_range_eq_top_of_isAlgClosed r hirr
  intro φ
  have hφ : φ ∈ Submodule.span E (Set.range r) := by rw [hs]; trivial
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact ⟨_, Submodule.subset_span ⟨g, rfl⟩, fun w => (hr g w).symm⟩
  | zero => exact ⟨0, Submodule.zero_mem _, fun w => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨X, hX, hXw⟩ := hx
    obtain ⟨Y, hY, hYw⟩ := hy
    exact ⟨X + Y, Submodule.add_mem _ hX hY, fun w => by rw [Matrix.add_mulVec, hXw, hYw]; simp⟩
  | smul c x _ hx =>
    obtain ⟨X, hX, hXw⟩ := hx
    exact ⟨c • X, Submodule.smul_mem _ c hX, fun w => by rw [Matrix.smul_mulVec, hXw]; simp⟩

end GlobalTheory.SplitField
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndSpannedOfIsIrrSubOfIsAlgClosedStatement

section

@[expose] public section

open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

theorem _root_.GlobalTheory.T.endSpanned_of_isIrrSub_of_isAlgClosed' : ∀ {Γ E : Type} [Group Γ] [Field E] [IsAlgClosed E] {a : ℕ} (σ : Γ →* GL (Fin a) E) (U : Submodule E (Fin a → E)), IsIrrSub σ U → EndSpanned σ U := by
  first | exact @GlobalTheory.SplitField.endSpanned_of_isIrrSub_of_isAlgClosed | exact GlobalTheory.SplitField.endSpanned_of_isIrrSub_of_isAlgClosed | (intros; apply GlobalTheory.SplitField.endSpanned_of_isIrrSub_of_isAlgClosed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInternalStableDecompositionDescendsToSubfi

section

@[expose] public section

open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

namespace GlobalTheory.SplitField

def coordMap {L E : Type} [Field L] [Field E] (f : L →+* E) (a : ℕ) :
    (Fin a → L) →ₛₗ[f] (Fin a → E) where
  toFun v := f ∘ v
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp [smul_eq_mul]

theorem coordMap_injective {L E : Type} [Field L] [Field E] (f : L →+* E) (a : ℕ) :
    Function.Injective (coordMap f a) := by
  intro v w h
  funext i
  exact f.injective (congrFun h i)

theorem descend_decomp {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a n : ℕ}
    (τ : Γ →* GL (Fin a) L) (Vs : Fin n → Submodule E (Fin a → E)) (hint : DirectSum.IsInternal Vs)
    (hinv : ∀ m, IsInv (mapRep f τ) (Vs m))
    (hspan : ∀ m, Vs m ≤ Submodule.span E ((fun v => f ∘ v) '' {v : Fin a → L | f ∘ v ∈ Vs m})) :
    ∃ Us : Fin n → Submodule L (Fin a → L), DirectSum.IsInternal Us ∧
      ∀ m, IsInv τ (Us m) ∧ Submodule.span E ((fun v => f ∘ v) '' (Us m : Set (Fin a → L))) = Vs m := by
  classical
  set F := coordMap f a with hF
  let Us : Fin n → Submodule L (Fin a → L) := fun m => (Vs m).comap F
  have hUs : ∀ m, (Us m : Set (Fin a → L)) = {v : Fin a → L | f ∘ v ∈ Vs m} := fun m => rfl
  obtain ⟨hindV, htopV⟩ := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top Vs).1 hint
  refine ⟨Us, ?_, fun m => ⟨?_, ?_⟩⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨?_, ?_⟩
    · rw [iSupIndep_def]
      intro i
      rw [Submodule.disjoint_def]
      intro v hv1 hv2
      have hle : (⨆ (j : Fin n) (_ : j ≠ i), Us j) ≤ (⨆ (j : Fin n) (_ : j ≠ i), Vs j).comap F :=
        iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ i) => Vs j) j hj)
      have h1 : F v ∈ Vs i := hv1
      have h2 : F v ∈ ⨆ (j : Fin n) (_ : j ≠ i), Vs j := hle hv2
      have h3 := (Submodule.disjoint_def.1 ((iSupIndep_def.1 hindV) i)) _ h1 h2
      exact coordMap_injective f a (by rw [h3, map_zero])
    · rw [eq_top_iff]
      intro v _
      have hle : (⨆ m, Vs m) ≤ Submodule.span E ((fun v => f ∘ v) '' ((⨆ m, Us m : Submodule L (Fin a → L)) : Set (Fin a → L))) := by
        refine iSup_le fun m => (hspan m).trans (Submodule.span_mono (Set.image_mono ?_))
        rw [← hUs m]
        exact le_iSup Us m
      have hv : f ∘ v ∈ ⨆ m, Vs m := by rw [htopV]; exact Submodule.mem_top
      have := mem_span_of_map_mem_span f _ v (hle hv)
      rwa [Submodule.span_eq] at this
  · intro g v hv
    have hv' : f ∘ v ∈ Vs m := hv
    show f ∘ ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec v ∈ Vs m
    have hm : f ∘ ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec v =
        ((mapRep f τ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E).mulVec (f ∘ v) := by
      funext i
      exact RingHom.map_mulVec f _ v i
    rw [hm]
    exact hinv m g _ hv'
  · refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      exact hv
    · rw [hUs m]
      exact hspan m

end GlobalTheory.SplitField
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInternalStableDecompositionDescendsToSubfiStatement

section

@[expose] public section

open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

theorem _root_.GlobalTheory.T.exists_internal_stable_decomposition_descends_to_subfield : ∀ {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a n : ℕ} (τ : Γ →* GL (Fin a) L) (Vs : Fin n → Submodule E (Fin a → E)), DirectSum.IsInternal Vs → (∀ m, IsInv (mapRep f τ) (Vs m)) → (∀ m, Vs m ≤ Submodule.span E ((fun v => f ∘ v) '' {v : Fin a → L | f ∘ v ∈ Vs m})) → ∃ Us : Fin n → Submodule L (Fin a → L), DirectSum.IsInternal Us ∧ ∀ m, IsInv τ (Us m) ∧ Submodule.span E ((fun v => f ∘ v) '' (Us m : Set (Fin a → L))) = Vs m := by
  first | exact @GlobalTheory.SplitField.descend_decomp | exact GlobalTheory.SplitField.descend_decomp | (intros; apply GlobalTheory.SplitField.descend_decomp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteExtAbsIrrSub

section

@[expose] public section

open Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.SplitField

theorem exists_finite_ext_absIrrSub : ∀ {K Γ ι : Type} [Field K] [Group Γ] [Finite ι] {a : ℕ} (ρ : ι → (Γ →* GL (Fin a) K)), (∀ j, IsSSRep (mapRep (algebraMap K (AlgebraicClosure K)) (ρ j))) → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K'), ∀ j W, IsIrrSub (mapRep (algebraMap K K') (ρ j)) W → AbsIrrSub (mapRep (algebraMap K K') (ρ j)) W := by
  intro K Γ ι _ _ _ a ρ hss
  classical
  have hdec := fun j => GlobalTheory.semisimple_matrix_rep_decomp (mapRep (algebraMap K (AlgebraicClosure K)) (ρ j)) (hss j)
  choose n Vs hint hirr using hdec
  let b : ∀ j m, Module.Basis (Fin (Module.finrank (AlgebraicClosure K) (Vs j m))) (AlgebraicClosure K) (Vs j m) :=
    fun j m => Module.finBasis (AlgebraicClosure K) (Vs j m)
  let S : Set (AlgebraicClosure K) := Set.range (fun p : (Σ j, Σ m : Fin (n j), Fin (Module.finrank (AlgebraicClosure K) (Vs j m)) × Fin a) =>
    ((b p.1 p.2.1 p.2.2.1 : Vs p.1 p.2.1) : Fin a → AlgebraicClosure K) p.2.2.2)
  obtain ⟨K', _, _, _, f, hf, hS⟩ := exists_finite_field S (Set.finite_range _)
  refine ⟨K', inferInstance, inferInstance, inferInstance, ?_⟩
  intro j
  set τ := mapRep (algebraMap K K') (ρ j) with hτ
  have hcomp : mapRep f τ = mapRep (algebraMap K (AlgebraicClosure K)) (ρ j) := by
    rw [hτ, mapRep_mapRep]
    congr 1
    exact RingHom.ext hf
  have hsp : ∀ m, Vs j m ≤ Submodule.span (AlgebraicClosure K) ((fun v => f ∘ v) '' {v : Fin a → K' | f ∘ v ∈ Vs j m}) := by
    intro m
    have h1 : Vs j m = Submodule.span _ (Set.range fun k => ((b j m k : Vs j m) : Fin a → AlgebraicClosure K)) := by
      have := congrArg (Submodule.map (Vs j m).subtype) (b j m).span_eq
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at this
      refine this.symm.trans ?_
      rw [← Set.range_comp]; rfl
    conv_lhs => rw [h1]
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have hc : ∀ i, ∃ c : K', f c = ((b j m k : Vs j m) : Fin a → AlgebraicClosure K) i :=
      fun i => hS ⟨⟨j, m, k, i⟩, rfl⟩
    choose c hc using hc
    have hfc : f ∘ c = ((b j m k : Vs j m) : Fin a → AlgebraicClosure K) := funext hc
    refine Submodule.subset_span ⟨c, ?_, ?_⟩
    · show f ∘ c ∈ Vs j m
      rw [hfc]; exact (b j m k).2
    · exact hfc
  obtain ⟨Us, hUi, hUs⟩ := GlobalTheory.T.exists_internal_stable_decomposition_descends_to_subfield f τ (Vs j) (hint j) (fun m => hcomp ▸ (hirr j m).2.1) hsp
  have hES : ∀ m, EndSpanned τ (Us m) := by
    intro m
    apply GlobalTheory.T.endSpannedByRepMatrices_of_scalarExtension f τ (Us m)
    rw [(hUs m).2, hcomp]
    exact GlobalTheory.T.endSpanned_of_isIrrSub_of_isAlgClosed' _ _ (hirr j m)
  have hne : ∀ m, Us m ≠ ⊥ := by
    intro m h
    apply (hirr j m).1
    rw [← (hUs m).2, h]
    simp
  have hUirr : ∀ m, IsIrrSub τ (Us m) := fun m => isIrrSub_of_endSpanned τ (Us m) (hne m) (hUs m).1 (hES m)
  intro W hW
  obtain ⟨m, hm⟩ := GlobalTheory.T.irreducible_subrep_iso_summand_of_isInternal τ Us hUi hUirr W hW
  exact absIrrSub_of_endSpanned τ W hW.1 hW.2.1 (endSpanned_of_isoSub τ W (Us m) hW.2.1 hm (hES m))
end GlobalTheory.SplitField
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteExtAbsIrrSubStatement

section

@[expose] public section

open Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.exists_finiteDimensional_ext_irrSub_absIrr : ∀ {K Γ ι : Type} [Field K] [Group Γ] [Finite ι] {a : ℕ} (ρ : ι → (Γ →* GL (Fin a) K)), (∀ j, IsSSRep (mapRep (algebraMap K (AlgebraicClosure K)) (ρ j))) → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K'), ∀ j W, IsIrrSub (mapRep (algebraMap K K') (ρ j)) W → AbsIrrSub (mapRep (algebraMap K K') (ρ j)) W := by
  first | exact @GlobalTheory.SplitField.exists_finite_ext_absIrrSub | exact GlobalTheory.SplitField.exists_finite_ext_absIrrSub | (intros; apply GlobalTheory.SplitField.exists_finite_ext_absIrrSub <;> assumption)
end
end
