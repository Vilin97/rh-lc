module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleSpanAfterMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRestrictEqTopOfAbsIrrSub
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleMatrixRepIsInternalIrreducible
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrSubOfIsIrrSubMap

section

@[expose] public section

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Polynomial

namespace GlobalTheory.AbsIrrOfAlgClosed

theorem span_restrict_eq_top_of_isIrrSub_map {k Γ L : Type} [Field k] [Group Γ] [Field L]
    [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k)
    (W : Submodule k (Fin a → k)) (hW : Stable (matRep ((Units.coeHom _).comp ρ)) W)
    (habs : IsIrrSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))))) :
    Submodule.span k (Set.range fun g =>
      (matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤ := by
  classical
  letI : Algebra k L := f.toAlgebra
  set τ := matRep ((Units.coeHom (Matrix (Fin a) (Fin a) k)).comp ρ) with hτ
  let r : Γ → Module.End k W := fun g => (τ g).restrict (hW g)
  have hr1 : r 1 = 1 := by
    ext v; simp [r]
  have hrm : ∀ g h, r (g * h) = r g * r h := by
    intro g h; ext v; simp [r]
  let d := Module.finrank k W
  let e : W ≃ₗ[k] (Fin d → k) := (Module.finBasis k W).equivFun
  let φ : Module.End k W ≃ₗ[k] Matrix (Fin d) (Fin d) k :=
    e.conj.trans LinearMap.toMatrix'
  have hφa : ∀ x, φ x = LinearMap.toMatrix' ((e : W →ₗ[k] (Fin d → k)) ∘ₗ x ∘ₗ
      (e.symm : (Fin d → k) →ₗ[k] W)) := fun _ => rfl
  have hφ1 : φ 1 = 1 := by
    rw [hφa]
    have : (e : W →ₗ[k] (Fin d → k)) ∘ₗ (1 : Module.End k W) ∘ₗ
        (e.symm : (Fin d → k) →ₗ[k] W) = LinearMap.id := LinearMap.ext fun v => by simp
    rw [this, LinearMap.toMatrix'_id]
  have hφm : ∀ x y, φ (x * y) = φ x * φ y := by
    intro x y
    rw [hφa, hφa, hφa, ← LinearMap.toMatrix'_comp]
    congr 1
    exact LinearMap.ext fun v => by simp
  let S : Γ →* Matrix (Fin d) (Fin d) k :=
    { toFun := fun g => φ (r g)
      map_one' := by rw [hr1, hφ1]
      map_mul' := fun g h => by rw [hrm, hφm] }
  let σ : Γ →* GL (Fin d) k := MonoidHom.toHomUnits S
  have hσ : ∀ g, (σ g : Matrix (Fin d) (Fin d) k) = φ (r g) := fun g => rfl
  let Li : (Fin d → k) →ₗ[k] (Fin a → k) := W.subtype ∘ₗ e.symm.toLinearMap
  have hLinj : Function.Injective Li := by
    intro x y hxy
    exact e.symm.injective (Subtype.val_injective hxy)
  obtain ⟨L', hL'⟩ := LinearMap.exists_leftInverse_of_injective Li (LinearMap.ker_eq_bot.2 hLinj)
  let B : Matrix (Fin a) (Fin d) k := LinearMap.toMatrix' Li
  let C : Matrix (Fin d) (Fin a) k := LinearMap.toMatrix' L'
  have hCB : C * B = 1 := by
    rw [← LinearMap.toMatrix'_comp, hL', LinearMap.toMatrix'_id]
  have hBv : ∀ c, B.mulVec c = Li c := fun c => LinearMap.toMatrix'_mulVec Li c
  have hint : ∀ g, (ρ g : Matrix (Fin a) (Fin a) k) * B = B * (σ g : Matrix (Fin d) (Fin d) k) := by
    intro g
    have hM : (ρ g : Matrix (Fin a) (Fin a) k) = LinearMap.toMatrix' (τ g) := by
      have : τ g = Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k) :=
        LinearMap.ext fun v => by rw [hτ, GlobalTheory.BurnsideSub.matRep_apply, Matrix.toLin'_apply]
      rw [this, LinearMap.toMatrix'_toLin']
    rw [hσ, hφa, hM, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun c => ?_
    change τ g ((e.symm c : W) : Fin a → k) = ((e.symm (e (r g (e.symm c))) : W) : Fin a → k)
    rw [e.symm_apply_apply]
    rfl
  have hspan : Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))) =
      LinearMap.range (B.map f).mulVecLin := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨f ∘ e ⟨w, hw⟩, ?_⟩
      funext i
      have h1 : B.mulVec (e ⟨w, hw⟩) = w := by
        rw [hBv]
        change ((e.symm (e ⟨w, hw⟩) : W) : Fin a → k) = w
        rw [e.symm_apply_apply]
      rw [Matrix.mulVecLin_apply, ← RingHom.map_mulVec, h1]
      rfl
    · rintro _ ⟨c, rfl⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [op_smul_eq_smul]
      refine Submodule.smul_mem _ _ ?_
      apply Submodule.subset_span
      refine ⟨Li (Pi.single j 1), (e.symm (Pi.single j 1)).2, ?_⟩
      funext i
      simp [← hBv, Matrix.mulVec_single_one]
  rw [hspan] at habs
  have hirr : IsIrrSub (mapRep f σ) ⊤ := by
    refine GlobalTheory.BurnsideSub.isIrrSub_top_of_intertwine (mapRep f ρ) (mapRep f σ) (B.map f)
      (C.map f) ?_ ?_ habs
    · rw [← Matrix.map_mul, hCB]
      exact Matrix.map_one _ f.map_zero f.map_one
    · intro g
      change (ρ g : Matrix (Fin a) (Fin a) k).map f * B.map f =
        B.map f * (σ g : Matrix (Fin d) (Fin d) k).map f
      rw [← Matrix.map_mul, ← Matrix.map_mul, hint g]
  have h2 := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub _ hirr
  have h3 : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (mapRep f σ) =
      fun g => (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ g).map (algebraMap k L) := by
    funext g
    ext p q
    simp [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, mapRep, RingHom.algebraMap_toAlgebra]
  rw [h3] at h2
  have h4 := GlobalTheory.BurnsideField.span_eq_top_of_span_map (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) h2
  have h5 : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) = φ '' Set.range r := by
    rw [← Set.range_comp]; rfl
  have h6 := Submodule.map_span φ.toLinearMap (Set.range r)
  change Submodule.span k (Set.range r) = ⊤
  refine Submodule.map_injective_of_injective φ.injective ?_
  rw [h6, Submodule.map_top, LinearEquiv.range]
  rw [h5] at h4
  exact h4

theorem absIrrSub_of_isIrrSub_map : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L]
    (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)), IsInv ρ W →
    IsIrrSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))) →
    AbsIrrSub ρ W := by
  intro k Γ L _ _ _ _ f a ρ W hinv hirr
  have hW : Stable (matRep ((Units.coeHom _).comp ρ)) W := fun g v hv => by
    have := hinv g v hv
    simpa [GlobalTheory.BurnsideSub.matRep_apply] using this
  have hne : W ≠ ⊥ := by
    intro h0
    apply hirr.1
    rw [h0]
    simp
  have hsp := span_restrict_eq_top_of_isIrrSub_map f ρ W hW hirr
  unfold AbsIrrSub
  exact GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top _ ρ W hW hne hsp

end GlobalTheory.AbsIrrOfAlgClosed
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrSubOfIsIrrSubMapStatement

section

@[expose] public section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

theorem _root_.GlobalTheory.T.absIrrSub_of_isIrrSub_span_map : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)), IsInv ρ W → IsIrrSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))) → AbsIrrSub ρ W := by
  first | exact @GlobalTheory.AbsIrrOfAlgClosed.absIrrSub_of_isIrrSub_map | exact GlobalTheory.AbsIrrOfAlgClosed.absIrrSub_of_isIrrSub_map | (intros; apply GlobalTheory.AbsIrrOfAlgClosed.absIrrSub_of_isIrrSub_map <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixSystemNonzeroSolutionDescends

section

@[expose] public section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

theorem matrix_system_nonzero_solution_descends {k L Γ : Type} [Field k] [Field L] (f : k →+* L)
    {a b c : ℕ} (A : Γ → Matrix (Fin a) (Fin a) k) (B : Γ → Matrix (Fin b) (Fin b) k)
    (Q : Matrix (Fin c) (Fin a) k) (C : Matrix (Fin a) (Fin b) L) :
    C ≠ 0 → (∀ g, (A g).map f * C = C * (B g).map f) → Q.map f * C = 0 →
      ∃ X : Matrix (Fin a) (Fin b) k, X ≠ 0 ∧ (∀ g, A g * X = X * B g) ∧ Q * X = 0 := by
  intro hC hAB hQ
  letI := f.toAlgebra
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, C i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hC (Matrix.ext h)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k L, φ (C i₀ j₀) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hij ((Module.forall_dual_apply_eq_zero_iff k (C i₀ j₀)).mp h)
  have key : ∀ (x : k) (y : L), φ (f x * y) = x * φ y := by
    intro x y
    have h1 : f x * y = x • y := (Algebra.smul_def x y).symm
    rw [h1, map_smul, smul_eq_mul]
  have key' : ∀ (x : k) (y : L), φ (y * f x) = φ y * x := by
    intro x y
    rw [mul_comm y, key, mul_comm]
  refine ⟨C.map φ, ?_, ?_, ?_⟩
  · intro h
    apply hφ
    have := congrFun (congrFun h i₀) j₀
    simpa using this
  · intro g
    ext i j
    have := congrArg φ (congrFun (congrFun (hAB g) i) j)

    simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum, key, key'] using this
  · ext i j
    have := congrArg φ (congrFun (congrFun hQ i) j)

    simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum, key, Matrix.zero_apply, map_zero]
    using this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixSystemNonzeroSolutionDescendsStatement

section

@[expose] public section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

theorem _root_.GlobalTheory.T.exists_ne_zero_intertwiner_of_map : ∀ {k L Γ : Type} [Field k] [Field L] (f : k →+* L) {a b c : ℕ} (A : Γ → Matrix (Fin a) (Fin a) k) (B : Γ → Matrix (Fin b) (Fin b) k) (Q : Matrix (Fin c) (Fin a) k) (C : Matrix (Fin a) (Fin b) L), C ≠ 0 → (∀ g, (A g).map f * C = C * (B g).map f) → Q.map f * C = 0 → ∃ X : Matrix (Fin a) (Fin b) k, X ≠ 0 ∧ (∀ g, A g * X = X * B g) ∧ Q * X = 0 := by
  first | exact @GlobalTheory.matrix_system_nonzero_solution_descends | exact GlobalTheory.matrix_system_nonzero_solution_descends | (intros; apply GlobalTheory.matrix_system_nonzero_solution_descends <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAbsolutelyIrreducibleSplitRepOfConstituentMode

section

@[expose] public section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory.SplitCrit

variable {k L : Type} [Field k] [Field L]

abbrev ext (f : k →+* L) {a : ℕ} (W : Submodule k (Fin a → k)) : Submodule L (Fin a → L) :=
  Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))

theorem map_mulVec_comp (f : k →+* L) {m n : ℕ} (M : Matrix (Fin m) (Fin n) k) (v : Fin n → k) :
    (M.map f).mulVec (f ∘ v) = f ∘ M.mulVec v := by
  funext i; exact (RingHom.map_mulVec f M v i).symm

theorem ext_le_comap (f : k →+* L) {m n : ℕ} (M : Matrix (Fin m) (Fin n) k)
    (U : Submodule k (Fin n → k)) (U' : Submodule k (Fin m → k)) (h : ∀ v ∈ U, M.mulVec v ∈ U') :
    ext f U ≤ (ext f U').comap (M.map f).mulVecLin := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, hv, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
  rw [map_mulVec_comp]
  exact Submodule.subset_span ⟨_, h v hv, rfl⟩

theorem ext_ne_bot (f : k →+* L) {a : ℕ} {W : Submodule k (Fin a → k)} (hW : W ≠ ⊥) : ext f W ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  intro h
  have : f ∘ v ∈ ext f W := Submodule.subset_span ⟨v, hv, rfl⟩
  rw [h, Submodule.mem_bot] at this
  apply hv0; funext i
  have := congrFun this i
  simpa using this

theorem finrank_ext_le (f : k →+* L) {a : ℕ} (W : Submodule k (Fin a → k)) :
    Module.finrank L (ext f W) ≤ Module.finrank k W := by
  let e := Module.finBasis k W
  have hle : ext f W ≤ Submodule.span L (Set.range fun i => f ∘ (e i : Fin a → k)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v = ∑ i, (e.repr ⟨v, hv⟩ i) • (e i : Fin a → k) := by
      have := congrArg Subtype.val (e.sum_repr ⟨v, hv⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    have : f ∘ v = ∑ i, f (e.repr ⟨v, hv⟩ i) • (f ∘ (e i : Fin a → k)) := by
      conv_lhs => rw [hv']
      funext j

      simp [Finset.sum_apply, map_sum]
    show f ∘ v ∈ _
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  calc Module.finrank L (ext f W)
      ≤ Module.finrank L (Submodule.span L (Set.range fun i => f ∘ (e i : Fin a → k))) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (Module.finrank k W)) := finrank_range_le_card _
    _ = Module.finrank k W := Fintype.card_fin _

theorem range_ne_bot {K : Type} [Field K] {m n : ℕ} {X : Matrix (Fin m) (Fin n) K} (hX : X ≠ 0) :
    LinearMap.range X.mulVecLin ≠ ⊥ := by
  intro h
  apply hX
  refine Matrix.ext_of_mulVec_single fun i => ?_
  have : X.mulVecLin (Pi.single i 1) ∈ LinearMap.range X.mulVecLin := LinearMap.mem_range_self _ _
  rw [h, Submodule.mem_bot, Matrix.mulVecLin_apply] at this
  rw [this, Matrix.zero_mulVec]

end GlobalTheory.SplitCrit

namespace GlobalTheory.SplitCrit

theorem splitRep_of_models : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k), (∀ V, IsIrrSub (mapRep f ρ) V → ∃ (b : ℕ) (σ : Γ →* GL (Fin b) k) (C : Matrix (Fin a) (Fin b) L), Function.Injective C.mulVec ∧ LinearMap.range C.mulVecLin = V ∧ ∀ g, ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * C = C * ((mapRep f σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L)) → GlobalTheory.SplitCoef.SplitRep ρ := by
  intro k Γ L _ _ _ _ f a ρ hmod W hW
  obtain ⟨hW0, hWi, hWmin⟩ := hW

  have hLi : IsInv (mapRep f ρ) (ext f W) := fun g v hv =>
    ext_le_comap f (ρ g : Matrix (Fin a) (Fin a) k) W W (hWi g) hv
  obtain ⟨V, hVle, hV⟩ := GlobalTheory.SemisimpleDecomp.exists_irr_le hLi (ext_ne_bot f hW0)
  obtain ⟨b, σ, C, hCinj, hCr, hCint⟩ := hmod V hV

  obtain ⟨W', hc⟩ := Submodule.exists_isCompl W
  let φ : (Fin a → k) →ₗ[k] (Fin a → k) := W'.subtype.comp (W'.projectionOnto W hc.symm)
  have hφ : ∀ v, φ v = 0 ↔ v ∈ W := by
    intro v
    have hk := Submodule.ker_projectionOnto hc.symm
    simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply, ZeroMemClass.coe_eq_zero]
    rw [← LinearMap.mem_ker, hk]
  let Q := LinearMap.toMatrix' φ
  have hQ : ∀ v, Q.mulVec v = 0 ↔ v ∈ W := fun v => by
    simp only [Q, LinearMap.toMatrix'_mulVec]; exact hφ v

  have hQL : ext f W ≤ LinearMap.ker (Q.map f).mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    rw [map_mulVec_comp, (hQ v).2 hv]
    funext i; simp
  have hQC : Q.map f * C = 0 := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
    have : C.mulVec (Pi.single j 1) ∈ V := hCr ▸ LinearMap.mem_range_self C.mulVecLin _
    have := hQL (hVle this)
    simpa using this
  have hC0 : C ≠ 0 := by
    intro h; apply hV.1; rw [← hCr, h]
    ext x; simp
  have hint : ∀ g, ((ρ g : Matrix (Fin a) (Fin a) k)).map f * C = C * ((σ g : Matrix (Fin b) (Fin b) k)).map f :=
    fun g => hCint g
  obtain ⟨X, hX0, hXint, hQX⟩ := GlobalTheory.T.exists_ne_zero_intertwiner_of_map f (fun g => (ρ g : Matrix (Fin a) (Fin a) k))
    (fun g => (σ g : Matrix (Fin b) (Fin b) k)) Q C hC0 hint hQC

  have hXW : LinearMap.range X.mulVecLin ≤ W := by
    rintro _ ⟨w, rfl⟩
    rw [← hQ, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQX, Matrix.zero_mulVec]
  have hXi : IsInv ρ (LinearMap.range X.mulVecLin) := by
    rintro g _ ⟨w, rfl⟩
    refine ⟨(σ g : Matrix (Fin b) (Fin b) k).mulVec w, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hXint g]
  have hXeq : LinearMap.range X.mulVecLin = W :=
    (hWmin _ hXW hXi).resolve_left (range_ne_bot hX0)
  have hWb : Module.finrank k W ≤ b := by
    rw [← hXeq]
    exact (LinearMap.finrank_range_le _).trans (Module.finrank_fin_fun k).le
  have hVb : Module.finrank L V = b := by
    rw [← hCr, LinearMap.finrank_range_of_inj hCinj, Module.finrank_fin_fun]
  have hVeq : V = ext f W :=
    Submodule.eq_of_le_of_finrank_le hVle ((finrank_ext_le f W).trans (hWb.trans hVb.ge))
  have hV' : IsIrrSub (mapRep f ρ) (ext f W) := hVeq ▸ hV
  exact GlobalTheory.T.absIrrSub_of_isIrrSub_span_map f ρ W hWi hV'

end GlobalTheory.SplitCrit
end
end
