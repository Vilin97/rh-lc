module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentTerms
public import Mathlib.RingTheory.Localization.FractionRing
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.Imports

section

@[expose] public section

namespace GlobalTheory.SmulMemOfMemSpan

theorem exists_smul_mem_of_mem_span {R K V : Type} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V]
    [IsScalarTower R K V] (M : Submodule R V) {v : V}
    (hv : v ∈ Submodule.span K (M : Set V)) : ∃ a : R, a ≠ 0 ∧ a • v ∈ M := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm a b, mul_smul]; exact M.smul_mem b hax
    · rw [mul_smul]; exact M.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors R) c
    dsimp only at hnd
    refine ⟨d * a, mul_ne_zero (nonZeroDivisors.ne_zero d.2) ha, ?_⟩
    have key : (d : R) • c • x = n • x := by
      rw [← algebraMap_smul K (d : R) (c • x), smul_smul, mul_comm, hnd, algebraMap_smul]
    rw [mul_comm (d : R) a, mul_smul, key, smul_comm a n x]
    exact M.smul_mem n hax

theorem main : ∀ {R K V : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field K] [inst_3 : Algebra R K] [IsFractionRing R K] [inst_5 : AddCommGroup V] [inst_6 : Module R V] [inst_7 : Module K V] [IsScalarTower R K V] (M : Submodule R V) {v : V}, v ∈ Submodule.span K (↑M : Set V) → ∃ (a : R), a ≠ (0 : R) ∧ a • v ∈ M :=
  by
  intro R K V _ _ _ _ _ _ _ _ _ M v hv
  exact exists_smul_mem_of_mem_span M hv

end GlobalTheory.SmulMemOfMemSpan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsAlt

section

@[expose] public section

namespace GlobalTheory.LemmaTwoFortyThirteen

theorem main {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) (h : ∀ v : V, ∃ a : R, a ≠ (0 : R) ∧ a • v ∈ M) :
    Submodule.span K (↑M : Set V) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨a, ha, hav⟩ := h v
  have hK : algebraMap R K a ≠ 0 := by
    simpa using (IsFractionRing.injective R K).ne ha
  have hv : v = (algebraMap R K a)⁻¹ • (a • v) := by
    rw [← algebraMap_smul K a v, smul_smul, inv_mul_cancel₀ hK, one_smul]
  rw [hv]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hav)

end GlobalTheory.LemmaTwoFortyThirteen
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLatticeChainLatAndComap

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.ChainLattice

theorem exists_smul_mem {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ a : R, a ≠ 0 ∧ a • v ∈ M := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R K V h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 M v hv; exact @_root_.GlobalTheory.SmulMemOfMemSpan.main)
  | exact @_root_.GlobalTheory.SmulMemOfMemSpan.main
  | exact _root_.GlobalTheory.SmulMemOfMemSpan.main
  | (apply _root_.GlobalTheory.SmulMemOfMemSpan.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemOfMemSpan.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemOfMemSpan.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemOfMemSpan.main ..)

theorem span_eq_top_of_smul_mem {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) (h : ∀ v : V, ∃ a : R, a ≠ 0 ∧ a • v ∈ M) :
    Submodule.span K (M : Set V) = ⊤ := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R K V h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 M h; exact @_root_.GlobalTheory.LemmaTwoFortyThirteen.main)
  | exact @_root_.GlobalTheory.LemmaTwoFortyThirteen.main
  | exact _root_.GlobalTheory.LemmaTwoFortyThirteen.main
  | (apply _root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LemmaTwoFortyThirteen.main ..)

theorem isLattice_chainLat_and_comap :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : Type) [Fintype n] [DecidableEq n] (c : ℕ),
      (∀ (ϖ : 𝒪[k]), (ϖ : k) ≠ 0 → ∀ L : Submodule 𝒪[k] (n → k), Submodule.IsLattice k L →
        Submodule.IsLattice k (chainLat ϖ c L)) ∧
      ∀ Λ : Submodule 𝒪[k] (n ⊕ Fin c → k), Submodule.IsLattice k Λ →
        Submodule.IsLattice k (Λ.comap (inX k n c)) := by
  intro k _ _ _ _ n _ _ c
  refine ⟨fun ϖ hϖ L hL => ⟨?_, ?_⟩, fun Λ hΛ => ⟨?_, ?_⟩⟩
  · exact (hL.fg.map _).sup (Submodule.fg_span (Set.finite_range _))
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · refine Submodule.fg_of_fg_map_injective (inX k n c) ?_
      (hΛ.fg.of_le (Submodule.map_comap_le _ _))
    intro x y hxy
    funext r
    have := congrFun hxy (Sum.inl r)
    simpa [inX_apply] using this
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

end GlobalTheory.RootEx.ChainLattice
end
end
