module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCentralScalarDistinctGeometricLemmaCellsStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleTensorOfJacquetSubquotient
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedParabolicInductionReindexEquivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntertwiningOfCentralFiltrationStep

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


namespace GlobalTheory

namespace CentralSplit

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

noncomputable def prodOp (ρ : Representation ℂ G V) (z : G) (a : ℕ → ℂ) : ℕ → Module.End ℂ V
  | 0 => 1
  | m + 1 => prodOp ρ z a m * (ρ z - a m • 1)

noncomputable def prodScal (c : ℂ) (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | m + 1 => prodScal c a m * (c - a m)

theorem prodOp_succ_apply (ρ : Representation ℂ G V) (z : G) (a : ℕ → ℂ) (m : ℕ) (v : V) :
    prodOp ρ z a (m + 1) v = prodOp ρ z a m (ρ z v - a m • v) := by
  simp [prodOp]

theorem prodOp_comm (ρ : Representation ℂ G V) (z : G) (hz : ∀ g, g * z = z * g) (a : ℕ → ℂ)
    (m : ℕ) (g : G) (v : V) : prodOp ρ z a m (ρ g v) = ρ g (prodOp ρ z a m v) := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    have hzg : ρ z (ρ g v) = ρ g (ρ z v) := by
      rw [← Module.End.mul_apply, ← map_mul, ← hz, map_mul, Module.End.mul_apply]
    rw [prodOp_succ_apply, prodOp_succ_apply, hzg, ← LinearMap.map_smul (ρ g),
      ← LinearMap.map_sub (ρ g), ih]

theorem prodScal_ne_zero (c : ℂ) (a : ℕ → ℂ) (M : ℕ) (h : ∀ m < M, a m ≠ c) :
    ∀ m ≤ M, prodScal c a m ≠ 0 := by
  intro m hm
  induction m with
  | zero => simp [prodScal]
  | succ m ih =>
    simp only [prodScal]
    exact mul_ne_zero (ih (by omega)) (sub_ne_zero.2 (h m (by omega)).symm)

end CentralSplit


open CentralSplit in
theorem exists_intertwining_of_central_step : ∀ {G V Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G Y) (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ),
    Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ → ∀ (z : G), (∀ g, g * z = z * g) →
    ∀ (t₀ : Fin N) (c : ℂ) (c' : Fin N → ℂ), (∀ t, t ≠ t₀ → c' t ≠ c) →
    (∀ t, t ≠ t₀ → ∀ y, subQuot (S t.succ) (S t.castSucc) z y = c' t • y) →
    Nonempty ((subQuot (S t₀.succ) (S t₀.castSucc)).Equiv τ) → (∀ y, τ z y = c • y) → Nontrivial Y →
    ∃ (φ : ρ.IntertwiningMap τ) (v : V), φ v ≠ 0 := by
  intro G V Y _ _ _ _ _ ρ τ N S _ _ htop z hz t₀ c c' hc' hstep hΨ hτ _
  obtain ⟨Ψ⟩ := hΨ
  set B := S t₀.succ with hBdef
  set A := S t₀.castSucc with hAdef
  let a : ℕ → ℂ := fun i => if h : i < N then c' ⟨i, h⟩ else 0
  let M := N - (t₀.val + 1)

  have hZ : ∀ y, subQuot B A z y = c • y := by
    intro y
    apply Ψ.toLinearEquiv.injective
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap z y
    rw [Representation.Equiv.toLinearEquiv_apply, h1, hτ, map_smul, Representation.Equiv.toLinearEquiv_apply]
  have ha : ∀ m (hm : t₀.val + 1 + m < N), a (t₀.val + 1 + m) = c' ⟨t₀.val + 1 + m, by omega⟩ := by
    intro m hm; simp [a, hm]

  have L1 : ∀ m, ∀ (h : t₀.val + 1 + m < N + 1), ∀ v, v ∈ (S ⟨t₀.val + 1 + m, h⟩).toSubmodule →
      prodOp ρ z (fun i => a (t₀.val + 1 + i)) m v ∈ B.toSubmodule := by
    intro m
    induction m with
    | zero =>
      intro h v hv
      have e : (⟨t₀.val + 1 + 0, h⟩ : Fin (N + 1)) = t₀.succ := by ext; simp
      rw [e] at hv
      exact hv
    | succ m ih =>
      intro h v hv
      let t : Fin N := ⟨t₀.val + 1 + m, by omega⟩
      have ht : t ≠ t₀ := fun e => by have := congrArg Fin.val e; simp only [t] at this; omega
      have hvs : v ∈ (S t.succ).toSubmodule := by
        have : t.succ = ⟨t₀.val + 1 + (m + 1), h⟩ := by ext; simp [t]; omega
        rw [this]; exact hv
      have hq := hstep t ht (Submodule.Quotient.mk ⟨v, hvs⟩)
      have hmem : ρ z v - c' t • v ∈ (S t.castSucc).toSubmodule := by
        have e2 : subQuot (S t.succ) (S t.castSucc) z (Submodule.Quotient.mk ⟨v, hvs⟩) =
            Submodule.Quotient.mk ⟨ρ z v, (S t.succ).apply_mem_toSubmodule z hvs⟩ := rfl
        rw [e2, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hq
        simpa using hq
      rw [prodOp_succ_apply]
      have e3 : a (t₀.val + 1 + m) = c' t := ha m (by omega)
      simp only [e3]
      exact ih (by omega) _ hmem

  have L2 : ∀ m, ∀ b (hb : b ∈ B.toSubmodule), ∃ h' : prodOp ρ z (fun i => a (t₀.val + 1 + i)) m b ∈ B.toSubmodule,
      (Submodule.Quotient.mk ⟨_, h'⟩ : B.toSubmodule ⧸ A.toSubmodule.comap B.toSubmodule.subtype) =
        prodScal c (fun i => a (t₀.val + 1 + i)) m • Submodule.Quotient.mk ⟨b, hb⟩ := by
    intro m
    induction m with
    | zero => intro b hb; exact ⟨hb, by simp [prodOp, prodScal]⟩
    | succ m ih =>
      intro b hb
      have hb' : ρ z b - a (t₀.val + 1 + m) • b ∈ B.toSubmodule :=
        B.toSubmodule.sub_mem (B.apply_mem_toSubmodule z hb) (B.toSubmodule.smul_mem _ hb)
      obtain ⟨h', e⟩ := ih _ hb'
      refine ⟨by rw [prodOp_succ_apply]; exact h', ?_⟩
      have e4 : (Submodule.Quotient.mk ⟨_, hb'⟩ : B.toSubmodule ⧸ A.toSubmodule.comap B.toSubmodule.subtype) =
          (c - a (t₀.val + 1 + m)) • Submodule.Quotient.mk ⟨b, hb⟩ := by
        have e5 : subQuot B A z (Submodule.Quotient.mk ⟨b, hb⟩) =
            Submodule.Quotient.mk ⟨ρ z b, B.apply_mem_toSubmodule z hb⟩ := rfl
        rw [sub_smul, ← hZ, e5, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub]
        rfl
      simp only [prodOp_succ_apply, prodScal]
      rw [mul_smul, ← e4, ← e]
  set op := prodOp ρ z (fun i => a (t₀.val + 1 + i)) M with hop
  have hNM : t₀.val + 1 + M = N := by omega
  have hM : ∀ v, op v ∈ B.toSubmodule := by
    intro v
    refine L1 M (by omega) v ?_
    have e : (⟨t₀.val + 1 + M, by omega⟩ : Fin (N + 1)) = Fin.last N := by ext; simp [hNM]
    rw [e, htop]
    trivial
  have hlam : prodScal c (fun i => a (t₀.val + 1 + i)) M ≠ 0 := by
    refine prodScal_ne_zero c _ M (fun m hm => ?_) M le_rfl
    show a (t₀.val + 1 + m) ≠ c
    rw [ha m (by omega)]
    exact hc' _ (fun e => by have := congrArg Fin.val e; simp only at this; omega)
  let φlin : V →ₗ[ℂ] Y := Ψ.toLinearMap ∘ₗ (A.toSubmodule.comap B.toSubmodule.subtype).mkQ ∘ₗ
    LinearMap.codRestrict B.toSubmodule op hM
  have hφ : ∀ g v, φlin (ρ g v) = τ g (φlin v) := by
    intro g v
    have e6 : (LinearMap.codRestrict B.toSubmodule op hM) (ρ g v) =
        B.toRepresentation g (LinearMap.codRestrict B.toSubmodule op hM v) :=
      Subtype.ext (prodOp_comm ρ z hz _ M g v)
    show Ψ.toIntertwiningMap (Submodule.mkQ _ (LinearMap.codRestrict _ op hM (ρ g v))) =
      τ g (Ψ.toIntertwiningMap (Submodule.mkQ _ (LinearMap.codRestrict _ op hM v)))
    have e8 : Submodule.mkQ (A.toSubmodule.comap B.toSubmodule.subtype)
        (B.toRepresentation g (LinearMap.codRestrict B.toSubmodule op hM v)) =
        subQuot B A g (Submodule.mkQ _ (LinearMap.codRestrict B.toSubmodule op hM v)) := rfl
    rw [e6, e8]
    exact Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap g _
  refine ⟨φlin.intertwiningMap_of_isIntertwiningMap ρ τ hφ, ?_⟩
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  obtain ⟨⟨b, hb⟩, hx⟩ := Submodule.Quotient.mk_surjective _ (Ψ.toLinearEquiv.symm y)
  obtain ⟨h', e⟩ := L2 M b hb
  refine ⟨b, ?_⟩
  rw [LinearMap.toIntertwiningMap]
  have e7 : φlin b = Ψ.toLinearEquiv (Submodule.Quotient.mk ⟨op b, h'⟩) := rfl
  rw [e7, e, hx, map_smul, LinearEquiv.apply_symm_apply]
  exact smul_ne_zero hlam hy

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntertwiningOfCentralFiltrationStepStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.exists_intertwining_of_central_filtration_step : ∀ {G V Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G Y) (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ),
    Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ → ∀ (z : G), (∀ g, g * z = z * g) →
    ∀ (t₀ : Fin N) (c : ℂ) (c' : Fin N → ℂ), (∀ t, t ≠ t₀ → c' t ≠ c) →
    (∀ t, t ≠ t₀ → ∀ y, subQuot (S t.succ) (S t.castSucc) z y = c' t • y) →
    Nonempty ((subQuot (S t₀.succ) (S t₀.castSucc)).Equiv τ) → (∀ y, τ z y = c • y) → Nontrivial Y →
    ∃ (φ : ρ.IntertwiningMap τ) (v : V), φ v ≠ 0 := by
  first | exact @GlobalTheory.exists_intertwining_of_central_step | exact GlobalTheory.exists_intertwining_of_central_step | (intros; apply GlobalTheory.exists_intertwining_of_central_step <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquivStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.geometricLemmaCell_one_block_swap_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)), d 1 = 1 →
    ∀ (b : SizeMatrix (fun i : Fin 2 => Fin (d i)) (fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j)))), b.1 1 0 = 1 →
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (Equiv.swap 0 1 j))),
      Nonempty ((cellFunctor f g (piTensor fun i => (σ i).π)).Equiv
        (piTensor fun j => (σ (Equiv.swap 0 1 j)).π)) := by
  first | exact @GlobalTheory.OneBlockCell.cellFunctor_swap_equiv | exact GlobalTheory.OneBlockCell.cellFunctor_swap_equiv | (intros; apply GlobalTheory.OneBlockCell.cellFunctor_swap_equiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalPairIrreducibleProduct

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


noncomputable section

namespace GlobalTheory.SwapTwo

open GlobalTheory.JacTensor GlobalTheory.EmptyFirstBlock

theorem nonempty_equiv_of_apply_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hρ : ρ.IsIrreducible)
    (hσ : σ.IsIrreducible) (f : ρ.IntertwiningMap σ) {v : V} (hv : f v ≠ 0) : Nonempty (ρ.Equiv σ) := by
  let K : Subrepresentation ρ := ⟨LinearMap.ker f.toLinearMap, fun g x hx => by
    show f (ρ g x) = 0
    rw [f.isIntertwining]
    have hx' : f x = 0 := hx
    rw [hx', map_zero]⟩
  let R : Subrepresentation σ := ⟨LinearMap.range f.toLinearMap, by
    rintro g _ ⟨x, rfl⟩
    exact ⟨ρ g x, f.isIntertwining _ _ g x⟩⟩
  refine ⟨GlobalTheory.LocGL.equivOfBijective f ⟨?_, ?_⟩⟩
  · rcases eq_bot_or_eq_top K with h | h
    · refine (injective_iff_map_eq_zero f.toLinearMap).2 fun x hx => ?_
      have : x ∈ K := hx
      rw [h] at this
      exact this
    · exact absurd (show v ∈ K from h ▸ trivial) hv
  · rcases eq_bot_or_eq_top R with h | h
    · exact absurd (show f v ∈ R from ⟨v, rfl⟩) (by rw [h]; exact hv)
    · intro w
      obtain ⟨x, hx⟩ := (show w ∈ R from h ▸ trivial)
      exact ⟨x, hx⟩

theorem exists_jac_map_ne_zero : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)),
    (∀ i, 0 < d i ∧ IsCuspidal (σ i).π) → d 1 = 1 →
    (∀ (h : d 0 = d 1) (α : ℂˣ), ¬ Nonempty ((h ▸ σ 0 : Irr k (d 1)).π.Equiv
      (twist (σ 1).π (detChar (Fin (d 1)) (unrChar k α))))) →
    ∀ (e : (Σ i, Fin (d i)) ≃ n) (e' : (Σ i, Fin (d (Equiv.swap 0 1 i))) ≃ n),
    ∃ (φ : (jac e' (multiProd e fun i => (σ i).π)).IntertwiningMap
        (piTensor fun i => (σ (Equiv.swap 0 1 i)).π)) (x : Jacquet (multiProd e fun i => (σ i).π) (unipRad k e')), φ x ≠ 0 := by
  intro _ hGL k _ _ _ _ n _ _ d σ hσ hd1 hnt e e'
  obtain ⟨z, c, c', hz, hcc, hX, hbad⟩ := GlobalTheory.T.exists_central_scalar_distinct_geometricLemma_cells k d σ hσ hd1 hnt
  obtain ⟨N, b, hb⟩ := (hGL k).1 (Fin 2) (Fin 2) n (fun i => Fin (d i)) (fun j => Fin (d (Equiv.swap 0 1 j))) e e'
  obtain ⟨S, hmono, h0, hN, h4⟩ := hb _ (piTensor fun i => (σ i).π) (isSmooth_piTensor fun i => (σ i).smooth)
  obtain ⟨G0, hG0⟩ : ∃ G0 : SizeMatrix (fun i : Fin 2 => Fin (d i)) (fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j))),
      G0.1 = ![![0, d 0], ![1, 0]] := ⟨⟨![![0, d 0], ![1, 0]], by
      refine ⟨fun i => ?_, fun j => ?_⟩
      · fin_cases i <;> simp [Fin.sum_univ_two, hd1]
      · fin_cases j <;> simp [Fin.sum_univ_two, hd1]⟩, rfl⟩
  have hgood : (b (b.symm G0)).1 1 0 = 1 := by rw [Equiv.apply_symm_apply, hG0]; rfl
  obtain ⟨f₀, g₀, ⟨E₀⟩⟩ := GlobalTheory.T.geometricLemmaCell_one_block_swap_equiv k d σ hd1 (b (b.symm G0)) hgood
  have hbad' : ∀ t, t ≠ b.symm G0 → (b t).1 1 0 = 0 := by
    intro t ht
    have r1 := (b t).2.1 1
    have c0 := (b t).2.2 0
    have r0 := (b t).2.1 0
    have c1 := (b t).2.2 1
    simp only [Fin.sum_univ_two, Fintype.card_fin, Equiv.swap_apply_left, Equiv.swap_apply_right] at r1 c0 r0 c1
    by_contra hne
    apply ht
    rw [Equiv.eq_symm_apply]
    apply Subtype.ext
    funext i j
    rw [hG0]
    fin_cases i <;> fin_cases j <;> simp <;> omega
  have hstep : ∀ t, t ≠ b.symm G0 → ∀ y, subQuot (S t.succ) (S t.castSucc) z y = c' • y := by
    intro t ht y
    have E := (h4 t (b t).nonempty_rows.some (b t).nonempty_cols.some).some
    apply E.toLinearEquiv.injective
    have h1 : E.toLinearEquiv (subQuot (S t.succ) (S t.castSucc) z y) = _ := LinearMap.congr_fun (E.isIntertwining' z) y
    have h2 := hbad (b t) (hbad' t ht) (b t).nonempty_rows.some (b t).nonempty_cols.some (E.toLinearEquiv y)
    exact h1.trans (h2.trans (LinearEquiv.map_smul E.toLinearEquiv c' y).symm)
  obtain ⟨φ, v, hv⟩ := GlobalTheory.T.exists_intertwining_of_central_filtration_step (jac e' (multiProd e fun i => (σ i).π))
    (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) N S hmono h0 hN z hz (b.symm G0) c (fun _ => c')
    (fun _ _ => hcc.symm) hstep
    ⟨(h4 (b.symm G0) f₀ g₀).some.trans E₀⟩ hX
    (GlobalTheory.ProdSupport.nontrivial_piTensor _ fun j => Model.nontrivial_of_isIrreducible (σ (Equiv.swap 0 1 j)).irr)
  exact ⟨φ, v, hv⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isIrreducible_of_comp {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ H V} (φ : G →* H) (h : Representation.IsIrreducible (ρ.comp φ)) :
    ρ.IsIrreducible := by
  haveI : Nontrivial V := Model.nontrivial_of_isIrreducible h
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h1 : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← e] at h1
    exact hv h1
  · rcases eq_bot_or_eq_top (⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (φ g) hv⟩ :
        Subrepresentation (ρ.comp φ)) with h' | h'
    · left
      have h2 := congrArg Subrepresentation.toSubmodule h'
      exact Subrepresentation.toSubmodule_injective h2
    · right
      have h2 := congrArg Subrepresentation.toSubmodule h'
      exact Subrepresentation.toSubmodule_injective h2

theorem not_equiv_twist_symm : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (π₁ : Irr k r) (π₂ : Irr k t),
    (∀ (h : r = t) (α : ℂˣ), ¬ Nonempty ((h ▸ π₁ : Irr k t).π.Equiv (twist π₂.π (detChar (Fin t) (unrChar k α))))) →
    ∀ (h : t = r) (α : ℂˣ), ¬ Nonempty ((h ▸ π₂ : Irr k r).π.Equiv (twist π₁.π (detChar (Fin r) (unrChar k α)))) := by
  intro k _ _ _ _ r t π₁ π₂ hnt h α ⟨φ⟩
  subst h
  refine hnt rfl α⁻¹ ?_
  have heq : twist (twist π₁.π (detChar (Fin t) (unrChar k α))) (detChar (Fin t) (unrChar k α⁻¹)) = π₁.π := by
    ext g v
    simp only [twist_apply, detChar_apply, unrChar_apply, smul_smul, inv_zpow]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have e := (GlobalTheory.LocGL.twistEquiv φ (detChar (Fin t) (unrChar k α⁻¹))).symm
  rw [heq] at e
  exact ⟨e⟩

theorem isIrreducible_multiProd_two (hU : GlobalTheory.Published.UnlinkedProductIrreducible) {n : Type} [Fintype n]
    [DecidableEq n] (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)) (hσ : ∀ i, 0 < d i ∧ IsCuspidal (σ i).π)
    (hnt : ∀ (h : d 0 = d 1) (α : ℂˣ), ¬ Nonempty ((h ▸ σ 0 : Irr k (d 1)).π.Equiv
      (twist (σ 1).π (detChar (Fin (d 1)) (unrChar k α)))))
    (e : (Σ i, Fin (d i)) ≃ n) : (multiProd e fun i => (σ i).π).IsIrreducible := by
  have hd : ∑ a, d a = d 0 + d 1 := Fin.sum_univ_two d
  have hsupp : ∀ i, IsCuspSupport (σ i).π (fun _ : Fin 1 => d i) (fun _ => (σ i).π) := fun i => by
    obtain ⟨φ⟩ := GlobalTheory.LocGL.nonempty_equiv_multiProd_one (σ i).smooth (oneBlock (d i)) fun _ _ => rfl
    exact ⟨(σ i).irr, fun _ => ⟨(hσ i).1, (σ i).irr, (hσ i).2⟩, oneBlock (d i),
      .of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective⟩
  have h2 := hU k (d 0) (d 1) 1 1 (σ 0) (σ 1) _ _ _ _ (hsupp 0) (hsupp 1) fun _ _ h α => hnt h α
  obtain ⟨E₁⟩ := GlobalTheory.LocGL.nonempty_prod₂_equiv_multiProd hd fun i => (σ i).π
  have h3 := GlobalTheory.Parabolic.isIrreducible_of_equiv E₁ h2
  have hc : Fintype.card (Fin (d 0 + d 1)) = Fintype.card n := by
    rw [Fintype.card_fin, ← hd, ← Fintype.card_congr e]; simp
  let ψ : Fin (d 0 + d 1) ≃ n := Fintype.equivOfCardEq hc
  obtain ⟨E₂⟩ := GlobalTheory.T.normalisedParabolicInduction_reindex_equiv k (Fin 2) (fun i => Fin (d i)) _ _ (stdBlocks d hd) ψ _ (piTensor fun i => (σ i).π)
  have h4 := isIrreducible_of_comp _ (GlobalTheory.Parabolic.isIrreducible_of_equiv E₂ h3)
  obtain ⟨E₃⟩ := (Placing.parInd_jac_placing k (Fin 2) n (fun i => Fin (d i)) ((stdBlocks d hd).trans ψ) e _).1
    (piTensor fun i => (σ i).π)
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv E₃ h4

theorem swap_two_equiv : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)), (∀ i, 0 < d i ∧ IsCuspidal (σ i).π) → d 1 = 1 → (∀ (h : d 0 = d 1) (α : ℂˣ), ¬ Nonempty ((h ▸ σ 0 : Irr k (d 1)).π.Equiv (twist (σ 1).π (detChar (Fin (d 1)) (unrChar k α))))) → ∀ (e : (Σ i, Fin (d i)) ≃ n) (e' : (Σ i, Fin (d (Equiv.swap 0 1 i))) ≃ n), Nonempty ((multiProd e fun i => (σ i).π).Equiv (multiProd e' fun i => (σ (Equiv.swap 0 1 i)).π)) := by
  intro hBZ hGL hU k _ _ _ _ n _ _ d σ hσ hd1 hnt e e'
  have h1 := isIrreducible_multiProd_two hU d σ hσ hnt e
  have h2 := isIrreducible_multiProd_two hU (fun i => d (Equiv.swap 0 1 i)) (fun i => σ (Equiv.swap 0 1 i))
    (fun i => hσ _) (not_equiv_twist_symm k (d 0) (d 1) (σ 0) (σ 1) hnt) e'
  obtain ⟨φ, x, hx⟩ := exists_jac_map_ne_zero hBZ hGL k n d σ hσ hd1 hnt e e'
  obtain ⟨f, hf⟩ := (Model.evalOne_bijective e' (isSmooth_parInd _ _)
    (piTensor fun i => (σ (Equiv.swap 0 1 i)).π)).2 φ
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hv : f v ≠ 0 := fun h => hx (by
    rw [← hf]
    show (f v).1.1 1 = 0
    rw [h]; rfl)
  exact nonempty_equiv_of_apply_ne_zero h1 h2 f hv

end GlobalTheory.SwapTwo

end
end
end
