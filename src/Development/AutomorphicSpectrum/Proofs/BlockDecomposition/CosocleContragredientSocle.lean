module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Mathlib.Topology.Algebra.Group.Units
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DepthZeroGoodLines
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvAtParabNeZero
import Mathlib.Tactic.Linter.Style
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleOfIsAtom

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses GlobalTheory.TypeDim ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.MaschkeForms

open Representation

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isIrreducible_of_isAtom {π : Representation ℂ G V} {U : Subrepresentation π}
    (hU : IsAtom U) : U.toRepresentation.IsIrreducible := by
  have hne : U.toSubmodule ≠ ⊥ := fun h => hU.1 (Subrepresentation.toSubmodule_injective h)
  have hnt : Nontrivial (Subrepresentation U.toRepresentation) := by
    refine ⟨⊥, ⊤, fun h => hne ?_⟩
    have h' : (⊥ : Submodule ℂ U.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
    rw [← U.toSubmodule.map_subtype_top, ← h', Submodule.map_bot]
  refine ⟨fun S => ?_⟩
  let T : Subrepresentation π := ⟨S.toSubmodule.map U.toSubmodule.subtype, by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨_, S.apply_mem_toSubmodule g hx, rfl⟩⟩
  have hT : T ≤ U := U.toSubmodule.map_subtype_le S.toSubmodule
  have hinj := Submodule.map_injective_of_injective U.toSubmodule.injective_subtype
  rcases hU.le_iff.mp hT with h | h
  · left
    refine Subrepresentation.toSubmodule_injective (hinj ?_)
    exact (congrArg Subrepresentation.toSubmodule h).trans (Submodule.map_bot _).symm
  · right
    refine Subrepresentation.toSubmodule_injective (hinj ?_)
    exact (congrArg Subrepresentation.toSubmodule h).trans U.toSubmodule.map_subtype_top.symm

end GlobalTheory.MaschkeForms
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleContragredientSocle

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.SocleContra

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}

variable [TopologicalSpace G] [IsTopologicalGroup G]

def pullForm (f : π.IntertwiningMap σ) : (contra σ).IntertwiningMap (contra π) where
  toLinearMap :=
    { toFun := fun l => ⟨l.1 ∘ₗ f.toLinearMap, mem_smoothPart_of_nhds (Filter.mem_of_superset
        (IsOpen.mem_nhds l.2 (by
          show σ.dual 1 l.1 = l.1
          rw [map_one]
          rfl)) fun g hg => LinearMap.ext fun v => by
          have h : σ.dual g l.1 = l.1 := hg
          have h2 := LinearMap.congr_fun h (f v)
          have h3 : σ.dual g l.1 (f v) = l.1 (σ g⁻¹ (f v)) := rfl
          rw [h3, ← f.isIntertwining] at h2
          exact h2)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' g := LinearMap.ext fun l => Subtype.ext (LinearMap.ext fun v => by
    show l.1 (σ g⁻¹ (f v)) = l.1 (f (π g⁻¹ v))
    rw [f.isIntertwining])

theorem pullForm_injective (f : π.IntertwiningMap σ) (hf : Function.Surjective f) :
    Function.Injective (pullForm f) := fun a b h => Subtype.ext (LinearMap.ext fun y => by
  obtain ⟨v, rfl⟩ := hf y
  exact LinearMap.congr_fun (congrArg Subtype.val h) v)

theorem mem_range_pullForm (f : π.IntertwiningMap σ) (hf : Function.Surjective f) (l : smoothPart π.dual)
    (hl : ∀ v, f v = 0 → l.1 v = 0) : l ∈ (pullForm f).range := by
  let q : (V ⧸ LinearMap.ker f.toLinearMap) →ₗ[ℂ] ℂ := (LinearMap.ker f.toLinearMap).liftQ l.1 (fun v hv => hl v hv)
  let l' : Module.Dual ℂ W := q ∘ₗ (f.toLinearMap.quotKerEquivOfSurjective hf).symm.toLinearMap
  have hl' : ∀ v, l' (f v) = l.1 v := fun v => by
    have : (f.toLinearMap.quotKerEquivOfSurjective hf).symm (f v) = Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show q ((f.toLinearMap.quotKerEquivOfSurjective hf).symm (f v)) = _
    rw [this]
    rfl
  have hs : l' ∈ smoothPart σ.dual := mem_smoothPart_of_nhds (Filter.mem_of_superset
    (IsOpen.mem_nhds l.2 (by
      show π.dual 1 l.1 = l.1
      rw [map_one]
      rfl)) fun g hg => LinearMap.ext fun w => by
      obtain ⟨v, rfl⟩ := hf w
      have h : π.dual g l.1 = l.1 := hg
      have h2 := LinearMap.congr_fun h v
      have h3 : π.dual g l.1 v = l.1 (π g⁻¹ v) := rfl
      rw [h3] at h2
      show l' (σ g⁻¹ (f v)) = l' (f v)
      rw [← f.isIntertwining, hl', hl', h2])
  exact ⟨⟨l', hs⟩, Subtype.ext (LinearMap.ext fun v => hl' v)⟩

theorem isSmooth_subContra (S : Subrepresentation (contra π)) : IsSmooth S.toRepresentation := fun l => by
  have : {g : G | S.toRepresentation g l = l} = {g : G | contra π g l.1 = l.1} := by
    ext g
    exact Subtype.ext_iff
  rw [this]
  exact isSmooth_contra π l.1

def evalForms (hπ : IsSmooth π) (S : Subrepresentation (contra π)) : π.IntertwiningMap (contra S.toRepresentation) where
  toLinearMap :=
    { toFun := fun v => ⟨{ toFun := fun l => l.1.1 v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ v).mem_nhds (by simp)) fun g hg =>
          LinearMap.ext fun l => by
            have h : π g v = v := hg
            show ((contra π g⁻¹ l.1 : smoothPart π.dual) : Module.Dual ℂ V) v = l.1.1 v
            rw [contra_apply, inv_inv, h])⟩
      map_add' := fun a b => Subtype.ext (LinearMap.ext fun l => map_add l.1.1 a b)
      map_smul' := fun c a => Subtype.ext (LinearMap.ext fun l => map_smul l.1.1 c a) }
  isIntertwining' g := LinearMap.ext fun v => Subtype.ext (LinearMap.ext fun l => by
    show l.1.1 (π g v) = ((contra π g⁻¹ l.1 : smoothPart π.dual) : Module.Dual ℂ V) v
    rw [contra_apply, inv_inv])

end General

theorem isSocle_contra_of_isCosocle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W) (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → IsCosocle σ π → IsSocle (contra σ) (contra π) := by
  intro k _ _ _ _ hA N V W _ _ _ _ σ π hπ _ hc
  obtain ⟨hi, f, hf, hu⟩ := hc
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis (k := k) N
  have hσ : IsSmooth σ := (IsSubquotient.of_surjective f hf).isSmooth hπ
  have hci : (contra σ).IsIrreducible := GlobalTheory.ContraRefl.contra_isIrreducible hG (hA k N _ _ hσ hi) hi
  refine ⟨hci, pullForm f, pullForm_injective f hf, fun S hS => ?_⟩
  have hSi := GlobalTheory.MaschkeForms.isIrreducible_of_isAtom hS
  have hcS : (contra S.toRepresentation).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible hG (hA k N _ _ (isSmooth_subContra S) hSi) hSi
  let e := evalForms hπ S
  have hr : e.range ≠ ⊥ := fun h0 => hS.1 (eq_bot_iff.2 fun l hl => by
    refine Subtype.ext (LinearMap.ext fun v => ?_)
    have hv : e v ∈ (⊥ : Subrepresentation (contra S.toRepresentation)) := h0 ▸ ⟨v, rfl⟩
    have hv0 : e v = 0 := hv
    exact LinearMap.congr_fun (congrArg Subtype.val hv0) ⟨l, hl⟩)
  have he : Function.Surjective e := fun y => by
    have : y ∈ e.range := by
      have ht : e.range = ⊤ := (eq_bot_or_eq_top _).resolve_left hr
      rw [ht]
      trivial
    exact this
  have hk : e.ker = f.ker := hu _ (isCoatom_ker hcS e he)
  have hle : S ≤ (pullForm f).range := fun l hl => mem_range_pullForm f hf l fun v hv => by
    have hv' : v ∈ e.ker := hk ▸ hv
    have hv0 : e v = 0 := hv'
    exact LinearMap.congr_fun (congrArg Subtype.val hv0) ⟨l, hl⟩
  exact ((isAtom_range hci _ (pullForm_injective f hf)).le_iff.1 hle).resolve_left hS.1

end GlobalTheory.CompanionTheory.SocleContra

end
end
end
