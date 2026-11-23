module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKerLeComapMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitImgMono
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKerLeComapMap
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrParIffCuspidalProduct
import Mathlib.Tactic.TypeStar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSubquotientEquivStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import GroundTheory.LocalFields.PadicLogSeries

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientOfExtension

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

namespace GlobalTheory.CompanionTheory.SubquotExt

theorem isSubquotient_sub_or_quot :
    ∀ (G V W : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (A B : Subrepresentation ρ), A ≤ B → σ.IsIrreducible → IsSubquotient σ B.toRepresentation →
    IsSubquotient σ A.toRepresentation ∨ IsSubquotient σ (subQuot B A) := by
  intro G V W _ _ _ _ _ ρ σ A B hAB hσ hB
  haveI : IsSimpleOrder (Subrepresentation σ) := hσ
  unfold GlobalTheory.SmGL.IsSubquotient at hB ⊢
  obtain ⟨S, f, hf⟩ := hB
  let P : Submodule ℂ S.toSubmodule :=
    (A.toSubmodule.comap B.toSubmodule.subtype).comap S.toSubmodule.subtype
  have hNinv : ∀ (g : G) ⦃w : W⦄, w ∈ P.map f.toLinearMap → σ g w ∈ P.map f.toLinearMap := by
    intro g w hw
    rw [Submodule.mem_map] at hw ⊢
    obtain ⟨s, hs, rfl⟩ := hw
    have hs' : ((s : B.toSubmodule) : V) ∈ A.toSubmodule := hs
    refine ⟨S.toRepresentation g s, A.apply_mem_toSubmodule g hs', ?_⟩
    exact f.isIntertwining _ _ g s
  let N : Subrepresentation σ := ⟨P.map f.toLinearMap, hNinv⟩
  let Z : Subrepresentation σ := ⟨⊥, by
    intro g w hw
    rw [Submodule.mem_bot] at hw ⊢
    rw [hw, map_zero]⟩
  let Fu : Subrepresentation σ := ⟨⊤, by
    intro g w _
    exact Submodule.mem_top⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top N with hN | hN
  · right
    have hle : N ≤ Z := by
      rw [hN]
      exact bot_le
    have hfP : P ≤ LinearMap.ker f.toLinearMap := by
      intro s hs
      have h0 : f.toLinearMap s ∈ (⊥ : Submodule ℂ W) := hle (Submodule.mem_map_of_mem hs)
      exact LinearMap.mem_ker.2 ((Submodule.mem_bot ℂ).1 h0)
    let A' : Submodule ℂ B.toSubmodule := A.toSubmodule.comap B.toSubmodule.subtype
    have hQ : ∀ (g : G) (b : B.toSubmodule), GlobalTheory.SmGL.subQuot B A g (A'.mkQ b) =
        A'.mkQ (B.toRepresentation g b) := by
      intro g b
      first
      | rfl
      | (unfold GlobalTheory.SmGL.subQuot
         rw [Representation.quotient_apply]
         rfl)
    have hSinv : ∀ (g : G) ⦃x : B.toSubmodule ⧸ A'⦄, x ∈ S.toSubmodule.map A'.mkQ →
        GlobalTheory.SmGL.subQuot B A g x ∈ S.toSubmodule.map A'.mkQ := by
      intro g x hx
      rw [Submodule.mem_map] at hx ⊢
      obtain ⟨b, hb, rfl⟩ := hx
      exact ⟨B.toRepresentation g b, S.apply_mem_toSubmodule g hb, (hQ g b).symm⟩
    let S'' : Subrepresentation (GlobalTheory.SmGL.subQuot B A) := ⟨S.toSubmodule.map A'.mkQ, hSinv⟩
    let ψ0 : S.toSubmodule →ₗ[ℂ] (S.toSubmodule.map A'.mkQ) :=
      LinearMap.codRestrict _ (A'.mkQ ∘ₗ S.toSubmodule.subtype) (fun s => Submodule.mem_map_of_mem s.2)
    have hPker : P ≤ LinearMap.ker ψ0 := by
      intro s hs
      have hs' : (s : B.toSubmodule) ∈ A' := hs
      rw [LinearMap.mem_ker]
      exact Subtype.ext ((Submodule.Quotient.mk_eq_zero A').2 hs')
    have hkerP : LinearMap.ker ψ0 ≤ P := by
      intro s hs
      rw [LinearMap.mem_ker] at hs
      have h2 : (Submodule.Quotient.mk (s : B.toSubmodule) : B.toSubmodule ⧸ A') = 0 := congrArg Subtype.val hs
      exact (Submodule.Quotient.mk_eq_zero A').1 h2
    have hinj : Function.Injective (P.liftQ ψ0 hPker) :=
      LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot P ψ0 hPker hkerP)
    have hsurj : Function.Surjective (P.liftQ ψ0 hPker) := by
      intro x
      obtain ⟨y, hy⟩ := x
      rw [Submodule.mem_map] at hy
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨Submodule.Quotient.mk ⟨b, hb⟩, rfl⟩
    let e := LinearEquiv.ofBijective (P.liftQ ψ0 hPker) ⟨hinj, hsurj⟩
    let F'' : (S.toSubmodule.map A'.mkQ) →ₗ[ℂ] W := P.liftQ f.toLinearMap hfP ∘ₗ e.symm.toLinearMap
    have key : ∀ s, F'' (ψ0 s) = f s := by
      intro s
      have he : ψ0 s = e (Submodule.Quotient.mk s) := rfl
      show P.liftQ f.toLinearMap hfP (e.symm (ψ0 s)) = f s
      rw [he, LinearEquiv.symm_apply_apply]
      rfl
    have hrep : ∀ (g : G) (s : S.toSubmodule), S''.toRepresentation g (ψ0 s) = ψ0 (S.toRepresentation g s) :=
      fun g s => Subtype.ext (hQ g s)
    have hψ0 : ∀ x : S.toSubmodule.map A'.mkQ, ∃ s, ψ0 s = x := by
      intro x
      obtain ⟨y, rfl⟩ := hsurj x
      obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective P y
      exact ⟨s, rfl⟩
    let f'' : S''.toRepresentation.IntertwiningMap σ := ⟨F'', fun g => LinearMap.ext fun x => by
      obtain ⟨s, rfl⟩ := hψ0 x
      show F'' (S''.toRepresentation g (ψ0 s)) = σ g (F'' (ψ0 s))
      rw [hrep, key, key]
      exact f.isIntertwining _ _ g s⟩
    refine ⟨S'', f'', fun w => ?_⟩
    obtain ⟨s, rfl⟩ := hf w
    exact ⟨ψ0 s, key s⟩
  · left
    have hge : Fu ≤ N := by
      rw [hN]
      exact le_top
    have hAB' : A.toSubmodule ≤ B.toSubmodule := fun x hx => hAB hx
    have hS'inv : ∀ (g : G) ⦃a : A.toSubmodule⦄, a ∈ S.toSubmodule.comap (Submodule.inclusion hAB') →
        A.toRepresentation g a ∈ S.toSubmodule.comap (Submodule.inclusion hAB') := by
      intro g a ha
      exact S.apply_mem_toSubmodule g ha
    let S' : Subrepresentation A.toRepresentation := ⟨S.toSubmodule.comap (Submodule.inclusion hAB'), hS'inv⟩
    let r : (S.toSubmodule.comap (Submodule.inclusion hAB')) →ₗ[ℂ] S.toSubmodule :=
      (Submodule.inclusion hAB').restrict (fun a ha => ha)
    let f' : S'.toRepresentation.IntertwiningMap σ := ⟨f.toLinearMap ∘ₗ r, fun g => LinearMap.ext fun x => by
      show f.toLinearMap (r (S'.toRepresentation g x)) = σ g (f.toLinearMap (r x))
      exact f.isIntertwining _ _ g (r x)⟩
    refine ⟨S', f', fun w => ?_⟩
    have hw : w ∈ P.map f.toLinearMap := hge (Submodule.mem_top : w ∈ (⊤ : Submodule ℂ W))
    rw [Submodule.mem_map] at hw
    obtain ⟨s, hs, rfl⟩ := hw
    have hs' : ((s : B.toSubmodule) : V) ∈ A.toSubmodule := hs
    have ha : (⟨((s : B.toSubmodule) : V), hs'⟩ : A.toSubmodule) ∈ S.toSubmodule.comap (Submodule.inclusion hAB') := by
      first
      | exact s.2
      | simpa using s.2
    exact ⟨⟨⟨((s : B.toSubmodule) : V), hs'⟩, ha⟩, rfl⟩

end GlobalTheory.CompanionTheory.SubquotExt

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientOfExtensionStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

theorem _root_.GlobalTheory.T.irreducible_subquotient_of_extension : ∀ (G V W : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (A B : Subrepresentation ρ), A ≤ B → σ.IsIrreducible → IsSubquotient σ B.toRepresentation →
    IsSubquotient σ A.toRepresentation ∨ IsSubquotient σ (subQuot B A) := by
  first | exact @GlobalTheory.CompanionTheory.SubquotExt.isSubquotient_sub_or_quot | exact GlobalTheory.CompanionTheory.SubquotExt.isSubquotient_sub_or_quot | (intros; apply GlobalTheory.CompanionTheory.SubquotExt.isSubquotient_sub_or_quot <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfIrreducibleImage

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.IsoSub

theorem nonempty_equiv_of_isotypic {A M T Q S : Type*} [Ring A] [AddCommGroup M] [Module A M]
    [AddCommGroup T] [Module A T] [AddCommGroup Q] [Module A Q] [AddCommGroup S] [Module A S]
    [IsSimpleModule A S] (h : isotypicComponent A M S = ⊤) (j : T →ₗ[A] M)
    (hj : Function.Injective j) (f : T →ₗ[A] Q) (hf : Function.Surjective f) :
    IsSimpleModule A Q → Nonempty (Q ≃ₗ[A] S) := by
  intro hQ
  have hiso : IsIsotypicOfType A M S := IsIsotypicOfType.of_isotypicComponent_eq_top h
  have hss : IsSemisimpleModule A M := by
    refine IsSemisimpleModule.of_sSup_simples_eq_top (top_le_iff.1 ?_)
    rw [← h]
    exact sSup_le_sSup fun m (hm : Nonempty (m ≃ₗ[A] S)) => IsSimpleModule.congr hm.some
  have hT : IsSemisimpleModule A T := IsSemisimpleModule.of_injective j hj
  obtain ⟨C, hC⟩ := exists_isCompl (LinearMap.ker f)
  let e₁ : C ≃ₗ[A] Q :=
    (Submodule.quotientEquivOfIsCompl _ _ hC).symm.trans (f.quotKerEquivOfSurjective hf)
  have hC' : IsSimpleModule A C := IsSimpleModule.congr e₁
  let e₂ : C ≃ₗ[A] C.map j := Submodule.equivMapOfInjective j hj C
  have hCj : IsSimpleModule A (C.map j) := IsSimpleModule.congr e₂.symm
  obtain ⟨e₃⟩ := hiso (C.map j)
  exact ⟨e₁.symm.trans (e₂.trans e₃)⟩

def inclusion {G Y : Type} [Group G] [AddCommGroup Y] [Module ℂ Y] {R : Representation ℂ G Y}
    (S : Subrepresentation R) : S.toRepresentation.IntertwiningMap R :=
  ⟨S.toSubmodule.subtype, fun _ => rfl⟩

theorem equiv_of_isSubquotient (G : Type) [Group G] (V Y W : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (R : Representation ℂ G Y) (σ : Representation ℂ G W)
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (hR : ⨆ f : ρ.IntertwiningMap R, LinearMap.range f.toLinearMap = ⊤)
    (hsq : IsSubquotient σ R) : Nonempty (σ.Equiv ρ) := by
  have hρs : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).1 hρ
  have hσs : IsSimpleModule (MonoidAlgebra ℂ G) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).1 hσ
  have htop : Subrepresentation.asSubmodule (GlobalTheory.CuspFactor.spanRep R ρ) = ⊤ := by
    have hX : (GlobalTheory.CuspFactor.spanRep R ρ).toSubmodule = ⊤ := hR
    apply SetLike.coe_injective
    show ((GlobalTheory.CuspFactor.spanRep R ρ).toSubmodule : Set Y) = Set.univ
    rw [hX]
    first
      | rfl
      | exact Submodule.top_coe
      | simp
  have h : isotypicComponent (MonoidAlgebra ℂ G) R.asModule ρ.asModule = ⊤ := by
    rw [← GlobalTheory.CuspFactor.spanRep_asSubmodule R ρ hρ]
    exact htop
  obtain ⟨S, f, hf⟩ := hsq
  let j := Representation.IntertwiningMap.equivLinearMapAsModule _ _
    (GlobalTheory.CompanionTheory.IsoSub.inclusion S)
  have hj : Function.Injective j := by
    first
      | exact Subtype.val_injective
      | (intro x y hxy; exact Subtype.val_injective hxy)
  let f' := Representation.IntertwiningMap.equivLinearMapAsModule _ _ f
  have hf' : Function.Surjective f' := by
    first
      | exact hf
      | (intro y; obtain ⟨x, hx⟩ := hf y; exact ⟨x, hx⟩)
  exact (GlobalTheory.CuspFactor.nonempty_equiv_iff σ ρ).2
    (GlobalTheory.CompanionTheory.IsoSub.nonempty_equiv_of_isotypic h j hj f' hf' hσs)

end GlobalTheory.CompanionTheory.IsoSub
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfIrreducibleImageStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL

theorem _root_.GlobalTheory.T.subquotient_equiv_of_irreducible_image : ∀ (G : Type) [Group G] (V Y W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (R : Representation ℂ G Y) (σ : Representation ℂ G W), ρ.IsIrreducible → σ.IsIrreducible →
    (⨆ f : ρ.IntertwiningMap R, LinearMap.range f.toLinearMap = ⊤) → IsSubquotient σ R → Nonempty (σ.Equiv ρ) := by
  first | exact @GlobalTheory.CompanionTheory.IsoSub.equiv_of_isSubquotient | exact GlobalTheory.CompanionTheory.IsoSub.equiv_of_isSubquotient | (intros; apply GlobalTheory.CompanionTheory.IsoSub.equiv_of_isSubquotient <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockSubquotientTensor

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

namespace GlobalTheory.CompanionTheory.BZNuPair

theorem whit2_isSubquotient_whitImg_top {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X : Type} [AddCommGroup X]
    [Module ℂ X] (J : Representation ℂ (Levi k fun a => Fin (d a)) X) :
    IsSubquotient (whit2 ψ d J) (whitImg ψ d J ⊤).toRepresentation := by
  let f : (whitImg ψ d J ⊤).toRepresentation.IntertwiningMap (whit2 ψ d J) :=
    ⟨(whitImg ψ d J ⊤).toSubmodule.subtype, fun _ => rfl⟩
  refine .of_surjective f fun w => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact ⟨⟨Submodule.Quotient.mk x, x, trivial, rfl⟩, rfl⟩

theorem not_isSubquotient_whitImg_bot {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X W : Type} [AddCommGroup X]
    [Module ℂ X] [AddCommGroup W] [Module ℂ W] (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    {σ : Representation ℂ (GL (Fin (d 0)) k) W} (hσ : σ.IsIrreducible) :
    ¬ IsSubquotient σ (whitImg ψ d J ⊥).toRepresentation := by
  rintro ⟨R, f, hf⟩
  have := nontrivial_of_irreducible hσ
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf w
  have hv : v = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨t, ht, h⟩ := v.1.2
    have ht0 : t = 0 := ht
    rw [← h, ht0]
    simp
  exact hw (by rw [hv, map_zero])

theorem exists_constituent_of_whit2 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (d : Fin 2 → ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) X), IsSmooth J → HasFiniteLength J → ∀ S : IrrRep (GL (Fin (d 0)) k),
    IsSubquotient S.ρ (whit2 ψ d J) → ∃ s : ∀ a, IrrRep (GL (Fin (d a)) k),
      IsSubquotient (piTensor fun a => (s a).ρ) J ∧ Nonempty ((s 0).ρ.Equiv S.ρ) := by
  intro k _ _ _ _ ψ _ d X _ _ J hs hfl S hS
  obtain ⟨hgt, hlt⟩ := (hasFiniteLength_iff_wellFounded J).1 hfl
  obtain ⟨T, hT, hmin⟩ := WellFounded.has_min hlt
    {T : Subrepresentation J | IsSubquotient S.ρ (whitImg ψ d J T).toRepresentation}
    ⟨⊤, hS.trans (whit2_isSubquotient_whitImg_top ψ d J)⟩
  have hne : T ≠ ⊥ := by
    rintro rfl
    exact not_isSubquotient_whitImg_bot ψ d J S.irr hT
  obtain ⟨T', hT'lt, hmax⟩ := WellFounded.has_min hgt {U : Subrepresentation J | U < T}
    ⟨⊥, bot_lt_iff_ne_bot.2 hne⟩
  have hcov : T' ⋖ T := ⟨hT'lt, fun c h1 h2 => hmax c h2 h1⟩
  have hq : IsSubquotient (subQuot T T') J :=
    ⟨T, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩
  let τ : IrrRep (Levi k fun a => Fin (d a)) :=
    ⟨_, subQuot T T', hq.isSmooth hs, isIrreducible_subQuot hcov⟩
  obtain ⟨s, ⟨Φ⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k (Fin 2)
    (fun a => Fin (d a)) τ
  have hspan := GlobalTheory.T.whittaker_subquotient_equiv k ψ d X J T T' (fun a => (s a).V) (fun a => (s a).ρ) hT'lt.le Φ
  refine ⟨s, (IsSubquotient.of_surjective Φ.toIntertwiningMap Φ.surjective).trans hq, ?_⟩
  rcases GlobalTheory.T.irreducible_subquotient_of_extension _ _ _ (whit2 ψ d J) S.ρ _ _ (whitImg_mono ψ d J hT'lt.le) S.irr hT with h | h
  · exact absurd hT'lt (hmin T' h)
  · obtain ⟨e⟩ := GlobalTheory.T.subquotient_equiv_of_irreducible_image _ _ _ _ (s 0).ρ _ S.ρ (s 0).irr S.irr hspan h
    exact ⟨e.symm⟩

end GlobalTheory.CompanionTheory.BZNuPair

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockSubquotientTensorStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

theorem _root_.GlobalTheory.T.whittaker_two_block_subquotient_tensor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (d : Fin 2 → ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) X), IsSmooth J → HasFiniteLength J → ∀ S : IrrRep (GL (Fin (d 0)) k),
    IsSubquotient S.ρ (whit2 ψ d J) → ∃ s : ∀ a, IrrRep (GL (Fin (d a)) k),
      IsSubquotient (piTensor fun a => (s a).ρ) J ∧ Nonempty ((s 0).ρ.Equiv S.ρ) := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPair.exists_constituent_of_whit2 | exact GlobalTheory.CompanionTheory.BZNuPair.exists_constituent_of_whit2 | (intros; apply GlobalTheory.CompanionTheory.BZNuPair.exists_constituent_of_whit2 <;> assumption)
end
end
