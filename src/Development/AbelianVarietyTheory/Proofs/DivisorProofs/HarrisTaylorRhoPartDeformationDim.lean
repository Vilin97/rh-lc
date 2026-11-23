module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructureStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAugmentationSubspaceQuotientActionTopStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEquivariantHomEqAugmentationQuotientStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFirstDeRhamHomologyHodgeFiltrationOfField
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomHarrisTaylorOrderMorita
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKsSubMapClsEqHomOStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMapEqOfKerEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFinrankDeRhamQuotientCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRhoPartLieDeRhamQuotient
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoidAlgebraActionViaRingActionApplyStatement
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFirstDeRhamHomologyHodgeFiltrationOfFieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.finrank_firstDeRhamHomology_hodgeFiltration_of_field : GlobalTheory.Published.AbelianDeRham.Free → GlobalTheory.Published.AbelianDeRham.Hodge → ∀ (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → FiniteDimensional k (HdR A) ∧ Module.finrank k (HdR A) = 2 * g ∧ Module.finrank k (Fil A) = g := by
  first | exact @GlobalTheory.finrank_HdR_Fil_of_field | exact GlobalTheory.finrank_HdR_Fil_of_field | (intros; apply GlobalTheory.finrank_HdR_Fil_of_field <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomHarrisTaylorOrderMoritaStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.finrank_hom_harrisTaylorOrder_morita : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] [IsAlgClosed k], (∀ n : ℕ, n.Coprime p → (n : k) ≠ 0) → ∀ (χ : 𝓞 D.F →+* k) (X Y : Type) [AddCommGroup X] [Module k X] [FiniteDimensional k X] [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y] (σX : D.O →+* Module.End k X) (σY : D.O →+* Module.End k Y), (∀ c, σX (algebraMap (𝓞 D.F) D.O c) = χ c • 1) → (∀ c, σY (algebraMap (𝓞 D.F) D.O c) = χ c • 1) → D.m ^ 2 * Module.finrank k (GlobalTheory.HTRho.homO σX σY) = Module.finrank k X * Module.finrank k Y := by
  first | (exact @GlobalTheory.HTRho.finrank_homO_morita) | (exact GlobalTheory.HTRho.finrank_homO_morita) | (intros; apply GlobalTheory.HTRho.finrank_homO_morita <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRhoPartLieDeRhamQuotientStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_rho_part_lie_deRham_quotient : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → GlobalTheory.HTRho.jSub (GlobalTheory.HTCount.crysAct o₀) (fun i => β.comp (b.t i)) ⊤ ≤ (Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1)) ∧ ∀ i, Module.finrank k (HdR o₀.A ⧸ ((Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1)) ⊔ GlobalTheory.HTRho.mSub (GlobalTheory.HTCount.crysAct o₀) (β.comp (b.t i)) ⊤)) = D.m := by
  first | (exact @GlobalTheory.HTLieRho.lie_rho_quot) | (exact GlobalTheory.HTLieRho.lie_rho_quot) | (intros; apply GlobalTheory.HTLieRho.lie_rho_quot  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerFormApply

section

@[expose] public section

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

namespace GlobalTheory.HTRho

theorem finrank_homO_eq_quot_mSub : ∀ {k O C W V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (σW : O →+* Module.End k W) (τ : O →+* Module.End k V) (χ : C →+* k),
    (∀ c, τ (algebraMap C O c) = χ c • 1) →
    finrank k (homO σW τ) = finrank k (homO (qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))) τ) := by
  intro k O C W V _ _ _ _ _ _ _ _ _ _ σW τ χ hτ
  have hker : ∀ T : W →ₗ[k] V, T ∈ homO σW τ → mSub σW χ ⊤ ≤ LinearMap.ker T := by
    intro T hT
    rw [mem_homO] at hT
    refine Submodule.span_le.mpr ?_
    rintro z ⟨c, x, -, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hT, hτ, LinearMap.smul_apply,
      Module.End.one_apply, sub_self]
  let qa := qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))
  let e : homO qa τ ≃ₗ[k] homO σW τ :=
    { toFun := fun f => ⟨f.1 ∘ₗ (mSub σW χ ⊤).mkQ, by
        rw [mem_homO]
        intro a x
        have h := (mem_homO _ _ _).mp f.2 a ((mSub σW χ ⊤).mkQ x)
        change f.1 ((mSub σW χ ⊤).mkQ (σW a x)) = τ a (f.1 ((mSub σW χ ⊤).mkQ x))
        rw [← qAct_mk]
        exact h⟩
      invFun := fun T => ⟨(mSub σW χ ⊤).liftQ T.1 (hker T.1 T.2), by
        rw [mem_homO]
        intro a y
        induction y using Submodule.Quotient.induction_on with
        | H x =>
          have h := (mem_homO _ _ _).mp T.2 a x
          change (mSub σW χ ⊤).liftQ T.1 _ (qa a ((mSub σW χ ⊤).mkQ x)) = τ a ((mSub σW χ ⊤).liftQ T.1 _ ((mSub σW χ ⊤).mkQ x))
          simp only [qa, qAct_mk, Submodule.liftQ_mkQ, Submodule.mkQ_apply, Submodule.liftQ_apply]
          exact h⟩
      map_add' := fun f g => by ext; rfl
      map_smul' := fun c f => by ext; rfl
      left_inv := fun f => by
        ext y
        rfl
      right_inv := fun T => by ext; rfl }
  exact e.finrank_eq.symm

end GlobalTheory.HTRho
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerFormApplyStatement

section

@[expose] public section

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

theorem _root_.GlobalTheory.T.finrank_homO_eq_augmentationQuotient_of_scalar_character : ∀ {k O C W V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O] [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup V] [Module k V] [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V) (χ : C →+* k), (∀ c, τ (algebraMap C O c) = χ c • 1) → finrank k (homO σW τ) = finrank k (homO (qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))) τ) := by
  first | exact @GlobalTheory.HTRho.finrank_homO_eq_quot_mSub | exact GlobalTheory.HTRho.finrank_homO_eq_quot_mSub | (intros; apply GlobalTheory.HTRho.finrank_homO_eq_quot_mSub <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRhoPartDeformationDim

section

@[expose] public section

noncomputable section

namespace GlobalTheory.HTRho
open Module

def trAct {k O X X' : Type*} [Field k] [Ring O] [AddCommGroup X] [Module k X] [AddCommGroup X'] [Module k X']
    (e : X ≃ₗ[k] X') (σ : O →+* Module.End k X) : O →+* Module.End k X' where
  toFun a := e.toLinearMap ∘ₗ σ a ∘ₗ e.symm.toLinearMap
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

theorem trAct_apply {k O X X' : Type*} [Field k] [Ring O] [AddCommGroup X] [Module k X] [AddCommGroup X']
    [Module k X'] (e : X ≃ₗ[k] X') (σ : O →+* Module.End k X) (a : O) (x : X') :
    trAct e σ a x = e (σ a (e.symm x)) := rfl

theorem finrank_homO_trAct {k O X Y X' Y' : Type*} [Field k] [Ring O] [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] [AddCommGroup X'] [Module k X'] [AddCommGroup Y'] [Module k Y']
    (eX : X ≃ₗ[k] X') (eY : Y ≃ₗ[k] Y') (σX : O →+* Module.End k X) (σY : O →+* Module.End k Y) :
    finrank k (homO σX σY) = finrank k (homO (trAct eX σX) (trAct eY σY)) := by
  have h : (homO σX σY).map (LinearEquiv.arrowCongr eX eY).toLinearMap = homO (trAct eX σX) (trAct eY σY) := by
    ext T'
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, mem_homO, mem_homO]
    simp only [LinearEquiv.coe_coe, LinearEquiv.arrowCongr_symm_apply, LinearMap.comp_apply, trAct_apply]
    constructor
    · intro hT a x
      have := congrArg eY (hT a (eX.symm x))
      simpa using this
    · intro hT a x
      have := hT a (eX x)
      rw [LinearEquiv.symm_apply_apply] at this
      rw [this, LinearEquiv.symm_apply_apply]
  rw [← h, LinearEquiv.finrank_map_eq]

end GlobalTheory.HTRho

namespace GlobalTheory.HTRho
open Module GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

universe v
variable {k O C : Type*} {H : Type v} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O]

theorem finrank_ks_map_cls [FiniteDimensional k H] (σ : O →+* Module.End k H) (G Z : Submodule k H)
    (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (hZ : ∀ a, ∀ x ∈ Z, σ a x ∈ Z) (hZG : Z ≤ G) :
    finrank k ((ksSub σ 0 G Z).map (cls G)) =
      finrank k (homO (qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx)) (qAct σ G hG)) := GlobalTheory.T.finrank_ksSub_map_cls_eq_finrank_homO σ G Z hG hZ hZG

theorem finrank_homO_crt {ι W V : Type*} [Fintype ι] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V)
    (χ : ι → C →+* k) (hχ : Function.Injective χ) (hJ : jSub τ χ ⊤ = ⊥) :
    finrank k (homO σW τ) =
      ∑ i, finrank k (homO σW (qAct τ (mSub τ (χ i) ⊤) (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)))) := GlobalTheory.T.characterAugmentationSubspace_quotientAction_top σW τ χ hχ hJ

theorem finrank_homO_quot {W V : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V)
    (χ : C →+* k) (hτ : ∀ c, τ (algebraMap C O c) = χ c • 1) :
    finrank k (homO σW τ) =
      finrank k (homO (qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))) τ) := GlobalTheory.T.finrank_homO_eq_augmentationQuotient_of_scalar_character σW τ χ hτ

theorem quot_facts {ι : Type*} (σ : O →+* Module.End k H) (G : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G)
    (χ : ι → C →+* k) :
    (jSub σ χ ⊤ ≤ G → jSub (qAct σ G hG) χ ⊤ = ⊥) ∧
    ∀ i, finrank k ((H ⧸ G) ⧸ mSub (qAct σ G hG) (χ i) ⊤) = finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) := GlobalTheory.T.finrank_equivariantHom_eq_augmentation_quotient σ G hG χ

theorem finrank_sub_quot {ι : Type*} [Fintype ι] [FiniteDimensional k H] (σ : O →+* Module.End k H)
    (χ : ι → C →+* k) (hχ : Function.Injective χ) (Fil : Submodule k H) (hFil : ∀ a, ∀ x ∈ Fil, σ a x ∈ Fil)
    (ω : C) (r₀ r₁ : k) (hr : r₀ ≠ r₁)
    (hω : (σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1) = 0) (hχω : ∀ i, χ i ω = r₀)
    (hG : ∀ a, ∀ x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1),
      σ a x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1))
    (hZ : ∀ a, ∀ x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)),
      σ a x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)))
    (hJ : jSub σ χ ⊤ ≤ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1)) (i : ι) :
    let G := Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1)
    let Z := jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1))
    let σW := qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx)
    finrank k ((G ⧸ Z.comap G.subtype) ⧸ mSub σW (χ i) ⊤) + finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) =
      finrank k (H ⧸ mSub σ (χ i) ⊤) := GlobalTheory.T.finrank_ksSub_quotient_augmentation_of_two_roots σ χ hχ Fil hFil ω r₀ r₁ hr hω hχω hG hZ hJ i

theorem count {ι : Type*} [Fintype ι] [FiniteDimensional k H] (σ : O →+* Module.End k H)
    (χ : ι → C →+* k) (hχ : Function.Injective χ) (Fil : Submodule k H) (hFil : ∀ a, ∀ x ∈ Fil, σ a x ∈ Fil)
    (ω : C) (r₀ r₁ : k) (hr : r₀ ≠ r₁)
    (hω : (σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1) = 0) (hχω : ∀ i, χ i ω = r₀)
    (m n : ℕ) (hm : 0 < m)
    (hrank : ∀ i, finrank k (H ⧸ mSub σ (χ i) ⊤) = m * n)
    (hJ : jSub σ χ ⊤ ≤ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1))
    (hlie : ∀ i, finrank k (H ⧸ ((Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1)) ⊔ mSub σ (χ i) ⊤)) = m)
    (hmor : ∀ i (X Y : Type v) [AddCommGroup X] [Module k X] [FiniteDimensional k X] [AddCommGroup Y] [Module k Y]
      [FiniteDimensional k Y] (σX : O →+* Module.End k X) (σY : O →+* Module.End k Y),
      (∀ c, σX (algebraMap C O c) = χ i c • 1) → (∀ c, σY (algebraMap C O c) = χ i c • 1) →
      m ^ 2 * finrank k (homO σX σY) = finrank k X * finrank k Y) :
    KSDim σ 0 (Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1))
      (jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1))) (Fintype.card ι * (n - 1)) := by
  set G := Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1) with hGdef
  set Z := jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)) with hZdef
  have hωc : ∀ a, σ a * σ (algebraMap C O ω) = σ (algebraMap C O ω) * σ a := fun a => by
    rw [← map_mul, ← map_mul, Algebra.commutes]
  have hRst : ∀ r : k, ∀ a, ∀ x ∈ LinearMap.range (σ (algebraMap C O ω) - r • 1),
      σ a x ∈ LinearMap.range (σ (algebraMap C O ω) - r • 1) := by
    rintro r a _ ⟨y, rfl⟩
    refine ⟨σ a y, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, hωc]
  have hG : ∀ a, ∀ x ∈ G, σ a x ∈ G := by
    intro a x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]
    exact add_mem (Submodule.mem_sup_left (hFil a y hy)) (Submodule.mem_sup_right (hRst r₀ a z hz))
  have hZ : ∀ a, ∀ x ∈ Z, σ a x ∈ Z := jSub_stable σ χ _ (hRst r₁)
  have hZG : Z ≤ G := le_trans (Submodule.span_mono (by
    rintro z ⟨r, lam, c, x, -, hc, rfl⟩; exact ⟨r, lam, c, x, trivial, hc, rfl⟩)) hJ
  have key := GlobalTheory.UPel.Sm.KSCount.ksDim_finrank σ 0 G Z
  rw [finrank_ks_map_cls σ G Z hG hZ hZG] at key
  convert key using 1
  obtain ⟨hF1, hF2⟩ := quot_facts σ G hG χ
  rw [finrank_homO_crt _ _ χ hχ (hF1 hJ)]
  rw [← Finset.card_univ, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finrank_homO_quot _ _ (χ i) (qAct_mSub_algebraMap _ (χ i))]
  have hD := finrank_sub_quot σ χ hχ Fil hFil ω r₀ r₁ hr hω hχω hG hZ hJ i
  have hM := hmor i ((G ⧸ Z.comap G.subtype) ⧸ mSub (qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx)) (χ i) ⊤)
    ((H ⧸ G) ⧸ mSub (qAct σ G hG) (χ i) ⊤) _ _ (qAct_mSub_algebraMap _ (χ i)) (qAct_mSub_algebraMap _ (χ i))
  rw [hF2 i, hlie i] at hM
  simp only at hD
  rw [hlie i, hrank i] at hD
  have h1 := Nat.eq_sub_of_add_eq hD
  rw [h1, ← Nat.mul_sub_one] at hM
  rw [show m * (n - 1) * m = m ^ 2 * (n - 1) by ring] at hM
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) hM).symm

end GlobalTheory.HTRho

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTRho

theorem rhoCount : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → KSDim (GlobalTheory.HTCount.crysAct o₀) 0 (Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1)) (GlobalTheory.HTCount.lieZ o₀ β) (D.a * (D.n - 1)) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β hβ
  obtain ⟨hFree, hHodge, -, -, -⟩ := GlobalTheory.T.abelianScheme_firstDeRham_structure
  have hA := o₀.ab
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o₀.A hA
  obtain ⟨hfd, -, -⟩ := GlobalTheory.T.finrank_firstDeRhamHomology_hodgeFiltration_of_field hFree hHodge k o₀.A g hA hg
  have hunit : ∀ n : ℕ, n.Coprime p → IsUnit (n : k) := fun n hn => by
    simpa using (b.unit n hn).map β
  set σ := GlobalTheory.HTCount.crysAct o₀ with hσ
  set χ : Fin D.a → (𝓞 D.F →+* k) := fun i => β.comp (b.t i) with hχdef
  have hχ : Function.Injective χ := by
    intro i j hij
    by_contra hne
    have h1 := b.comax i j hne
    have hle : Ideal.span (Set.range fun x => b.t i x - b.t j x) ≤ RingHom.ker β := by
      rw [Ideal.span_le]
      rintro _ ⟨x, rfl⟩
      have := congrArg (fun f : 𝓞 D.F →+* k => f x) hij
      simp only [χ, RingHom.comp_apply] at this
      simp [RingHom.mem_ker, this]
    have h1' : (1 : R) ∈ RingHom.ker β := hle (by rw [h1]; trivial)
    simp at h1'
  have hFil : ∀ a, ∀ x ∈ Fil o₀.A, σ a x ∈ Fil o₀.A := fun a x hx => by
    haveI := o₀.act.hom a
    rw [hσ, GlobalTheory.HTCount.crysAct_apply]
    exact push_mem_Fil _ hx
  have hχω : ∀ i, χ i D.ω = β b.ρ := fun i => by simp [χ, b.t_ω]
  have hchar : ∀ n : ℕ, n.Coprime p → (n : k) ≠ 0 := fun n hn => (hunit n hn).ne_zero
  have hρk : β b.ρ ^ 2 - (D.tr : k) * β b.ρ + (D.nm : k) = 0 := by
    have := congrArg β b.ρ_root
    simpa using this
  have hr : β b.ρ ≠ (D.tr : k) - β b.ρ := by
    intro h
    have hd : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = 0 := by
      push_cast
      linear_combination (-(D.tr : k) + 2 * β b.ρ) * h - 4 * hρk
    have hp : (p : ℕ).Prime := Fact.out
    have hcop : (D.tr ^ 2 - 4 * D.nm).natAbs.Coprime p := by
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hdv => D.disc_p ?_)
      exact Int.natCast_dvd.2 hdv
    apply hchar _ hcop
    have hm := congrArg (Int.cast : ℤ → k) (Int.natAbs_mul_self' (D.tr ^ 2 - 4 * D.nm))
    rw [Int.cast_mul, Int.cast_mul, hd, mul_zero, Int.cast_natCast] at hm
    exact mul_self_eq_zero.1 hm
  have hω : (σ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1) * (σ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : k) - β b.ρ) • 1) = 0 := by
    have e1 : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
      rw [← D.tr_eq, ← D.nm_eq]; ring
    have e2 : σ (algebraMap (𝓞 D.F) D.O (D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F))) = 0 := by
      rw [e1]; simp
    simp only [map_add (f := _), map_sub, map_mul, map_intCast] at e2
    refine LinearMap.ext fun x => ?_
    have e3 := congrArg (fun T => T x) e2
    simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at e3
    simp only [Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul k] at e3
    simp only [LinearMap.smul_apply, Module.End.one_apply, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.zero_apply, map_sub, map_smul]
    set w := σ (algebraMap (𝓞 D.F) D.O D.ω)
    have : β b.ρ * ((D.tr : k) - β b.ρ) = D.nm := by linear_combination -hρk
    linear_combination (norm := module) e3 - hρk • x
  have hS2 := GlobalTheory.T.harrisTaylor_rho_part_lie_deRham_quotient p D R b N ‹_› ‹_› k t o₀ β hβ
  have key := count σ χ hχ (Fil o₀.A) hFil D.ω (β b.ρ) ((D.tr : k) - β b.ρ) hr hω hχω D.m D.n D.m_pos
    (GlobalTheory.T.harrisTaylor_finrank_deRham_quotient_character p D R b N ‹_› ‹_› k t o₀ β hβ) hS2.1 hS2.2
    (fun i X Y _ _ _ _ _ _ σX σY hX hY => by
      let eX := (Module.finBasis k X).equivFun
      let eY := (Module.finBasis k Y).equivFun
      rw [finrank_homO_trAct eX eY σX σY]
      have := GlobalTheory.T.finrank_hom_harrisTaylorOrder_morita p D k hchar (χ i) _ _ (trAct eX σX) (trAct eY σY)
        (fun c => LinearMap.ext fun x => by rw [trAct_apply, hX]; simp) (fun c => LinearMap.ext fun x => by rw [trAct_apply, hY]; simp)
      rwa [← eX.finrank_eq, ← eY.finrank_eq] at this)
  rw [Fintype.card_fin] at key
  exact key

end GlobalTheory.HTRho
end
end
end
