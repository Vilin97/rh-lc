module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodIdempotentBadPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnGaLMemGoodPart
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActionPreservesPrincipalFlagMultiplic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionIsAction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleSubrepWithGroupAlgebraFixedStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitFramePrincipalLevelFiniteGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleNotKilledByGoodProjectorSatisfiesHStatement
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotypicFactorOfIsIrreduciblePiFiniteGroups
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteGroupActionPrincipalLevelFixedVector

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.PrinFixedRep

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
  {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GfC V) W}

theorem mem_fixed_iff {x : W} :
    x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V)) ↔
      ∀ h : GfC V, (h : GA D V) ∈ levG V β (flag1L L) → σ h x = x := by
  unfold GlobalTheory.PRep.fixed GlobalTheory.PRep.eig
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
    MonoidHom.one_apply, Units.val_one, one_smul]
  constructor
  · intro H h hh
    exact H ⟨h, (Subgroup.mem_subgroupOf).2 hh⟩
  · intro H h
    exact H h ((Subgroup.mem_subgroupOf).1 h.2)

theorem act_eq_of_lifts {g0 : G0 L.Pg L.r} {κ κ' : GfC V} (hκ : IsLevelLift V β L g0 κ)
    (hκ' : IsLevelLift V β L g0 κ') {x : W}
    (hx : x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))) : σ κ' x = σ κ x := by
  have hm : ((κ⁻¹ * κ' : GfC V) : GA D V) ∈ levG V β (flag1L L) := by
    simpa using lift_div_mem hκ hκ'
  have e : κ' = κ * (κ⁻¹ * κ') := by group
  rw [e, map_mul, Module.End.mul_apply, (mem_fixed_iff.1 hx) _ hm]

theorem act_mem_fixed {g0 : G0 L.Pg L.r} {κ : GfC V} (hκ : IsLevelLift V β L g0 κ) {x : W}
    (hx : x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))) :
    σ κ x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V)) := by
  rw [mem_fixed_iff] at hx ⊢
  intro h hh
  have hc := (GlobalTheory.FlagAction.conj_mem_flag1 hκ hh).1
  have hc' : ((κ⁻¹ * (h * κ) : GfC V) : GA D V) ∈ levG V β (flag1L L) := by simpa using hc
  have e : h * κ = κ * (κ⁻¹ * (h * κ)) := by group
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hx _ hc']

theorem main : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank),
    LiftsExist V β L → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W),
    ∃ ρ : Representation ℂ (G0 L.Pg L.r) (GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))),
      ∀ (g0 : G0 L.Pg L.r) (κ : GfC V), IsLevelLift V β L g0 κ → ∀ x, (ρ g0 x : W) = σ κ x := by
  intro D V β L hl W _ _ σ
  let lift : G0 L.Pg L.r → GfC V := fun g0 => ⟨(hl g0).choose, (hl g0).choose_spec.1⟩
  have hlift : ∀ g0, IsLevelLift V β L g0 (lift g0) := fun g0 => (hl g0).choose_spec
  let F := GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))
  have hs : ∀ g0, ∀ x ∈ F, σ (lift g0) x ∈ F := fun g0 x hx => act_mem_fixed (hlift g0) hx
  let ρ : Representation ℂ (G0 L.Pg L.r) F :=
    { toFun := fun g0 => (σ (lift g0)).restrict (hs g0)
      map_one' := LinearMap.ext fun x => Subtype.ext (by
        show σ (lift 1) x = x
        have h1 : IsLevelLift V β L 1 ((1 : GfC V) : GA D V) :=
          GlobalTheory.FlagAction.isLift_one_of_mem (Subgroup.one_mem _)
        rw [act_eq_of_lifts h1 (hlift 1) x.2, map_one, Module.End.one_apply])
      map_mul' := fun g g' => LinearMap.ext fun x => Subtype.ext (by
        show σ (lift (g * g')) x = σ (lift g) (σ (lift g') x)
        have hm : IsLevelLift V β L (g * g') ((lift g * lift g' : GfC V) : GA D V) :=
          GlobalTheory.FlagAction.isLift_mul (hlift g) (hlift g')
        rw [act_eq_of_lifts hm (hlift (g * g')) x.2, map_mul, Module.End.mul_apply]) }
  refine ⟨ρ, fun g0 κ hκ x => ?_⟩
  show σ (lift g0) x = σ κ x
  exact act_eq_of_lifts hκ (hlift g0) x.2

end GlobalTheory.PrinFixedRep

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteGroupActionPrincipalLevelFixedVectorStatement

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.exists_finiteGroupAction_principalLevelFixedVectors : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), LiftsExist V β L → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), ∃ ρ : Representation ℂ (G0 L.Pg L.r) (GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))), ∀ (g0 : G0 L.Pg L.r) (κ : GfC V), IsLevelLift V β L g0 κ → ∀ x, (ρ g0 x : W) = σ κ x := by
  first | exact @GlobalTheory.PrinFixedRep.main | exact GlobalTheory.PrinFixedRep.main | (intros; apply GlobalTheory.PrinFixedRep.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitFramePrincipalLevelFiniteGroupStatement

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.exists_splitFrame_principalLevel_finiteGroup : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank) (h : L.r = V.rank), IsBaseFrame V β Λ N → L.Q = ∅ → (∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → ∃ (a : GfC V) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ L.Pg) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v) (ρ : ∀ v : S, ResF v.1 ≃+* kP (pl v).1), (∀ v ∉ S, ∀ k ∈ Kv V v, ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ levG V β (flag1L L)) ∧ ∀ (v : S) (k : Kv V v), ∃ g0 : G0 L.Pg L.r, IsLevelLift V β L g0 ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∧ (∀ PP, PP ≠ pl v → g0 PP = 1) ∧ ∀ i j : Fin L.r, (g0 (pl v)).1 i j = ρ v (((s v).red k).1 (i.cast h) (j.cast h)) := by
  first | exact @GlobalTheory.TrPtFrame.exists_splitFrame_levG | exact GlobalTheory.TrPtFrame.exists_splitFrame_levG | (intros; apply GlobalTheory.TrPtFrame.exists_splitFrame_levG <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotypicFactorOfIsIrreduciblePiFiniteGroupsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.isotypic_factor_of_isIrreducible_pi_finite_groups : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (∀ i, G i) W), ρ.IsIrreducible → ∀ i, ∃ (n : ℕ) (τ : Representation ℂ (G i) (Fin n → ℂ)), τ.IsIrreducible ∧ (∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, Function.Injective φ ∧ ∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ Submodule.span ℂ {y | ∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, (∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ y ∈ LinearMap.range φ} = ⊤ := by
  first | exact @GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi | exact GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi | (intros; apply GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypeVectorOfGoodLevelRepresentation

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.TypeVec

section Gen

theorem isIrreducible_comp {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X]
    (τ : Representation ℂ H' X) (f : H →* H') (hf : Function.Surjective f) (hτ : τ.IsIrreducible) :
    Representation.IsIrreducible (τ.comp f) := by
  let e : Subrepresentation (τ.comp f : Representation ℂ H X) ≃o Subrepresentation τ :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        obtain ⟨g', rfl⟩ := hf g
        exact U.apply_mem_toSubmodule g' hv⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact (OrderIso.isSimpleOrder_iff e).2 hτ

def glMap {K K' : Type} [CommRing K] [CommRing K'] {m n : ℕ} (e : K ≃+* K') (h : m = n) :
    GL (Fin n) K →* GL (Fin m) K' :=
  (Units.map (Matrix.reindexAlgEquiv K' K' (finCongr h.symm)).toAlgHom.toRingHom.toMonoidHom).comp
    (Matrix.GeneralLinearGroup.map e.toRingHom)

theorem glMap_apply {K K' : Type} [CommRing K] [CommRing K'] {m n : ℕ} (e : K ≃+* K') (h : m = n)
    (g : GL (Fin n) K) (i j : Fin m) : (glMap e h g).1 i j = e (g.1 (Fin.cast h i) (Fin.cast h j)) := rfl

theorem glMap_symm {K K' : Type} [CommRing K] [CommRing K'] {m n : ℕ} (e : K ≃+* K') (h : m = n)
    (g : GL (Fin m) K') : glMap e h (glMap e.symm h.symm g) = g := by
  apply Units.ext
  ext i j
  rw [glMap_apply, glMap_apply]
  simp

theorem glMap_surjective {K K' : Type} [CommRing K] [CommRing K'] {m n : ℕ} (e : K ≃+* K') (h : m = n) :
    Function.Surjective (glMap e h) := fun g => ⟨glMap e.symm h.symm g, glMap_symm e h g⟩

theorem mem_fixed_iff {H X : Type} [Group H] [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ H X}
    {K : Subgroup H} {x : X} : x ∈ GlobalTheory.PRep.fixed ρ K ↔ ∀ h : K, ρ h x = x := by
  show (∀ h : K, ρ h x = ((1 : K →* ℂˣ) h : ℂ) • x) ↔ _
  simp

end Gen

variable {D : D7}

def typeOf {V : HSp D} {P : Finset (HeightOneSpectrum (𝓞 D.host.E))} {r : ℕ} (hr : r = V.rank)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ P) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v)
    (ρv : ∀ v : S, ResF v.1 ≃+* kP (pl v).1) (n : P → ℕ)
    (τ : ∀ PP : P, Representation ℂ (GL (Fin r) (kP PP.1)) (Fin (n PP) → ℂ)) (hτ : ∀ PP, (τ PP).IsIrreducible) :
    TypeDataG V where
  S := S
  frame := s
  W := fun w => Fin (n (pl w)) → ℂ
  τ := fun w => (τ (pl w)).comp (glMap (ρv w) hr)
  irred := fun w => isIrreducible_comp _ _ (glMap_surjective _ _) (hτ (pl w))

theorem noFixed_typeOf {V : HSp D} {P : Finset (HeightOneSpectrum (𝓞 D.host.E))} {r : ℕ} (hr : r = V.rank)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ P) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v)
    (ρv : ∀ v : S, ResF v.1 ≃+* kP (pl v).1) (n : P → ℕ)
    (τ : ∀ PP : P, Representation ℂ (GL (Fin r) (kP PP.1)) (Fin (n PP) → ℂ)) (hτ : ∀ PP, (τ PP).IsIrreducible)
    (hne : S.Nonempty)
    (h : ∀ a, 0 < a → a < V.rank → ∃ v : S, ∀ y : Fin (n (pl v)) → ℂ,
      (∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.unipBlock (ResF v.1) V.rank a, τ (pl v) (glMap (ρv v) hr g) y = y) → y = 0) :
    NoFixed (typeOf hr S pl s ρv n τ hτ) :=
  ⟨hne, h⟩

theorem hasTypeVec_typeOf {V : HSp D} {P : Finset (HeightOneSpectrum (𝓞 D.host.E))} {r : ℕ} (hr : r = V.rank)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ P) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v)
    (ρv : ∀ v : S, ResF v.1 ≃+* kP (pl v).1) (n : P → ℕ)
    (τ : ∀ PP : P, Representation ℂ (GL (Fin r) (kP PP.1)) (Fin (n PP) → ℂ)) (hτ : ∀ PP, (τ PP).IsIrreducible)
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) (x : W) (hx : x ≠ 0)
    (hoff : ∀ v ∉ S, ∀ k ∈ Kv V v, σ (locFin V v k) x = x)
    (hon : ∀ v : S, x ∈ Submodule.span ℂ {y | ∃ φ : (Fin (n (pl v)) → ℂ) →ₗ[ℂ] W,
      (∀ (k : Kv V v) z, φ (τ (pl v) (glMap (ρv v) hr ((s v).red k)) z) = σ (locFin V v k) (φ z)) ∧
        y ∈ LinearMap.range φ}) :
    HasTypeVec (typeOf hr S pl s ρv n τ hτ) σ :=
  ⟨x, hx, hoff, hon⟩



theorem hasTypeVec_of_goodRep : GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC (Yc D 0)) W), IsAdmissible σ → GlobalTheory.CuspMult.IsGoodRep (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (RealDat.eC (A := A) D.what₂.embLL) σ → ∃ T : TypeDataG (Yc D 0), NoFixed T ∧ HasTypeVec T σ := by
  intro hGC D G _ _ Pl0 T A Ks _ _ _ R F hF W _ _ σ _hadm hgood
  classical
  have hrk : (Yc D 0).rank = D.R.r := by rw [D.sp.Y_rank _ (min_le_right _ _)]; simp [Ranks.rankY]
  have hr2 : 2 ≤ D.R.r := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hlev := hF.core.lev
  obtain ⟨c0, hbase⟩ := hlev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  have hnc : ∀ PP ∈ (R.dat0 R.triv).Pg, ∀ PP' ∈ (R.dat0 R.triv).Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP' := by
    intro PP hP PP' hP'
    obtain ⟨k, hk⟩ := (hlev.Pg PP).1 hP
    obtain ⟨k', hk'⟩ := (hlev.Pg PP').1 hP'
    exact GlobalTheory.ProjectedLift.not_isConjPl R.C.P hk hk'
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_finiteGroupAction_principalLevelFixedVectors D (Yc D 0) (R.βY 0) (R.dat0 R.triv) (GlobalTheory.ProjectedLift.liftsExist_rows R hlev) W σ
  obtain ⟨v, hv0, hvK, κ, hκ, hve⟩ := hgood
  have hvmem : v ∈ GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0))) :=
    mem_fixed_iff.2 fun k => hvK _ (Subgroup.mem_subgroupOf.1 k.2)
  haveI : Finite (G0 R.Pg D.R.r) := Finite.of_equiv G R.eG.toEquiv
  have hfix : ∑ g, RealDat.eC (A := A) D.what₂.embLL g • ρ (R.eG g) ⟨v, hvmem⟩ = ⟨v, hvmem⟩ := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Eq.trans (Finset.sum_congr rfl fun g _ => ?_) hve
    rw [SetLike.val_smul, hρ (R.eG g) (κ g) (hκ g)]
  obtain ⟨U, hUfd, hUirr, y, hy0, hye⟩ := GlobalTheory.T.exists_irreducible_subrep_with_groupAlgebra_fixed _ _ _ ρ (fun g => R.eG g) _ ⟨v, hvmem⟩
    (fun h => hv0 (congrArg Subtype.val h)) hfix
  haveI := hUfd
  have hH := GlobalTheory.T.irreducible_not_killed_by_good_projector_satisfies_H hGC R F hF U.toSubmodule U.toRepresentation hUirr ⟨y, hy0, hye⟩
  choose n τ hτ hrest using GlobalTheory.T.isotypic_factor_of_isIrreducible_pi_finite_groups (↥R.Pg) (fun PP => GL (Fin D.R.r) (kP PP.1)) U.toSubmodule U.toRepresentation hUirr
  obtain ⟨a, S, pl, s, ρv, hoff, hon⟩ : ∃ (a : GfC (Yc D 0)) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ R.Pg)
      (s : ∀ v : S, SplitAt D.sp.cm.sig (Yc D 0).gram (frameLat (Yc D 0)) v) (ρv : ∀ v : S, ResF v.1 ≃+* kP (pl v).1),
      (∀ v ∉ S, ∀ k ∈ Kv (Yc D 0) v, ((a * locFin (Yc D 0) v k * a⁻¹ : GfC (Yc D 0)) : GA D (Yc D 0)) ∈
        levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))) ∧
      ∀ (v : S) (k : Kv (Yc D 0) v), ∃ g0 : G0 R.Pg D.R.r, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0
          ((a * locFin (Yc D 0) v k * a⁻¹ : GfC (Yc D 0)) : GA D (Yc D 0)) ∧
        (∀ PP, PP ≠ pl v → g0 PP = 1) ∧
        ∀ i j : Fin D.R.r, (g0 (pl v)).1 i j = ρv v (((s v).red k).1 (i.cast hrk.symm) (j.cast hrk.symm)) :=
    GlobalTheory.T.exists_splitFrame_principalLevel_finiteGroup D (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hrk.symm hbase rfl hnc

  let yW : W := (((y : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W)
  have hyK : ∀ h : ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0))), σ h yW = yW := mem_fixed_iff.1 (y : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))).2

  have hcomm : ∀ (l : GfC (Yc D 0)) (q : W), σ a⁻¹ (σ (a * l * a⁻¹) q) = σ l (σ a⁻¹ q) := by
    intro l q
    have e1 : σ a⁻¹ * σ (a * l * a⁻¹) = σ l * σ a⁻¹ := by
      rw [← map_mul, ← map_mul, show a⁻¹ * (a * l * a⁻¹) = l * a⁻¹ by group]
    exact congrArg (fun f : Module.End ℂ W => f q) e1
  have hconj : ∀ l : GfC (Yc D 0), σ (a * l * a⁻¹) yW = yW → σ l (σ a⁻¹ yW) = σ a⁻¹ yW :=
    fun l hl => (hcomm l yW).symm.trans (congrArg (σ a⁻¹) hl)
  refine ⟨typeOf hrk.symm S pl s ρv n τ hτ, noFixed_typeOf _ _ _ _ _ _ _ _ ?_ ?_,
    hasTypeVec_typeOf _ _ _ _ _ _ _ _ σ (σ a⁻¹ yW) ?_ ?_ ?_⟩
  · obtain ⟨PP, -⟩ := hH 1 one_pos (by omega)
    exact ⟨(pl.symm PP).1, (pl.symm PP).2⟩
  · intro b hb hbr
    obtain ⟨PP, hPP⟩ := hH b hb (lt_of_lt_of_eq hbr hrk)
    refine ⟨pl.symm PP, fun z hz => ?_⟩
    obtain ⟨⟨φ, hφi, hφ⟩, -⟩ := hrest (pl (pl.symm PP))
    have hpl : pl (pl.symm PP) = PP := pl.apply_symm_apply PP
    rw [← hpl] at hPP
    apply hφi
    refine Eq.trans ?_ (map_zero φ).symm
    apply hPP
    rintro u ⟨hu1, hu2⟩
    have e1 := hφ (u (pl (pl.symm PP))) z
    have hmem : glMap (ρv (pl.symm PP)).symm hrk (u (pl (pl.symm PP))) ∈ GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.unipBlock (ResF (pl.symm PP).1) (Yc D 0).rank b := by
      intro i j hij
      rw [glMap_apply]
      have hent : (u (pl (pl.symm PP))).1 (Fin.cast hrk i) (Fin.cast hrk j) =
          (1 : Matrix (Fin D.R.r) (Fin D.R.r) (kP (pl (pl.symm PP)).1)) (Fin.cast hrk i) (Fin.cast hrk j) := by
        by_contra hne
        exact hij (hu2 _ _ hne)
      by_cases hij' : i = j
      · subst hij'
        have h1 : (u (pl (pl.symm PP))).1 (Fin.cast hrk i) (Fin.cast hrk i) = 1 := by simpa using hent
        simp only [h1, map_one, Matrix.one_apply_eq]
      · have h1 : (u (pl (pl.symm PP))).1 (Fin.cast hrk i) (Fin.cast hrk j) = 0 := by
          rw [hent, Matrix.one_apply_ne (fun h => hij' (Fin.cast_injective hrk h))]
        simp only [h1, map_zero, Matrix.one_apply_ne hij']
    have h2 := hz _ hmem
    rw [glMap_symm] at h2
    refine Eq.trans ?_ (congrArg φ h2)
    refine Eq.trans ?_ e1.symm
    refine congrArg (fun g => U.toRepresentation g (φ z)) ?_
    funext P'
    by_cases h : P' = pl (pl.symm PP)
    · subst h
      exact (Pi.mulSingle_eq_same (M := fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) _ _).symm
    · exact (hu1 P' h).trans (Pi.mulSingle_eq_of_ne (M := fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) h _).symm
  · intro h0
    apply hy0
    have h1 : yW = 0 := by
      have := congrArg (σ a) h0
      rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, map_zero] at this
    exact Subtype.ext (Subtype.ext h1)
  · intro w hw k hk
    exact hconj _ (hyK ⟨_, Subgroup.mem_subgroupOf.2 (hoff w hw k hk)⟩)
  · intro w
    obtain ⟨-, hsp⟩ := hrest (pl w)
    have hkey : ∀ (k : Kv (Yc D 0) w) (q : U.toSubmodule),
        σ a⁻¹ ((((U.toRepresentation (Pi.mulSingle (pl w) (glMap (ρv w) hrk.symm ((s w).red k))) q) :
          U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W) =
          σ (locFin (Yc D 0) w k) (σ a⁻¹ (((q : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W)) := by
      intro k q
      have h2 := hon w k
      have hlift := h2.choose_spec.1
      have hone := h2.choose_spec.2.1
      have hent := h2.choose_spec.2.2
      have hg0 : Pi.mulSingle (pl w) (glMap (ρv w) hrk.symm ((s w).red k)) = h2.choose := by
        funext P'
        by_cases hP : P' = pl w
        · subst hP
          refine (Pi.mulSingle_eq_same (M := fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) _ _).trans ?_
          apply Units.ext
          ext i j
          exact (glMap_apply _ _ _ i j).trans (hent i j).symm
        · exact (Pi.mulSingle_eq_of_ne (M := fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) hP _).trans (hone P' hP).symm
      have e2 := hρ _ (a * locFin (Yc D 0) w k * a⁻¹) hlift (q : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0))))
      exact (congrArg (fun g => σ a⁻¹ ((((U.toRepresentation g q) : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W)) hg0).trans
        ((congrArg (σ a⁻¹) e2).trans (hcomm _ _))
    have hy := Submodule.eq_top_iff'.1 hsp y
    show σ a⁻¹ (((y : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W) ∈ _
    clear hconj hyK yW hye hy0
    induction hy using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨ψ, hψ, z, rfl⟩ := hu
      exact Submodule.subset_span ⟨(σ a⁻¹ ∘ₗ (GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))).subtype ∘ₗ U.toSubmodule.subtype) ∘ₗ ψ,
        fun k z' => (congrArg (fun q : U.toSubmodule => σ a⁻¹ (((q : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W))
          (hψ _ z')).trans (hkey k (ψ z')), z, rfl⟩
    | zero => simpa using zero_mem _
    | add u u' _ _ hu hu' => simpa only [Submodule.coe_add, map_add (f := _)] using add_mem hu hu'
    | smul c u _ hu => simpa only [Submodule.coe_smul, map_smul] using Submodule.smul_mem _ c hu

end GlobalTheory.TypeVec
end
end
end
