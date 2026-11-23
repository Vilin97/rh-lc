module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieMultIffExistsFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductAdjointStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductPullbackUnique
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrincipalBaseChangeIffStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinearStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMap
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
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
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolarizedDataFieldExtension
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianPullbackTorusExtensionStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionModuleStructureStatement
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsAdapted
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondenceStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_pullback_correspondence : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (x : Sp R ⟶ X) (G : Over X) [GrpObj G] (G₀ : Over (Sp R)) [GrpObj G₀] (ψ : G₀.left ⟶ G.left) (L : Type) [AddCommGroup L] [Module R L], IsGrpPullback G₀ G x ψ → (∀ M : LieModel G x L, ∃ M₀ : LieModel G₀ (𝟙 _) L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left) ∧ ∀ M₀ : LieModel G₀ (𝟙 _) L, ∃ M : LieModel G x L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieMove.main | exact GlobalTheory.CompanionTheory.Ar.LieMove.main | (intros; apply GlobalTheory.CompanionTheory.Ar.LieMove.main <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.IntValSmul

section

@[expose] public section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights TensorProduct

noncomputable section
namespace LevelTowerAlt.Lin

variable {E L Ψ : Type} [Field E] [NumberField E] [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V]

theorem mem_eigSp {R W O : Type} [CommRing R] [AddCommGroup W] [Module R W] [CommRing O]
    (ρ : O →+* Module.End R W) (σ : O →+* R) (x : W) : x ∈ eigSp ρ σ ↔ ∀ a, ρ a x = σ a • x := by
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

def intVal (σ : 𝓞 E →+* L) (a : 𝓞 E) : 𝓞 L :=
  ⟨σ a, (NumberField.RingOfIntegers.isIntegral a).map σ.toIntAlgHom⟩

theorem intVal_coe (σ : 𝓞 E →+* L) (a : 𝓞 E) : ((intVal σ a : 𝓞 L) : L) = σ a := rfl

theorem intVal_smul (σ : 𝓞 E →+* L) (a : 𝓞 E) (x : V) : intVal σ a • x = σ a • x := by
  rw [← intVal_coe σ a]
  exact (algebraMap_smul L (intVal σ a) x).symm

structure Pre (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] (V : Type) [AddCommGroup V]
    [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (V₀ : Type) [AddCommGroup V₀] [Module (𝓞 L) V₀]
    (B : HermitianBundle.{0} L) where
  ρ : 𝓞 E →+* Module.End L V
  σ : Ψ ⊕ Ψ → (𝓞 E →+* L)
  σ_bij : Function.Bijective σ
  σ_inj : ∀ s, Function.Injective (σ s)
  fin : Module.Finite (𝓞 L) V₀
  j : V₀ →ₗ[𝓞 L] V
  j_inj : Function.Injective j
  span : Submodule.span L (Set.range j) = ⊤
  ρ₀ : 𝓞 E → V₀ → V₀
  j_ρ : ∀ a x, j (ρ₀ a x) = ρ a (j x)
  r : ℕ
  ε : Fin r → V₀
  ε_li : LinearIndependent (𝓞 L) ε
  I_stable : ∀ a, ∀ x ∈ AddSubgroup.closure (Set.range fun i => j (ε i)),
    ρ a x ∈ AddSubgroup.closure (Set.range fun i => j (ε i))
  f : V₀ →ₗ[𝓞 L] B.carrier
  ker : LinearMap.ker f = Submodule.span (𝓞 L) (Set.range ε)
  full : ∀ y, ∃ (a : 𝓞 L) (x : V₀), a ≠ 0 ∧ f x = a • y
  ρ' : 𝓞 E → B.carrier → B.carrier
  f_ρ : ∀ a x, f (ρ₀ a x) = ρ' a (f x)
  bar : 𝓞 E → 𝓞 E
  bar_conj : ∀ (τ : 𝓞 E →+* ℂ), Function.Injective τ → ∀ a, τ (bar a) = starRingEnd ℂ (τ a)
  adj : ∀ (ι : L →+* ℂ) a x y, (B.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] ρ' a x) ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] y) =
    (B.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] ρ' (bar a) y)

variable {V₀ : Type} [AddCommGroup V₀] [Module (𝓞 L) V₀] {B : HermitianBundle.{0} L} (P : Pre E L Ψ V V₀ B)

theorem Pre.eig {s : Ψ ⊕ Ψ} {x : V₀} (hx : P.j x ∈ eigSp P.ρ (P.σ s)) (a : 𝓞 E) :
    P.ρ' a (P.f x) = intVal (P.σ s) a • P.f x := by
  have h1 : P.ρ₀ a x = intVal (P.σ s) a • x := by
    apply P.j_inj
    rw [P.j_ρ, map_smul, intVal_smul]
    exact (mem_eigSp _ _ _).1 hx a
  rw [← P.f_ρ, h1, map_smul]

theorem Pre.orth {s s' : Ψ ⊕ Ψ} (h : s ≠ s') (ι : L →+* ℂ) {x y : V₀} (hx : P.j x ∈ eigSp P.ρ (P.σ s))
    (hy : P.j y ∈ eigSp P.ρ (P.σ s')) :
    (B.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] P.f x) ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] P.f y) = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, P.σ s a ≠ P.σ s' a := by
    by_contra hc
    push_neg at hc
    exact h (P.σ_bij.1 (RingHom.ext hc))
  have key : ∀ (c : 𝓞 L) (u : B.carrier), ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] (c • u) : Fibre ι B.carrier) =
      (ι (c : L) : ℂ) • ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] u) := by
    intro c u
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    congr 1
  have hτ : Function.Injective (ι.comp (P.σ s')) := ι.injective.comp (P.σ_inj s')
  have e := P.adj ι a (P.f x) (P.f y)
  rw [P.eig hx, P.eig hy, key, key, (B.metric.form ι).smul_left,
    InnerProductSpace.Core.inner_smul_right (c := (B.metric.form ι).toCore), intVal_coe, intVal_coe] at e
  have hb := P.bar_conj _ hτ a
  simp only [RingHom.comp_apply] at hb
  rw [hb] at e
  have hne : (starRingEnd ℂ) (ι (P.σ s a)) ≠ (starRingEnd ℂ) (ι (P.σ s' a)) := by
    intro heq
    exact ha (ι.injective ((starRingEnd ℂ).injective heq))
  have : ((starRingEnd ℂ) (ι (P.σ s a)) - (starRingEnd ℂ) (ι (P.σ s' a))) *
      (B.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] P.f x) ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] P.f y) = 0 := by
    rw [sub_mul, e, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

theorem Pre.li {ι : Type} {x : ι → V₀} (hx : LinearIndependent (𝓞 L) x) : LinearIndependent L fun i => P.j (x i) := by
  have h := hx.map' P.j (LinearMap.ker_eq_bot.2 P.j_inj)
  exact h.localization (Rₛ := L) (S := nonZeroDivisors (𝓞 L))

def Pre.inv : LinearMap.range P.j →ₗ[𝓞 L] V₀ := (LinearEquiv.ofInjective P.j P.j_inj).symm.toLinearMap

theorem Pre.j_inv (x : LinearMap.range P.j) : P.j (P.inv x) = x := by
  have := (LinearEquiv.ofInjective P.j P.j_inj).apply_symm_apply x
  exact congrArg Subtype.val this

theorem Pre.inv_j (x : V₀) : P.inv ⟨P.j x, x, rfl⟩ = x := P.j_inj (P.j_inv _)

def Pre.lin : LinPt E L Ψ V where
  ρ := P.ρ
  σ := P.σ
  σ_bij := P.σ_bij
  σ_inj := P.σ_inj
  Λ := LinearMap.range P.j
  fg := by
    haveI := P.fin
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  span := P.span
  stable := by
    rintro a _ ⟨x, rfl⟩
    exact ⟨_, P.j_ρ a x⟩
  I := AddSubgroup.closure (Set.range fun i => P.j (P.ε i))
  I_le := fun x hx => (AddSubgroup.closure_le (LinearMap.range P.j).toAddSubgroup).2
    (by rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩) hx
  I_stable := P.I_stable
  I_basis := ⟨P.r, _, P.li P.ε_li, rfl⟩
  Bq := B
  f := P.f.comp P.inv
  ker := fun x => by
    have e : Submodule.span (𝓞 L) (AddSubgroup.closure (Set.range fun i => P.j (P.ε i)) : Set V) =
        (Submodule.span (𝓞 L) (Set.range P.ε)).map P.j := by
      rw [Submodule.map_span, ← Set.range_comp]
      refine le_antisymm (Submodule.span_le.2 fun y hy => ?_) (Submodule.span_mono AddSubgroup.subset_closure)
      exact (AddSubgroup.closure_le (Submodule.span (𝓞 L) (Set.range (P.j ∘ P.ε))).toAddSubgroup).2
        Submodule.subset_span hy
    rw [e, ← P.ker, LinearMap.comp_apply]
    constructor
    · intro h
      exact ⟨_, h, P.j_inv x⟩
    · rintro ⟨y, hy, hxy⟩
      have : P.inv x = y := P.j_inj ((P.j_inv x).trans hxy.symm)
      rw [this]
      exact hy
  full := fun y => by
    obtain ⟨a, x, ha, h⟩ := P.full y
    exact ⟨a, ⟨P.j x, x, rfl⟩, ha, by rw [LinearMap.comp_apply, P.inv_j, h]⟩
  orth := by
    rintro s s' h ι _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact P.orth h ι (by rw [P.j_inv]; exact hx) (by rw [P.j_inv]; exact hy)

include P in
theorem Pre.rank_le [Module.Finite L V] : Module.finrank (𝓞 L) B.carrier ≤ Module.finrank L V := by
  have h2 : Module.rank (𝓞 L) V₀ ≤ (Module.finrank L V : Cardinal) := by
    apply _root_.rank_le
    intro s hs
    have := (P.li hs).fintype_card_le_finrank
    simpa using this
  have hq : Module.rank (𝓞 L) (B.carrier ⧸ LinearMap.range P.f) = 0 := by
    rw [rank_eq_zero_iff]
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨a, x, ha, h⟩ := P.full y
    refine ⟨a, ha, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← h]
    exact ⟨x, rfl⟩
  have h1 : Module.rank (𝓞 L) B.carrier ≤ Module.rank (𝓞 L) V₀ := by
    rw [← rank_quotient_add_rank_of_isDomain (LinearMap.range P.f), hq, zero_add]
    exact rank_range_le P.f
  exact Module.finrank_le_of_rank_le (h1.trans h2)

end LevelTowerAlt.Lin
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.TorusModelCochar

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open GroundTheory.Heights₂.Heights TensorProduct

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace LevelTowerAlt.Lin

theorem pull_inj {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} {v v' : T ⟶ G'}
    (e : v.left ≫ φ = v'.left ≫ φ) : v = v' :=
  Over.OverMorphism.ext (h.1.hom_ext e (by rw [Over.w, Over.w]))

theorem isGrpPullback_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom] :
    IsGrpPullback A B (𝟙 S) e.hom.left := by
  refine ⟨?_, fun T x y x₀ y₀ hx hy => ?_⟩
  · haveI : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · have e₁ : (x * y) ≫ e.hom = (x ≫ e.hom) * (y ≫ e.hom) := by
      first | exact Hom.mul_comp _ _ _ | exact MonObj.mul_comp _ _ _ | exact CategoryTheory.Hom.mul_comp _ _ _
    have : (x * y).left ≫ e.hom.left = ((x ≫ e.hom) * (y ≫ e.hom)).left := by
      rw [← e₁]; rfl
    rw [this]
    exact mul_left_congr (Category.comp_id _) _ _ _ _ hx hy

variable {L : Type} [Field L] [NumberField L]

theorem exists_generic {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (z : Sp (𝓞 L) ⟶ X)
    {V₀ : Type} [AddCommGroup V₀] [Module (𝓞 L) V₀] (M₀ : LieModel G z V₀) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module L V) (_ : Module (𝓞 L) V) (_ : IsScalarTower (𝓞 L) L V)
      (Mz : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) V) (j : V₀ →ₗ[𝓞 L] V),
      (∀ e, (Mz.pt (j e)).left = spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (M₀.pt e).left) ∧ Function.Injective j ∧
        Submodule.span L (Set.range j) = ⊤ ∧ Module.Finite (𝓞 L) V₀ ∧ Module.Finite L V := by
  obtain ⟨V, _, _, ⟨Mz⟩⟩ := lieModel_exists X G L (spMap (algebraMap (𝓞 L) L) ≫ z)
  letI : Module (𝓞 L) V := Module.compHom V (algebraMap (𝓞 L) L)
  haveI : IsScalarTower (𝓞 L) L V := ⟨fun a b x => by
    show (a • b) • x = algebraMap (𝓞 L) L a • b • x
    rw [Algebra.smul_def, mul_smul]⟩
  obtain ⟨j₀, hj₀, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear X G (𝓞 L) L (algebraMap (𝓞 L) L) z V₀ V M₀ Mz
  let j : V₀ →ₗ[𝓞 L] V :=
    { toFun := j₀
      map_add' := j₀.map_add
      map_smul' := fun a x => j₀.map_smulₛₗ a x }
  have hj : ∀ e, (Mz.pt (j e)).left = spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (M₀.pt e).left := fun e =>
    (Category.comp_id _).symm.trans (hj₀ e)
  obtain ⟨hf, hp, hb⟩ := GlobalTheory.T.lie_model_finite_base_change X G (𝓞 L) z V₀ M₀
  have hbc : IsBaseChange L j := hb L V Mz j hj
  haveI : IsLocalizedModule (nonZeroDivisors (𝓞 L)) j := (isLocalizedModule_iff_isBaseChange _ L j).2 hbc
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, Mz, j, hj, ?_, ?_, hf,
    (GlobalTheory.T.lie_model_finite_base_change X G L _ V Mz).1⟩
  · refine (injective_iff_map_eq_zero j).2 fun x hx => ?_
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors (𝓞 L)) j).1 hx
    exact (smul_eq_zero.1 (show (s : 𝓞 L) • x = 0 from hs)).resolve_left (nonZeroDivisors.coe_ne_zero s)
  · refine eq_top_iff.2 fun x _ => ?_
    induction x using hbc.inductionOn with
    | tmul m => exact Submodule.subset_span ⟨m, rfl⟩
    | smul s n hn => exact Submodule.smul_mem _ _ (hn trivial)
    | add a b ha hb => exact Submodule.add_mem _ (ha trivial) (hb trivial)

theorem generic_inj {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (z : Sp (𝓞 L) ⟶ X)
    {V₀ : Type} [AddCommGroup V₀] [Module (𝓞 L) V₀] (M₀ : LieModel G z V₀) {e e' : V₀}
    (h : spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (M₀.pt e).left =
      spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (M₀.pt e').left) : e = e' := by
  obtain ⟨V, _, _, _, _, Mz, j, hj, hi, -⟩ := exists_generic G z M₀
  exact hi (Mz.inj (Over.OverMorphism.ext ((hj e).trans (h.trans (hj e').symm))))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem comp_bar (H : Host E) (τ : 𝓞 E →+* ℂ) (hτ : Function.Injective τ) (a : 𝓞 E) :
    τ (H.bar a) = starRingEnd ℂ (τ a) := by
  let ψ : E →+* ℂ := IsFractionRing.lift hτ
  have hψ : ∀ b : 𝓞 E, ψ (b : E) = τ b := fun b => IsFractionRing.lift_algebraMap hτ b
  rw [← hψ, ← hψ, H.bar_eq, IsCMField.complexEmbedding_complexConj]

theorem adj_model (t' : SAB H (Sp (𝓞 L))) (tB : SAB H (Sp L)) (m' : SABMap tB t' (spMap (algebraMap (𝓞 L) L)))
    (hpr : IsPrincipal tB) (B : HermitianBundle.{0} L) (MB : LieModel t'.G (𝟙 _) B.carrier)
    (hB : IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B MB) (ρ' : 𝓞 E →+* Module.End (𝓞 L) B.carrier)
    (hρ' : MB.IsActOf t'.act.act ρ') (eC : L →+* ℂ) (a : 𝓞 E) (x y : B.carrier) :
    (B.metric.form eC).inner ((1 : ComplexAt eC) ⊗ₜ[𝓞 L] ρ' a x) ((1 : ComplexAt eC) ⊗ₜ[𝓞 L] y) =
      (B.metric.form eC).inner ((1 : ComplexAt eC) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt eC) ⊗ₜ[𝓞 L] ρ' (H.bar a) y) := by
  let epsBase {R R' : Type} [CommRing R] [CommRing R'] {S : Scheme.{0}} {z : Sp R ⟶ S}
      {z' : Sp R' ⟶ S} (φ : R →+* R') (h : spMap φ ≫ z = z') : epsAt z' ⟶ epsAt z :=
    Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ)) (by
      have heq : spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
          Spec.map (CommRingCat.ofHom (algebraMap R' (DualNumber R'))) ≫ spMap φ := by
        simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        ext r <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
      change _ ≫ _ ≫ z = _ ≫ z'
      rw [← Category.assoc, heq, Category.assoc, h])
  have isTanAt_base {R R' : Type} [CommRing R] [CommRing R'] {S : Scheme.{0}}
      {G : Over S} [GrpObj G] {z : Sp R ⟶ S} {z' : Sp R' ⟶ S}
      (φ : R →+* R') (hφ : spMap φ ≫ z = z') {v : epsAt z ⟶ G}
      (h : IsTanAt G z v) : IsTanAt G z' (epsBase φ hφ ≫ v) := by
    have heq : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R' R' R').toRingHom) ≫
        spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) =
        spMap φ ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      refine RingHom.ext fun a => ?_
      simp [GlobalTheory.CompanionTheory.Ar.dualMap]
    change _ ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ v.left = _
    rw [← Category.assoc, heq, Category.assoc, h]
    exact congrArg (·.left)
      (comp_one (M := G) (Over.homMk (spMap φ) hφ : Over.mk z' ⟶ Over.mk z))
  let w := fun u : B.carrier => epsBase (eC.comp (algebraMap (𝓞 L) L)) rfl ≫ MB.pt u
  have hl : ∀ u, ((w u).left ≫ (𝟙 t'.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (eC.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt u).left) := fun u => Category.comp_id _
  have ht : ∀ u, IsTanAt t'.G _ (w u) := fun u => isTanAt_base _ rfl (MB.tan u)
  have ha : ∀ b u, w (ρ' b u) = w u ≫ t'.act.act b := fun b u => by
    simp only [w]
    rw [hρ' b u, Category.assoc]
  have hpol : ∃ (t'' : SAB H (Sp ℂ)) (_ : SABMap t'' t' (spMap (eC.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _)),
      IsProper t''.G.hom ∧ Out.RelAmple t''.G t''.PP.L := by
    rw [Category.comp_id, ← Sl.BaseExt.spMap_comp]
    obtain ⟨t'', ⟨m⟩⟩ := Sl.BaseExt.exists_pull (spMap eC) tB
    obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ t' tB t'' _ _ m' m
    have := (GlobalTheory.T.isPrincipal_base_change_iff E H L ℂ eC tB t'' m).2 hpr
    exact ⟨t'', n, this.1, this.2.1⟩
  have h1 := hB eC (ρ' a x) y _ _ (hl _) (hl _)
  have h2 := hB eC x (ρ' (H.bar a) y) _ _ (hl _) (hl _)
  rw [ha] at h1 h2
  exact HodgeUnique.hodgeInnerProduct_eq ((GlobalTheory.T.hodge_inner_product_adjoint E H _ t' _ (w x) (w y) a _ hpol (ht x) (ht y)).1 h1) h2

theorem closure_basis {X V : Type} [AddCommGroup X] [AddCommGroup V] {r : ℕ} (bs : Module.Basis (Fin r) ℤ X)
    (κ : X →+ V) (x : V) : x ∈ AddSubgroup.closure (Set.range fun i => κ (bs i)) ↔ ∃ δ, κ δ = x := by
  constructor
  · intro hx
    exact (AddSubgroup.closure_le κ.range).2 (by rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩) hx
  · rintro ⟨δ, rfl⟩

    rw [← bs.sum_repr δ, map_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _

theorem torusModel_cochar (X : Type) [AddCommGroup X] :
    IsCocharLie (Fl.Test.torusModel (𝟙 (Sp L)) X) := fun δ χ =>
  (GlobalTheory.Diag.charVal_eq_torusFst _ χ).symm.trans (GlobalTheory.Diag.charVal_epsVec δ χ)

theorem exists_lin {Ψ : Type} {X : Scheme.{0}} (t : SAB H X) (z : Sp (𝓞 L) ⟶ X)
    (P : AbPart t (spMap (algebraMap (𝓞 L) L) ≫ z)) (t' : SAB H (Sp (𝓞 L)))
    (m' : SABMap P.tB t' (spMap (algebraMap (𝓞 L) L))) (hpr : IsPrincipal P.tB) (B : HermitianBundle.{0} L)
    (MB : LieModel t'.G (𝟙 _) B.carrier) (hB : IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B MB)
    (σ : Ψ ⊕ Ψ → (𝓞 E →+* L)) (hσ : Function.Bijective σ) (hσ' : ∀ s, Function.Injective (σ s)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module L V) (_ : Module (𝓞 L) V) (_ : IsScalarTower (𝓞 L) L V)
      (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L Ψ V), A.σ = σ ∧ MV.IsActOf P.tK.act.act A.ρ ∧
      (∀ x, x ∈ A.Λ ↔ ∃ v : epsAt z ⟶ t.G, IsTanAt t.G z v ∧
        (MV.pt x).left ≫ P.m.φ = spMap (dualMap (algebraMap (𝓞 L) L)) ≫ v.left) ∧
      P.IsCochars MV A.I ∧
      (∃ (MB : LieModel t'.G (𝟙 _) A.Bq.carrier), IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) A.Bq MB ∧
        ∀ x : A.Λ, ((MV.pt x ≫ P.τ.q ≫ P.e.hom).left ≫ m'.φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt (A.f x)).left)) ∧
      Module.finrank (𝓞 L) A.Bq.carrier ≤ Module.finrank L V := by
  letI := P.τ.addCommGroup
  letI := P.τ.grpB
  haveI := P.τ.free
  haveI := P.τ.finite
  haveI := P.τ.q_hom
  haveI := P.τ.i_hom
  haveI := P.e_hom
  haveI heinv : IsMonHom P.e.inv := inferInstance
  haveI : Smooth t.G.hom := t.semi.smooth
  haveI : Smooth t'.G.hom := t'.semi.smooth
  obtain ⟨V₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X t.G (𝓞 L) z
  obtain ⟨V, _, _, _, _, Mz, j, hj, hinj, hspan, hfin₀, hfin⟩ := exists_generic t.G z M₀
  obtain ⟨MV, hMV⟩ := (GlobalTheory.T.lie_model_pullback_correspondence L X _ t.G P.tK.G P.m.φ V P.m.cart).1 Mz
  have hj' : ∀ e, (MV.pt (j e)).left ≫ P.m.φ = spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (M₀.pt e).left :=
    fun e => (hMV _).trans (hj e)
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act _ _ L (𝟙 _) _ MV (𝓞 E) P.tK.act.act P.tK.act.hom
    P.tK.act.one P.tK.act.mul P.tK.act.add
  obtain ⟨ρ₀, hρ₀, -⟩ := lieModel_exists_unique_act _ _ (𝓞 L) z _ M₀ (𝓞 E) t.act.act t.act.hom
    t.act.one t.act.mul t.act.add
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act _ _ (𝓞 L) (𝟙 _) _ MB (𝓞 E) t'.act.act t'.act.hom
    t'.act.one t'.act.mul t'.act.add
  have hjρ : ∀ a x, j (ρ₀ a x) = ρ a (j x) := fun a x => MV.inj (pull_inj P.m.cart (by
    rw [hj', hρ₀ a x, hρ a (j x), Over.comp_left, Over.comp_left, Category.assoc, P.m.act a, ← Category.assoc,
      ← Category.assoc, hj']))
  obtain ⟨md, hmd⟩ := GlobalTheory.T.torus_extension_module_structure L P.tK.G P.τ (𝓞 E) P.tK.act (fun a => by
    haveI := P.tB.act.hom a
    refine ⟨P.e.hom ≫ P.tB.act.act a ≫ P.e.inv, inferInstance, ?_⟩
    refine (cancel_mono P.e.hom).1 ?_
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using P.act a)
  letI := md
  let MT := Fl.Test.torusModel (𝟙 (Sp L)) P.τ.X
  have hMT : IsCocharLie MT := torusModel_cochar _
  obtain ⟨iL, hiL, -⟩ := lieModel_exists_unique_diff _ _ _ L (𝟙 _) _ _ MT MV P.τ.i
  let κ : (P.τ.X →+ ℤ) →+ V := iL.toAddMonoidHom.comp (AddMonoidHom.compHom (Int.castAddHom L))
  have hκ : ∀ δ, MV.pt (κ δ) = MT.pt ((Int.castAddHom L).comp δ) ≫ P.τ.i := fun δ => hiL _
  let bs := Module.finBasis ℤ (P.τ.X →+ ℤ)
  have hφ' : IsGrpPullback P.τ.B t'.G (spMap (algebraMap (𝓞 L) L)) (P.e.hom.left ≫ m'.φ) := by
    have := (isGrpPullback_iso P.e).comp m'.cart
    simpa using this
  obtain ⟨ε, f, hε, hf, hli, hker, hsur⟩ := GlobalTheory.T.semi_abelian_pullback_torus_extension X t.G t.semi L z P.tK.G P.m.φ P.τ t'.G _ t'.semi P.m.cart hφ'
    MT hMT V₀ B.carrier M₀ MB _ bs
  have hjε : (fun i => j (ε i)) = fun i => κ (bs i) := funext fun i => MV.inj (pull_inj P.m.cart (by
    rw [hj', hκ]
    exact (hε i).symm))
  have hfl : ∀ e, (MV.pt (j e) ≫ P.τ.q ≫ P.e.hom).left ≫ m'.φ =
      spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt (f e)).left := fun e => by
    refine Eq.trans ?_ (hf e _ (hj' e))
    simp only [Over.comp_left, Category.assoc]
  let Q : Pre E L Ψ V V₀ B :=
    { ρ := ρ, σ := σ, σ_bij := hσ, σ_inj := hσ', fin := hfin₀, j := j, j_inj := hinj, span := hspan
      ρ₀ := fun a x => ρ₀ a x, j_ρ := hjρ, r := _, ε := ε, ε_li := hli
      I_stable := fun a x hx => by
        rw [hjε, closure_basis] at hx ⊢
        obtain ⟨δ, rfl⟩ := hx
        refine ⟨δ.comp (DistribSMul.toAddMonoidHom P.τ.X a), MV.inj ?_⟩
        rw [hρ a, hκ, hκ, Category.assoc, ← hmd a, ← Category.assoc]
        exact congrArg (· ≫ P.τ.i) (GlobalTheory.Diag.epsVec_comp_diagMap ((Int.castAddHom L).comp δ) _).symm
      f := f, ker := hker, full := hsur, ρ' := fun a x => ρ' a x
      f_ρ := fun a x => generic_inj t'.G (𝟙 _) MB (by
        have e1 : MV.pt (j (ρ₀ a x)) ≫ P.τ.q ≫ P.e.hom =
            (MV.pt (j x) ≫ P.τ.q ≫ P.e.hom) ≫ P.tB.act.act a := by
          rw [hjρ, hρ a]
          simp only [Category.assoc]
          rw [P.act a]
        rw [← hfl, e1, Over.comp_left, Category.assoc]
        refine (congrArg (_ ≫ ·) (m'.act a)).trans ?_
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (congrArg (· ≫ (t'.act.act a).left) (hfl x)).trans ?_
        rw [hρ' a, Over.comp_left, Category.assoc])
      bar := H.bar, bar_conj := comp_bar H, adj := adj_model t' P.tB m' hpr B MB hB ρ' hρ' }
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, MV, Q.lin, rfl, hρ, fun x => ?_,
    ⟨MT, hMT, fun x => ?_⟩, ⟨MB, hB, fun x => ?_⟩, Q.rank_le⟩
  · constructor
    · rintro ⟨e, rfl⟩
      exact ⟨M₀.pt e, M₀.tan e, hj' e⟩
    · rintro ⟨v, hv, h⟩
      obtain ⟨e, rfl⟩ := M₀.onto v hv
      exact ⟨e, MV.inj (pull_inj P.m.cart ((hj' e).trans h.symm))⟩
  · show x ∈ AddSubgroup.closure (Set.range fun i => j (ε i)) ↔ _
    rw [hjε, closure_basis]
    refine exists_congr fun δ => ?_
    rw [← hκ]
    exact ⟨fun h => by rw [h], fun h => (MV.inj h).symm⟩
  · have := hfl (Q.inv x)
    rw [show j (Q.inv x) = x from Q.j_inv x] at this
    exact this

end LevelTowerAlt.Lin
end
end
end
