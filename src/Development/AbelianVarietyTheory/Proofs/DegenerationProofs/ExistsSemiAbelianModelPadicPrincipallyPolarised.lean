module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelSplitSpecialFibre
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotModelTrans
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemistableOfRationalLTorsion
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
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPointsPolarisedAbelianVarietyGaloisStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
import Mathlib.RingTheory.Henselian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemistableOfRationalLTorsionStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.potentialSemistable_of_rational_lTorsion : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ (l : ℕ), l.Prime → 3 ≤ l → IsUnit (l : V) → ∀ (P : Out.PolAV (Sp K)), (∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ P.A), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  first | exact @GlobalTheory.SS.potModel_of_rational_torsion | exact GlobalTheory.SS.potModel_of_rational_torsion | (intros; apply GlobalTheory.SS.potModel_of_rational_torsion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PrincipallyPolarizedAbelianVarietyPotentialSemiA

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SemiPol

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem exists_prime_unit (V : Type) [CommRing V] [IsLocalRing V] :
    ∃ l : ℕ, l.Prime ∧ 3 ≤ l ∧ IsUnit (l : V) := by
  have h : IsUnit ((2 : V) * ((3 : ℕ) : V) + -((5 : ℕ) : V)) := by
    have : (2 : V) * ((3 : ℕ) : V) + -((5 : ℕ) : V) = 1 := by push_cast; ring
    rw [this]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
  · exact ⟨3, Nat.prime_three, le_rfl, isUnit_of_mul_isUnit_right h⟩
  · exact ⟨5, Nat.prime_five, by norm_num, by simpa using h⟩

theorem exists_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (P : Out.PolAV S) :
    ∃ (P' : Out.PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ := by
  obtain ⟨P', φ, hφ, -, mul, -⟩ :=
    polBaseChange_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally S S' f P
  refine ⟨P', φ, hφ, fun T x y x₀ y₀ hx hy => ?_⟩
  have e₁ : x₀ = Out.toBase hφ.w x := Over.OverMorphism.ext hx
  have e₂ : y₀ = Out.toBase hφ.w y := Over.OverMorphism.ext hy
  rw [e₁, e₂, ← mul]
  rfl

theorem fixed_of_rational {K K₁ Ω Ω₁ : Type} [Field K] [Field K₁] [Field Ω] [Field Ω₁] [Algebra K K₁] [Algebra K Ω]
    [Algebra K₁ Ω] [IsScalarTower K K₁ Ω] [Algebra K₁ Ω₁] (j : Ω ≃ₐ[K₁] Ω₁)
    {A : Over (Sp K)} [GrpObj A] {A₁ : Over (Sp K₁)} [GrpObj A₁] {φ : A₁.left ⟶ A.left}
    (h : IsGrpPullback A₁ A (spMap (algebraMap K K₁)) φ) (l : ℕ)
    (hr : ∀ x : Over.mk (spMap (algebraMap K Ω)) ⟶ A, x ^ l = 1 →
      ∃ y : Sp K₁ ⟶ A.left, spMap (algebraMap K₁ Ω) ≫ y = x.left)
    (τ : Ω₁ ≃ₐ[K₁] Ω₁) (x : Over.mk (spMap (algebraMap K₁ Ω₁)) ⟶ A₁) (hx : x ^ l = 1) :
    spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback h (spMap (algebraMap K₁ Ω₁))
    (spMap (algebraMap K₁ Ω₁) ≫ spMap (algebraMap K K₁)) rfl
  let u : Over.mk (spMap (algebraMap K Ω)) ⟶ Over.mk (spMap (algebraMap K₁ Ω₁) ≫ spMap (algebraMap K K₁)) :=
    Over.homMk (spMap j.symm.toRingEquiv.toRingHom) (by
      show spMap _ ≫ spMap _ ≫ spMap _ = spMap _
      rw [sp_comp, sp_comp]
      congr 1
      ext c
      simp [← IsScalarTower.algebraMap_apply])
  obtain ⟨y, hy⟩ := hr (u ≫ e x) (by rw [← MonObj.comp_pow, ← map_pow, hx, map_one, MonObj.comp_one])
  have hy' : spMap (algebraMap K₁ Ω) ≫ y = spMap j.symm.toRingEquiv.toRingHom ≫ x.left ≫ φ := by
    rw [hy, ← he]; rfl
  have h₁ : spMap (algebraMap K₁ Ω₁) ≫ y = x.left ≫ φ := by
    have e₁ : spMap j.toRingEquiv.toRingHom ≫ spMap (algebraMap K₁ Ω) = spMap (algebraMap K₁ Ω₁) := by
      rw [sp_comp]; congr 1; ext c; simp
    have e₂ : spMap j.toRingEquiv.toRingHom ≫ spMap j.symm.toRingEquiv.toRingHom = 𝟙 _ := by
      rw [sp_comp, ← Spec.map_id]; congr 1; ext c; simp
    refine (congrArg (· ≫ y) e₁.symm).trans ((Category.assoc _ _ _).trans ?_)
    rw [hy', ← Category.assoc, e₂]
    exact Category.id_comp _
  have hτ : spMap τ.toRingEquiv.toRingHom ≫ spMap (algebraMap K₁ Ω₁) = spMap (algebraMap K₁ Ω₁) := by
    rw [sp_comp]; congr 1; ext c; simp
  refine h.1.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) h₁.symm).trans ?_
    rw [← Category.assoc, hτ, h₁]
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (Over.w x)).trans ?_
    exact hτ.trans (Over.w x).symm

theorem exists_finset (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (l : ℕ) (hl : l.Prime) :
    ∃ s : Finset Ω, ∀ (K₁ : Type) [Field K₁] [Algebra K K₁] [Algebra K₁ Ω] [IsScalarTower K K₁ Ω],
      (∀ c ∈ s, c ∈ (algebraMap K₁ Ω).fieldRange) →
      ∀ x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A, x ^ l = 1 →
        ∃ y : Sp K₁ ⟶ P.A.left, spMap (algebraMap K₁ Ω) ≫ y = x.left := by
  classical
  have hc := (GlobalTheory.T.torsion_points_polarised_abelianVariety_galois K P Ω l hl).1 1
  rw [pow_one] at hc
  have hfin : Finite {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hl.ne_zero)
  have hsm := P.smoothDim
  have hsm' : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g _
  have hft : LocallyOfFiniteType P.A.hom := inferInstance
  have key : ∀ x : {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l = 1}, ∃ s : Finset Ω,
      ∀ (K₁ : Type) [Field K₁] [Algebra K K₁] [Algebra K₁ Ω] [IsScalarTower K K₁ Ω],
      (∀ c ∈ s, c ∈ (algebraMap K₁ Ω).fieldRange) →
        ∃ y : Sp K₁ ⟶ P.A.left, spMap (algebraMap K₁ Ω) ≫ y = x.1.left := by
    intro x
    obtain ⟨E, -, h₂, h₃⟩ := GlobalTheory.SS.exists_fieldOfValues P.A.left Ω x.1.left
    obtain ⟨L, hL, rfl⟩ := h₃ K P.A.hom hft (Over.w x.1) inferInstance
    obtain ⟨s, hs⟩ : (Subalgebra.toSubmodule L.toSubalgebra).FG :=
      (Submodule.fg_iff_finiteDimensional _).2 hL
    refine ⟨s, fun K₁ _ _ _ _ hK => (h₂ K₁ _).1 fun c hc => ?_⟩
    have : Subalgebra.toSubmodule L.toSubalgebra ≤
        Subalgebra.toSubmodule (IsScalarTower.toAlgHom K K₁ Ω).range := by
      rw [← hs, Submodule.span_le]
      exact fun d hd => hK d hd
    exact this hc
  choose s hs using key
  have := Fintype.ofFinite {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l = 1}
  exact ⟨Finset.univ.biUnion s, fun K₁ _ _ _ _ hK x hx => hs ⟨x, hx⟩ K₁ fun c hc =>
    hK c (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, hc⟩)⟩

theorem potModel_semiAbelian : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ P : Out.PolAV (Sp K), PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V K _ _ _ _ _ _ _ _ hres P
  obtain ⟨l, hl, h3, hu⟩ := exists_prime_unit V
  let Ω := AlgebraicClosure K
  obtain ⟨s, hs⟩ := exists_finset K P Ω l hl
  have hV : CharZero V := (algebraMap V K).charZero
  have hinj : Function.Injective (algebraMap V Ω) := by
    rw [IsScalarTower.algebraMap_eq V K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective V K)
  have hf : FaithfulSMul V Ω := (faithfulSMul_iff_algebraMap_injective V Ω).2 hinj
  have ha : Algebra.IsAlgebraic V Ω :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := K) (C := Ω)).2 inferInstance
  obtain ⟨W, hW, hWc, -, hWf, -, hWl, hWs, -⟩ := exists_complete_dvr_finite_subalgebra V Ω s
  let K₁ := FractionRing W
  have hinj₁ : Function.Injective ((algebraMap W K₁).comp (algebraMap V W)) :=
    (IsFractionRing.injective W K₁).comp fun a b h => hinj (congrArg Subtype.val h)
  let _ : Algebra K K₁ := (IsFractionRing.lift hinj₁ : K →+* K₁).toAlgebra
  let _ : Algebra K₁ Ω := (IsFractionRing.lift (g := algebraMap W Ω) Subtype.val_injective : K₁ →+* Ω).toAlgebra
  have c₁ : ∀ a, algebraMap K K₁ (algebraMap V K a) = algebraMap W K₁ (algebraMap V W a) := fun a =>
    IsFractionRing.lift_algebraMap hinj₁ a
  have c₂ : ∀ a : W, algebraMap K₁ Ω (algebraMap W K₁ a) = a := fun a =>
    IsFractionRing.lift_algebraMap (g := algebraMap W Ω) Subtype.val_injective a
  have hT : IsScalarTower K K₁ Ω := IsScalarTower.of_algebraMap_eq' (by
    refine IsLocalization.ringHom_ext (nonZeroDivisors V) (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply]
    rw [c₁, c₂, ← IsScalarTower.algebraMap_apply]
    rfl)
  have hK₁ : CharZero K₁ := charZero_of_injective_algebraMap (algebraMap K K₁).injective
  have hal : Algebra.IsAlgebraic K₁ Ω := Algebra.IsAlgebraic.tower_top (K := K) K₁
  have hac : IsAlgClosure K₁ Ω := ⟨inferInstance, hal⟩
  have hres₁ : Finite (IsLocalRing.ResidueField W) :=
    Module.finite_of_finite (IsLocalRing.ResidueField V)
  obtain ⟨P₁, φ, hφ⟩ := exists_pullback (spMap (algebraMap K K₁)) P
  refine GlobalTheory.SS.potModel_trans V K W K₁ (RingHom.ext fun a => (c₁ a).symm) hWf hWl P.A P₁.A φ hφ _ ?_
  refine GlobalTheory.T.potentialSemistable_of_rational_lTorsion W K₁ hres₁ l hl h3 (by simpa using hu.map (algebraMap V W)) P₁ ?_
  refine fixed_of_rational (IsAlgClosure.equiv K₁ Ω (AlgebraicClosure K₁)) hφ l (hs K₁ fun c hc => ?_)
  obtain ⟨a, ha, b, hb, hb0, h⟩ := hWs c hc
  refine ⟨algebraMap W K₁ ⟨a, ha⟩ / algebraMap W K₁ ⟨b, hb⟩, ?_⟩
  rw [map_div₀, c₂, c₂]
  exact (div_eq_iff hb0).2 h.symm

end GlobalTheory.SemiPol
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PrincipallyPolarizedAbelianVarietyPotentialSemiAStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.principallyPolarizedAbelianVariety_potentialSemiAbelianModel : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ P : Out.PolAV (Sp K), PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  first | exact @GlobalTheory.SemiPol.potModel_semiAbelian | exact GlobalTheory.SemiPol.potModel_semiAbelian | (intros; apply GlobalTheory.SemiPol.potModel_semiAbelian <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelPadicPrincipallyPolarised

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem finiteDimensional_of_finite_of_isFractionRing (V K W L : Type) [CommRing V] [IsDomain V] [Field K]
    [Algebra V K] [IsFractionRing V K] [CommRing W] [IsDomain W] [Field L] [Algebra V W] [Algebra W L] [Algebra K L]
    [IsFractionRing W L] [Module.Finite V W]
    (e : (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K)) :
    FiniteDimensional K L := by
  letI : Algebra V L := ((algebraMap W L).comp (algebraMap V W)).toAlgebra
  haveI : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq' e
  haveI : FaithfulSMul V W := by
    rw [faithfulSMul_iff_algebraMap_injective]
    have h : Function.Injective ((algebraMap W L).comp (algebraMap V W)) := by
      rw [e]; exact (algebraMap K L).injective.comp (IsFractionRing.injective V K)
    exact Function.Injective.of_comp (f := algebraMap W L) h
  exact Module.Finite.of_isLocalization V W (nonZeroDivisors V)

theorem exists_ringHom_integralClosure (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (W L : Type) [CommRing W] [IsDomain W] [Field L]
    [Algebra (integralClosure ℤ_[p] K) W] [Algebra W L] [Algebra K L] [IsFractionRing W L]
    [Module.Finite (integralClosure ℤ_[p] K) W]
    (e : (algebraMap W L).comp (algebraMap (integralClosure ℤ_[p] K) W) =
      (algebraMap K L).comp (algebraMap (integralClosure ℤ_[p] K) K)) :
    ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K'), FiniteDimensional ℚ_[p] K' ∧
      ∃ (τ : L →+* K') (f : W →+* integralClosure ℤ_[p] K'),
        τ.comp (algebraMap K L) = (IntermediateField.inclusion h).toRingHom ∧
        τ.comp (algebraMap W L) = (algebraMap (integralClosure ℤ_[p] K') K').comp f := by
  haveI := finiteDimensional_of_finite_of_isFractionRing _ K W L e
  let σ : L →ₐ[K] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let K' : IntermediateField ℚ_[p] (PadicAlgCl p) := σ.fieldRange.restrictScalars ℚ_[p]
  have h : K ≤ K' := fun x hx => ⟨algebraMap K L ⟨x, hx⟩, σ.commutes _⟩
  let τ : L →+* K' := σ.toRingHom.codRestrict K' fun x => ⟨x, rfl⟩
  have hτ : τ.comp (algebraMap K L) = (IntermediateField.inclusion h).toRingHom :=
    RingHom.ext fun x => Subtype.ext (σ.commutes x)
  have hK' : FiniteDimensional ℚ_[p] K' := by
    letI : Algebra ℚ_[p] L := ((algebraMap K L).comp (algebraMap ℚ_[p] K)).toAlgebra
    haveI : IsScalarTower ℚ_[p] K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Module.Finite ℚ_[p] L := Module.Finite.trans K L
    let τ' : L →ₐ[ℚ_[p]] K' := { τ with commutes' := fun x => Subtype.ext (σ.commutes (algebraMap ℚ_[p] K x)) }
    refine Module.Finite.of_surjective τ'.toLinearMap ?_
    rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  have hint : ∀ w : W, IsIntegral ℤ_[p] (τ (algebraMap W L w)) := fun w => by
    have h₁ : (algebraMap (integralClosure ℤ_[p] K) W).IsIntegralElem w := Algebra.IsIntegral.isIntegral w
    letI alg : Algebra (integralClosure ℤ_[p] K) K' :=
      ((IntermediateField.inclusion h).toRingHom.comp (algebraMap (integralClosure ℤ_[p] K) K)).toAlgebra
    haveI tower : IsScalarTower ℤ_[p] (integralClosure ℤ_[p] K) K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have h₂ := h₁.map (τ.comp (algebraMap W L))
    rw [RingHom.comp_assoc, e, ← RingHom.comp_assoc, hτ] at h₂
    change IsIntegral (integralClosure ℤ_[p] K) (τ (algebraMap W L w)) at h₂
    exact @isIntegral_trans _ _ _ _ _ _ alg _ _ tower _ _ h₂
  exact ⟨K', h, hK', τ, (τ.comp (algebraMap W L)).codRestrict _ hint, hτ, RingHom.ext fun _ => rfl⟩

theorem exists_semiAbelian_model_padic_polAV : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (P : Out.PolAV (Sp K)), ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K'), FiniteDimensional ℚ_[p] K' ∧ ∃ (G : Over (Sp (integralClosure ℤ_[p] K'))) (_ : GrpObj G), IsSemiAbelian G ∧ ∃ φ : pullback G.hom (spMap (algebraMap (integralClosure ℤ_[p] K') K')) ⟶ P.A.left, IsGrpPullback ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K') K'))).obj G) P.A (spMap (IntermediateField.inclusion h).toRingHom) φ := by
  intro p _ K _ P
  haveI := GlobalTheory.DiscEval.isAdicComplete_integralClosure K
  obtain ⟨W, L, _, _, _, _, _, _, _, _, e, hfin, -, -, G, _, ⟨i, hi⟩, hG⟩ :=
    GlobalTheory.T.principallyPolarizedAbelianVariety_potentialSemiAbelianModel (integralClosure ℤ_[p] K) K (GlobalTheory.DiscEval.finite_residueField_integralClosure K) P
  obtain ⟨K', h, hK', τ, f, hτ, hf⟩ := exists_ringHom_integralClosure p K W L e
  refine ⟨K', h, hK', (Over.pullback (spMap f)).obj G, inferInstance, IsSemiAbelian.pullback _ G hG, ?_⟩
  exact GlobalTheory.SplitReduction.exists_isGrpPullback_of_square hf hτ G P.A
    (((isGrpPullback_of_iso i).comp (isGrpPullback_pullback P.A (spMap (algebraMap K L)))).congr
      (Category.id_comp _) rfl)

end GlobalTheory.SS
end
end
