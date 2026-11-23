module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixElementaryShearPropertiesStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearedGenericFlagEqGenericFlagAtSpecialStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgHomFunctionFieldOfSpecializesGenericPoi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagCommonClosedPointOfGeneric

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuativeCriterionVarieties

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPush

theorem exists_lift_of_var : ∀ (F : Type) [Field F] (X Y : Var F) (f : Y.X ⟶ X.X), f ≫ X.str = Y.str → ∀ (K : Type) [Field K] (V : ValuationSubring K) (v₁ : Sp V ⟶ Y.X) (q₂ : Sp K ⟶ Y.X), q₂ ≫ f = spMap (algebraMap V K) ≫ v₁ ≫ f → ∃ v₂ : Sp V ⟶ Y.X, spMap (algebraMap V K) ≫ v₂ = q₂ ∧ v₂ ≫ f = v₁ ≫ f := by
  intro F _ X Y f hs K _ V v₁ q₂ hq
  haveI : IsProper (f ≫ X.str) := hs ▸ inferInstance
  haveI : UniversallyClosed f := UniversallyClosed.of_comp_of_isSeparated f X.str
  have hE : ValuativeCriterion.Existence f :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) f).1
  obtain ⟨⟨l⟩⟩ := hE { R := V, K := K, i₁ := q₂, i₂ := v₁ ≫ f, commSq := ⟨hq⟩ }
  exact ⟨l.l, l.fac_left, l.fac_right⟩

end GlobalTheory.FlagPush
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuativeCriterionVarietiesStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.exists_lift_valuative_criterion_varieties : ∀ (F : Type) [Field F] (X Y : Var F) (f : Y.X ⟶ X.X), f ≫ X.str = Y.str → ∀ (K : Type) [Field K] (V : ValuationSubring K) (v₁ : Sp V ⟶ Y.X) (q₂ : Sp K ⟶ Y.X), q₂ ≫ f = spMap (algebraMap V K) ≫ v₁ ≫ f → ∃ v₂ : Sp V ⟶ Y.X, spMap (algebraMap V K) ≫ v₂ = q₂ ∧ v₂ ≫ f = v₁ ≫ f := by
  first | exact @GlobalTheory.FlagPush.exists_lift_of_var | exact GlobalTheory.FlagPush.exists_lift_of_var | (intros; apply GlobalTheory.FlagPush.exists_lift_of_var <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringRatFuncXResidueZero

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_valuationSubring_ratFunc_residue_X_eq_zero :
    ∀ (k : Type) [Field k], ∃ (V : ValuationSubring (RatFunc k)) (c : k →+* V) (t : V), (algebraMap V (RatFunc k)).comp c = algebraMap k (RatFunc k) ∧ (t : RatFunc k) = RatFunc.X ∧ IsLocalRing.residue V t = 0 := by
  intro k _
  let v := (Polynomial.idealX k).valuation (RatFunc k)
  have hc : ∀ a : k, algebraMap k (RatFunc k) a ∈ v.valuationSubring := by
    intro a
    rw [Valuation.mem_valuationSubring_iff,
      IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k)]
    exact (Polynomial.idealX k).valuation_le_one _
  have hX : v RatFunc.X < 1 := by
    rw [← RatFunc.algebraMap_X]
    exact ((Polynomial.idealX k).valuation_lt_one_iff_mem _).2 (by
      rw [Polynomial.idealX_span]; exact Ideal.mem_span_singleton_self _)
  have hX' : RatFunc.X ∈ v.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff]; exact hX.le
  refine ⟨v.valuationSubring, (algebraMap k (RatFunc k)).codRestrict v.valuationSubring hc,
    ⟨RatFunc.X, hX'⟩, ?_, rfl, ?_⟩
  · ext a; rfl
  · rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact ((Valuation.isEquiv_valuation_valuationSubring v).lt_one_iff_lt_one).1 hX

end GlobalTheory.FlagPush
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringRatFuncXResidueZeroStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.exists_valuationSubring_ratFunc_X_residue_zero : ∀ (k : Type) [Field k], ∃ (V : ValuationSubring (RatFunc k)) (c : k →+* V) (t : V), (algebraMap V (RatFunc k)).comp c = algebraMap k (RatFunc k) ∧ (t : RatFunc k) = RatFunc.X ∧ IsLocalRing.residue V t = 0 := by
  first | exact @GlobalTheory.FlagPush.exists_valuationSubring_ratFunc_residue_X_eq_zero | exact GlobalTheory.FlagPush.exists_valuationSubring_ratFunc_residue_X_eq_zero | (intros; apply GlobalTheory.FlagPush.exists_valuationSubring_ratFunc_residue_X_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOfDominantPointAsTriangularMatrix

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem val_spMap_pt {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {K : Type} [Field K]
    (σ : Ω →+* K) (x : Ω) : M.val (spMap σ ≫ M.pt) x = σ x := by
  have hx : x ∈ M.O (genericPoint M.Z) := by rw [RatModel.O_genericPoint]; exact Algebra.mem_top
  have := M.val_spMap_comp σ M.pt (M.pt_specializes _ _) ⟨x, hx⟩
  rw [RatModel.valLoc_eq_val, RatModel.val_pt] at this
  exact this

theorem flag_conv : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ A ∈ E.S (f (genericPoint Y.X)), ∀ (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K) (U : Mat m K), spMap ψ₁ ≫ (ratOf Y).pt ≫ f = spMap ψ₂ ≫ (ratOf Y).pt ≫ f → Bears E' φ A (U * (B * (A.map φ)⁻¹).map ψ₁) (spMap ψ₂ ≫ (ratOf Y).pt) → (∀ u : X.Fn, ψ₁ (φ u) = ψ₂ (φ u)) ∧ Par m ⊤ (U * (B.map ψ₁ * (B.map ψ₂)⁻¹)) := by
  intro F _ X Y ι _ m E E' φ f hR B hB A hA K _ ψ₁ ψ₂ U hpt hBe
  have hom : (ratOf Y).pt ≫ f = spMap φ.toRingHom ≫ (ratOf X).pt := hR.hom
  have key : ∀ σ : Y.Fn →+* K, spMap σ ≫ (ratOf Y).pt ≫ f = spMap (σ.comp φ.toRingHom) ≫ (ratOf X).pt := by
    intro σ
    rw [hom]
    show Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map (CommRingCat.ofHom (σ.comp φ.toRingHom)) ≫ _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact (Category.assoc _ _ _).symm
  have h1 : ∀ u : X.Fn, ψ₁ (φ u) = ψ₂ (φ u) := by
    intro u
    have e1 := val_spMap_pt (ratOf X) (ψ₁.comp φ.toRingHom) u
    have e2 := val_spMap_pt (ratOf X) (ψ₂.comp φ.toRingHom) u
    rw [← key, hpt, key] at e1
    exact e1.symm.trans e2
  refine ⟨h1, ?_⟩
  obtain ⟨A', hA', hP⟩ := hBe
  have hgen : (spMap ψ₂ ≫ (ratOf Y).pt) (IsLocalRing.closedPoint K) = genericPoint Y.X :=
    (ratOf Y).pt_apply _
  rw [hgen] at hA'
  have hval : (ratOf Y).val (spMap ψ₂ ≫ (ratOf Y).pt) = ψ₂ := funext (val_spMap_pt (ratOf Y) ψ₂)
  rw [hval] at hP
  have hAd : ∀ τ, (A τ).det ≠ 0 := Fr.det_ne hA
  have hBd : ∀ τ, (B τ).det ≠ 0 := Fr.det_ne hB
  have hA'd : ∀ τ, (A' τ).det ≠ 0 := Fr.det_ne hA'
  set C : Mat m Y.Fn := A.map φ with hC
  have hCd : ∀ τ, (C τ).det ≠ 0 := fun τ => by
    rw [hC]; exact fun h0 => (map_ne_zero φ.toRingHom).2 (hAd τ) ((Mat.det_map A φ.toRingHom τ).symm.trans h0)
  have hCψ : C.map ψ₁ = C.map ψ₂ := by
    funext τ; ext i j; exact h1 (A τ i j)
  have hC2d : ∀ τ, (C.map ψ₂ τ).det ≠ 0 := fun τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hCd τ)
  have hA'2d : ∀ τ, (A'.map ψ₂ τ).det ≠ 0 := fun τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hA'd τ)
  have e : U * (B * C⁻¹).map ψ₁ * ((A' * C⁻¹).map ψ₂)⁻¹ = U * B.map ψ₁ * (A'.map ψ₂)⁻¹ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, hCψ, Mat.mul_inv_rev, Mat.inv_inv hC2d]
    rw [mul_assoc U, mul_assoc (B.map ψ₁), ← mul_assoc (C.map ψ₂)⁻¹, Mat.inv_mul hC2d, one_mul, ← mul_assoc]
  rw [e] at hP
  have hQ : Par m (⊤ : Subring K) ((A' * B⁻¹).map ψ₂) := by
    have := (Fr.mem_iff hB).1 hA'
    exact this.map ψ₂ (fun _ _ => trivial)
  have := hP.mul hQ
  rw [Mat.map_mul, Mat.map_inv] at this
  have e2 : U * B.map ψ₁ * (A'.map ψ₂)⁻¹ * (A'.map ψ₂ * (B.map ψ₂)⁻¹) = U * (B.map ψ₁ * (B.map ψ₂)⁻¹) := by
    rw [mul_assoc (U * B.map ψ₁), ← mul_assoc (A'.map ψ₂)⁻¹, Mat.inv_mul hA'2d, one_mul, mul_assoc]
  rwa [e2] at this

end GlobalTheory.FlagPush
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOfDominantPointAsTriangularMatrixStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.flag_of_dominant_point_as_triangular_matrix : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ A ∈ E.S (f (genericPoint Y.X)), ∀ (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K) (U : Mat m K), spMap ψ₁ ≫ (ratOf Y).pt ≫ f = spMap ψ₂ ≫ (ratOf Y).pt ≫ f → Bears E' φ A (U * (B * (A.map φ)⁻¹).map ψ₁) (spMap ψ₂ ≫ (ratOf Y).pt) → (∀ u : X.Fn, ψ₁ (φ u) = ψ₂ (φ u)) ∧ Par m ⊤ (U * (B.map ψ₁ * (B.map ψ₂)⁻¹)) := by
  first | exact @GlobalTheory.FlagPush.flag_conv | exact GlobalTheory.FlagPush.flag_conv | (intros; apply GlobalTheory.FlagPush.flag_conv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPairFlagsDifferingOneStep

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.Gen

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B) (h : B →+* C) :
    spMap h ≫ spMap g = spMap (h.comp g) := by
  rw [← Spec.map_comp]
  rfl

theorem exists_genPair : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ (τ : ι) (a b : Fin (m τ)), a < b → ∃ ψ₂ : Y.Fn →+* RatFunc Y.Fn, GenPair Y (algebraMap Y.Fn (RatFunc Y.Fn)) ψ₂ ∧ (∀ u : X.Fn, algebraMap Y.Fn (RatFunc Y.Fn) (φ u) = ψ₂ (φ u)) ∧ Par m ⊤ (shear τ a b (RatFunc.X : RatFunc Y.Fn) * (B.map (algebraMap Y.Fn (RatFunc Y.Fn)) * (B.map ψ₂)⁻¹)) := by
  intro F _ X Y ι _ m E E' φ f hf B hB τ a b hab
  obtain ⟨V, c, t, hc, ht, hr⟩ := GlobalTheory.T.exists_valuationSubring_ratFunc_X_residue_zero Y.Fn
  obtain ⟨A, hA⟩ := E.nonempty (f (genericPoint Y.X))
  have hM : Par 0 ((ratOf Y).O (genericPoint Y.X)).toSubring (B * (A.map φ)⁻¹) := hf.sub _ B hB A hA
  obtain ⟨pt, hpt⟩ : ∃ pt : Sp Y.Fn ⟶ Y.X, pt = (ratOf Y).pt := ⟨_, rfl⟩
  have hpa (w) : pt w = genericPoint Y.X := hpt ▸ (ratOf Y).pt_apply w
  have hps : pt ≫ Y.str = spMap (algebraMap F Y.Fn) := hpt ▸ (ratOf Y).pt_s
  have hq : spMap (algebraMap V (RatFunc Y.Fn)) ≫ spMap c ≫ pt = spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt := by
    rw [← Category.assoc, spMap_comp, hc]
  have hh : Par 0 ⊤ (shear τ a b (RatFunc.X : RatFunc Y.Fn) *
      (B * (A.map φ)⁻¹).map (algebraMap Y.Fn (RatFunc Y.Fn))) := by
    refine Par.mul (ClosedPt.par_zero_top fun σ => ?_) (hM.map _ fun _ _ => trivial)
    rw [(GlobalTheory.T.blockMatrixElementaryShear_properties ι m τ a b hab _ _).1 σ]
    exact one_ne_zero
  have hx : ((spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt) ≫ f)
      (IsLocalRing.closedPoint (RatFunc Y.Fn)) = f (genericPoint Y.X) :=
    congrArg f (hpa _)
  have hA' : A ∈ E.S (((spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt) ≫ f)
      (IsLocalRing.closedPoint (RatFunc Y.Fn))) := (congrArg (fun z : X.X => A ∈ E.S z) hx).mpr hA
  obtain ⟨q₂, hq₂, hb⟩ : ∃ q₂ : Sp (RatFunc Y.Fn) ⟶ Y.X,
      q₂ ≫ f = (spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt) ≫ f ∧ Bears E' φ A (shear τ a b (RatFunc.X : RatFunc Y.Fn) *
      (B * (A.map φ)⁻¹).map (algebraMap Y.Fn (RatFunc Y.Fn))) q₂ := (hf.lifts (RatFunc Y.Fn) _ A hA' _ hh).exists
  have hs : f ≫ X.str = Y.str := hf.hom.inducedModelMorphism_comp_structureMap
  obtain ⟨v₂, hv₂, hv₂f⟩ := GlobalTheory.T.exists_lift_valuative_criterion_varieties F X Y f hs _ V (spMap c ≫ pt) q₂ (by
    rw [hq₂, ← hq]; simp only [Category.assoc])
  have hmeet : spMap (IsLocalRing.residue V) ≫ spMap c ≫ pt = spMap (IsLocalRing.residue V) ≫ v₂ := by
    subst hpt
    exact GlobalTheory.T.shearedGenericFlag_eq_genericFlag_at_special F X Y ι m E E' φ f hf B hB A hA τ a b hab _ V c t hr v₂
      (hv₂f.trans (Category.assoc _ _ _)) (by subst hv₂; rw [hc, ht]; exact hb)
  have h1 : (spMap c ≫ pt) (IsLocalRing.closedPoint V) = genericPoint Y.X := hpa _
  have h2 : v₂ (IsLocalRing.closedPoint V) = genericPoint Y.X := by
    rw [← ClosedPt.closedPt_comp v₂, ← hmeet, ClosedPt.closedPt_comp, h1]
  letI : Algebra F (RatFunc Y.Fn) := ((algebraMap Y.Fn (RatFunc Y.Fn)).comp (algebraMap F Y.Fn)).toAlgebra
  have hsp : q₂ (IsLocalRing.closedPoint (RatFunc Y.Fn)) ⤳ genericPoint Y.X := by
    have := ClosedPt.gen_specializes v₂ (IsLocalRing.closedPoint (RatFunc Y.Fn))
    rwa [hv₂, h2] at this
  have hstr : q₂ ≫ Y.str = spMap ((algebraMap Y.Fn (RatFunc Y.Fn)).comp (algebraMap F Y.Fn)) := by
    rw [← hs, ← Category.assoc, hq₂, Category.assoc, hs, Category.assoc, ← spMap_comp, hps]
  obtain ⟨ψ, hψ⟩ := exists_algHom_of_specializes_genericPoint F Y (RatFunc Y.Fn) q₂ hsp hstr
  subst hpt
  have hcv := GlobalTheory.T.flag_of_dominant_point_as_triangular_matrix F X Y ι m E E' φ f hf B hB A hA _ (algebraMap Y.Fn (RatFunc Y.Fn)) ψ.toRingHom
    (shear τ a b RatFunc.X) (by
      subst hψ
      exact (Category.assoc _ _ _).symm.trans (hq₂.symm.trans (Category.assoc _ _ _))) (by subst hψ; exact hb)
  refine ⟨ψ.toRingHom, ⟨?_, V, spMap c ≫ (ratOf Y).pt, v₂, hq, hv₂.trans hψ, hmeet, h1⟩, hcv.1, hcv.2⟩
  exact RingHom.ext fun r => (ψ.commutes r).symm

end GlobalTheory.FlagPush.Gen
end
end
end
