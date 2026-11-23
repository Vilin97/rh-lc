module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulSecK
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultiplicationPullbackIntegralFamilyOddStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOddMultiplicationPullbackAtTraitStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomFromSpecResidueField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatOfIsFiniteOfFinitePresentationOfFlatGeometri
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftFrobenius

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultiplicationPullbackGenericSectionCover

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.MulPull in
theorem mulPull_gen_labCover {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    (C : LabCover D) (m : ℕ) :
    ∃ u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]),
      u.IsGen := by
  have hL : C.P.L.L.IsLB := C.P.L.isLB
  have hcube : HasGen C.P.L.L (thφ C.G (x3 C.G)) thε := ⟨C.P.c.t, C.P.c.isGen⟩
  have hrig : HasGen C.P.L.L (K := PUnit) (fun _ => eSec C.G) (fun _ => 1) := ⟨C.P.L.rig, C.P.L.rigGen⟩
  have hone : HasGen C.P.L.L (K := Fin 1) ![(1 : C.G ⟶ C.G).left] ![1] := by
    refine (hrig.pull (toUnit C.G).left).of_formEq hL (fun U _ h => ?_)
    simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Matrix.cons_val_zero, _root_.mul_one]
    rfl
  have hsym0 : HasGen C.P.L.L (K := Fin 2) ![(ι[C.G]).left, 𝟙 C.G.left] ![1, -1] := ⟨C.P.sym, C.P.sym_gen⟩
  have e1 : ((𝟙 C.G)⁻¹ : C.G ⟶ C.G).left = (ι[C.G]).left := by
    show ((𝟙 C.G) ≫ ι[C.G]).left = _
    rw [Category.id_comp]
  have e2 : (𝟙 C.G : C.G ⟶ C.G).left = 𝟙 C.G.left := rfl
  have hsym : HasGen C.P.L.L (K := Fin 2) ![(𝟙 C.G : C.G ⟶ C.G).left, ((𝟙 C.G)⁻¹ : C.G ⟶ C.G).left] ![1, -1] := by
    refine hsym0.inv.of_formEq hL (fun U _ h => ?_)
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, e1, e2]
    simp only [neg_neg, zpow_one, _root_.mul_one]
    exact mul_comm _ _
  have H := hasGen_pow hL hcube (𝟙 C.G) hone hsym m
  have e3 : ((𝟙 C.G) ^ m : C.G ⟶ C.G).left = (mulA C.G m).left := by
    rw [← GlobalTheory.ZH.TorsFrame.comp_mulA]
  refine H.of_formEq hL (fun U _ h => ?_)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, e2, e3]
  push_cast
  rfl


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem exists_mulSecK (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (_hR : Base R) (D : DegData R (maximalIdeal R))
    (C : LabCover D) (m : ℕ) (_hm : Odd m) (θ₀ : SecK C.P.L.L C.α 1) :
    ∃ S : SecK C.P.L.L C.α (m ^ 2), MulSecK C m θ₀ S := by
  obtain ⟨u, hu⟩ := mulPull_gen_labCover C m
  have hL : C.P.L.L.IsLB := C.P.L.isLB
  have hc : (mulA C.A.A m).left ≫ C.α = C.α ≫ (mulA C.G m).left := GlobalTheory.ZH.TorsFrame.mulA_comm C.α_cart m
  let S₀ := pullMulSec θ₀ (mulA C.A.A m).left (LB.pullGen C.P.L.L _ _ u C.α) (DVR.pullGen_isGen C.P.L.L _ _ u hu C.α)
  have hf : FormEq (Sum.elim (fun _ : Fin 1 => (mulA C.A.A m).left ≫ C.α)
      (fun k : Fin 2 => C.α ≫ (![𝟙 C.G.left, (mulA C.G m).left] : Fin 2 → _) k))
      (Sum.elim (fun _ : Fin 1 => ((1 : ℕ) : ℤ)) (![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)] : Fin 2 → ℤ))
      (fun _ : Fin 1 => C.α) (fun _ => ((m ^ 2 : ℕ) : ℤ)) := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Category.comp_id, hc]
    simp only [Nat.cast_one, zpow_one, zpow_neg, _root_.mul_one]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨S, hS⟩ := exists_sec hL hf S₀
  refine ⟨S, u, hu, fun Z p z J hJ => ?_⟩
  rw [hS Z p z J hJ, sval_pullMulSec θ₀ _ _ _ p z hJ, val_pull hJ, mul_comm]

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultiplicationPullbackGenericSectionCoverStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_multiplicationPullback_genericSection_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ θ₀ : SecK C.P.L.L C.α 1, ∃ S : SecK C.P.L.L C.α (m ^ 2), MulSecK C m θ₀ S := by
  first | exact @GlobalTheory.Mum.exists_mulSecK | exact GlobalTheory.Mum.exists_mulSecK | (intros; apply GlobalTheory.Mum.exists_mulSecK <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationPullbackFamilyNeZeroOdd

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mulFam_exists_ne_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)), MulFam m F₁ G → (∃ α j, (F₁.f α).f j ≠ 0) → ∃ α j, (G.f α).f j ≠ 0 := by
  intro R _ _ _ _ D m hm F₁ G hG ⟨α, j, hj⟩
  by_contra hcon
  push_neg at hcon
  apply hj
  have hfinite : IsFinite (mulA D.toPre.P.A m).left := GlobalTheory.MulFinite.isFinite_mulA
    (GlobalTheory.MulPull.mulPull_of_cube_of_symm GlobalTheory.AbLaw.CubeAssembly.cube_gen
      (GlobalTheory.exists_gen_negLB GlobalTheory.laws_without_cohomology.1)).1 GlobalTheory.laws_without_cohomology.2.2.1
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ D.toPre.P m hm.pos
  have hc := D.toPre.P.isAb.comm
  have hsm := D.toPre.P.isAb.smooth
  have hmhom := GlobalTheory.AbLaw.MulN.isMonHom_mulA D.toPre.P.A m
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ _),
      Flat ((Over.pullback t).map (mulA D.toPre.P.A m)).left ∧
        Surjective ((Over.pullback t).map (mulA D.toPre.P.A m)).left := fun K _ _ t =>
    GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
      (TLinPf.isAb_pullback t D.toPre.P.A D.toPre.P.isAb) _ inferInstance
      (MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) hfinite)
  have h₂ : Flat (mulA D.toPre.P.A m).left :=
    GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres _ _ _ _ inferInstance inferInstance
      inferInstance hfinite fun K _ _ t => (hgeo K t).1
  have h₃ : Surjective (mulA D.toPre.P.A m).left :=
    GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => (hgeo K t).2
  obtain ⟨u, -, -, e⟩ := hG.1 α
  refine GlobalTheory.PullLin.sec_eq_zero_of_flat D.toPre.P.isLB (F₁.f α) (mulA D.toPre.P.A m).left (fun x J hJ => ?_) j
  have e₁ := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ (𝟙 _) x J hJ
  rw [ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftFrobenius.sval_zero _ (hcon _), Category.id_comp] at e₁
  exact (Units.mul_left_eq_zero _).1 e₁.symm

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationPullbackFamilyNeZeroOddStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.multiplicationPullback_family_ne_zero_odd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)), MulFam m F₁ G → (∃ α j, (F₁.f α).f j ≠ 0) → ∃ α j, (G.f α).f j ≠ 0 := by
  first | exact @GlobalTheory.Mum.mulFam_exists_ne_zero | exact GlobalTheory.Mum.mulFam_exists_ne_zero | (intros; apply GlobalTheory.Mum.mulFam_exists_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOddMultiplicationPullbackThetaFamilyDegree

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_mulPull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (θ₀ : SecK C.P.L.L C.α 1), ∃ (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)) (S : SecK C.P.L.L C.α (m ^ 2)), ((∃ α j, (F₁.f α).f j ≠ 0) → ∃ α j, (G.f α).f j ≠ 0) ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), a ≠ 0 → T.Exp a b θ₀ F₁ → ∃ v : Wˣ, T.Exp a (b * v) S G := by
  intro R _ _ _ hR D C m hm F₁ θ₀
  obtain ⟨G, hG⟩ := GlobalTheory.T.exists_multiplicationPullback_integralFamily_odd R hR D m hm F₁
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_multiplicationPullback_genericSection_cover R hR D C m hm θ₀
  exact ⟨G, S, GlobalTheory.T.multiplicationPullback_family_ne_zero_odd R hR D m hm F₁ G hG,
    fun W _ _ _ T a b ha h => GlobalTheory.T.expansion_oddMultiplicationPullback_at_trait R hR D C m hm F₁ G θ₀ S hG hS W T a b ha h⟩

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOddMultiplicationPullbackThetaFamilyDegreeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_oddMultiplication_pullback_thetaFamily_degree_sq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (θ₀ : SecK C.P.L.L C.α 1), ∃ (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)) (S : SecK C.P.L.L C.α (m ^ 2)), ((∃ α j, (F₁.f α).f j ≠ 0) → ∃ α j, (G.f α).f j ≠ 0) ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), a ≠ 0 → T.Exp a b θ₀ F₁ → ∃ v : Wˣ, T.Exp a (b * v) S G := by
  first | exact @GlobalTheory.Mum.exists_mulPull | exact GlobalTheory.Mum.exists_mulPull | (intros; apply GlobalTheory.Mum.exists_mulPull <;> assumption)
end
end
