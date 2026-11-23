module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorFieldPointThroughGenericPoint
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfLabelledCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralImageOfField
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisEquivariantTorsionValuesUltrametric
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPointOfAlgebraicSeriesOneTraitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsFinExt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GaloisHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullFib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorFieldPointThroughGenericPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_factor_field_point_through_generic_point : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (L : Type) [Field L] (ρ : R →+* L) (y : Sp L ⟶ M.S), Function.Injective ρ → y ≫ M.π = spMap ρ → ∃ ga : FractionRing R →+* L, (∀ r, ga (algebraMap R _ r) = ρ r) ∧ y = spMap ga ≫ M.gp := by
  first | exact @GlobalTheory.Mum.Modif.factor_gp | exact GlobalTheory.Mum.Modif.factor_gp | (intros; apply GlobalTheory.Mum.Modif.factor_gp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisEquivariantTorsionValuesUltrametricStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.galois_equivariant_torsion_values_ultrametric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → GalEqN n lab → (∀ (j : ℕ) (v : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → Kb R), (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → QkPt D.toPre C ((n ^ j) ^ 2)) (q : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → N.QT ((n ^ j) ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx (n ^ j) (q i)) → IsThetaPt A (n ^ j) (lab ((n ^ j) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p))) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∃ hD : IsPullDeg φ D.toPre D'.toPre, ∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (_ : Algebra (FractionRing R) C) (em : Kb R →ₐ[FractionRing R] C), (∀ r, algebraMap (FractionRing R) C (algebraMap R _ r) = algebraMap (FractionRing W) C (algebraMap W _ (φ r))) ∧ ∀ j : ℕ, ∀ (p : QkPt D.toPre (Kb R) (n ^ j)) (p₁ : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)) (x' : TFK (R := W) C ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD C p₁.g p'.g → x'.left ≫ a = spMap em.toRingHom ≫ (lab (n ^ j) p).left → QkToAkU U'.toUnifPre C (n ^ j) p' x' := by
  first | exact @GlobalTheory.Mum.Recog.recognition_core | exact GlobalTheory.Mum.Recog.recognition_core | (intros; apply GlobalTheory.Mum.Recog.recognition_core <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsInducedAllEmbeddingsOfGalois

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.AllEmb

open GlobalTheory.LabTrans GlobalTheory.ArcPull GlobalTheory.TorusExt GlobalTheory.ArcExt ReciprocityTheory.ChartRestriction.G.DVR

theorem lab_indep_level {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} (hB : D.TauBimult) {A : PolAV (Sp (FractionRing R))} {lab : Labels D A}
    (hlab : ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D (Kb R) k), QkExt σ.toRingHom p p' →
      (lab k p').left = spMap σ.toRingHom ≫ (lab k p).left)
    (τ₁ τ₂ : Kb R →ₐ[FractionRing R] F) {p q : QkPt D (Kb R) k} {r : QkPt D F k}
    (h₁ : QkExt τ₁.toRingHom p r) (h₂ : QkExt τ₂.toRingHom q r) :
    spMap τ₁.toRingHom ≫ (lab k p).left = spMap τ₂.toRingHom ≫ (lab k q).left := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Kb R →ₐ[FractionRing R] Kb R, τ₂.toRingHom.comp σ.toRingHom = τ₁.toRingHom := by
    letI : Algebra (Kb R) F := τ₂.toRingHom.toAlgebra
    haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun x => (τ₂.commutes x).symm
    exact ⟨τ₁.restrictNormal (Kb R), RingHom.ext fun x => τ₁.restrictNormal_commutes (Kb R) x⟩
  obtain ⟨q', hq'⟩ := exists_ext hB σ p
  obtain ⟨r', hr'⟩ := exists_ext hB τ₂ q'
  have h₃ := qkExt_trans hq' hr'
  rw [hσ] at h₃
  obtain rfl := ext_unique hB τ₁ h₁ h₃
  obtain rfl := qkExt_inj hB τ₂ h₂ hr'
  rw [hlab σ p q hq', ← Category.assoc, ← Geo.Tor.spMap_comp, hσ]

theorem induces_of_one_embedding : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → GalEqN n lab → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∀ (hD : IsPullDeg φ D.toPre D'.toPre) (j : ℕ), (∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (_ : Algebra (FractionRing R) C) (em : Kb R →ₐ[FractionRing R] C), (∀ r, algebraMap (FractionRing R) C (algebraMap R _ r) = algebraMap (FractionRing W) C (algebraMap W _ (φ r))) ∧  ∀ (p : QkPt D.toPre (Kb R) (n ^ j)) (p₁ : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)) (x' : TFK (R := W) C ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD C p₁.g p'.g → x'.left ≫ a = spMap em.toRingHom ≫ (lab (n ^ j) p).left → QkToAkU U'.toUnifPre C (n ^ j) p' x') → Induces lab φ U' hD a (n ^ j) := by
  intro R _ _ _ hR D A lab n hn _ _ hlab W _ _ _ hW φ iφ _ G' _ _ D' A' U' a hG ⟨ga, hga, gpa, _⟩ hD j
    ⟨C, _, _, _, _, emC, cC, HC⟩ F _ _ _ _ em cF p p₁ p' x' y₁ y₂ y₃ y₄
  have hGF := GlobalTheory.firstFiveLaws.1.globalFns
  have := hR.2
  have := hW.1
  have := hW.2.2
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  letI : Algebra (FractionRing R) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp ga).toAlgebra
  have cK : Compat φ (Kb W) := fun r => congrArg (algebraMap (FractionRing W) (Kb W)) (hga r)
  obtain ⟨e⟩ := nonempty_lift (FractionRing R) (Kb W)

  have fac : ∀ (L : Type) [Field L] [Algebra (FractionRing W) L] [Algebra (FractionRing R) L], Compat φ L →
      algebraMap (FractionRing R) L = (algebraMap (FractionRing W) L).comp ga := fun L _ _ _ c =>
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (c r).trans
      (congrArg (algebraMap (FractionRing W) L) (hga r).symm))
  have up : ∀ (L : Type) [Field L] [Algebra (FractionRing W) L] [Algebra (FractionRing R) L], Compat φ L →
      ∀ i : Kb W →ₐ[FractionRing W] L, ∃ i' : Kb W →ₐ[FractionRing R] L, i'.toRingHom = i.toRingHom := fun L _ _ _ c i =>
    ⟨⟨i.toRingHom, fun t => by rw [fac L c]; exact i.commutes (ga t)⟩, rfl⟩

  have key : ∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra (FractionRing W) L] [Algebra (FractionRing R) L],
      Compat φ L → ∀ (i : Kb W →ₐ[FractionRing W] L) (m : Kb R →ₐ[FractionRing R] L)
      (q : QkPt D.toPre (Kb R) (n ^ j)) (q₁ : QkPt D.toPre (Kb W) (n ^ j)) (x₀ : TFK (R := W) (Kb W) ⟶ A'.A),
      QkExt e.toRingHom q q₁ → x₀.left ≫ a = spMap e.toRingHom ≫ (lab (n ^ j) q).left →
      ∀ (s : QkPt D.toPre (Kb R) (n ^ j)) (s₁ : QkPt D.toPre L (n ^ j)) (s' : QkPt D'.toPre L (n ^ j))
        (z : TFK (R := W) L ⟶ A'.A), QkExt i.toRingHom q₁ s₁ → QkExt m.toRingHom s s₁ → s'.y = hD.xe.symm s₁.y →
        IsPullGtF φ hD L s₁.g s'.g → z.left ≫ a = spMap m.toRingHom ≫ (lab (n ^ j) s).left →
        (QkToAkU U'.toUnifPre (Kb W) (n ^ j) (pullQk hD hGF cK hB hB' q₁) x₀ ↔ QkToAkU U'.toUnifPre L (n ^ j) s' z) := by
    intro L _ _ _ _ c i m q q₁ x₀ hq hx₀ s s₁ s' z w₀ w₁ w₂ w₃ w₄
    obtain ⟨i', hi'⟩ := up L c i
    obtain ⟨⟨t, ht⟩, -, hgal⟩ := GlobalTheory.UT.Cl.galois_holds W _ bW D' A' G' hG U' _ L i (n ^ j) hk
      (pullQk hD hGF cK hB hB' q₁)
    have t₁ : IsPullGtF φ hD L s₁.g t.g :=
      isPullGtF_ext hD c i.toRingHom i.comp_algebraMap (isPullGtF_pullGt hD hGF cK _) w₀ ht
    have t₂ : t.y = hD.xe.symm s₁.y := by rw [ht.1, w₀.1]; rfl
    obtain rfl : s' = t := ((eq_pullQk_iff hD hGF c hB hB' _ _).2 ⟨w₂, w₃⟩).trans
      ((eq_pullQk_iff hD hGF c hB hB' _ _).2 ⟨t₂, t₁⟩).symm
    have u : QkExt (i'.comp e).toRingHom q s₁ := by
      have := qkExt_trans hq w₀
      rw [← hi'] at this
      exact this
    have l := lab_indep_level hB (fun σ => hlab σ j) m (i'.comp e) w₁ u
    refine hgal s' x₀ z ht ?_
    apply gpa.1.hom_ext
    · rw [w₄, Category.assoc, hx₀, ← Category.assoc, ← Geo.Tor.spMap_comp, l, ← hi']
      rfl
    · rw [Category.assoc, Over.w z, Over.w x₀]
      exact ((Geo.Tor.spMap_comp _ _).symm.trans (congrArg spMap i.comp_algebraMap)).symm
  obtain ⟨i⟩ := nonempty_lift (FractionRing W) F
  obtain ⟨i₀⟩ := nonempty_lift (FractionRing W) C
  obtain ⟨i', hi'⟩ := up F cF i
  obtain ⟨i₀', hi₀'⟩ := up C cC i₀
  obtain ⟨q₁, hq₁⟩ := exists_of_ext hB i' hk p₁
  obtain ⟨q, hq⟩ := exists_of_ext hB e hk q₁
  obtain ⟨x₀, hx₀⟩ := exists_lift_pt gpa.1 e.toRingHom e.comp_algebraMap (lab (n ^ j) q)
  obtain ⟨r₁, hr₁⟩ := exists_ext hB i₀' q₁
  obtain ⟨r, hr⟩ := exists_of_ext hB emC hk r₁
  obtain ⟨z, hz⟩ := exists_lift_pt gpa.1 emC.toRingHom (emC.comp_algebraMap.trans (fac C cC)) (lab (n ^ j) r)
  have hC := HC r r₁ (pullQk hD hGF cC hB hB' r₁) z hr rfl (isPullGtF_pullGt hD hGF cC _) hz
  exact (key F cF i em q q₁ x₀ hq hx₀ p p₁ p' x' (hi' ▸ hq₁) y₁ y₂ y₃ y₄).1
    ((key C cC i₀ emC q q₁ x₀ hq hx₀ r r₁ _ z (hi₀' ▸ hr₁) hr rfl (isPullGtF_pullGt hD hGF cC _) hz).2 hC)

end GlobalTheory.Mum.AllEmb
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsInducedAllEmbeddingsOfGaloisStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.labels_induced_all_embeddings_of_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → GalEqN n lab → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∀ (hD : IsPullDeg φ D.toPre D'.toPre) (j : ℕ), (∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (_ : Algebra (FractionRing R) C) (em : Kb R →ₐ[FractionRing R] C), (∀ r, algebraMap (FractionRing R) C (algebraMap R _ r) = algebraMap (FractionRing W) C (algebraMap W _ (φ r))) ∧  ∀ (p : QkPt D.toPre (Kb R) (n ^ j)) (p₁ : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)) (x' : TFK (R := W) C ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD C p₁.g p'.g → x'.left ≫ a = spMap em.toRingHom ≫ (lab (n ^ j) p).left → QkToAkU U'.toUnifPre C (n ^ j) p' x') → Induces lab φ U' hD a (n ^ j) := by
  first | exact @GlobalTheory.Mum.AllEmb.induces_of_one_embedding | exact GlobalTheory.Mum.AllEmb.induces_of_one_embedding | (intros; apply GlobalTheory.Mum.AllEmb.induces_of_one_embedding <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RecognitionDegDataLabelsAtEveryTrait

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Recognition

theorem pullDeg_induces : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → GalEqN n lab → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∃ hD : IsPullDeg φ D.toPre D'.toPre, ∀ j : ℕ, Induces lab φ U' hD a (n ^ j) := by
  intro R _ _ _ hR D A lab n hn ho hu hOT hGal W _ _ _ hW φ hφ hloc G' _ _ D' A' U' a hG hF
  obtain ⟨hD, C, i1, i2, i3, i4, em, hc, hP⟩ := GlobalTheory.T.galois_equivariant_torsion_values_ultrametric R hR D A lab n hn ho hu hOT hGal
    (GlobalTheory.T.isThetaPoint_of_algebraic_series_one_trait R hR D A lab n hn ho hu hOT) W hW φ hφ hloc G' D' A' U' a hG hF
  exact ⟨hD, fun j => GlobalTheory.T.labels_induced_all_embeddings_of_galois R hR D A lab n hn ho hu hGal W hW φ hφ hloc G' D' A' U' a hG hF hD j
    ⟨C, i1, i2, i3, i4, em, hc, hP j⟩⟩

end GlobalTheory.Mum.Recognition
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RecognitionDegDataLabelsAtEveryTraitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.recognition_degData_labels_at_every_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → GalEqN n lab → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∃ hD : IsPullDeg φ D.toPre D'.toPre, ∀ j : ℕ, Induces lab φ U' hD a (n ^ j) := by
  first | exact @GlobalTheory.Mum.Recognition.pullDeg_induces | exact GlobalTheory.Mum.Recognition.pullDeg_induces | (intros; apply GlobalTheory.Mum.Recognition.pullDeg_induces <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLabelledCoverOfOddPrime

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.UCoverLab

theorem jK_mono (R : Type) [CommRing R] [IsDomain R] : Mono (jK R) := by
  haveI : Scheme.Spec.IsRightAdjoint := ΓSpec.adjunction.isRightAdjoint
  have : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))).op) := inferInstance
  exact this

theorem gp_mono {R : Type} [CommRing R] [IsDomain R] (M : Modif R) : Mono M.gp := by
  have : Mono (M.gp ≫ M.π) := by rw [M.gp_π]; exact jK_mono R
  exact mono_of_mono M.gp M.π

theorem mono_α {R : Type} [CommRing R] [IsDomain R] {M : Modif R} {X : Over M.S} [GrpObj X]
    {A : Over (Sp (FractionRing R))} [GrpObj A] {α : A.left ⟶ X.left} (h : IsGrpPullback A X M.gp α) : Mono α := by
  haveI := gp_mono M
  refine ⟨fun u v huv => h.1.hom_ext huv ?_⟩
  apply (cancel_mono M.gp).1
  rw [Category.assoc, Category.assoc, ← h.1.w, ← Category.assoc, huv, Category.assoc]

end GlobalTheory.Mum.UCoverLab


open GlobalTheory.Mum.UCoverLab GlobalTheory.Mum.CoverFin in
theorem GlobalTheory.Mum.UCover.labCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : UCover R) (lab : Labels D.toPre C.A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre C.A lab → GalEqN n lab → Nonempty (LabCover D) := by
  intro R _ _ _ hB D C lab n hn ho hu hone hgal
  refine ⟨{ toModif := C.toModif
            G := C.G
            semi := C.semi
            P := C.P
            A := C.A
            α := C.α
            α_cart := C.α_cart
            α_lb := C.α_lb
            n := n
            n_prime := hn
            n_odd := ho
            n_unit := hu
            lab := fun j => lab (n ^ j)
            trait := ?_ }⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, G', _, _, β, D', A', U', hW', hio, hfin, hcart, hlb⟩ := C.trait W hW φ ξ hφ hξ
  haveI : IsLocalHom io := hfin.to_isIntegral.isLocalHom hio
  have hsemi : IsSemiAbelian G' := semiAbelian_of_pull hcart C.semi
  have hγ : IsGrpPullback A'.A G' (jK W') (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) :=
    GlobalTheory.ThetaBaseChange.grp_generic U'.toUnifPre
  have hinj : Function.Injective ((algebraMap W' (FractionRing W')).comp (io.comp φ)) :=
    (IsFractionRing.injective W' _).comp (hio.comp hφ)
  obtain ⟨ga, hga, hy⟩ := GlobalTheory.T.exists_factor_field_point_through_generic_point R C.toModif (FractionRing W') _ (jK W' ≫ spMap io ≫ ξ) hinj (by
    rw [Category.assoc, Category.assoc, hξ]
    simp only [jK, spMap, ← Spec.map_comp]
    rfl)
  have hcomp : IsGrpPullback A'.A C.G (spMap ga ≫ C.gp) ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β) :=
    (hγ.comp hcart).congr hy rfl
  let a : A'.A.left ⟶ C.A.A.left := C.α_cart.1.lift ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β)
    (A'.A.hom ≫ spMap ga) (by rw [hcomp.1.w, Category.assoc])
  have ha : a ≫ C.α = (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β := C.α_cart.1.lift_fst _ _ _
  have ha2 : a ≫ C.A.A.hom = A'.A.hom ≫ spMap ga := C.α_cart.1.lift_snd _ _ _
  have hcart' : IsGrpPullback A'.A C.A.A (spMap ga) a := IsGrpPullback.cancel C.α_cart (hcomp.congr rfl ha.symm) ha2
  have hgi : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hA' : LBIso A'.L (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W'))) :=
    LBIso.chartPull (h := U'.gen.inv.left) (chartPullSec A'.L _ _ hgi)
      (chartPullSame U'.LG.L _ (fun _ => pullback.fst G'.hom (jK W')) _ _ fun _ => rfl) U'.ext
  have h2 : LBIso (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')))
      (C.P.L.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β)) :=
    LBIso.chartPull (chartPullPull U'.LG.L _) (chartPullSame C.P.L.L _ _ _ _ fun _ => rfl) hlb
  have h3 : LBIso A'.L (C.P.L.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β)) :=
    LBIso.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB C.P.L.isLB _) hA' h2
  have hfib : IsFib (io.comp φ) C.A A' a :=
    ⟨ga, fun r => hga r, hcart', lbIso_factor C.P.L.isLB C.A.isLB A'.isLB ha C.α_lb h3⟩
  obtain ⟨hD, hind⟩ := GlobalTheory.T.recognition_degData_labels_at_every_trait R hB D C.A lab n hn ho hu hone hgal W' hW' (io.comp φ) (hio.comp hφ)
    inferInstance G' D' A' U' a hsemi hfib
  refine ⟨W', inferInstance, inferInstance, inferInstance, io, G', inferInstance, inferInstance, β, D', A', U', hD, hW',
    hio, hfin, hcart, hlb, ?_⟩
  intro F _ _ _ _ em hF j p p₁ p' x' h₁ h₂ h₃ h₄
  refine hind j F em hF p p₁ p' x' h₁ h₂ h₃ ?_
  haveI := mono_α C.α_cart
  rw [← cancel_mono C.α, Category.assoc, ha]
  simpa only [Category.assoc] using h₄
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLabelledCoverOfOddPrimeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.nonempty_labelled_cover_of_odd_prime : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : UCover R) (lab : Labels D.toPre C.A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre C.A lab → GalEqN n lab → Nonempty (LabCover D) := by
  first | exact @GlobalTheory.Mum.UCover.labCover | exact GlobalTheory.Mum.UCover.labCover | (intros; apply GlobalTheory.Mum.UCover.labCover <;> assumption)
end
end
