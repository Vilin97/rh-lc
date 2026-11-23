module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveGeomFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionDual
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHomExtensionSemiAbelianNormal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatOfIsFiniteOfFinitePresentationOfFlatGeometri
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfDualHomomorphismKernelKilled

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualHomFlat

theorem geomFibre_flat (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left)
    (la : A ⟶ B) [IsMonHom la] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hd : IsDual A B P)
    [LocallyQuasiFinite la.left] (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) :
    Flat ((Over.pullback s).map la).left := by
  letI : GrpObj ((Over.pullback s).obj A) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback s).obj B) := Functor.grpObjObj
  have hA' := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  have hB' := GlobalTheory.isAbelianScheme_pullback_obj s B hB
  obtain ⟨gA, hgA⟩ := GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj A) hA'
  obtain ⟨gB, hgB⟩ := GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj B) hB'
  let Ak : AV.AbVar K := { X := (Over.pullback s).obj A, ab := hA', dim := gA, smooth := hgA }
  let Bk : AV.AbVar K := { X := (Over.pullback s).obj B, ab := hB', dim := gB, smooth := hgB }
  have key : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback s).map a).left ≫ pullback.fst Y.hom s = pullback.fst X.hom s ≫ a.left :=
    fun a ↦ pullback.lift_fst _ _ _
  let h : ((Over.pullback s).obj A ⊗ (Over.pullback s).obj B).left ⟶ (A ⊗ B).left :=
    (Functor.LaxMonoidal.μ (Over.pullback s) A B).left ≫ pullback.fst (A ⊗ B).hom s
  have h₁ : h ≫ (fst A B).left = (fst ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫
      pullback.fst A.hom s := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (fst A B) = fst _ _ by simp]
  have h₂ : h ≫ (snd A B).left = (snd ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫
      pullback.fst B.hom s := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (snd A B) = snd _ _ by simp]
  have hP' : (P.pull h).IsLB := pull_isLB hd.isLB _
  have hd' : IsDual Ak.X Bk.X (P.pull h) := IsDual.baseChange (isGrpPullback_pullback A s)
    (isGrpPullback_pullback B s) h₁ h₂ hP' ((cls_eq_iff hP' hP').1 rfl) hd
  have hdim : gB = gA := DualTower.dim_eq_of_isDual Ak Bk (P.pull h) hd'
  subst hdim
  have : LocallyQuasiFinite ((Over.pullback s).map la).left :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (AbLaw.MulN.isPullback_baseChange s la)
      inferInstance
  exact (IsogenyQuasiInverse.flat_surjective_of_field _ _ gB hA' hB' hgA hgB _).1

end GlobalTheory.DualHomFlat

namespace GlobalTheory.DualHomFlat

theorem main : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left)
    (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q →
    IsDual B A (swap Q) → IsMonHom la → 0 < d →
    (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Flat la.left := by
  intro S A B _ _ Q la d hA hB hd _ hla hdpos hker
  have := hA.smooth
  have := hB.smooth
  have := hA.proper
  have := hB.proper
  have : LocallyOfFiniteType (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType la.left := locallyOfFiniteType_of_comp _ B.hom
  have : QuasiCompact (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact la.left := QuasiCompact.of_comp _ B.hom
  have hSA := isSemiAbelian_of_isAbelianScheme A hA
  have : LocallyQuasiFinite la.left :=
    locallyQuasiFinite_of_finite_geometric_ker _ A B la hla inferInstance inferInstance
      fun Ω _ _ t => by
        have := HomExt.finite_torsion_points hSA t hdpos
        exact Finite.of_injective (β := {x : Over.mk t ⟶ A // x ^ d = 1})
          (fun x => ⟨x.1, hker _ x.1 x.2⟩) fun a b e =>
            Subtype.ext (congrArg (fun z : {x : Over.mk t ⟶ A // x ^ d = 1} => z.1) e)
  have h1 : IsProper (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper la.left := IsProper.of_comp _ B.hom
  have hf : IsFinite la.left := .of_isProper_of_locallyQuasiFinite _
  exact flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres S A B la inferInstance
    inferInstance inferInstance hf fun K _ _ t => geomFibre_flat S A B Q la hA hB hd K t

end GlobalTheory.DualHomFlat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfDualHomomorphismKernelKilledStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual

theorem _root_.GlobalTheory.T.flat_of_dual_homomorphism_kernel_killed : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Flat la.left := by
  first | (exact @GlobalTheory.DualHomFlat.main) | (exact GlobalTheory.DualHomFlat.main) | (intros; apply GlobalTheory.DualHomFlat.main  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfDualHomomorphismKernelKilled

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
open ReciprocityTheory.ChartRestriction.G
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.DualHomSurj

theorem surjective_of_ker_killed : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Surjective la.left := by
  intro S A B _ _ Q la d hA hB hd _ hla hd0 hk
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  have : LocallyOfFiniteType (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType la.left := locallyOfFiniteType_of_comp _ B.hom
  have : QuasiCompact (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact la.left := QuasiCompact.of_comp _ B.hom
  have hSA := GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA
  have hLQF : LocallyQuasiFinite la.left :=
    GlobalTheory.locallyQuasiFinite_of_finite_geometric_ker _ A B la hla inferInstance inferInstance
      fun Ω _ _ t => by
        have := GlobalTheory.HomExt.finite_torsion_points hSA t hd0
        exact Finite.of_injective (β := {x : Over.mk t ⟶ A // x ^ d = 1})
          (fun x => ⟨x.1, hk _ x.1 x.2⟩) fun a b e =>
            Subtype.ext (congrArg (fun z : {x : Over.mk t ⟶ A // x ^ d = 1} => z.1) e)
  haveI : IsMonHom la := hla
  refine GlobalTheory.AbLaw.MulN.surjective_of_geomFibres la fun K _ _ s => ?_
  have hA' := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  have hB' := GlobalTheory.isAbelianScheme_pullback_obj s B hB
  obtain ⟨gA, hgA⟩ := GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj A) hA'
  obtain ⟨gB, hgB⟩ := GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj B) hB'
  let Ak : GlobalTheory.AV.AbVar K := { X := (Over.pullback s).obj A, ab := hA', dim := gA, smooth := hgA }
  let Bk : GlobalTheory.AV.AbVar K := { X := (Over.pullback s).obj B, ab := hB', dim := gB, smooth := hgB }
  have key : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback s).map a).left ≫ pullback.fst Y.hom s = pullback.fst X.hom s ≫ a.left :=
    fun a ↦ pullback.lift_fst _ _ _
  let h : ((Over.pullback s).obj A ⊗ (Over.pullback s).obj B).left ⟶ (A ⊗ B).left :=
    (Functor.LaxMonoidal.μ (Over.pullback s) A B).left ≫ pullback.fst (A ⊗ B).hom s
  have h₁ : h ≫ (fst A B).left = (fst ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫
      pullback.fst A.hom s := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (fst A B) = fst _ _ by simp]
  have h₂ : h ≫ (snd A B).left = (snd ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫
      pullback.fst B.hom s := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (snd A B) = snd _ _ by simp]
  have hP' : (Q.pull h).IsLB := pull_isLB hd.isLB _
  have hd' : IsDual Ak.X Bk.X (Q.pull h) := IsDual.baseChange (isGrpPullback_pullback A s)
    (isGrpPullback_pullback B s) h₁ h₂ hP' ((cls_eq_iff hP' hP').1 rfl) hd
  have hdim : gB = gA := GlobalTheory.DualTower.dim_eq_of_isDual Ak Bk (Q.pull h) hd'
  have : LocallyQuasiFinite ((Over.pullback s).map la).left :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange s la)
      inferInstance
  exact (GlobalTheory.IsogenyQuasiInverse.flat_surjective_of_field _ _ gA hA' hB' hgA (hdim ▸ hgB) _).2

end GlobalTheory.DualHomSurj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfDualHomomorphismKernelKilledStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual

theorem _root_.GlobalTheory.T.surjective_of_dual_homomorphism_kernel_killed : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Surjective la.left := by
  first | (exact @GlobalTheory.DualHomSurj.surjective_of_ker_killed) | (exact GlobalTheory.DualHomSurj.surjective_of_ker_killed) | (intros; apply GlobalTheory.DualHomSurj.surjective_of_ker_killed  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianSchemeHomCompEqMulOfKer

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualFactor

theorem factor_of_flat {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A]
    [IsCommMonObj B] (la : A ⟶ B) [IsMonHom la] [Flat la.left] [Surjective la.left]
    [QuasiCompact la.left] (d : ℕ)
    (hk : ∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) :
    ∃ mu : B ⟶ A, IsMonHom mu ∧ la ≫ mu = 𝟙 A ^ d ∧ mu ≫ la = 𝟙 B ^ d := by
  obtain ⟨mu, hmu⟩ := GlobalTheory.AbelianQuotient.exists_desc la (𝟙 A ^ d) (by
    intro W a b h
    rw [comp_pow, comp_pow, Category.comp_id, Category.comp_id]
    have h1 : (a / b) ≫ la = 1 := by
      rw [GrpObj.div_comp, h, div_self']
    have h2 := hk W _ h1
    rwa [div_pow, div_eq_one] at h2)
  have := FlatQuotient.epi_of_flat_surjective la
  have := FlatQuotient.epi_tensorHom la la
  refine ⟨mu, ⟨?_, ?_⟩, hmu, ?_⟩
  · have e : (η[A] : 𝟙_ (Over S) ⟶ A) = 1 := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [← IsMonHom.one_hom la, Category.assoc, hmu, comp_pow, Category.comp_id, e, one_pow]
  · rw [← cancel_epi (la ⊗ₘ la), ← IsMonHom.mul_hom_assoc, hmu, tensorHom_comp_tensorHom_assoc, hmu,
      comp_pow, Category.comp_id]
    have hμ : (μ[A] : A ⊗ A ⟶ A) = fst A A * snd A A := by
      rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    rw [hμ, comp_mul, tensorHom_fst, tensorHom_snd, comp_pow, comp_pow, Category.comp_id,
      Category.comp_id, mul_pow]
  · rw [← cancel_epi la, reassoc_of% hmu, comp_pow, Category.comp_id, pow_comp, Category.id_comp]

theorem main : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → ∃ mu : B ⟶ A, IsMonHom mu ∧ la ≫ mu = 𝟙 A ^ d ∧ mu ≫ la = 𝟙 B ^ d := by
  intro S A B _ _ Q la d hA hB hAB hBA hla hd hk
  have := hA.comm
  have := hB.comm
  have := hA.proper
  have := hB.proper
  have : Surjective la.left := GlobalTheory.T.surjective_of_dual_homomorphism_kernel_killed S A B Q la d hA hB hAB hBA hla hd hk
  have : Flat la.left := GlobalTheory.T.flat_of_dual_homomorphism_kernel_killed S A B Q la d hA hB hAB hBA hla hd hk
  have : QuasiCompact la.left := by
    have : QuasiCompact (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
    exact QuasiCompact.of_comp la.left B.hom
  exact factor_of_flat A B la d hk

end GlobalTheory.DualFactor
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianSchemeHomCompEqMulOfKerStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual

theorem _root_.GlobalTheory.T.exists_dualAbelianScheme_hom_comp_eq_mul_of_ker : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → ∃ mu : B ⟶ A, IsMonHom mu ∧ la ≫ mu = 𝟙 A ^ d ∧ mu ≫ la = 𝟙 B ^ d := by
  first | (exact @GlobalTheory.DualFactor.main) | (exact GlobalTheory.DualFactor.main) | (intros; apply GlobalTheory.DualFactor.main <;> assumption)
end
end
