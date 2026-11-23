module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentMumfordBundleQuotientStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianSchemeFiniteFlatSubgroup
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetsInAffineOpenAbelianSchemeRelAmpleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleFiniteFlatSubgroupScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodOfFiniteSurjective
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianSchemeFiniteFlatSubgroupStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_quotient_abelianScheme_finiteFlat_subgroup : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (H : Over (Sp R)) [GrpObj H] (i : H ⟶ A), IsAbelianScheme A → IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → ∃ (B : Over (Sp R)) (_ : GrpObj B) (q : A ⟶ B) (π : B ⟶ A), IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ IsFinite π.left ∧ IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q := by
  first | exact @GlobalTheory.AbQuotientAny.exists_quotient_abelianScheme | exact GlobalTheory.AbQuotientAny.exists_quotient_abelianScheme | (intros; apply GlobalTheory.AbQuotientAny.exists_quotient_abelianScheme <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleFiniteFlatSubgroupSchemeStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.kernelOfLineBundle_finiteFlat_subgroupScheme : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∃ (H : Over (Sp R)) (_ : GrpObj H) (i : H ⟶ A), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Flat H.hom ∧ ∀ (T : Over (Sp R)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ i = x := by
  first | exact @GlobalTheory.kernel_finiteFlat_subgroup | exact GlobalTheory.kernel_finiteFlat_subgroup | (intros; apply GlobalTheory.kernel_finiteFlat_subgroup <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionDescendsFiniteFlatSurje

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FiniteSurjRelDim

theorem eq_of_finite_surjective {S X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Surjective f] (p : Y ⟶ S)
    [Nonempty Y] {g m : ℕ} (hX : SmoothOfRelativeDimension g (f ≫ p)) (hY : SmoothOfRelativeDimension m p) :
    g = m := by
  let y : Y := Classical.arbitrary Y
  let t := S.fromSpecResidueField (p y)
  have hpb₂ := IsPullback.of_hasPullback p t
  have hpb₁ := IsPullback.of_hasPullback f (pullback.fst p t)
  have hpX : IsPullback (pullback.fst f (pullback.fst p t))
      (pullback.snd f (pullback.fst p t) ≫ pullback.snd p t) (f ≫ p) t := hpb₁.paste_vert hpb₂
  have hgK : SmoothOfRelativeDimension g (pullback.snd f (pullback.fst p t) ≫ pullback.snd p t) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hpX hX
  have hmK : SmoothOfRelativeDimension m (pullback.snd p t) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange m).of_isPullback hpb₂ hY
  obtain ⟨w, hw⟩ : p y ∈ Set.range t := by
    rw [Scheme.range_fromSpecResidueField]; rfl
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback y w hw.symm
  obtain ⟨a, -⟩ := (pullback.snd f (pullback.fst p t)).surjective z
  have : Nonempty ↥(pullback f (pullback.fst p t)) := ⟨a⟩
  exact GlobalTheory.FiniteSurjDim.eq_of_finite_surjective (k := (p y |> S.residueField))
    (pullback.snd f (pullback.fst p t)) (pullback.snd p t) hgK hmK

theorem smoothOfRelativeDimension_of_finite_surjective : ∀ (S : Scheme.{0}) (A B : Over S) (g : ℕ) (q : A ⟶ B),
    SmoothOfRelativeDimension g A.hom → Smooth B.hom → IsFinite q.left → Flat q.left → Surjective q.left →
    SmoothOfRelativeDimension g B.hom := by
  intro S A B g q hg hB hfin _ hsurj
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim B.hom
  have hn : ∀ y, n y = g := fun y => by
    have : Nonempty (W y) := ⟨⟨y, hW y⟩⟩
    have hd' := hd y
    have : Surjective (q.left ∣_ W y) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› _
    have hX : SmoothOfRelativeDimension g ((q.left ∣_ W y) ≫ (W y).ι ≫ B.hom) := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w q]
      have : SmoothOfRelativeDimension (0 + g) ((q.left ⁻¹ᵁ W y).ι ≫ A.hom) := inferInstance
      simpa using this
    exact (eq_of_finite_surjective (q.left ∣_ W y) ((W y).ι ≫ B.hom) hX hd').symm
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  rw [← hn x]; exact hd x

end GlobalTheory.FiniteSurjRelDim
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionDescendsFiniteFlatSurjeStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_descends_finite_flat_surjective : ∀ (S : Scheme.{0}) (A B : Over S) (g : ℕ) (q : A ⟶ B), SmoothOfRelativeDimension g A.hom → Smooth B.hom → IsFinite q.left → Flat q.left → Surjective q.left → SmoothOfRelativeDimension g B.hom := by
  first | exact @GlobalTheory.FiniteSurjRelDim.smoothOfRelativeDimension_of_finite_surjective | exact GlobalTheory.FiniteSurjRelDim.smoothOfRelativeDimension_of_finite_surjective | (intros; apply GlobalTheory.FiniteSurjRelDim.smoothOfRelativeDimension_of_finite_surjective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientKernelPolarisationDescendedBundle

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualQuot

theorem exists_quotient_lam : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∃ (B : Over (Sp R)) (P : LB (A ⊗ B).left) (q : A ⟶ B) (hP : Fam A P), Good g B.hom ∧ FinAff B.left ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ (∀ (Y : Over (Sp R)) (a x : Y ⟶ A), evc hP.isLB a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL)) ∧ (∀ (Y : Over (Sp R)) (x y : Y ⟶ A), x ≫ q = y ≫ q ↔ GlobalTheory.MemKL A L (x * y⁻¹)) := by
  intro R _ _ A _ g hA hg L hL hamp
  obtain ⟨H, _, i, hi, hmono, hHf, hHfl, hrep⟩ := GlobalTheory.T.kernelOfLineBundle_finiteFlat_subgroupScheme R A hA L hL hamp
  obtain ⟨B, _, q, π, hB, hq, hqf, hqfl, hqs, hπ, hpb⟩ := GlobalTheory.T.exists_quotient_abelianScheme_finiteFlat_subgroup R A H i hA hi hmono hHf hHfl
  obtain ⟨P₀, hP₀, hform⟩ := GlobalTheory.T.exists_descent_mumfordBundle_quotient R A hA L hL H i hi hmono hHf hHfl hrep B q hB hq hqf hqfl hqs hpb
  have hc := hA.comm
  let c : A ⊗ B ⟶ A ⊗ B := snd A B ≫ lift (1 : B ⟶ A) (𝟙 B)
  let P : LB (A ⊗ B).left := tens P₀ (dual (P₀.pull c.left))
  have hP : P.IsLB := isLB_tens hP₀ (isLB_dual (pull_isLB hP₀ _))
  have hcls : cls P hP = cls P₀ hP₀ - GlobalTheory.CechPic.pull c.left (cls P₀ hP₀) := by
    rw [cls_tens hP₀ (isLB_dual (pull_isLB hP₀ _)), cls_dual (pull_isLB hP₀ _), cls_pull hP₀, sub_eq_add_neg]
  have hev : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ B), evc hP a t = evc hP₀ a t - evc hP₀ 1 t := by
    intro Y a t
    have e : lift a t ≫ c = lift (1 : Y ⟶ A) t := by
      simp only [c, lift_snd_assoc, comp_lift, MonObj.comp_one, Category.comp_id, lift_snd]
    simp only [evc]
    rw [hcls, map_sub, ← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, e]
  have hform' : ∀ (Y : Over (Sp R)) (a x : Y ⟶ A), evc hP a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL) := by
    intro Y a x
    rw [hev, hform, hform, _root_.one_mul]
    abel
  have h0l : Triv (ev P (1 : B ⟶ A) (𝟙 B)) := by
    rw [triv_ev_iff hP, hev, sub_self]
  have h0r : Triv (ev P (𝟙 A) (1 : A ⟶ B)) := by
    have e : (1 : A ⟶ B) = (1 : A ⟶ A) ≫ q := (MonObj.one_comp q).symm
    rw [triv_ev_iff hP, e, hform', _root_.mul_one]
    abel
  have hadd : IsAdditive P := GlobalTheory.CubeNoeth.isAdditive_of_triv_axes hA hB hP h0l h0r
  have hBsm := hB.smooth
  have hAfa := GlobalTheory.T.finiteSetsInAffineOpen_abelianScheme_relAmple R A hA L hL hamp
  refine ⟨B, P, q, ⟨hP, hadd⟩, ⟨hB.proper, GlobalTheory.T.smoothOfRelativeDimension_descends_finite_flat_surjective _ A B g q hg hBsm hqf hqfl hqs, hB.geomConnected⟩, ?_, hqf, hqfl, hqs, hform', ?_⟩
  · intro F
    classical
    obtain ⟨U, hU, hF⟩ := hAfa (F.image π.left)
    exact ⟨π.left ⁻¹ᵁ U, hU.preimage π.left, fun x hx ↦ hF _ (Finset.mem_image_of_mem _ hx)⟩
  · intro Y x y
    constructor
    · intro h
      refine (hrep Y (x * y⁻¹)).2 ⟨hpb.lift x y h ≫ fst H A, ?_⟩
      have h1 := hpb.lift_fst x y h
      rw [comp_mul, hpb.lift_snd] at h1
      rw [eq_mul_inv_iff_mul_eq, Category.assoc, h1]
    · intro h
      obtain ⟨z, hz⟩ := (hrep Y (x * y⁻¹)).1 h
      have hx : x = lift z y ≫ ((fst H A ≫ i) * snd H A) := by
        rw [comp_mul, lift_fst_assoc, lift_snd, hz, inv_mul_cancel_right]
      rw [hx, Category.assoc, hpb.w, lift_snd_assoc]

end GlobalTheory.DualQuot
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientKernelPolarisationDescendedBundleStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_quotient_kernel_polarisation_descended_bundle : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∃ (B : Over (Sp R)) (P : LB (A ⊗ B).left) (q : A ⟶ B) (hP : Fam A P), Good g B.hom ∧ FinAff B.left ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ (∀ (Y : Over (Sp R)) (a x : Y ⟶ A), evc hP.isLB a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL)) ∧ (∀ (Y : Over (Sp R)) (x y : Y ⟶ A), x ≫ q = y ≫ q ↔ GlobalTheory.MemKL A L (x * y⁻¹)) := by
  first | exact @GlobalTheory.DualQuot.exists_quotient_lam | exact GlobalTheory.DualQuot.exists_quotient_lam | (intros; apply GlobalTheory.DualQuot.exists_quotient_lam <;> assumption)
end
end
