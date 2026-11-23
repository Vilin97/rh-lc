module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasePointOfFiniteEtaleOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomOver

section

section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et.CovChar

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

variable {R} {X Y : Scheme.{0}} (f : Y ⟶ X)

end GlobalTheory.Et.CovChar

namespace GlobalTheory.AV.AbVar

open ReciprocityTheory.ChartRestriction.G.Geo.Tor MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {K : Type} [Field K]

abbrev geomX (A : AbVar K) : Scheme.{0} := GlobalTheory.Et.geom (AlgebraicClosure K) A.X.hom

abbrev geomOver (A : AbVar K) : Over (Sp K) :=
  Over.mk (pullback.fst A.X.hom (spMap (algebraMap K (AlgebraicClosure K))) ≫ A.X.hom)

def transl (A : AbVar K) (a : A.Pt) : geomX A ⟶ geomX A :=
  pullback.lift
    ((lift (Over.homMk (pullback.fst _ _) : geomOver A ⟶ A.X)
      (Over.homMk (pullback.snd _ _ ≫ a.left) (by
        rw [Category.assoc, Over.w a]; exact pullback.condition.symm) : geomOver A ⟶ A.X) ≫ μ[A.X]).left)
    (pullback.snd _ _) (by
      rw [Over.w]; exact pullback.condition)

end GlobalTheory.AV.AbVar
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsPullbackAbelianScheme

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et GlobalTheory.Et.CovChar
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerConst

open GlobalTheory.LevelCompare

theorem finite_etale_ker {S : Scheme.{0}} (A : Over S) [GrpObj A] (k : ℕ)
    (hf : IsFinite (𝟙 A ^ k).left) (he : Etale (𝟙 A ^ k).left) :
    IsFinite (Ker A k).hom ∧ Etale (Ker A k).hom := by
  have h := (IsPullback.of_hasPullback (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms.mulBy A k) η[A]).map (Over.forget S)
  have h₁ : IsFinite (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms.mulBy A k).left := hf
  have h₁' : Etale (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms.mulBy A k).left := he
  have h₂ : IsFinite (pullback.snd (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms.mulBy A k) η[A]).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) h h₁
  have h₂' : Etale (pullback.snd (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms.mulBy A k) η[A]).left :=
    MorphismProperty.of_isPullback (P := @Etale) h h₁'
  rw [← Over.w (pullback.snd (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms.mulBy A k) η[A])]
  exact ⟨MorphismProperty.comp_mem @IsFinite _ _ h₂ (inferInstanceAs (IsFinite (𝟙 S))),
    by haveI := h₂'; haveI : Etale (𝟙_ (Over S)).hom := inferInstanceAs (Etale (𝟙 S)); infer_instance⟩

end GlobalTheory.KerConst

namespace GlobalTheory.KerConst

open GlobalTheory.LevelCompare

theorem isPullback_const_ker (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (G : Over (Spec (CommRingCat.of Ω))) [GrpObj G] : IsAbelianScheme G → ∀ (n : ℕ), (n : Ω) ≠ 0 →
    IsPullback (Sigma.desc (f := fun _ : {x : 𝟙_ (Over (Spec (CommRingCat.of Ω))) ⟶ G // x ^ n = 1} =>
      𝟙_ (Over (Spec (CommRingCat.of Ω)))) fun x => x.1) (toUnit _) (𝟙 G ^ n) η[G] := by
  intro hG n hn
  have := hG.comm
  have := hG.smooth
  have := hG.proper
  have hu : IsUnit (n : Γ(Spec (CommRingCat.of Ω), ⊤)) := by
    have h1 : IsUnit (n : Ω) := hn.isUnit
    simpa using h1.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  obtain ⟨hfin, het⟩ := finite_etale_ker G n (GlobalTheory.GrpTangent.isFinite_id_pow G hu)
    (GlobalTheory.GrpTangent.etale_id_pow G hu)
  refine (isKer_iff (A := G) (k := n) (fun x : {x : 𝟙_ (Over (Spec (CommRingCat.of Ω))) ⟶ G // x ^ n = 1} => x.1)
    (fun x => x.2)).2 ?_
  haveI := formallyUnramified_ker G hu
  haveI := locallyOfFiniteType_ker G n
  apply isIso_desc_of_lists
  intro K _ _ s u
  letI : Algebra Ω K := (Spec.preimage s).hom.toAlgebra
  have hs : s = spMap (algebraMap Ω K) := (Spec.map_preimage s).symm
  have hts : ∀ (T : Over (Spec (CommRingCat.of Ω))), (toUnit T).left = T.hom := fun T => by
    simpa using Over.w (toUnit T)
  obtain ⟨x₀, hx₀, hx⟩ := GlobalTheory.FinEtPoints.exists_point_of_finite_etale Ω K (Ker G n).left
    (Ker G n).hom hfin het u.left (by rw [Over.w u]; exact hs)
  let t₀ : 𝟙_ (Over (Spec (CommRingCat.of Ω))) ⟶ Ker G n := Over.homMk x₀ hx₀
  have hp : (t₀ ≫ pullback.fst _ _) ^ n = 1 := by
    rw [← comp_mulBy, Category.assoc, pullback.condition, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  refine existsUnique_of_exists_of_unique ⟨⟨_, hp⟩, ?_⟩ ?_
  · have e : kerPt (t₀ ≫ pullback.fst _ _) hp = t₀ := ker_ext (kerPt_fst _ _)
    show toUnit _ ≫ kerPt (t₀ ≫ pullback.fst _ _) hp = u
    rw [e]
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hts]
    show s ≫ x₀ = u.left
    exact (congrArg (· ≫ x₀) hs).trans hx
  · intro i j hi hj
    have h1 := congrArg (fun v => v ≫ pullback.fst _ _) (hi.trans hj.symm)
    simp only [Category.assoc, kerPt_fst] at h1
    have h2 := congrArg CommaMorphism.left h1
    simp only [Over.comp_left, hts] at h2
    haveI : Epi s := hs ▸ GlobalTheory.FinEtPoints.epi_spMap_field Ω K (algebraMap Ω K)
    exact Subtype.ext (Over.OverMorphism.ext ((cancel_epi s).mp h2))

end GlobalTheory.KerConst
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointLocallyConstantGeomPoin

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TorsLocConst

theorem push_injective {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (x : S' ⟶ S) (T : Over S') :
    Function.Injective (pushHom (isGrpPullback_pullback A x) T) := by
  intro a b h
  have h' := congrArg CommaMorphism.left h
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h'
  · exact (Over.w a).trans (Over.w b).symm

theorem locally_const_torsion :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (k : Type) [Field k] [IsAlgClosed k]
      (x : Sp k ⟶ S) (n : ℕ), (n : k) ≠ 0 → ∀ (Z : Over S) (t : Z ⟶ Over.mk x) (z : Z ⟶ A), z ^ n = 1 →
      ∀ w : Z.left, ∃ (V : Over S) (i : V ⟶ Z) (y : Over.mk x ⟶ A) (w' : V.left),
        IsOpenImmersion i.left ∧ i.left w' = w ∧ y ^ n = 1 ∧ i ≫ z = i ≫ t ≫ y := by
  intro S A _ hA k _ _ x n hn Z t z hz w
  have hB : IsAbelianScheme ((Over.pullback x).obj A) := Out.TLinPf.isAb_pullback x A hA
  have hg := isGrpPullback_pullback A x
  have htx : t.left ≫ x = Z.hom := Over.w t
  let Z' : Over (Sp k) := Over.mk t.left
  let z' : Z' ⟶ (Over.pullback x).obj A :=
    Over.homMk (pullback.lift z.left t.left ((Over.w z).trans htx.symm)) (pullback.lift_snd _ _ _)
  let e : Z ⟶ Over.mk (Z'.hom ≫ x) := Over.homMk (𝟙 Z.left) (by
    show 𝟙 _ ≫ t.left ≫ x = Z.hom
    rw [Category.id_comp, htx])
  let e' : Over.mk (Z'.hom ≫ x) ⟶ Z := Over.homMk (𝟙 Z.left) (by
    show 𝟙 _ ≫ Z.hom = t.left ≫ x
    rw [Category.id_comp, htx])
  have hee : e' ≫ e = 𝟙 _ := Over.OverMorphism.ext (by show 𝟙 Z.left ≫ 𝟙 Z.left = 𝟙 Z.left; exact Category.id_comp _)
  have hez : e ≫ pushHom hg Z' z' = z := Over.OverMorphism.ext (by
    show 𝟙 _ ≫ (pullback.lift _ _ _ ≫ pullback.fst _ _) = z.left
    rw [Category.id_comp, pullback.lift_fst])
  have hz' : z' ^ n = 1 := by
    apply push_injective A x Z'
    rw [map_pow, map_one]
    calc (pushHom hg Z' z') ^ n = e' ≫ e ≫ (pushHom hg Z' z') ^ n := by
          rw [← Category.assoc, hee, Category.id_comp]
      _ = e' ≫ (e ≫ pushHom hg Z' z') ^ n := by rw [MonObj.comp_pow]
      _ = 1 := by rw [hez, hz, MonObj.comp_one]
  have hK := GlobalTheory.KerConst.isPullback_const_ker k ((Over.pullback x).obj A) hB n hn
  have hcond : z' ≫ 𝟙 _ ^ n = toUnit Z' ≫ η[(Over.pullback x).obj A] := by
    rw [MonObj.comp_pow, Category.comp_id, hz', Hom.one_def]
  let g := hK.lift z' (toUnit Z') hcond
  have hgz : g ≫ Sigma.desc (fun c => c.1) = z' := hK.lift_fst _ _ _
  let P := {c : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback x).obj A // c ^ n = 1}
  let D : (∐ fun _ : P => 𝟙_ (Over (Sp k))) ⟶ GlobalTheory.PointQuot.constObj (Sp k) P :=
    Sigma.desc fun c => GlobalTheory.PointQuot.constPt (Sp k) c
  have hDE : D ≫ GlobalTheory.PointQuot.constDesc (fun c : P => c.1) = Sigma.desc (fun c : P => c.1) :=
    Sigma.hom_ext _ _ fun c => by
      rw [← Category.assoc, Sigma.ι_desc, Sigma.ι_desc, GlobalTheory.PointQuot.constPt_desc]
  obtain ⟨U, hwU, c, hc⟩ := GlobalTheory.PointQuot.locally_const_desc (fun c : P => c.1) (g ≫ D) w
  have hU : GlobalTheory.PointQuot.openι Z' U ≫ z' = toUnit _ ≫ c.1 := by
    rw [← hc, ← hgz, ← hDE]
    simp only [Category.assoc]
  let y : Over.mk x ⟶ A := Over.homMk (c.1.left ≫ pullback.fst A.hom x) (by
    show (c.1.left ≫ pullback.fst A.hom x) ≫ A.hom = x
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hc1 : c.1.left ≫ pullback.snd A.hom x = 𝟙 _ := Over.w c.1
    rw [hc1, Category.id_comp])
  let e'' : Over.mk x ⟶ Over.mk ((𝟙_ (Over (Sp k))).hom ≫ x) := Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ 𝟙 _ ≫ x = x
    rw [Category.id_comp, Category.id_comp])
  have hy : y = e'' ≫ pushHom hg _ c.1 := Over.OverMorphism.ext (by
    show c.1.left ≫ pullback.fst A.hom x = 𝟙 _ ≫ (c.1.left ≫ pullback.fst A.hom x)
    rw [Category.id_comp])
  refine ⟨GlobalTheory.PointQuot.openObj Z U, GlobalTheory.PointQuot.openι Z U, y, ⟨w, hwU⟩, ?_, rfl, ?_, ?_⟩
  · show IsOpenImmersion U.ι
    infer_instance
  · rw [hy, ← MonObj.comp_pow, ← map_pow, c.2, map_one, MonObj.comp_one]
  · apply Over.OverMorphism.ext
    have h1 := congrArg CommaMorphism.left hU
    have h2 : (toUnit (GlobalTheory.PointQuot.openObj Z' U)).left = U.ι ≫ t.left :=
      (Category.comp_id _).symm.trans (Over.w (toUnit (GlobalTheory.PointQuot.openObj Z' U)))
    show U.ι ≫ z.left = U.ι ≫ t.left ≫ c.1.left ≫ pullback.fst A.hom x
    have h3 : z.left = z'.left ≫ pullback.fst A.hom x := (pullback.lift_fst _ _ _).symm
    simp only [Over.comp_left] at h1
    rw [h3, ← Category.assoc]
    erw [h1, h2]
    exact Category.assoc _ _ _

end GlobalTheory.TorsLocConst
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointLocallyConstantGeomPoinStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor


theorem _root_.GlobalTheory.T.abelianScheme_torsionPoint_locally_constant_geomPoint : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), (n : k) ≠ 0 → ∀ (Z : Over S) (t : Z ⟶ Over.mk x) (z : Z ⟶ A), z ^ n = 1 → ∀ w : Z.left, ∃ (V : Over S) (i : V ⟶ Z) (y : Over.mk x ⟶ A) (w' : V.left), IsOpenImmersion i.left ∧ i.left w' = w ∧ y ^ n = 1 ∧ i ≫ z = i ≫ t ≫ y := by
  first | (exact @GlobalTheory.TorsLocConst.locally_const_torsion) | (exact GlobalTheory.TorsLocConst.locally_const_torsion) | (intros; apply GlobalTheory.TorsLocConst.locally_const_torsion  <;> assumption)
end
end
