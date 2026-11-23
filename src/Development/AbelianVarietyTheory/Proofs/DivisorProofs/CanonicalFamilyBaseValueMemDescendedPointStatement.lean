module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapFixingDescendedPointsSubfieldStatement
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.SurjOfCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMulEquivPointsOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackPointDescendsAlgClosedSubfieldStatement
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledLowerObjectGroupIdentificationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShimuraObjectPullbackCompCancelStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubfieldOfForallRingEquivFixedOfIsAlgClosedAl

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem mem_subfield_of_forall_ringEquiv_fixed_of_isAlgClosed :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ x : K,
      (∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → σ x = x) → x ∈ k₀ := by
  intro K _ _ k₀ hk₀ x hfix
  by_contra hx
  have htr : Transcendental k₀ x := by
    intro halg
    have hint : IsIntegral k₀ x := halg.isIntegral
    have hdeg : (minpoly k₀ x).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible hint)
    obtain ⟨r, hr⟩ := minpoly.mem_range_of_degree_eq_one k₀ x hdeg
    apply hx
    rw [← hr]
    exact r.2
  obtain ⟨σ, hσk, hσx⟩ := GlobalTheory.FixedRoots.exists_ringEquiv_add_one k₀ x htr
  have h := hfix σ hσk
  rw [hσx] at h
  simp at h

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubfieldOfForallRingEquivFixedOfIsAlgClosedAlStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mem_subfield_of_forall_ringEquiv_fixed_of_isAlgClosed' : ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ x : K, (∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → σ x = x) → x ∈ k₀ := by
  first | exact @GlobalTheory.mem_subfield_of_forall_ringEquiv_fixed_of_isAlgClosed | exact GlobalTheory.mem_subfield_of_forall_ringEquiv_fixed_of_isAlgClosed | (intros; apply GlobalTheory.mem_subfield_of_forall_ringEquiv_fixed_of_isAlgClosed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledLowerObjectDescendsWithPointsSubfield

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.PtsDescent

theorem pow_left_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (x : T ⟶ G') (z : Over.mk (T.hom ≫ f) ⟶ G)
    (hz : z.left = x.left ≫ φ) (n : ℕ) : (z ^ n).left = (x ^ n).left ≫ φ := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LamF.exists_mulEquiv_points_of_isGrpPullback S S' f G G' φ h T
  have e : Φ x = z := Over.OverMorphism.ext ((hΦ x).trans hz.symm)
  rw [← hΦ, map_pow, e]

theorem degPre_c_nsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (y : D.X) (n : ℕ) :
    D.c (n • y) = D.c y ^ n := by
  have h0 : D.c 0 = 1 := by
    have := D.c_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [succ_nsmul, D.c_add, ih, pow_succ]; rfl

end GlobalTheory.UCanon.PtsDescent

namespace GlobalTheory.UCanon.PtsDescent

theorem pulledObj_descends_with_points : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (o' : LowObj D' c ((ev.comp iw).comp L.b)) (m₁ : ObjMap o' L.o (spMap (ev.comp iw))), ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left)) (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)) (θ : o'.t.G.left ⟶ B'.left), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' Q.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ → w.IsGen → (∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) → IsGrpPullback o'.t.G B' (𝟙 _) θ → LBIso o'.t.PP.L (Q.P.L.pull (θ ≫ π₁)) → (∀ (x : Sp K ⟶ o'.t.G.left) (a : Q.X), x ≫ o'.t.G.hom = 𝟙 _ → x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c (l.M' • e a)).left → x ≫ θ ≫ π₁ = spMap ev ≫ (Q.c a).left) → IsGrpPullback o'.t.G B₀ (spMap k₀.subtype) (θ ≫ π₀) ∧ LBIso o'.t.PP.L (M₀.pull (θ ≫ π₀)) ∧ ∀ y : L.D.X, ∃ x : Sp K ⟶ o'.t.G.left, x ≫ o'.t.G.hom = 𝟙 _ ∧ x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c y).left ∧ ∃ x₀ : Sp k₀ ⟶ B₀.left, x ≫ θ ≫ π₀ = spMap k₀.subtype ≫ x₀ := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e hdiv K _ _ _ ev k₀ hk₀ o' m₁ B₀ _ _ M₀ c₀ B' _ π₁ π₀ w c' θ hB₀ hM₀ hpb1 hpb0 hw hc' hθ hL hpts
  have h1 : IsGrpPullback o'.t.G B₀ (spMap k₀.subtype) (θ ≫ π₀) :=
    (hθ.comp hpb0).congr (Category.id_comp _) rfl
  refine ⟨h1, ?_, ?_⟩
  · exact LBIso.trans o'.t.PP.isLB (pull_isLB Q.P.isLB _) (pull_isLB hM₀ _) hL
      (GlobalTheory.GenSpread.lbIso_pull_comp θ rfl rfl ⟨w, hw⟩)

  · intro y
    have hpb : IsGrpPullback o'.t.G L.D.P.A (spMap (ev.comp iw)) (m₁.toSABMap.φ ≫ L.φB) :=
      (m₁.cart.comp L.ab.1).congr (Category.comp_id _) rfl
    let x : Sp K ⟶ o'.t.G.left := hpb.1.lift (spMap (ev.comp iw) ≫ (L.D.c y).left) (𝟙 _)
      (by rw [Category.assoc, Over.w (L.D.c y)]; simp)
    have hx1 : x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c y).left := hpb.1.lift_fst _ _ _
    have hx2 : x ≫ o'.t.G.hom = 𝟙 _ := hpb.1.lift_snd _ _ _
    refine ⟨x, hx2, hx1, ?_⟩
    let xp : 𝟙_ (Over (Sp K)) ⟶ o'.t.G := Over.homMk x (by simpa using hx2)
    let z : Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw)) ⟶ L.D.P.A := toUnit _ ≫ L.D.c y
    have htu : (toUnit (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw)))).left =
        (𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw) := by
      simpa using Over.w (toUnit (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw))))
    have hz : z.left = xp.left ≫ m₁.toSABMap.φ ≫ L.φB := by
      show (toUnit (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw))) ≫ L.D.c y).left = x ≫ m₁.toSABMap.φ ≫ L.φB
      rw [Over.comp_left, htu, hx1]; simp
    have hpow := pow_left_of_isGrpPullback hpb _ xp z hz l.M'
    have hxa : (xp ^ l.M').left ≫ m₁.toSABMap.φ ≫ L.φB =
        spMap (ev.comp iw) ≫ (L.D.c (l.M' • e (e.symm y))).left := by
      rw [LinearEquiv.apply_symm_apply, degPre_c_nsmul, ← hpow]
      show ((toUnit (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw))) ≫ L.D.c y) ^ l.M').left = _
      rw [← MonObj.comp_pow, Over.comp_left, htu]; simp
    have hxs : (xp ^ l.M').left ≫ o'.t.G.hom = 𝟙 _ := by simpa using Over.w (xp ^ l.M')
    have h₁ := hpts _ (e.symm y) hxs hxa
    have hsec : (xp ^ l.M').left ≫ θ = c' (e.symm y) := by
      apply hpb1.1.hom_ext
      · rw [Category.assoc, h₁, (hc' _).2.1]
      · rw [Category.assoc, hθ.1.w, ← Category.assoc, hxs, (hc' _).1]; simp
    have hM' : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
    obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.grpPullback_point_descends_algClosed_subfield K k₀ hk₀ B₀ o'.t.G (θ ≫ π₀) hB₀ h1 l.M' hM' xp (c₀ (e.symm y))
      (by rw [← Category.assoc, hsec, (hc' _).2.2])
    exact ⟨y₀, hy₀⟩

end GlobalTheory.UCanon.PtsDescent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledLowerObjectDescendsWithPointsSubfieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pulledLowerObject_descends_with_points_subfield : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (o' : LowObj D' c ((ev.comp iw).comp L.b)) (m₁ : ObjMap o' L.o (spMap (ev.comp iw))), ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left)) (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)) (θ : o'.t.G.left ⟶ B'.left), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' Q.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ → w.IsGen → (∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) → IsGrpPullback o'.t.G B' (𝟙 _) θ → LBIso o'.t.PP.L (Q.P.L.pull (θ ≫ π₁)) → (∀ (x : Sp K ⟶ o'.t.G.left) (a : Q.X), x ≫ o'.t.G.hom = 𝟙 _ → x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c (l.M' • e a)).left → x ≫ θ ≫ π₁ = spMap ev ≫ (Q.c a).left) → IsGrpPullback o'.t.G B₀ (spMap k₀.subtype) (θ ≫ π₀) ∧ LBIso o'.t.PP.L (M₀.pull (θ ≫ π₀)) ∧ ∀ y : L.D.X, ∃ x : Sp K ⟶ o'.t.G.left, x ≫ o'.t.G.hom = 𝟙 _ ∧ x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c y).left ∧ ∃ x₀ : Sp k₀ ⟶ B₀.left, x ≫ θ ≫ π₀ = spMap k₀.subtype ≫ x₀ := by
  first | exact @GlobalTheory.UCanon.PtsDescent.pulledObj_descends_with_points | exact GlobalTheory.UCanon.PtsDescent.pulledObj_descends_with_points | (intros; apply GlobalTheory.UCanon.PtsDescent.pulledObj_descends_with_points <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBaseValueMemDescendedPoint

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.BaseDescent

theorem ratHom_mem_of_isAlgClosed : ∀ (K : Type) [Field K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (F : IntermediateField ℚ ℂ), FiniteDimensional ℚ F → ∀ (g : F →+* K) (x : F), g x ∈ k₀ := by
  intro K _ k₀ hk₀ F hF g x
  haveI : CharZero K := (RingHom.charZero_iff g.injective).mp inferInstance
  haveI : CharZero k₀ := (RingHom.charZero_iff k₀.subtype.injective).mpr inferInstance
  have h1 : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have h2 : IsAlgebraic ℚ (g x) := by
    have := h1.algHom g.toRatAlgHom
    simpa using this
  have h3 : IsIntegral k₀ (g x) := (h2.extendScalars (algebraMap ℚ k₀).injective).isIntegral
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible h3)
  obtain ⟨y, hy⟩ := minpoly.mem_range_of_degree_eq_one k₀ (g x) hdeg
  rw [← hy]
  exact y.2

theorem pulledObj_descends : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (o' : LowObj D' c ((ev.comp iw).comp L.b)) (m₁ : ObjMap o' L.o (spMap (ev.comp iw))), (∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left)) (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' Q.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧ w.IsGen ∧ ∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) → ∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (π : o'.t.G.left ⟶ B₀.left), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback o'.t.G B₀ (spMap k₀.subtype) π ∧ LBIso o'.t.PP.L (M₀.pull π) ∧ ∀ y : L.D.X, ∃ x : Sp K ⟶ o'.t.G.left, x ≫ o'.t.G.hom = 𝟙 _ ∧ x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c y).left ∧ ∃ x₀ : Sp k₀ ⟶ B₀.left, x ≫ π = spMap k₀.subtype ≫ x₀ := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e hDiv K _ _ _ ev k₀ hk₀ o' m₁ hB
  obtain ⟨B₀, _, _, M₀, c₀, B', _, π₁, π₀, w, c', hab, hM, h1, h0, hw, hc⟩ := hB
  obtain ⟨θ, hθ, hLθ, hrel⟩ := GlobalTheory.T.pulledLowerObject_group_identification L Q oQ iw s ε e hDiv K ev o' m₁ B' π₁ h1
  obtain ⟨hpb, hL, hpts⟩ := GlobalTheory.T.pulledLowerObject_descends_with_points_subfield L Q oQ iw s ε e hDiv K ev k₀ hk₀ o' m₁ B₀ M₀ c₀ B' π₁ π₀ w c' θ hab hM h1 h0 hw hc hθ hLθ hrel
  exact ⟨B₀, inferInstance, inferInstance, M₀, θ ≫ π₀, hab, hM, hpb, hL, fun y => by
    obtain ⟨x, hx1, hx2, x₀, hx₀⟩ := hpts y
    exact ⟨x, hx1, hx2, x₀, by rw [← Category.assoc] at hx₀ ⊢; simpa using hx₀⟩⟩

end GlobalTheory.UCanon.BaseDescent

theorem GlobalTheory.UCanon.base_value_mem_of_descended_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left)) (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' Q.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧ w.IsGen ∧ ∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) → ∀ a, ev (iw a) ∈ k₀ := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e hDiv K _ _ ev k₀ hk₀ hB a
  let f : L.W →+* K := ev.comp iw
  have hF : ∀ x : c.F, (f.comp L.b) x ∈ k₀ := GlobalTheory.UCanon.BaseDescent.ratHom_mem_of_isAlgClosed K k₀ hk₀ c.F c.fin (f.comp L.b)
  haveI : CharZero K := (RingHom.charZero_iff (f.comp L.b).injective).mp inferInstance
  obtain ⟨o', ⟨m₁⟩⟩ := (GlobalTheory.T.shimuraObject_pullback_comp_cancel (D := D') (l := GlobalTheory.LowDat.lowLevel l)).1 (lowMap c L.b) L.o (spMap f)
    (lowMap c (f.comp L.b)) (by simp only [lowMap, spMap, ← Spec.map_comp]; rfl)
  obtain ⟨B₀, _, _, M₀, π, hab, hM, hpb, hL, hpts⟩ := GlobalTheory.UCanon.BaseDescent.pulledObj_descends L Q oQ iw s ε e hDiv K ev k₀ hk₀ o' m₁ hB
  choose x hx1 hx2 hx3 using hpts
  apply GlobalTheory.T.mem_subfield_of_forall_ringEquiv_fixed_of_isAlgClosed' K k₀ hk₀
  intro σ hσ
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_objMap_fixing_descended_points_subfield K k₀ hk₀ o' B₀ M₀ π hab hM hpb hL σ hσ
  have hcomp : ∀ g' : Sp K ⟶ Sp L.W, g' = spMap (σ : K →+* K) ≫ spMap f →
      ∃ k : ObjMap o' L.o g', k.toSABMap.φ = n.toSABMap.φ ≫ m₁.toSABMap.φ := by
    rintro g' rfl
    exact ((GlobalTheory.T.shimuraObject_pullback_comp_cancel (D := D') (l := GlobalTheory.LowDat.lowLevel l)).2 _ _ _ L.o o' o' (spMap f) (spMap (σ : K →+* K)) m₁).1 n
  obtain ⟨m₂, hm₂⟩ := hcomp (spMap ((σ : K →+* K).comp f)) (by simp only [spMap, ← Spec.map_comp]; rfl)
  have key := L.fineRed K f ((σ : K →+* K).comp f)
    (by ext y; simp only [RingHom.comp_apply]; exact (hσ _ (hF y)).symm) o' m₁ m₂ x hx2
    (fun y => by
      rw [hm₂, Category.assoc, ← Category.assoc (x y), hn (x y) (hx1 y) (hx3 y), Category.assoc, hx2 y]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, f]) hx1
  have := congrArg (fun g : L.W →+* K => g a) key
  simpa [f] using this.symm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBaseValueMemDescendedPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.canonicalFamily_base_value_mem_descended_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left)) (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' Q.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧ w.IsGen ∧ ∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) → ∀ a, ev (iw a) ∈ k₀ := by
  first | exact @GlobalTheory.UCanon.base_value_mem_of_descended_point | exact GlobalTheory.UCanon.base_value_mem_of_descended_point | (intros; apply GlobalTheory.UCanon.base_value_mem_of_descended_point <;> assumption)
end
end
