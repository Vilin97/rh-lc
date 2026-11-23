module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PsiWeightZeroLinearCombination
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartIdentificationsAgreeConstantTangentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyPeriodsInCoordinatesStatement
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Localization.Integer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantUnitPulledBackBundleAutomorphismStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBaseIdentityAlongMorphismStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRigidOfBase

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TautRigid

def dlog (k : Type) [Field k] : (DualNumber k)ˣ →* Multiplicative k where
  toFun x := Multiplicative.ofAdd ((x : DualNumber k).snd / (x : DualNumber k).fst)
  map_one' := by simp
  map_mul' x y := by
    have fne : ∀ x : (DualNumber k)ˣ, (x : DualNumber k).fst ≠ 0 := fun x h => by
      have := congrArg TrivSqZeroExt.fst x.mul_inv
      rw [TrivSqZeroExt.fst_mul, h, zero_mul, TrivSqZeroExt.fst_one] at this
      exact zero_ne_one this
    have hx := fne x
    have hy := fne y
    rw [← ofAdd_add]
    congr 1
    simp only [Units.val_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    field_simp
    ring

theorem fst_ne_zero {k : Type} [Field k] (x : (DualNumber k)ˣ) : (x : DualNumber k).fst ≠ 0 := fun h => by
  have := congrArg TrivSqZeroExt.fst x.mul_inv
  rw [TrivSqZeroExt.fst_mul, h, zero_mul, TrivSqZeroExt.fst_one] at this
  exact zero_ne_one this

theorem dlog_apply {k : Type} [Field k] (x : (DualNumber k)ˣ) :
    Multiplicative.toAdd (dlog k x) = (x : DualNumber k).snd / (x : DualNumber k).fst := rfl

def onePlus {k : Type} [Field k] (s : k) : (DualNumber k)ˣ where
  val := 1 + TrivSqZeroExt.inr s
  inv := 1 - TrivSqZeroExt.inr s
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

theorem dlog_onePlus {k : Type} [Field k] (s : k) : Multiplicative.toAdd (dlog k (onePlus s)) = s := by
  rw [dlog_apply]; simp [onePlus]

end GlobalTheory.TautRigid

namespace GlobalTheory.TautRigid

open GlobalTheory.RigChart GlobalTheory.ToricData

variable {R : Type} [CommRing R] [IsDomain R]

def lamC (Q : DegPre R) {k : Type} [Field k] {B' : Scheme.{0}} {π₁ π₂ : B' ⟶ Q.P.A.left}
    (w : LB.Iso (Q.P.L.pull π₁) (Q.P.L.pull π₂)) (c' : Q.X → (Sp (DualNumber k) ⟶ B')) (y z : Q.X)
    (zz : Sp (DualNumber k)) (J : (Sp (DualNumber k) ⟶ Q.P.A.left) → Q.P.L.ι) : ((Sp (DualNumber k)).presheaf.stalk zz)ˣ :=
  gm (c' (y + z)) zz _ (w.s (fun _ => J (c' (y + z) ≫ π₂), fun _ => J (c' (y + z) ≫ π₁))) *
    (gm (c' y) zz _ (w.s (fun _ => J (c' y ≫ π₂), fun _ => J (c' y ≫ π₁))))⁻¹ *
    (gm (c' z) zz _ (w.s (fun _ => J (c' z ≫ π₂), fun _ => J (c' z ≫ π₁))))⁻¹ *
    gm (c' 0) zz _ (w.s (fun _ => J (c' 0 ≫ π₂), fun _ => J (c' 0 ≫ π₁)))

def AbConst (Q : DegPre R) {k : Type} [Field k] (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B']
    (π₁ π₂ : B'.left ⟶ Q.P.A.left) (w : LB.Iso (Q.P.L.pull π₁) (Q.P.L.pull π₂)) (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)) :
    Prop :=
  IsGrpPullback B' Q.P.A (spMap ρ) π₁ ∧ IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ ∧
    (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k),
      x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) ∧
    w.IsGen ∧ (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (Q.c y).left ∧
      c' y ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left)

end GlobalTheory.TautRigid
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfIsPartOfBasisBalFormsOfMem

section

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM

namespace GlobalTheory.PolFan

theorem eq_zero_of_linearIndependent_int_rat {Y ι : Type} [Fintype ι] {f : ι → Y → ℤ}
    (hf : LinearIndependent ℤ f) (q : ι → ℚ) (hq : ∀ y, ∑ i, q i * (f i y : ℚ) = 0) : q = 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
  have hb' : ∀ i, ∃ r : ℤ, (r : ℚ) = ((b : ℤ) : ℚ) * q i := fun i => by
    obtain ⟨r, hr⟩ := hb i
    exact ⟨r, by simpa [Algebra.smul_def] using hr⟩
  choose n hn using hb'
  have h0 : n = 0 := by
    rw [Fintype.linearIndependent_iff] at hf
    funext i
    refine hf n ?_ i
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have : ((∑ i, n i * f i y : ℤ) : ℚ) = ((b : ℤ) : ℚ) * ∑ i, q i * (f i y : ℚ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hn i]; ring
    rw [hq y, mul_zero] at this
    exact_mod_cast this
  funext i
  have hbne : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero b
  have h := hn i
  rw [h0] at h
  simp only [Pi.zero_apply, Int.cast_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hbne

theorem eq_zero_of_linearIndependent_int {Y ι : Type} [Fintype ι] {f : ι → Y → ℤ}
    (hf : LinearIndependent ℤ f) (k : Type) [Field k] [CharZero k] (a : ι → k)
    (ha : ∀ y, ∑ i, a i * (f i y : k) = 0) : a = 0 := by
  classical
  let B := Module.Basis.ofVectorSpace ℚ k
  have key : ∀ j, (fun i => B.coord j (a i)) = 0 := fun j =>
    eq_zero_of_linearIndependent_int_rat hf _ fun y => by
      have h := congrArg (B.coord j) (ha y)

      rw [map_sum, map_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm (a i), ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  funext i
  apply B.repr.injective
  ext j
  have := congrFun (key j) i
  simpa [Module.Basis.coord_apply] using this

end GlobalTheory.PolFan

namespace GlobalTheory.PolFan

end GlobalTheory.PolFan
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfGrpPullback

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GrpPullAb

theorem isAbelianScheme_of_grpPullback :
    ∀ {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
      (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → IsAbelianScheme G → IsAbelianScheme G' :=
  fun _ h hG => GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG h

end GlobalTheory.GrpPullAb
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfGrpPullbackStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isAbelianScheme_of_grpPullback' : ∀ {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → IsAbelianScheme G → IsAbelianScheme G' := by
  first | exact @GlobalTheory.GrpPullAb.isAbelianScheme_of_grpPullback | exact GlobalTheory.GrpPullAb.isAbelianScheme_of_grpPullback | (intros; apply GlobalTheory.GrpPullAb.isAbelianScheme_of_grpPullback <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusRigiditySndEqZeroCanonicalChart

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorRigid

open GlobalTheory.RigChart GlobalTheory.ToricData

theorem commGroup_fourfold_cancellation {G : Type*} [CommGroup G] (a1 a2 a3 a4 b1 b2 b3 b4 U V : G) :
    a1 * a2⁻¹ * a3⁻¹ * a4 * V = ((b1⁻¹ * (U * a1)) * (b2⁻¹ * (U * a2))⁻¹ * (b3⁻¹ * (U * a3))⁻¹ * (b4⁻¹ * (U * a4))) *
      (b1 * b2⁻¹ * b3⁻¹ * b4 * V) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem val_const_of_fromBase : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (τ₀ : Gens Q) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* R), FromBase Q τ₀ ιb → ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k), ρ.comp ιb = GlobalTheory.RigChart.constHom (ρ.comp ιb) → ∀ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ Q.P.A.left) (w : LB.Iso (Q.P.L.pull π₁) (Q.P.L.pull π₂)) (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)), GlobalTheory.TautRigid.AbConst Q ρ B' π₁ π₂ w c' → ∀ (y z : Q.X) (zz : Sp (DualNumber k)) (J : (Sp (DualNumber k) ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L zz J → val (τ₀ y z) (spMap ρ) zz J = GlobalTheory.TautRigid.lamC Q w c' y z zz J * val (τ₀ y z) (spMap (GlobalTheory.RigChart.constHom ρ)) zz J := by
  intro R _ _ Q τ₀ W₀ _ ιb hFB k _ ρ hρ B' iG π₁ π₂ w c' hA y z zz J hJ
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hA
  obtain ⟨B₀, iB₀, M₀, c₀, τ₁, β, wF, hB₀, hM₀, hβ, hwF, hc₀, hτ₁, hpt⟩ := GlobalTheory.T.fromBase_identity_along_morphism Q τ₀ ιb hFB
  have hπ : π₁ ≫ β = π₂ ≫ β := GlobalTheory.T.abelianPart_identifications_agree_constant_tangent Q ιb B₀ β hβ k ρ hρ B' π₁ π₂ h₁ h₂ h₃
  have hB'ab : IsAbelianScheme B' := GlobalTheory.T.isAbelianScheme_of_grpPullback' π₁ h₁ Q.P.isAb
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_constant_unit_pulledBack_bundle_automorphism (DualNumber k) B' hB'ab Q.P.L M₀ β wF π₁ π₂ w Q.P.isLB hM₀ hwF h₄ hπ
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.UU.exists_good_pt hM₀ zz
  have e1 := hpt _ (spMap ρ) y z zz J J₀ hJ hJ₀
  have e2 := hpt _ (spMap (GlobalTheory.RigChart.constHom ρ)) y z zz J J₀ hJ hJ₀
  have hιb : spMap ρ ≫ spMap ιb = spMap (GlobalTheory.RigChart.constHom ρ) ≫ spMap ιb := by
    have h' : (GlobalTheory.RigChart.constHom ρ).comp ιb = GlobalTheory.RigChart.constHom (ρ.comp ιb) := by
      exact RingHom.ext fun x => rfl
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom (hρ.trans h'.symm)
  rw [hιb] at e1
  have q1 : ∀ x, spMap ρ ≫ cpt Q x = c' x ≫ π₁ := fun x => ((h₅ x).2.1).symm
  have q2 : ∀ x, spMap (GlobalTheory.RigChart.constHom ρ) ≫ cpt Q x = c' x ≫ π₂ := fun x => ((h₅ x).2.2).symm
  have q1' : ∀ x, spMap ρ ≫ cpt Q x ≫ β = c' x ≫ π₁ ≫ β := fun x => by
    rw [← Category.assoc, q1, Category.assoc]
  have q2' : ∀ x, spMap (GlobalTheory.RigChart.constHom ρ) ≫ cpt Q x ≫ β = c' x ≫ π₂ ≫ β := fun x => by
    rw [← Category.assoc, q2, Category.assoc]
  rw [q1', q1', q1', q1', q1, q1, q1, q1] at e1
  rw [q2', q2', q2', q2', q2, q2, q2, q2] at e2
  have hW : ∀ x, gm (c' x) zz _ (w.s (fun _ => J (c' x ≫ π₂), fun _ => J (c' x ≫ π₁))) =
      (gm (c' x ≫ π₂) zz _ (wF.s (fun _ => J₀ (c' x ≫ π₂ ≫ β), J (c' x ≫ π₂))))⁻¹ *
        (gm (𝟙 _) zz ⊤ (unitOn u) * gm (c' x ≫ π₁) zz _ (wF.s (fun _ => J₀ (c' x ≫ π₁ ≫ β), J (c' x ≫ π₁)))) :=
    fun x => eq_inv_mul_of_mul_eq (hu (c' x) (h₅ x).1 zz J J₀ hJ hJ₀)
  unfold GlobalTheory.TautRigid.lamC
  rw [e1, e2, hW, hW, hW, hW]
  exact commGroup_fourfold_cancellation _ _ _ _ _ _ _ _ _ _

theorem snd_eq_zero_of_isConstAlong : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k) (a : Fin C.m → k), GlobalTheory.RigChart.IsConstAlong C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ρ a → ρ.comp (Cn.ψ.comp MvPolynomial.C) = GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C)) → ∀ j, (ρ (Cn.ψ (MvPolynomial.X (.inr j)))).snd = 0 := by
  classical
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hB C Cn k _ ρ a hC hconst j
  obtain ⟨ε', τ₀, hε', hFB, hτ⟩ := GlobalTheory.T.canonicalFamily_periods_in_coordinates Xo c φ R hB C Cn
  obtain ⟨B', iG, π₁, π₂, w, c', h₁, h₂, h₃, h₄, h₅, h₆⟩ := hC
  have hA : GlobalTheory.TautRigid.AbConst C.P.D.toPre ρ B' π₁ π₂ w c' := ⟨h₁, h₂, h₃, h₄, h₅⟩
  have hB1 := val_const_of_fromBase C.P.D.toPre τ₀ (Cn.ψ.comp MvPolynomial.C) hFB k ρ hconst B' iG π₁ π₂ w c' hA
  haveI : CharZero k := by
    let f : c.F →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom.comp (ρ.comp C.b)
    exact (f.charZero_iff f.injective).1 inferInstance
  set M : ℕ := l.M' with hMdef
  have hM : 0 < M := level_pos l
  let Q := C.P.D.toPre
  let u : Fin Cn.N → Rˣ := fun j => (Cn.tor j).unit
  have hu : ∀ j, (u j : R) = Cn.ψ (MvPolynomial.X (.inr j)) := fun j => IsUnit.unit_spec _
  let δ : Fin C.m → LinearMap.BilinForm ℤ Q.X := C.δ
  let ε : Fin Cn.N → LinearMap.BilinForm ℤ Q.X := fun j => (ε' (.inr j) : LinearMap.BilinForm ℤ Q.X)
  have hδ : ∀ i, (ε' (.inl i) : LinearMap.BilinForm ℤ Q.X) = C.δ i := fun i => by
    rw [hε', Cn.cone i]
  have hli : LinearIndependent ℤ (Sum.elim δ ε) := by
    have h0 : LinearIndependent ℤ (fun κ => (ε' κ : LinearMap.BilinForm ℤ Q.X)) :=
      ε'.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)
    have hEq : Sum.elim δ ε = fun κ => (ε' κ : LinearMap.BilinForm ℤ Q.X) := by
      funext κ; rcases κ with i | i
      · exact (hδ i).symm
      · rfl
    rw [hEq]; exact h0
  have key : ∀ y z, ∑ j, ((M : ℤ) * ε j y z) • Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map ρ.toMonoidHom (u j))) =
      ∑ i, a i * ((((M : ℤ) • δ i) y z : ℤ) : k) := by
    intro y z
    set v : Rˣ := ∏ j, u j ^ ((M : ℤ) * ε j y z) with hvdef
    let f : Rˣ →* (FractionRing R)ˣ := Units.map (algebraMap R (FractionRing R)).toMonoidHom
    obtain ⟨hg, kk, hk, hv⟩ := hτ y z
    have hU' : GlobalTheory.RigChart.IsUnitTau Q C.s (fun i => (M : ℤ) • C.δ i) y z (GlobalTheory.UU.scaleGen (unitOn v) (τ₀ y z)) := by
      refine ⟨GlobalTheory.UU.scaleGen_isGen _ hg, kk * (f v)⁻¹, ?_, fun zz J hJ => ?_⟩
      · have hfv : ((f v : (FractionRing R)ˣ) : FractionRing R) =
            ∏ j, algebraMap R (FractionRing R) (u j : R) ^ ((M : ℤ) * ε j y z) := by
          simp only [f, v, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.coe_map,
            MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
        have hne : ((f v : (FractionRing R)ˣ) : FractionRing R) ≠ 0 := (f v).ne_zero
        rw [Units.val_mul, hk, Units.val_inv_eq_inv_val, Fin.prod_univ_add]
        simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, LinearMap.smul_apply, smul_eq_mul,
          Cn.bd, hδ, ← hu]
        rw [← hfv, mul_inv_cancel_right₀ hne]
      · have e : gm (toUnit (TK R)).left zz ⊤ (unitOn v) = gm (𝟙 (TK R).left) zz ⊤ (unitOn (f v)) := by
          rw [GlobalTheory.UU.gm_top]
          exact congrArg _ (pullTop_unitOn (algebraMap R (FractionRing R)) _)
        rw [hv zz J hJ, GlobalTheory.UU.val_scaleGen _ _ _ hJ, e, ← _root_.mul_assoc, ← map_mul, ← unitOn_mul,
          inv_mul_cancel_right]
    set s : k := ∑ i, a i * ((((M : ℤ) • δ i) y z : ℤ) : k) with hs
    have hE : ∀ zz : Sp (DualNumber k), gm (𝟙 _) zz ⊤ (unitOn (Units.map ρ.toMonoidHom v)) =
        gm (𝟙 _) zz ⊤ (unitOn (GlobalTheory.TautRigid.onePlus s * Units.map (GlobalTheory.RigChart.constHom ρ).toMonoidHom v)) := by
      intro zz
      obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt C.P.D.toPre.P.isLB zz
      have hp := h₆ y z _ hU' (GlobalTheory.TautRigid.onePlus s) rfl zz J hJ
      have hb := hB1 y z zz J hJ
      have e₁ : gm (spMap ρ) zz ⊤ (unitOn v) = gm (𝟙 _) zz ⊤ (unitOn (Units.map ρ.toMonoidHom v)) := by
        rw [GlobalTheory.UU.gm_top]; exact congrArg _ (pullTop_unitOn ρ v)
      have e₂ : gm (spMap (GlobalTheory.RigChart.constHom ρ)) zz ⊤ (unitOn v) =
          gm (𝟙 _) zz ⊤ (unitOn (Units.map (GlobalTheory.RigChart.constHom ρ).toMonoidHom v)) := by
        rw [GlobalTheory.UU.gm_top]; exact congrArg _ (pullTop_unitOn (GlobalTheory.RigChart.constHom ρ) v)
      rw [GlobalTheory.UU.val_scaleGen _ _ _ hJ, GlobalTheory.UU.val_scaleGen _ _ _ hJ, e₁, e₂, hb] at hp
      change _ = GlobalTheory.TautRigid.lamC Q w c' y z zz J * _ * _ at hp
      rw [unitOn_mul, map_mul]
      exact mul_right_cancel (hp.trans ((congrArg (· * _) (_root_.mul_comm _ _)).trans (mul_mul_mul_comm _ _ _ _)))
    have hv2 := unitOn_inj.1 (unit_ext fun x _ => hE x)
    have h3 := congrArg (fun x => Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k x)) hv2
    rw [map_mul, toAdd_mul, GlobalTheory.TautRigid.dlog_onePlus] at h3
    have hc0 : Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map (GlobalTheory.RigChart.constHom ρ).toMonoidHom v)) = 0 := by
      have hs0 : ∀ r : R, (GlobalTheory.RigChart.constHom ρ r).snd = 0 := fun r => by
        simp only [GlobalTheory.RigChart.constHom, RingHom.comp_apply]
        rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]
      rw [GlobalTheory.TautRigid.dlog_apply, Units.coe_map]
      erw [hs0, zero_div]
    rw [hc0, add_zero] at h3
    rw [← h3, hvdef, map_prod, map_prod, toAdd_prod]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zpow, map_zpow, toAdd_zpow]
  set L : Fin Cn.N → k := fun j => Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map ρ.toMonoidHom (u j))) with hL
  let F : Fin C.m ⊕ Fin Cn.N → Q.X × Q.X → ℤ := fun κ p => Sum.elim δ ε κ p.1 p.2
  have hF : LinearIndependent ℤ F := by
    let e : LinearMap.BilinForm ℤ Q.X →ₗ[ℤ] (Q.X × Q.X → ℤ) :=
      { toFun := fun β p => β p.1 p.2
        map_add' := fun β β' => by funext p; rfl
        map_smul' := fun n β => by funext p; rfl }
    have he : LinearMap.ker e = ⊥ := LinearMap.ker_eq_bot.mpr fun β β' h =>
      LinearMap.ext fun y => LinearMap.ext fun z => congrFun h (y, z)
    have hEq : F = e ∘ Sum.elim δ ε := by
      funext κ p
      rcases κ with i | j <;> rfl
    rw [hEq]
    exact hli.map' e he
  have hz := GlobalTheory.PolFan.eq_zero_of_linearIndependent_int hF k
    (Sum.elim (fun i => a i * (M : k)) (fun j => -(L j * (M : k)))) fun p => by
      rw [Fintype.sum_sum_type]
      have hk := key p.1 p.2
      simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, LinearMap.smul_apply, smul_eq_mul] at hk
      simp only [Sum.elim_inl, Sum.elim_inr, F]
      have e1 : ∑ i, a i * (M : k) * ((δ i p.1 p.2 : ℤ) : k) = ∑ i, a i * ((M : k) * ((δ i p.1 p.2 : ℤ) : k)) :=
        Finset.sum_congr rfl fun i _ => by ring
      have e2 : ∑ j, -(L j * (M : k)) * ((ε j p.1 p.2 : ℤ) : k) =
          -∑ j, (M : k) * ((ε j p.1 p.2 : ℤ) : k) * L j := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e1, e2, ← hk]
      ring
  have h1 := congrFun hz (Sum.inr j)
  simp only [Sum.elim_inr, Pi.zero_apply, neg_eq_zero, mul_eq_zero, Nat.cast_eq_zero] at h1
  have hLj : Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map ρ.toMonoidHom (u j))) = 0 := h1.resolve_right hM.ne'
  rw [GlobalTheory.TautRigid.dlog_apply, Units.coe_map] at hLj
  have := (div_eq_zero_iff.1 hLj).resolve_right (by
    have := GlobalTheory.TautRigid.fst_ne_zero (Units.map ρ.toMonoidHom (u j))
    rwa [Units.coe_map] at this)
  rw [← hu]
  exact this

end GlobalTheory.TorRigid
end
end
end
