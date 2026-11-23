module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalAbelianPartValuesOfNormalForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusConstMul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationThetaSectionNonvanishingFibresStatement
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Parity
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorOfDualPointAdditiveLieCombStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleValueClassicalNormalForm
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalAbelianPartValuesOfNormalFormStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.exists_classical_abelianPart_values_of_normalForm : AllC fun {R} _ _ {D} _ {N} ν => ∀ (y : KeyIn R) (_ : y.P = D.P), HEq y.rig D.rig → (∃ th : D.P.L.Sec, HEq y.th th ∧ ∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i, ν.th.f (fun _ => i) = resG _ h (th.f i)) → ∀ (x : KeyIn ℂ) (hg : x.P.g = D.P.g) (hy : y.P.g = D.P.g) (u : HolUnif x.P.A x.P.L D.P.g) (τ : Matrix (Fin D.P.g) (Fin D.P.g) ℂ) (a b : Fin D.P.g → ℂ) (c : ℂ) (W : Fin D.P.g → Fin D.P.g → ℂ), KeyPB x y ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) → NF x hg u τ a b c W → ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), d.c = c ∧ ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)), (∀ i, HEq (y.v (i.cast hy.symm)) (vB i)) → ∀ i (bb : TE R ℂ ⟶ D.P.A), bb.left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ (vB i).left → ∀ W', IsD ν d W' bb ↔ W' = W i := by
  exact @GlobalTheory.MBLow.Cl.exists_ab_geo_of_nf
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalThetaNormalFormKeyDatum

section

@[expose] public section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.MBLow.Cl

namespace GlobalTheory.MBLow.Cl

theorem exists_NF : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g), ∃ u τ a b c W, NF x hg u τ a b c W := by
  intro g x hg
  subst hg
  obtain ⟨⟨τ, M, a, b, c, hab, hc, -, u, h₁, h₂, h₃, h₄, h₅, h₆⟩, -⟩ :=
    GlobalTheory.KeyNormalExists.exists_normalAt GlobalTheory.thetaUnifAV_all x
  exact ⟨u, τ, a, b, c, fun i => (2 * Real.pi * Complex.I : ℂ)⁻¹ • M i, h₁, h₂, hab.1, hab.2, hc, h₃, h₄, h₅, h₆⟩

end GlobalTheory.MBLow.Cl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalThetaNormalFormKeyDatumStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.exists_classicalThetaNormalForm_keyDatum : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g), ∃ u τ a b c W, NF x hg u τ a b c W := by
  first | exact @GlobalTheory.MBLow.Cl.exists_NF | exact GlobalTheory.MBLow.Cl.exists_NF | (intros; apply GlobalTheory.MBLow.Cl.exists_NF <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumBaseChangeLieBasisChangeDetPow

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.KeyLieChg

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m n : ℕ} (e : m = n)
    {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) : IsLieBasis (fun i : Fin m => v (i.cast e)) := by
  subst e
  exact hv

theorem lieComb_of_over {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {G : Over (Sp R)} [GrpObj G]
    {G' : Over (Sp R')} [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) φ) {n m : ℕ}
    (e : m = n) (M : Matrix (Fin n) (Fin n) R) (v v' : Fin n → (epsR R ⟶ G)) (u u' : Fin m → (epsR R' ⟶ G'))
    (hv : ∀ i, IsLieComb (M i) v (v' i))
    (huv : ∀ i, (u i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v (i.cast e)).left)
    (hu'v' : ∀ i, (u' i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v' (i.cast e)).left) (i : Fin m) :
    IsLieComb (fun j : Fin m => f (M (i.cast e) (j.cast e))) u (u' i) := by
  subst e
  exact (lieComb_baseChange R R' f G G' φ h m v (v' i) (M i) u (u' i) huv (hv i)).1 (hu'v' i)

theorem constFn_one {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    Geo.Tor.constFn p U (1 : R) = 1 := by
  simp [Geo.Tor.constFn]

theorem exists_keyPB_det : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (R : Type) [CommRing R] (y : KeyIn R) (x : KeyIn ℂ) (f : R →+* ℂ), KeyPB x y f → ∀ (v' : Fin y.P.g → (epsR R ⟶ y.P.A)) (hv' : IsLieBasis v') (M : Matrix (Fin y.P.g) (Fin y.P.g) R), (∀ i, IsLieComb (M i) y.v (v' i)) → ∃ x' : KeyIn ℂ, KeyPB x' ⟨y.P, y.g_pos, y.rig, y.rig_gen, y.th, y.th_ne, v', hv'⟩ f ∧ (κ ℂ x' : ℂ) = (M.map f).det ^ 4 * κ ℂ x := by
  intro κ hκ R _ y x f hxy v' hv' M hM
  obtain ⟨φ, he, w, hg, F, hp, hw, hrig, hsec, hF, hε, hlie⟩ := hxy
  have hF' : F = Chart.dualMapR f := KeyCancel.dualNumber_ringHom_ext
    (fun b => (hF b).trans (by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]))
    (hε.trans (by ext <;> simp [Chart.dualMapR]))
  subst hF'
  haveI := y.P.isAb.comm
  haveI := x.P.isAb.comm
  obtain ⟨u, hu, huv⟩ := exists_isLieBasis_baseChange R ℂ f y.P.A x.P.A φ hp y.P.isAb.smooth y.P.g v' hv'
  have hb : IsLieBasis (fun i : Fin x.P.g => u (i.cast hg)) := isLieBasis_cast hg hu
  refine ⟨⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, fun i => u (i.cast hg), hb⟩,
    ⟨φ, he, w, hg, Chart.dualMapR f, hp, hw, hrig, hsec, hF, hε, fun i => huv (i.cast hg)⟩, ?_⟩
  have hc := lieComb_of_over f hp hg M y.v v' x.v (fun i => u (i.cast hg)) hM hlie (fun i => huv (i.cast hg))
  have k := hκ ℂ x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis x.th x.th_ne (fun i => u (i.cast hg)) hb 1
    (fun i j => f (M (i.cast hg) (j.cast hg))) (fun i => by rw [constFn_one, _root_.one_mul]) hc
  have hd : (Matrix.of fun i j : Fin x.P.g => f (M (i.cast hg) (j.cast hg))).det = (M.map f).det :=
    Matrix.det_submatrix_equiv_self (finCongr hg) (M.map f)
  simp only [Nat.mul_one, one_pow, _root_.one_mul] at k
  rw [k]
  exact congrArg (· ^ 4 * (κ ℂ x : ℂ)) hd

end GlobalTheory.KeyLieChg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumBaseChangeLieBasisChangeDetPowStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.exists_keyDatumBaseChange_lieBasisChange_detPow : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (R : Type) [CommRing R] (y : KeyIn R) (x : KeyIn ℂ) (f : R →+* ℂ), KeyPB x y f → ∀ (v' : Fin y.P.g → (epsR R ⟶ y.P.A)) (hv' : IsLieBasis v') (M : Matrix (Fin y.P.g) (Fin y.P.g) R), (∀ i, IsLieComb (M i) y.v (v' i)) → ∃ x' : KeyIn ℂ, KeyPB x' ⟨y.P, y.g_pos, y.rig, y.rig_gen, y.th, y.th_ne, v', hv'⟩ f ∧ (κ ℂ x' : ℂ) = (M.map f).det ^ 4 * κ ℂ x := by
  first | exact @GlobalTheory.KeyLieChg.exists_keyPB_det | exact GlobalTheory.KeyLieChg.exists_keyPB_det | (intros; apply GlobalTheory.KeyLieChg.exists_keyPB_det <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleValueClassicalNormalFormStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.thetaKeyRule_value_classicalNormalForm : ∀ κ : Rule, Homog (fun _ => 1) κ → ThetaOne κ → ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (Mx : Matrix (Fin g) (Fin g) ℂ), NF x hg u τ a b c (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) → Mx.det ≠ 0 ∧ (κ ℂ x : ℂ) * c ^ 8 = Mx.det ^ 4 := by
  first | exact @GlobalTheory.MBLow.Cl.key_value_of_nf | exact GlobalTheory.MBLow.Cl.key_value_of_nf | (intros; apply GlobalTheory.MBLow.Cl.key_value_of_nf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalThetaDescriptionAbelianPart

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.AbCl

theorem exists_te {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] (v : epsR R ⟶ D.P.A) :
    ∃ bb : TE R ℂ ⟶ D.P.A, bb.left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ v.left := by
  refine ⟨Over.homMk (spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ v.left) ?_, rfl⟩
  rw [Category.assoc, Over.w v]
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ (Spec.map _ ≫ Spec.map _)
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem isD_unique {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    {ν : NumOf D ℂ N} {g : ℕ} {d : AB N.toNumB g} {b₀ b : TE R ℂ ⟶ D.P.A} {W₀ W₁ W₂ : Fin g → ℂ}
    (h₀ : ∀ W', IsD ν d W' b₀ ↔ W' = W₀) (h₁ : IsD ν d W₁ b) (h₂ : IsD ν d W₂ b) : W₁ = W₂ := by
  have key : IsD ν d (W₀ + (W₁ - W₂)) b₀ := by
    intro U f hU
    rw [(h₀ W₀).2 rfl U f hU]
    have e := congrArg TrivSqZeroExt.snd ((h₁ U f hU).symm.trans (h₂ U f hU))
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at e
    rw [map_add (f := _), map_sub, e, sub_self, add_zero]
  have := (h₀ _).1 key
  have h3 : W₁ - W₂ = 0 := by simpa using this
  exact sub_eq_zero.1 h3

theorem exists_ab_keyOK : ∀ κ : Rule, Rule4 κ → AllC fun {R} _ _ {D} _ {N} ν => 1 ≤ D.P.g → ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), KeyOK κ ν d := by
  intro κ hκ R _ _ _ _ D hψ hτ _ N ν hg
  obtain ⟨th, hth, hcomp⟩ := GlobalTheory.T.exists_degenerationThetaSection_nonvanishingFibres R D ℂ N ν
  obtain ⟨vB₀, hv₀⟩ := GlobalTheory.KeyPow.exists_isLieBasis D.P.A D.P.smoothDim
  let y₀ : KeyIn R := ⟨D.P, hg, D.rig, D.rig_gen, th, hth, vB₀, hv₀⟩
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.KeyPow.exists_keyPB y₀ ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))
  have hg₀ : x₀.P.g = D.P.g := by obtain ⟨_, _, _, hgg, _⟩ := hx₀; exact hgg
  obtain ⟨u, τ, a, b, c, W, hNF⟩ := GlobalTheory.T.exists_classicalThetaNormalForm_keyDatum D.P.g x₀ hg₀
  obtain ⟨d, G, hdc, huniq⟩ := GlobalTheory.T.exists_classical_abelianPart_values_of_normalForm R D hψ hτ N ν y₀ rfl HEq.rfl ⟨th, HEq.rfl, hcomp⟩ x₀ hg₀ rfl u τ a b c W hx₀ hNF
  refine ⟨d, G, ?_⟩
  intro vB bs MB k₀ hv hbs hIsD hBK
  have hM : ∀ i, ∃ c : Fin D.P.g → R, IsLieComb c vB₀ (vB i) := fun i => (hv₀.2 (vB i) (hv.1 i)).exists
  choose M' hMc using hM
  let M : Matrix (Fin D.P.g) (Fin D.P.g) R := Matrix.of M'
  obtain ⟨x, hKx, hκx⟩ := GlobalTheory.T.exists_keyDatumBaseChange_lieBasisChange_detPow κ hκ.1 R y₀ x₀ _ hx₀ vB hv M hMc
  have hk : (κ ℂ x : ℂ) = k₀ := hBK.2 hg D.rig_gen th hth hv x hcomp hKx
  choose b₀ hb₀ using fun j => exists_te (D := D) (vB₀ j)
  have hW : ∀ j, ∀ W', IsD ν d W' (b₀ j) ↔ W' = W j := fun j => huniq vB₀ (fun i => HEq.rfl) j (b₀ j) (hb₀ j)
  have hlin : ∀ i, IsD ν d (∑ j, (algebraMap (FractionRing R) ℂ) (algebraMap R (FractionRing R) (M i j)) • W j) (bs i) :=
    fun i => GlobalTheory.T.tangentVectorOfDualPoint_additive_lieComb R D N ν D.P.g d D.P.g (M i) vB₀ (vB i) W b₀ (bs i) hv₀.1 (hMc i) hb₀ (hbs i) (fun j => (hW j _).2 rfl)
  have hrow : ∀ i, (2 * Real.pi * Complex.I : ℂ)⁻¹ • MB i =
      ∑ j, (algebraMap (FractionRing R) ℂ) (algebraMap R (FractionRing R) (M i j)) • W j :=
    fun i => isD_unique (hW ⟨0, hg⟩) (hIsD i) (hlin i)
  have h2π : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let Mx : Matrix (Fin D.P.g) (Fin D.P.g) ℂ := Matrix.of fun j k => (2 * Real.pi * Complex.I : ℂ) * W j k
  have hNF' : NF x₀ hg₀ u τ a b c (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) := by
    have e : (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) = W := by
      funext j k
      show (2 * Real.pi * Complex.I : ℂ)⁻¹ * ((2 * Real.pi * Complex.I : ℂ) * W j k) = W j k
      rw [← _root_.mul_assoc, inv_mul_cancel₀ h2π, _root_.one_mul]
    rw [e]; exact hNF
  obtain ⟨hdet, hval⟩ := GlobalTheory.T.thetaKeyRule_value_classicalNormalForm κ hκ.1 hκ.2.2.1 D.P.g x₀ hg₀ u τ a b c Mx hNF'
  have hMB : MB = (M.map ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) * Mx := by
    ext i k
    have e := congrFun (hrow i) k
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at e
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply, Mx, Matrix.of_apply, RingHom.comp_apply]
    calc MB i k = (2 * Real.pi * Complex.I : ℂ) * ((2 * Real.pi * Complex.I : ℂ)⁻¹ * MB i k) := by field_simp
      _ = _ := by rw [e, Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by simp [M]; ring
  have hne : (κ ℂ x : ℂ) ≠ 0 := Units.ne_zero _
  rw [hMB, Matrix.det_mul]
  rw [hκx] at hk hne
  have hf : (M.map ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))).det ≠ 0 := by
    intro h0; apply hne; rw [h0]; ring
  refine ⟨mul_ne_zero hf hdet, ?_⟩
  rw [← hk, hdc, _root_.mul_assoc, hval]
  ring

end GlobalTheory.MBLow.AbCl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalThetaDescriptionAbelianPartStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.exists_classicalThetaDescription_abelianPart : ∀ κ : Rule, Rule4 κ → AllC fun {R} _ _ {D} _ {N} ν => 1 ≤ D.P.g → ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), KeyOK κ ν d := by
  first | exact @GlobalTheory.MBLow.AbCl.exists_ab_keyOK | exact GlobalTheory.MBLow.AbCl.exists_ab_keyOK | (intros; apply GlobalTheory.MBLow.AbCl.exists_ab_keyOK <;> assumption)
end
end
