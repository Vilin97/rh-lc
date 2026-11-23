module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyClosedRepresentsFixedPullbackHoms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyClosedRepresentsFixedPullbackHomsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

theorem _root_.GlobalTheory.T.exists_locallyClosed_represents_fixedPullback_homs : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Rigidified A L → Rigidified B M → RelAmple A L → 1 ≤ k → VeryAmpleAt B M k → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤) → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow B M (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow B M (k : ℤ) (baseAt t))), (∀ i, IsPullSec B M (k : ℤ) (homAt t ▷ B) (whiskerRight_snd (homAt t) B) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) = ⊤) → ∃ (N : ℕ) (X : Scheme.{0}) (c : X ⟶ Sp (MvPolynomial (Fin N) Rg)) (H : Scheme.{0}) (i : H ⟶ X)
    (AH : Over H) (_ : GrpObj AH) (BH : Over H) (_ : GrpObj BH) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left)
    (Φ : AH ⟶ BH), IsClosedImmersion c ∧ IsOpenImmersion i ∧
    IsGrpPullback AH A (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) φA ∧ IsGrpPullback BH B (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) φB ∧ IsMonHom Φ ∧
    LBIso (L.pull φA) ((M.pull φB).pull Φ.left) ∧
    ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : Sp R ⟶ H, h ≫ i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg))) = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left := by
  first | (exact @GlobalTheory.HomFixMat.exists_locClosed_homFix) | (exact GlobalTheory.HomFixMat.exists_locClosed_homFix) | (intros; apply GlobalTheory.HomFixMat.exists_locClosed_homFix  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepOfAffineTests

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.EndLoc.HomFixGlue

variable {S H : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {AH BH : Over H} [GrpObj AH] [GrpObj BH]

def IsSol (π : H ⟶ S) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH) {T : Scheme.{0}} (t : T ⟶ S)
    (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B')
    (h : T ⟶ H) : Prop :=
  h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
    IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left

def IsRestr {T U : Scheme.{0}} (g : U ⟶ T) {A' B' : Over T} [GrpObj A'] [GrpObj B'] (Φ' : A' ⟶ B')
    {A'' B'' : Over U} [GrpObj A''] [GrpObj B''] (Φ'' : A'' ⟶ B'') (ρA : A''.left ⟶ A'.left)
    (ρB : B''.left ⟶ B'.left) : Prop :=
  IsGrpPullback A'' A' g ρA ∧ IsGrpPullback B'' B' g ρB ∧ Φ''.left ≫ ρB = ρA ≫ Φ'.left

variable {π : H ⟶ S} {φA : AH.left ⟶ A.left} {φB : BH.left ⟶ B.left} {Φ : AH ⟶ BH}

theorem isRestr_pullback {T U : Scheme.{0}} (g : U ⟶ T) {A' B' : Over T} [GrpObj A'] [GrpObj B'] (Φ' : A' ⟶ B') :
    IsRestr g Φ' ((Over.pullback g).map Φ') (pullback.fst A'.hom g) (pullback.fst B'.hom g) :=
  ⟨isGrpPullback_pullback A' g, isGrpPullback_pullback B' g, pullback.lift_fst _ _ _⟩

theorem IsSol.restr {T U : Scheme.{0}} {t : T ⟶ S} {A' B' : Over T} [GrpObj A'] [GrpObj B']
    {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'} {h : T ⟶ H}
    (hs : IsSol π φA φB Φ t A' B' φA' φB' Φ' h) {g : U ⟶ T} {A'' B'' : Over U} [GrpObj A''] [GrpObj B'']
    {Φ'' : A'' ⟶ B''} {ρA : A''.left ⟶ A'.left} {ρB : B''.left ⟶ B'.left} (hr : IsRestr g Φ' Φ'' ρA ρB) :
    IsSol π φA φB Φ (g ≫ t) A'' B'' (ρA ≫ φA') (ρB ≫ φB') Φ'' (g ≫ h) := by
  obtain ⟨h1, ψA, ψB, pA, pB, eA, eB, eΦ⟩ := hs
  obtain ⟨rA, rB, rΦ⟩ := hr
  refine ⟨by rw [Category.assoc, h1], ρA ≫ ψA, ρB ≫ ψB, rA.comp pA, rB.comp pB, by rw [Category.assoc, eA],
    by rw [Category.assoc, eB], ?_⟩
  rw [← Category.assoc, rΦ, Category.assoc, eΦ, Category.assoc]

theorem IsRestr.factor {T U W : Scheme.{0}} {f : U ⟶ T} {k : W ⟶ U} {A' B' : Over T} [GrpObj A'] [GrpObj B']
    {Φ' : A' ⟶ B'} {Aα Bα : Over U} [GrpObj Aα] [GrpObj Bα] {Φα : Aα ⟶ Bα} {ρAα : Aα.left ⟶ A'.left}
    {ρBα : Bα.left ⟶ B'.left} (hα : IsRestr f Φ' Φα ρAα ρBα) {AW BW : Over W} [GrpObj AW] [GrpObj BW]
    {ΦW : AW ⟶ BW} {ρAW : AW.left ⟶ A'.left} {ρBW : BW.left ⟶ B'.left} (hW : IsRestr (k ≫ f) Φ' ΦW ρAW ρBW) :
    ∃ (σA : AW.left ⟶ Aα.left) (σB : BW.left ⟶ Bα.left), IsRestr k Φα ΦW σA σB ∧ σA ≫ ρAα = ρAW ∧
      σB ≫ ρBα = ρBW := by
  obtain ⟨aα, bα, cα⟩ := hα
  obtain ⟨aW, bW, cW⟩ := hW
  have wA : ρAW ≫ A'.hom = (AW.hom ≫ k) ≫ f := by rw [aW.1.w, Category.assoc]
  have wB : ρBW ≫ B'.hom = (BW.hom ≫ k) ≫ f := by rw [bW.1.w, Category.assoc]
  refine ⟨aα.1.lift _ _ wA, bα.1.lift _ _ wB, ⟨aα.cancel (aW.congr rfl (aα.1.lift_fst _ _ wA).symm)
    (aα.1.lift_snd _ _ wA), bα.cancel (bW.congr rfl (bα.1.lift_fst _ _ wB).symm) (bα.1.lift_snd _ _ wB), ?_⟩,
    aα.1.lift_fst _ _ wA, bα.1.lift_fst _ _ wB⟩
  apply bα.1.hom_ext
  · rw [Category.assoc, Category.assoc, bα.1.lift_fst, cW, cα, ← Category.assoc, aα.1.lift_fst]
  · rw [Category.assoc, Category.assoc, bα.1.lift_snd, Over.w Φα, aα.1.lift_snd, ← Category.assoc, Over.w ΦW]

theorem IsSol.pull {T U W : Scheme.{0}} {t : T ⟶ S} {f : U ⟶ T} {A' B' : Over T} [GrpObj A'] [GrpObj B']
    {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'} {Aα Bα : Over U} [GrpObj Aα] [GrpObj Bα]
    {Φα : Aα ⟶ Bα} {ρAα : Aα.left ⟶ A'.left} {ρBα : Bα.left ⟶ B'.left} (hα : IsRestr f Φ' Φα ρAα ρBα) {hα' : U ⟶ H}
    (hs : IsSol π φA φB Φ (f ≫ t) Aα Bα (ρAα ≫ φA') (ρBα ≫ φB') Φα hα') (k : W ⟶ U) {g : W ⟶ T} (hg : g = k ≫ f)
    {AW BW : Over W} [GrpObj AW] [GrpObj BW] {ΦW : AW ⟶ BW} {ρAW : AW.left ⟶ A'.left} {ρBW : BW.left ⟶ B'.left}
    (hW : IsRestr g Φ' ΦW ρAW ρBW) : IsSol π φA φB Φ (g ≫ t) AW BW (ρAW ≫ φA') (ρBW ≫ φB') ΦW (k ≫ hα') := by
  subst hg
  obtain ⟨σA, σB, hr, eA, eB⟩ := hα.factor hW
  have := hs.restr hr
  rw [← eA, ← eB]
  simp only [Category.assoc] at this ⊢
  exact this

theorem isSol_of_local (pbA : IsGrpPullback AH A π φA) (pbB : IsGrpPullback BH B π φB) {T : Scheme.{0}} {t : T ⟶ S}
    {A' B' : Over T} [GrpObj A'] [GrpObj B'] {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'}
    (hA : IsGrpPullback A' A t φA') (hB : IsGrpPullback B' B t φB') {h : T ⟶ H} (hh : h ≫ π = t) {Idx : Type}
    {U : Idx → Scheme.{0}} (f : ∀ i, U i ⟶ T) (Aα Bα : ∀ i, Over (U i)) [∀ i, GrpObj (Aα i)] [∀ i, GrpObj (Bα i)]
    (Φα : ∀ i, Aα i ⟶ Bα i) (ρA : ∀ i, (Aα i).left ⟶ A'.left) (ρB : ∀ i, (Bα i).left ⟶ B'.left)
    (hr : ∀ i, IsRestr (f i) Φ' (Φα i) (ρA i) (ρB i))
    (hs : ∀ i, IsSol π φA φB Φ (f i ≫ t) (Aα i) (Bα i) (ρA i ≫ φA') (ρB i ≫ φB') (Φα i) (f i ≫ h))
    (hepi : ∀ (u v : A'.left ⟶ BH.left), (∀ i, ρA i ≫ u = ρA i ≫ v) → u = v) :
    IsSol π φA φB Φ t A' B' φA' φB' Φ' h := by
  have wA : φA' ≫ A.hom = (A'.hom ≫ h) ≫ π := by rw [hA.1.w, Category.assoc, hh]
  have wB : φB' ≫ B.hom = (B'.hom ≫ h) ≫ π := by rw [hB.1.w, Category.assoc, hh]
  refine ⟨hh, pbA.1.lift _ _ wA, pbB.1.lift _ _ wB,
    pbA.cancel (hA.congr hh.symm (pbA.1.lift_fst _ _ wA).symm) (pbA.1.lift_snd _ _ wA),
    pbB.cancel (hB.congr hh.symm (pbB.1.lift_fst _ _ wB).symm) (pbB.1.lift_snd _ _ wB),
    pbA.1.lift_fst _ _ wA, pbB.1.lift_fst _ _ wB, hepi _ _ fun i => ?_⟩
  obtain ⟨-, ψA, ψB, pA, pB, eA, eB, eΦ⟩ := hs i
  obtain ⟨rA, rB, rΦ⟩ := hr i
  have hψA : ψA = ρA i ≫ pbA.1.lift _ _ wA := pbA.1.hom_ext (by rw [eA, Category.assoc, pbA.1.lift_fst])
    (by rw [pA.1.w, Category.assoc, pbA.1.lift_snd, ← Category.assoc (ρA i), rA.1.w, Category.assoc])
  have hψB : ψB = ρB i ≫ pbB.1.lift _ _ wB := pbB.1.hom_ext (by rw [eB, Category.assoc, pbB.1.lift_fst])
    (by rw [pB.1.w, Category.assoc, pbB.1.lift_snd, ← Category.assoc (ρB i), rB.1.w, Category.assoc])
  rw [← Category.assoc, ← rΦ, Category.assoc, ← hψB, eΦ, hψA, Category.assoc]

theorem lbIso_restr {XA XB A'l B'l A''l B''l : Scheme.{0}} {L : LB XA} {M : LB XB} (hL : L.IsLB) (hM : M.IsLB)
    {φA' : A'l ⟶ XA} {φB' : B'l ⟶ XB} {Φl : A'l ⟶ B'l} {ρA : A''l ⟶ A'l} {ρB : B''l ⟶ B'l} {Φ''l : A''l ⟶ B''l}
    (e : Φ''l ≫ ρB = ρA ≫ Φl) (iso : LBIso (L.pull φA') ((M.pull φB').pull Φl)) :
    LBIso (L.pull (ρA ≫ φA')) ((M.pull (ρB ≫ φB')).pull Φ''l) := by
  have hN := pull_isLB hM φB'
  have i1 : LBIso (L.pull (ρA ≫ φA')) ((M.pull φB').pull (Φ''l ≫ ρB)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp ρA rfl e iso
  have i2 : LBIso ((M.pull φB').pull (Φ''l ≫ ρB)) (((M.pull φB').pull ρB).pull Φ''l) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hN Φ''l rfl
  have i3 : LBIso (((M.pull φB').pull ρB).pull Φ''l) ((M.pull (ρB ≫ φB')).pull Φ''l) :=
    GlobalTheory.GenSpread.lbIso_pullback (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hM ρB rfl)) Φ''l
  exact LBIso.trans (pull_isLB hL _) (pull_isLB hN _) (pull_isLB (pull_isLB hM _) _) i1
    (LBIso.trans (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) (pull_isLB (pull_isLB hM _) _) i2 i3)

theorem rep_of_affine : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB →
  ∀ (H : Scheme.{0}) (π : H ⟶ S) (AH : Over H) [GrpObj AH] (BH : Over H) [GrpObj BH]
    (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH),
    IsGrpPullback AH A π φA → IsGrpPullback BH B π φB →
    (∀ (R : Type) [CommRing R] (t : Sp R ⟶ S) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : Sp R ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left) →
    ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : T ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left := by
  intro S A B _ _ L M hL hM H π AH _ BH _ φA φB Φ pbA pbB haff T t A' B' _ _ φA' φB' Φ' hA hB hΦ iso
  have key : ∀ (R : Type) [CommRing R] (f : Sp R ⟶ T), ∃! k : Sp R ⟶ H, IsSol π φA φB Φ (f ≫ t)
      ((Over.pullback f).obj A') ((Over.pullback f).obj B') (pullback.fst A'.hom f ≫ φA') (pullback.fst B'.hom f ≫ φB')
      ((Over.pullback f).map Φ') k := fun R _ f =>
    haff R (f ≫ t) ((Over.pullback f).obj A') ((Over.pullback f).obj B') _ _ ((Over.pullback f).map Φ')
      ((isRestr_pullback f Φ').1.comp hA) ((isRestr_pullback f Φ').2.1.comp hB) inferInstance
      (lbIso_restr hL hM (isRestr_pullback f Φ').2.2 iso)
  let 𝒜 := T.affineOpenCover
  let 𝒰 := 𝒜.openCover
  have hloc : ∀ i, ∃! k : 𝒰.X i ⟶ H, IsSol π φA φB Φ (𝒰.f i ≫ t) ((Over.pullback (𝒰.f i)).obj A')
      ((Over.pullback (𝒰.f i)).obj B') (pullback.fst A'.hom (𝒰.f i) ≫ φA') (pullback.fst B'.hom (𝒰.f i) ≫ φB')
      ((Over.pullback (𝒰.f i)).map Φ') k := fun i => key (𝒜.X i) (𝒰.f i)
  choose k hk hku using hloc
  have hagree : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ k i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ k j := by
    intro i j
    let 𝒲 := (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover
    refine 𝒲.openCover.hom_ext _ _ fun l => ?_
    let g : Sp (𝒲.X l) ⟶ T := (𝒲.openCover.f l ≫ pullback.fst _ _) ≫ 𝒰.f i
    have hg : g = (𝒲.openCover.f l ≫ pullback.snd _ _) ≫ 𝒰.f j :=
      (Category.assoc _ _ _).trans ((congrArg (𝒲.openCover.f l ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
    have hu := key (𝒲.X l) g
    rw [← Category.assoc, ← Category.assoc]
    exact hu.unique (IsSol.pull (isRestr_pullback _ Φ') (hk i) _ rfl (isRestr_pullback g Φ'))
      (IsSol.pull (isRestr_pullback _ Φ') (hk j) _ hg (isRestr_pullback g Φ'))
  let hg := 𝒰.glueMorphisms k hagree
  have hι : ∀ i, 𝒰.f i ≫ hg = k i := 𝒰.ι_glueMorphisms k hagree
  have hh : hg ≫ π = t := 𝒰.hom_ext _ _ fun i => by rw [← Category.assoc, hι]; exact (hk i).1
  have hsol : IsSol π φA φB Φ t A' B' φA' φB' Φ' hg :=
    isSol_of_local pbA pbB hA hB hh 𝒰.f (fun i => (Over.pullback (𝒰.f i)).obj A')
      (fun i => (Over.pullback (𝒰.f i)).obj B') (fun i => (Over.pullback (𝒰.f i)).map Φ')
      (fun i => pullback.fst A'.hom (𝒰.f i)) (fun i => pullback.fst B'.hom (𝒰.f i))
      (fun i => isRestr_pullback _ Φ') (fun i => by rw [hι]; exact hk i)
      (fun u v h => Scheme.Cover.hom_ext (Precoverage.ZeroHypercover.pullback₁ A'.hom 𝒰) u v h)
  refine ⟨hg, hsol, fun h' hs' => 𝒰.hom_ext _ _ fun i => ?_⟩
  rw [hι]
  exact hku i _ (IsSol.restr hs' (isRestr_pullback _ Φ'))

end GlobalTheory.EndLoc.HomFixGlue
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepOfAffineTestsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

theorem _root_.GlobalTheory.T.homFixedPullbackRep_of_affineTests : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB →
  ∀ (H : Scheme.{0}) (π : H ⟶ S) (AH : Over H) [GrpObj AH] (BH : Over H) [GrpObj BH]
    (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH),
    IsGrpPullback AH A π φA → IsGrpPullback BH B π φB →
    (∀ (R : Type) [CommRing R] (t : Sp R ⟶ S) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : Sp R ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left) →
    ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : T ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left := by
  first | exact @GlobalTheory.EndLoc.HomFixGlue.rep_of_affine | exact GlobalTheory.EndLoc.HomFixGlue.rep_of_affine | (intros; apply GlobalTheory.EndLoc.HomFixGlue.rep_of_affine <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedPullbackHomSchemeOfSectionBases

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixGlob


open TopologicalSpace in
theorem lc_props {Rg : Type} [CommRing Rg] [IsNoetherianRing Rg] {N : ℕ} {X H : Scheme.{0}}
    (c : X ⟶ Sp (MvPolynomial (Fin N) Rg)) (i : H ⟶ X) [IsClosedImmersion c] [IsOpenImmersion i] :
    QuasiCompact (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) ∧
    IsSeparated (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) ∧
    LocallyOfFiniteType (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) := by
  refine ⟨?_, inferInstance, ?_⟩
  · have h1 : NoetherianSpace (Sp (MvPolynomial (Fin N) Rg)) :=
      inferInstanceAs (NoetherianSpace (PrimeSpectrum (MvPolynomial (Fin N) Rg)))
    have h2 : NoetherianSpace H :=
      ((i ≫ c).isEmbedding).isInducing.noetherianSpace
    exact (quasiCompact_iff_compactSpace _).2 inferInstance
  · have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      show (algebraMap Rg (MvPolynomial (Fin N) Rg)).FiniteType
      exact RingHom.finiteType_algebraMap.2 inferInstance
    infer_instance

theorem exists_homFixRep_of_secBases : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Rigidified A L → Rigidified B M → RelAmple A L → 1 ≤ k → VeryAmpleAt B M k → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤) → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow B M (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow B M (k : ℤ) (baseAt t))), (∀ i, IsPullSec B M (k : ℤ) (homAt t ▷ B) (whiskerRight_snd (homAt t) B) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) = ⊤) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro Rg _ _ A B _ _ _ _ L M k hA hB hL hM rA rM aL hk vM bA bB
  obtain ⟨N, X, c, H, i, AH, _, BH, _, φA, φB, Φ, hc, hi, pA, pB, hΦ, hiso, hrep⟩ :=
    GlobalTheory.T.exists_locallyClosed_represents_fixedPullback_homs Rg A B L M k hA hB hL hM rA rM aL hk vM bA bB
  obtain ⟨q1, q2, q3⟩ := lc_props c i
  exact ⟨HomFixRep.mk H (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg))))
    AH BH φA φB pA pB Φ hΦ hiso (GlobalTheory.T.homFixedPullbackRep_of_affineTests _ A B L M hL hM H _ AH BH φA φB Φ pA pB hrep), q1, q2, q3⟩

end GlobalTheory.HomFixGlob
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedPullbackHomSchemeOfSectionBasesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

theorem _root_.GlobalTheory.T.exists_fixedPullbackHomScheme_of_sectionBases : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Rigidified A L → Rigidified B M → RelAmple A L → 1 ≤ k → VeryAmpleAt B M k → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤) → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow B M (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow B M (k : ℤ) (baseAt t))), (∀ i, IsPullSec B M (k : ℤ) (homAt t ▷ B) (whiskerRight_snd (homAt t) B) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) = ⊤) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  first | (exact @GlobalTheory.HomFixGlob.exists_homFixRep_of_secBases) | (exact GlobalTheory.HomFixGlob.exists_homFixRep_of_secBases) | (intros; apply GlobalTheory.HomFixGlob.exists_homFixRep_of_secBases  <;> assumption)
end
end
