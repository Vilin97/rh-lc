module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.CohHomNatCastZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.ExistsStalkFactor
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FrobNNat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FrobNSucc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.PowCardChi
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.PullbackFirstFiltrationPrimitive
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSpecFieldSmoothOfRelativeDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcObjIsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamVectorExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTowerAndHeightEqTwoDim
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeFrobeniusGrpSchemeCharPStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Root
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupTower

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB mulN)
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory.DeRham (spOver)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbelianTower

open TensorProduct
open scoped CategoryTheory.Obj

theorem exists_isUnivTorsion {O : Type} [CommRing O] {A : Over (Sp O)} [GrpObj A] (hA : IsAbelianScheme A) {g : ℕ}
    (hg : SmoothOfRelativeDimension g A.hom) {N : ℕ} (hN : N ≠ 0) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (y : SpAlg O R ⟶ A), Module.Finite O R ∧
      Module.Projective O R ∧ AbelianPDiv.IsUnivTorsion N y ∧
      ∀ q : PrimeSpectrum O, Module.rankAtStalk R q = N ^ (2 * g) := by
  obtain ⟨R, _, _, y, h1, h2, h⟩ := AbelianPDiv.exists_isPullback (N := N) hA (Nat.one_le_iff_ne_zero.2 hN)
  refine ⟨R, inferInstance, inferInstance, y, h1, h2, AbelianPDiv.isUnivTorsion_of_isPullback y h, fun q => ?_⟩
  let K := q.asIdeal.ResidueField
  obtain ⟨y', h'⟩ := AbelianPDiv.exists_isPullback_baseChange y h K
  let B : AV.AbVar K :=
    { X := (Over.pullback (spMap (algebraMap O K))).obj A
      ab := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback _ A hA
      dim := g
      smooth := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback A.hom (spMap (algebraMap O K))) hg }
  have hr := AVTower.finrank_torsion B hN (S := K ⊗[O] R) y' h'
  have hq : PrimeSpectrum.comap (algebraMap O K) ⊥ = q :=
    PrimeSpectrum.ext ((RingHom.ker_eq_comap_bot _).symm.trans (Ideal.ker_algebraMap_residueField _))
  rw [← hq, ← Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_finrank_of_free, hr]
  rfl

theorem exists_pDivGroup (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A]
    (hA : IsAbelianScheme A) (g : ℕ) (hg : SmoothOfRelativeDimension g A.hom) :
    ∃ (G : PDivGroup p O) (_ : G.TorsionTower A), G.height = 2 * g := by
  have := hA.comm
  choose R _ _ y h1 h2 h hr using fun n : ℕ => exists_isUnivTorsion (N := p ^ n) hA hg
    (pow_ne_zero _ hp.out.ne_zero)
  choose r r1 r2 r3 using fun n : ℕ => (h n).exists_res (h (n + 1))
    (by rw [pow_succ, pow_mul, (h n).1, one_pow])
  let G : PDivGroup p O :=
    { height := 2 * g
      A := R
      hopf := fun n => (h n).hopfAlgebra
      cocomm := fun n => (h n).isCocomm
      finite := h1
      projective := h2
      rank_eq := fun n q => (hr n q).trans (pow_mul _ _ _).symm
      res := r
      res_surjective := r1
      ker_res := r2 }
  exact ⟨G, {
    y := y
    mul := fun n B _ _ => (h n).mul_y
    inj := fun n B _ _ _ _ => (h n).inj
    surj := fun n B _ _ z hz => ((h n).2 B z hz).exists
    res := r3 }, rfl⟩

theorem exists_pDivGroup_tower : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (G : PDivGroup p R) (_ : G.TorsionTower A), G.height = 2 * g :=
  fun p _ R _ _ A _ g hA hg => exists_pDivGroup p R A hA g hg

end GlobalTheory.AbelianTower
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCorrFormPullTensorForm

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.CurveRootGeometry GlobalTheory.ConjSeq
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrobAdjoint

section Dual

open GlobalTheory.CechPic GlobalTheory.AbLaw

variable {S : Scheme.{0}} {A T Y : Over S} [GrpObj A] {P : LB (A ⊗ A).left}


end Dual

section Down

variable {R R' : Type} [CommRing R] [CommRing R'] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A']
  {σ : R →+* R'} {φ : A'.left ⟶ A.left}

def down (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x : Y ⟶ A') :
    Over.mk (Y.hom ≫ spMap σ) ⟶ A :=
  Over.homMk (x.left ≫ φ) (by simp [m.w])

theorem down_mul (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x y : Y ⟶ A') :
    down m (x * y) = down m x * down m y :=
  Over.OverMorphism.ext (m.mul Y x y (down m x) (down m y) rfl rfl).symm

end Down

section Frob

open GlobalTheory.CechPic GlobalTheory.AbLaw

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0) {A A₁ : Over (Sp R)} [GrpObj A] [GrpObj A₁]
  {π : A₁.left ⟶ A.left}

variable {G : PDivGroup p R} (t : G.TorsionTower A)

theorem absFrob_y (n : ℕ) : spMap ((absFrob hR G).app n).toRingHom ≫ (t.y n).left =
    (t.y n).left ≫ VB.frob A.left p (cast_left p R hR A) := by
  have h := natCast_eq_zero_of_algebra hR (G.A n)
  exact (congrArg (· ≫ (t.y n).left) (frob_sp p _ h (SS.FrobField.cast_zero_sp _ h)).symm).trans
    (VB.frob_naturality p _ (t.y n).left _)

theorem exists_tower (hπ : IsGrpPullback A₁ A (spMap (frobR p R hR)) π) :
    ∃ t₁ : (frobTwist hR G).TorsionTower A₁, ∀ n,
      spMap ((frobProj hR G).app n).toRingHom ≫ (t.y n).left = (t₁.y n).left ≫ π :=
  letI := (frobRing hR).toAlgebra
  ⟨t.baseChange (O' := R) hπ, t.toBase_y (O' := R) hπ⟩

theorem map_eq_verschiebung (t₁ : (frobTwist hR G).TorsionTower A₁)
    (ht : ∀ n, spMap ((frobProj hR G).app n).toRingHom ≫ (t.y n).left = (t₁.y n).left ≫ π)
    (F : A ⟶ A₁) (V : A₁ ⟶ A) [IsMonHom F] [IsMonHom V]
    (hF : F.left ≫ π = VB.frob A.left p (cast_left p R hR A)) (hV : F ≫ V = 𝟙 A ^ p) :
    t₁.map t V = verschiebung hR G := by
  have e : t.map t₁ F = relFrob hR G := frobTwist_hom_ext hR fun n a ↦
    (t₁.semiOf_semiOf t t (s' := SemiHom.ofHom (t.map t₁ F)) (s'' := absFrob hR G) (ψ := F.left) ht
      (fun n ↦ congrArg Over.Hom.left (t.map_y t₁ F n)) (fun n ↦ by rw [hF]; exact absFrob_y hR t n) n a).symm.trans
      ((absFrob_app hR G n a).trans (relFrob_app_frobProj hR n a).symm)
  have : IsMonHom (𝟙 A ^ p) := hV ▸ inferInstance
  refine eq_verschiebung_of_relFrob_comp hR ?_
  rw [← e, ← t.map_comp, t.map_congr t hV, t.map_pow_id]

end Frob

section Pairing

open GlobalTheory.CatCoh GlobalTheory.AbLaw

variable {R R' : Type} [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'} {S S' : Scheme.{0}}
  {κ : DividedPowers I} {t : S ⟶ Sp R} {A B : Over S} [GrpObj A] [GrpObj B]
  {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'} {A' B' : Over S'} [GrpObj A'] [GrpObj B']

end Pairing

end GlobalTheory.FrobAdjoint
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.RankV

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.FrobAdjoint

theorem UpperTheory.Gal.Ord.rankV :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (σ : k →+* k) (V : A.left ⟶ A.left) (m : SMor A σ V), (∀ x, σ x ^ p = x) →
      GlobalTheory.VB.frob A.left p (cast_left p k hk A) ≫ V = ((𝟙 A) ^ p : A ⟶ A).left → ∀ y, m.pull y = 0 → ∃ z, frobDR p k hk A z = y := by
  intro p _ k _ _ hk A _ _ hA σ V m hσ hV y hy
  obtain ⟨e, he, -⟩ := GlobalTheory.deRhamVectorExtension p
  have hn : IsNilpotent (p : k) := ⟨1, by rw [pow_one, hk]⟩
  obtain ⟨g, hg⟩ : ∃ g, SmoothOfRelativeDimension g A.hom := GlobalTheory.T.abelianScheme_specField_smoothOfRelativeDimension k A hA
  obtain ⟨G, t, -⟩ := GlobalTheory.AbelianTower.exists_pDivGroup_tower p k hn A g hA hg
  let A₁ := (Over.pullback (spMap (frobR p k hk))).obj A
  have hπ : IsGrpPullback A₁ A _ _ := isGrpPullback_pullback A (spMap (frobR p k hk))
  have hA₁ : IsAbelianScheme A₁ := isAbelianScheme_pullback_obj _ A hA
  obtain ⟨F, hFm, hF⟩ := GlobalTheory.T.exists_relativeFrobenius_grpScheme_charP p k hk A A₁ _ hπ
  obtain ⟨t₁, ht⟩ := exists_tower hk t hπ
  have mπ := grpMor_of_isGrpPullback hπ
  have hid : (frobR p k hk).comp σ = RingHom.id k := RingHom.ext fun x => (frobR_apply p k hk _).trans (hσ x)
  have hb : spMap (frobR p k hk) ≫ spMap σ = 𝟙 _ := by rw [← GlobalTheory.Cris.spMap_comp, hid, GlobalTheory.Cris.spMap_id]
  have mc := m.comp mπ
  let V₁ : A₁ ⟶ A := Over.homMk (_ ≫ V) (mc.w.trans (by rw [hb, Category.comp_id]))
  have hm : IsMonHom V₁ := isMonHom_of_mul _ fun T x x' => by
    have hw : (T.hom ≫ spMap (frobR p k hk) ≫ spMap σ) = T.hom := by rw [hb, Category.comp_id]
    let j : Over.mk (T.hom ≫ spMap (frobR p k hk) ≫ spMap σ) ⟶ T := Over.homMk (𝟙 _) (by simpa using hw.symm)
    have h := mc.mul T x x' (j ≫ x ≫ V₁) (j ≫ x' ≫ V₁) (by simp [j, V₁]) (by simp [j, V₁])
    rw [← MonObj.comp_mul] at h
    refine Over.OverMorphism.ext ?_
    simpa [j, V₁] using h.symm
  have hFV : F ≫ V₁ = 𝟙 A ^ p := Over.OverMorphism.ext (by
    change F.left ≫ _ ≫ V = _
    rw [← Category.assoc, hF, hV])
  have h0 : primPull (dp0 k) (𝟙 _) V₁ y = 0 := by
    have h1 := GrpMor.pull_pull m mπ (homMor (dp0 k) (𝟙 _) V₁) (fun r => RingHom.congr_fun hid r) rfl y
    rw [hy, map_zero] at h1
    exact h1.symm
  have h1 : rigExtMap (verschiebung hk G) (e hn hA t y) = 0 := by
    rw [← map_eq_verschiebung hk t t₁ ht F V₁ hF hFV, ← he.primPull hn hA₁ hA t₁ t, h0, (e hn hA₁ t₁).map_zero]
  obtain ⟨-, -, -, -, -, h2, h3⟩ := rigExt_field_of_charP p k hk G
  have h4 : e hn hA t y ∈ Submodule.span k (Set.range (absFrob hk G).rig) := h3 ▸ h2 ▸ h1
  have h5 : ∀ z, e hn hA t (frobDR p k hk A z) = (absFrob hk G).rig (e hn hA t z) := fun z => by
    rw [(t.eq_semiOf_iff t (frobMor p k hk A (cast_left p k hk A)) (absFrob hk G)).2 (absFrob_y hk t)]
    exact he hn hn hA hA t t _ z
  have h6 : ∀ u ∈ Submodule.span k (Set.range (absFrob hk G).rig), ∃ z, e hn hA t (frobDR p k hk A z) = u := fun u hu => by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨v, rfl⟩ := hu
      exact ⟨(e hn hA t).symm v, by rw [h5]; exact congrArg (absFrob hk G).rig ((e hn hA t).apply_symm_apply v)⟩
    | zero => exact ⟨0, by rw [map_zero (f := frobDR p k hk A), (e hn hA t).map_zero]⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨b, rfl⟩ := hv
      exact ⟨a + b, by rw [map_add (f := _), map_add (f := _)]⟩
    | smul l u _ hu =>
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨r, rfl⟩ := IsAlgClosed.exists_pow_nat_eq l (Fact.out : p.Prime).pos
      exact ⟨r • a, by rw [map_smulₛₗ, map_smul, frobR_apply]⟩
  obtain ⟨z, hz⟩ := h6 _ h4
  exact ⟨z, (e hn hA t).injective hz⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Point

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

theorem UpperTheory.Gal.Ord.point :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      IsWOrd o w (𝟙 (Sp k)) ∨ NOo hk o π := by
  intro p _ D R _ b N hN hNp hm k _ _ hk β o i w f hw hnorm hf π
  rcases cnt p D R b N hN hNp hm k hk β o i w f hw hnorm hf π with h | ⟨v, hv1, hv2, hv3⟩
  · exact Or.inl h
  right
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (R := k) (Fact.out : p.Prime)).mpr hk
  have hL := lin p D R b N hN hNp hm k hk β o i w f hw hnorm hf π
  obtain ⟨σ, ψ, hσ, m, hψ⟩ := va p D R b N hN hNp hm k hk β o i w f hw hnorm hf π
  have hH := hasse p D R b N hN hNp hm k hk β o i w f hw hnorm hf π σ hσ ψ m hψ v hv1 hv2 hv3
  have hpow : ∀ n : ℕ, o.act.act ((n : D.O)) = 𝟙 o.A ^ n := by
    intro n
    induction n with
    | zero =>
      rw [Nat.cast_zero, pow_zero]
      have h0 := o.act.add 0 0
      rw [add_zero] at h0
      simpa using h0
    | succ n ih => rw [Nat.cast_succ, o.act.add, ih, o.act.one, pow_succ]
  haveI hmon : IsMonHom (o.act.act ((p : D.O))) := o.act.hom _
  have hp0 : ∀ x : ↥(primDR o.A), primPull (dp0 k) (𝟙 (Sp k)) (o.act.act ((p : D.O))) x = 0 := by
    intro x
    have h1 : ((p : D.O)) = (algebraMap (𝓞 D.F) D.O) (p : 𝓞 D.F) := by simp
    have h2 : ∀ n : ℕ, coh o (n : 𝓞 D.F) = (n : k) • (1 : Module.End k ↥(primDR o.A)) := by
      intro n
      induction n with
      | zero =>
        have h0 := hL.add 0 0
        simp only [add_zero] at h0
        simpa using h0
      | succ n ih => rw [Nat.cast_succ, hL.add, ih, hL.one, Nat.cast_succ, add_smul, one_smul]
    have h3 := congrArg (fun φ : Module.End k ↥(primDR o.A) => φ x) (h2 p)
    simp only [hk, zero_smul] at h3
    have h4 : coh o (p : 𝓞 D.F) x = primPull (dp0 k) (𝟙 (Sp k)) (o.act.act ((p : D.O))) x := by
      simp only [coh, h1]
    rw [← h4]
    exact h3
  have mp : SMor o.A (RingHom.id k) (Over.Hom.left (o.act.act ((p : D.O)))) := by
    have := homMor (dp0 k) (𝟙 (Sp k)) (o.act.act ((p : D.O)))
    simpa [SMor, spMap_id] using this
  obtain ⟨τ, V, hτ, n, hτp, hV⟩ := root p k hk o.A o.ab (RingHom.id k) Function.bijective_id _ mp (by
    intro x _
    exact hp0 x)
  have hV' := hV
  rw [hpow] at hV'
  have hrel := rel p D R b N hN hNp hm k hk β o i w f hw hnorm hf π σ τ ψ V m n hψ hV'
  have hrk := rankV p k hk o.A o.ab τ V n (fun x => by simpa using hτp x) hV'
  have hcard : Nat.card (𝓞 D.F ⧸ w) = p ^ f := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]; exact hnorm
  intro x hx
  obtain ⟨z, hz⟩ := alg1 p k (𝓞 D.F) w f hf hcard π (β.comp (b.t i)) ↥(primDR o.A) (coh o) (PrimitiveSubmodule o.A)
    (frobDR p k hk o.A).toAddMonoidHom hL (GrpMor.pull n).toAddMonoidHom (GrpMor.pull m).toAddMonoidHom
    (fun y hy => hrk y hy) (fun y => hrel y) (fun x hx => hH x hx) x hx
  exact Submodule.subset_span ⟨z, hz.symm⟩
end
end
