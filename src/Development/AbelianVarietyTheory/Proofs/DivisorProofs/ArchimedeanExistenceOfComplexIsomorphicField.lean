module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationValuesTransportFieldIsoStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianKeyValueAdaptedVectorsFieldIso

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TrAdapt

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) :=
  RingHom.ext fun z => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F]
  [Algebra (FractionRing R) F'] (e : F ≃+* F')
  (he : ∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x)

include he in
theorem toF_comp : (e : F →+* F').comp (toF R F) = toF R F' :=
  RingHom.ext fun r => by simp [toF, he]


include he in
def rhoE : TE R F' ⟶ TE R F :=
  Over.homMk (spMap (dualMap (e : F →+* F'))) (by
    show spMap (dualMap (e : F →+* F')) ≫ spMap (algebraMap F (DualNumber F)) ≫
        spMap (algebraMap (FractionRing R) F) ≫ spMap (algebraMap R (FractionRing R)) =
      spMap (algebraMap F' (DualNumber F')) ≫ spMap (algebraMap (FractionRing R) F') ≫
        spMap (algebraMap R (FractionRing R))
    simp only [← spMap_comp']
    apply congrArg spMap
    ext r <;> simp [dualMap, he, TrivSqZeroExt.algebraMap_eq_inl])


include he in
def sigE : TF (R := R) F' ⟶ TF (R := R) F :=
  Over.homMk (spMap (e : F →+* F')) (by
    show spMap (e : F →+* F') ≫ spMap (algebraMap (FractionRing R) F) ≫ spMap (algebraMap R (FractionRing R)) =
      spMap (algebraMap (FractionRing R) F') ≫ spMap (algebraMap R (FractionRing R))
    simp only [← spMap_comp']
    congr 1
    exact RingHom.ext fun r => by simp [he])

theorem rhoE_left : (rhoE e he).left = spMap (dualMap (e : F →+* F')) := rfl

theorem sigE_left : (sigE e he).left = spMap (e : F →+* F') := rfl

theorem red_comm : (sigE e he).left ≫ redE F = redE F' ≫ (rhoE e he).left := by
  rw [sigE_left, rhoE_left]
  show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
  rw [← spMap_comp', ← spMap_comp']
  congr 1
  exact RingHom.ext fun z => by simp [dualMap]

include he in
theorem bKey_map (κ : Rule) (hκ : Funct κ) [CharZero F] [CharZero F'] (D : DegPre R) {N : NumD F} (ν : NumOf D F N)
    {N' : NumD F'} (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N') (hh : ∀ x, I.h x = 1) (hl : I.lam = 1)
    (hth : ν'.th = ν.th) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (k : F) (hk : BKey κ ν vB k) :
    BKey κ ν' vB (e k) := by
  refine ⟨fun h0 => ?_, fun hg hr th hth' hv x' hres hpb => ?_⟩
  · have h1 := I.th_eq 1
    rw [map_one, hh, hl] at h1
    rw [h1, Units.val_mul, Units.val_one, _root_.one_mul, _root_.one_mul, ← map_pow, RingEquiv.coe_toRingHom, ← map_mul, hk.1 h0,
      map_one]
  · obtain ⟨x, hx⟩ := GlobalTheory.KeyPow.exists_keyPB x' (e.symm : F' →+* F)
    have hc : (e.symm : F' →+* F).comp ((algebraMap (FractionRing R) F').comp (algebraMap R (FractionRing R))) =
        (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) :=
      RingHom.ext fun r => by simp [← he]
    have hpb' := GlobalTheory.keyPB_trans _ _ _ _ x' x _ _ hpb hx
    rw [hc] at hpb'
    have hkx := hk.2 hg hr th hth' hv x (by rw [← hth]; exact hres) hpb'
    have hf := hκ F' F (e.symm : F' →+* F) x' x hx
    rw [hkx] at hf
    rw [hf]
    simp

include he in
theorem adapted_map [CharZero F] [CharZero F'] (D : DegPre R) {N : NumD F} (ν : NumOf D F N)
    {N' : NumD F'} (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N') (heX : ∀ χ, ν'.eX (I.e χ) = ν.eX χ)
    (hpull : ∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' →
      ∀ χ, vE (gm'.s χ) (𝟙 _) ν'.J = dualMap (e : F →+* F') (vE (gm.s χ) (𝟙 _) ν.J))
    (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r)
    (gm : Fin g → GtPt D (TE R F)) (had : Adapted ν vB bX σ gm) :
    ∃ gm' : Fin g → GtPt D (TE R F'), (∀ j, GtPt.IsPull (spMap (dualMap (e : F →+* F'))) (gm j) (gm' j)) ∧
      Adapted ν' vB (bX.map I.e.toIntLinearEquiv) σ gm' := by
  obtain ⟨hv, hz, hb, ht⟩ := had
  choose gm' hgm' using fun j => GlobalTheory.ConstLie.exists_isPullGt (rhoE e he) (gm j)
  have hzT : rhoE e he ≫ DegPre.zeroT D (TE R F) = DegPre.zeroT D (TE R F') := by
    simp only [DegPre.zeroT, ← Category.assoc, comp_toUnit]
  have hzF : sigE e he ≫ DegPre.zeroF D F = DegPre.zeroF D F' := by
    simp only [DegPre.zeroF, ← Category.assoc, comp_toUnit]
  refine ⟨gm', hgm', hv, fun j => ?_, fun i => ?_, fun l => ⟨?_, fun χ => ?_⟩⟩
  · obtain ⟨o, ho, hpo⟩ := hz j
    obtain ⟨o', ho'⟩ := GlobalTheory.ConstLie.exists_isPullGt (sigE e he)
      (⟨o.b, o.s, o.isGen, o.s_zero, o.mult⟩ : GtPt D (TF (R := R) F))
    refine ⟨⟨o'.b, o'.s, o'.isGen, o'.s_zero, o'.mult⟩, ⟨?_, fun χ => ?_⟩, ?_, fun χ => ?_⟩
    · exact Over.OverMorphism.ext (ho'.1.trans ((congrArg (fun q => (sigE e he).left ≫ q.left) ho.1).trans
        (congrArg Over.Hom.left hzF)))
    · refine corr_of_val D.P.isLB fun y J hJ => ?_
      exact ((val_corr hJ (ho'.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (ho.2 χ) _).trans
        (val_one _)))).trans (val_one _).symm
    · refine ho'.1.trans ((congrArg ((sigE e he).left ≫ ·) hpo.1).trans ?_)
      rw [← Category.assoc, red_comm, Category.assoc, ← (hgm' j).1]
    · refine corr_of_val D.P.isLB fun y J hJ => ?_
      refine ((val_corr hJ (ho'.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (hpo.2 χ) _).trans
        (val_pull hJ _ _ _)))).trans (Eq.trans ?_ ((val_pull hJ _ _ _).trans ((val_corr hJ ((hgm' j).2 χ) _).trans
        (val_pull hJ _ _ _))).symm)
      rw [Category.id_comp, Category.id_comp, red_comm]
  · refine (hgm' _).1.trans ?_
    rw [hb i, ← Category.assoc, rhoE_left, ← spMap_comp', dualMap_comp, toF_comp e he]
  · exact Over.OverMorphism.ext ((hgm' _).1.trans ((congrArg (fun q => (rhoE e he).left ≫ q.left) (ht l).1).trans
      (congrArg Over.Hom.left hzT)))
  · obtain ⟨χ₀, rfl⟩ := I.e.surjective χ
    rw [heX, hpull _ _ (hgm' _), (ht l).2 χ₀, Module.Basis.map_repr]
    simp [dualMap]

end GlobalTheory.MBLow.TrAdapt

theorem GlobalTheory.MBLow.bKey_adapted_map : ∀ κ : Rule, Funct κ → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F] [Field F'] [CharZero F] [CharZero F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (e : F ≃+* F'), (∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x) → ∀ (N : NumD F) (ν : NumOf D F N) (N' : NumD F') (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N'), (∀ x, I.h x = 1) → I.lam = 1 → (∀ χ, ν'.eX (I.e χ) = ν.eX χ) → ν'.th = ν.th → (∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' → ∀ χ, vE (gm'.s χ) (𝟙 _) ν'.J = dualMap (e : F →+* F') (vE (gm.s χ) (𝟙 _) ν.J)) → ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)), (∀ k, BKey κ ν vB k → BKey κ ν' vB (e k)) ∧ ∀ (r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r) (gm : Fin g → GtPt D (TE R F)), Adapted ν vB bX σ gm → ∃ gm' : Fin g → GtPt D (TE R F'), (∀ j, GtPt.IsPull (spMap (dualMap (e : F →+* F'))) (gm j) (gm' j)) ∧ Adapted ν' vB (bX.map I.e.toIntLinearEquiv) σ gm' := by
  intro κ hκ R _ _ D F F' _ _ _ _ _ _ e he N ν N' ν' I hh hl heX hth hpull vB
  exact ⟨fun k hk => GlobalTheory.MBLow.TrAdapt.bKey_map e he κ hκ D ν ν' I hh hl hth vB k hk,
    fun r g bX σ gm had => GlobalTheory.MBLow.TrAdapt.adapted_map e he D ν ν' I heX hpull vB r g bX σ gm had⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianKeyValueAdaptedVectorsFieldIsoStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianKeyValue_adaptedVectors_fieldIso : ∀ κ : Rule, Funct κ → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F] [Field F'] [CharZero F] [CharZero F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (e : F ≃+* F'), (∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x) → ∀ (N : NumD F) (ν : NumOf D F N) (N' : NumD F') (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N'), (∀ x, I.h x = 1) → I.lam = 1 → (∀ χ, ν'.eX (I.e χ) = ν.eX χ) → ν'.th = ν.th → (∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' → ∀ χ, vE (gm'.s χ) (𝟙 _) ν'.J = dualMap (e : F →+* F') (vE (gm.s χ) (𝟙 _) ν.J)) → ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)), (∀ k, BKey κ ν vB k → BKey κ ν' vB (e k)) ∧ ∀ (r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r) (gm : Fin g → GtPt D (TE R F)), Adapted ν vB bX σ gm → ∃ gm' : Fin g → GtPt D (TE R F'), (∀ j, GtPt.IsPull (spMap (dualMap (e : F →+* F'))) (gm j) (gm' j)) ∧ Adapted ν' vB (bX.map I.e.toIntLinearEquiv) σ gm' := by
  exact @GlobalTheory.MBLow.bKey_adapted_map
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataValuesIsoTransportFormsLevelsFam

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow.TrNum

section
variable {O O' : Type} [CommRing O] [CommRing O'] {f : O →+* O'} {N : NumD O} {N' : NumD O'} (I : NumD.Hom f N N')

theorem img_mul (g h : N.Gt) : I.img (g * h) = I.img g * I.img h :=
  ((I.rel_iff _ _).1 ((I.rel_img g).mul (I.rel_img h))).symm

theorem img_pow (g : N.Gt) (n : ℕ) : I.img (g ^ n) = I.img g ^ n :=
  ((I.rel_iff _ _).1 ((I.rel_img g).pow n)).symm

theorem img_io (y : N.X) : I.img (N.io y) = N'.io (I.e y) :=
  ((I.rel_iff _ _).1 (I.rel_io y)).symm

def imgQ {k : ℕ} (p : N.QT k) : N'.QT k :=
  ⟨(Multiplicative.ofAdd (I.e p.1.1.toAdd), I.img p.1.2), by
    have h : p.1.2 ^ k = N.io p.1.1.toAdd := p.2
    change I.img p.1.2 ^ k = N'.io (I.e p.1.1.toAdd)
    rw [← img_pow, h, img_io]⟩

theorem imgQ_mul {k : ℕ} (p q : N.QT k) : imgQ I (p * q) = imgQ I p * imgQ I q :=
  Subtype.ext (Prod.ext (congrArg Multiplicative.ofAdd (map_add I.e p.1.1.toAdd q.1.1.toAdd)) (img_mul I p.1.2 q.1.2))

theorem qEq_imgQ (hi : Function.Injective I.img) {k : ℕ} (p q : N.QT k) :
    N'.QEq (imgQ I p) (imgQ I q) ↔ N.QEq p q := by
  constructor
  · rintro ⟨z, h1, h2⟩
    obtain ⟨z, rfl⟩ := I.e.surjective z
    refine ⟨z, I.e.injective ?_, hi ?_⟩
    · rw [map_add (f := _), map_nsmul]; exact h1
    · rw [img_mul, img_io]; exact h2
  · rintro ⟨z, h1, h2⟩
    refine ⟨I.e z, ?_, ?_⟩
    · change I.e q.1.1.toAdd = I.e p.1.1.toAdd + k • I.e z
      rw [h1, map_add (f := _), map_nsmul]
    · change I.img q.1.2 = I.img p.1.2 * N'.io (I.e z)
      rw [h2, img_mul, img_io]

theorem imgQ_surjective (hi : Function.Bijective I.img) {k : ℕ} : Function.Surjective (imgQ I (k := k)) := by
  intro p'
  obtain ⟨g, hg⟩ := hi.2 p'.1.2
  have h : p'.1.2 ^ k = N'.io p'.1.1.toAdd := p'.2
  refine ⟨⟨(Multiplicative.ofAdd (I.e.symm p'.1.1.toAdd), g), ?_⟩, Subtype.ext (Prod.ext ?_ hg)⟩
  · change g ^ k = N.io (I.e.symm p'.1.1.toAdd)
    apply hi.1
    rw [img_pow, img_io, hg, h, AddEquiv.apply_symm_apply]
  · change Multiplicative.ofAdd (I.e (I.e.symm p'.1.1.toAdd)) = p'.1.1
    rw [AddEquiv.apply_symm_apply]; rfl

def formImg {k : ℕ} (β : N.Form k) : N'.Form k where
  be := β.be.compl₁₂ I.e.symm.toIntLinearEquiv.toLinearMap I.e.symm.toIntLinearEquiv.toLinearMap
  symm y z := β.symm _ _
  pos y hy := β.pos (I.e.symm y) (fun h => hy (by simpa using congrArg I.e h))
  dvd y z := β.dvd _ _

end

variable {F F' : Type} [Field F] [Field F'] {e : F ≃+* F'} {N : NumD F} {N' : NumD F'} (I : NumD.Hom (e : F →+* F') N N')

theorem units_bij (e : F ≃+* F') : Function.Bijective (Units.map (e : F →+* F').toMonoidHom) :=
  (Units.mapEquiv e.toMulEquiv).bijective

theorem img_bijective (hφ : Function.Bijective I.φ) (hh : ∀ x, I.h x = 1) : Function.Bijective I.img := by
  have hu := units_bij e
  constructor
  · intro g g' h
    have a := I.rel_img g
    have b := I.rel_img g'
    rw [h] at a
    refine NumD.Gt.ext (hφ.1 (a.1.symm.trans b.1)) (funext fun χ => hu.1 ?_)
    have a2 := a.2 χ
    have b2 := b.2 χ
    simp only [hh, _root_.mul_one] at a2 b2
    exact a2.symm.trans b2
  · intro g'
    obtain ⟨b, hb⟩ := hφ.2 g'.b
    choose s hs using fun χ => hu.2 (g'.s (I.e χ))
    refine ⟨⟨b, s, fun χ χ' => hu.1 ?_⟩, ((I.rel_iff _ _).1 ⟨hb.symm, fun χ => ?_⟩).symm⟩
    · have a := I.θ_eq (N.c χ) (N.c χ') b
      simp only [hh, _root_.mul_one] at a
      rw [map_mul, map_mul, hs, hs, hs, ← a, ← I.c_eq, ← I.c_eq, hb, map_add (f := _)]
      exact g'.mult _ _
    · simp only [hh, _root_.mul_one]
      exact (hs χ).symm

theorem transport : ∀ (F F' : Type) [Field F] [Field F'] (e : F ≃+* F') (N : NumD F) (N' : NumD F') (I : NumD.Hom (e : F →+* F') N N'), Function.Bijective I.φ → (∀ x, I.h x = 1) → I.lam = 1 → (∀ (k : ℕ) (β : N.Form k), ∃ β' : N'.Form k, ∀ a b, β'.be (I.e a) (I.e b) = β.be a b) ∧ ∀ (m g : ℕ), Odd m → ∀ (ζ : Fˣ) (q : (Fin (2 * g) → ZMod (m ^ 2)) → N.QT (m ^ 2)), QLevel N g (m ^ 2) ζ q → ∃ q' : (Fin (2 * g) → ZMod (m ^ 2)) → N'.QT (m ^ 2), QLevel N' g (m ^ 2) (Units.map (e : F →+* F').toMonoidHom ζ) q' ∧ ∀ a (f : N.X → N.A → F) (f' : N'.X → N'.A → F'), IsEvFam N m (q a) f → (∀ α x, f' (I.e α) (I.φ x) = e (f α x)) → IsEvFam N' m (q' a) f' := by
  intro F F' _ _ e N N' I hφ hh hl
  have hi := img_bijective I hφ hh
  have hu := units_bij e
  refine ⟨fun k β => ⟨formImg I β, fun a b => ?_⟩, fun m g hm ζ q hq => ⟨fun a => imgQ I (q a), ?_, ?_⟩⟩
  · change β.be (I.e.symm (I.e a)) (I.e.symm (I.e b)) = _
    rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hq
    refine ⟨h1.map_of_injective hu.1, fun a b => ?_, fun a b h => h3 a b ((qEq_imgQ I hi.1 _ _).1 h), fun p => ?_,
      fun i j => ?_⟩
    · rw [← imgQ_mul]; exact (qEq_imgQ I hi.1 _ _).2 (h2 a b)
    · obtain ⟨p, rfl⟩ := imgQ_surjective I hi p
      obtain ⟨a, ha⟩ := h4 p
      exact ⟨a, (qEq_imgQ I hi.1 _ _).2 ha⟩
    · rw [I.wp_eq (q (Pi.single i 1)) (q (Pi.single j 1)) _ _ rfl (I.rel_img _) rfl (I.rel_img _), h5, map_zpow]
  · rintro a f f' ⟨h1, h2⟩ hf
    refine ⟨fun h' χ => ?_, fun α hα x => ?_⟩
    · obtain ⟨h, rfl⟩ := hi.2 h'
      obtain ⟨χ, rfl⟩ := I.e.surjective χ
      rw [I.evT_eq hm (q a) _ rfl (I.rel_img _) χ h _ (I.rel_img _), ← h1]
      have r := (I.rel_img h).2 ((q a).1.1.toAdd + m • χ)
      simp only [hh, _root_.mul_one] at r
      have t : (imgQ I (q a)).1.1.toAdd + m • I.e χ = I.e ((q a).1.1.toAdd + m • χ) := by
        rw [map_add (f := _), map_nsmul]; rfl
      rw [t, r, (I.rel_img h).1, hf, hl, hh]
      simp
    · obtain ⟨α, rfl⟩ := I.e.surjective α
      obtain ⟨x, rfl⟩ := hφ.2 x
      rw [hf, h2 α (fun χ h => hα (I.e χ) (by rw [h, map_add (f := _), map_nsmul]; rfl)), map_zero]

end GlobalTheory.MBLow.TrNum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataValuesIsoTransportFormsLevelsFamStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.degenerationDataValuesIso_transport_formsLevelsFamilies : ∀ (F F' : Type) [Field F] [Field F'] (e : F ≃+* F') (N : NumD F) (N' : NumD F') (I : NumD.Hom (e : F →+* F') N N'), Function.Bijective I.φ → (∀ x, I.h x = 1) → I.lam = 1 → (∀ (k : ℕ) (β : N.Form k), ∃ β' : N'.Form k, ∀ a b, β'.be (I.e a) (I.e b) = β.be a b) ∧ ∀ (m g : ℕ), Odd m → ∀ (ζ : Fˣ) (q : (Fin (2 * g) → ZMod (m ^ 2)) → N.QT (m ^ 2)), QLevel N g (m ^ 2) ζ q → ∃ q' : (Fin (2 * g) → ZMod (m ^ 2)) → N'.QT (m ^ 2), QLevel N' g (m ^ 2) (Units.map (e : F →+* F').toMonoidHom ζ) q' ∧ ∀ a (f : N.X → N.A → F) (f' : N'.X → N'.A → F'), IsEvFam N m (q a) f → (∀ α x, f' (I.e α) (I.φ x) = e (f α x)) → IsEvFam N' m (q' a) f' := by
  first | exact @GlobalTheory.MBLow.TrNum.transport | exact GlobalTheory.MBLow.TrNum.transport | (intros; apply GlobalTheory.MBLow.TrNum.transport <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanExistenceOfComplexIsomorphicField

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem archF_of_arch : ∀ κ : Rule, Funct κ → Arch κ → ArchF κ := by
  intro κ hF hA R _ _ _ _ D hP hT F _ _ _ e N ν g r m k hg hm hk β ζ q hq s hs vB bX σ gm hAd k₀ hK
  letI : Algebra (FractionRing R) ℂ := ((e : F →+* ℂ).comp (algebraMap (FractionRing R) F)).toAlgebra
  have he : ∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) ℂ x := fun _ => rfl
  obtain ⟨N', ν', I, hb, hh, hl, heX, hth, hrg, hvE, hfam⟩ := GlobalTheory.T.degenerationValues_transport_fieldIso R D F ℂ e he N ν
  obtain ⟨hform, hlev⟩ := GlobalTheory.T.degenerationDataValuesIso_transport_formsLevelsFamilies F ℂ e N N' I hb hh hl
  obtain ⟨β', hβ⟩ := hform k β
  obtain ⟨q', hq', hev⟩ := hlev m g hm ζ q hq
  obtain ⟨hBK, hadp⟩ := GlobalTheory.T.abelianKeyValue_adaptedVectors_fieldIso κ hF R D F ℂ e he N ν N' ν' I hh hl heX hth hvE vB
  obtain ⟨gm', hpull, hAd'⟩ := hadp r g bX σ gm hAd
  choose s' hs1 hs2 using fun a => hfam (m ^ 2) (s a)
  have hs' : ∀ a, ∃ f, ν'.FamV (s' a) f ∧ IsEvFam N' m (q' a) f := by
    intro a
    obtain ⟨f, hf, hf2⟩ := hs a
    obtain ⟨f', hf', hff⟩ := hs1 a f hf
    exact ⟨f', hf', hev a f f' hf2 hff⟩
  obtain ⟨ε, hε, H⟩ := hA R D hP hT N' ν' g r m k hg hm hk β' _ q' hq' s' hs' vB _ σ gm' hAd' _ (hBK k₀ hK)
  have h1 : ∀ a j α, (jc ν' (s' a) (gm' j) (I.e α)).fst = e (jc ν (s a) (gm j) α).fst := by
    intro a j α
    rw [hs2 a _ _ (hpull j) α]
    simp [dualMap]
  have h2 : ∀ a j α, (jc ν' (s' a) (gm' j) (I.e α)).snd = e (jc ν (s a) (gm j) α).snd := by
    intro a j α
    rw [hs2 a _ _ (hpull j) α]
    simp [dualMap]
  refine ⟨ε, hε, fun u hu hu' => ?_⟩
  obtain ⟨hsum, x₀, hg₀, lev₀, ϑ, hϑ, hJ, hκ⟩ := H u hu hu'
  refine ⟨fun a j => ⟨?_, ?_⟩, x₀, hg₀, lev₀, ϑ, fun a j => ?_, ?_, hκ⟩
  · have := ((I.e.toEquiv.summable_iff.2 (hsum a j).1)).mul_left ‖(e (ν.rg ^ (m ^ 2)))⁻¹‖
    refine this.congr fun α => ?_
    simp only [Function.comp, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h1, hβ]
    rw [← norm_mul, map_div₀, div_eq_inv_mul, _root_.mul_assoc]
  · have := ((I.e.toEquiv.summable_iff.2 (hsum a j).2)).mul_left ‖(e (ν.rg ^ (m ^ 2)))⁻¹‖
    refine this.congr fun α => ?_
    simp only [Function.comp, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h2, hβ]
    rw [← norm_mul, map_div₀, div_eq_inv_mul, _root_.mul_assoc]
  · rw [hϑ a j, ← I.e.toEquiv.tsum_eq]
    refine tsum_congr fun α => ?_
    simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h1, hβ, hrg, map_div₀, map_pow]
  · convert hJ using 3 with a j
    rw [← I.e.toEquiv.tsum_eq]
    refine tsum_congr fun α => ?_
    simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h2, hβ, hrg, map_div₀, map_pow]

end GlobalTheory.MBLow
end
end
