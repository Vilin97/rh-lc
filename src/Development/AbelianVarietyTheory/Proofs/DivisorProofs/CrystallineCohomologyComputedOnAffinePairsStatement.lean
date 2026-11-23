module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePointPairsCommaAcyclicDegreeLeTwoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraCoefficientsRestrictionBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineH2SmallCoverBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallDescentH1Surjective
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Mathlib.RingTheory.DividedPowers.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCohomologyRestrictAffinePointPairsBij

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.SmallPairs

variable {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) {X : Scheme.{0}} (t : X ⟶ Sp R)
  {Y : Scheme.{0}} (i : X ⟶ Y)

def cov (V : Y.affineOpens) : X.Opens := i ⁻¹ᵁ V.1

theorem iSup_cov : ⨆ V, cov i V = ⊤ := by
  simp only [cov]
  rw [← Scheme.Hom.preimage_iSup, AlgebraicGeometry.iSup_affineOpens_eq_top Y]
  simp

abbrev SC : Type 1 := (IsSmall κ t (cov i)).FullSubcategory

abbrev PC : Type 1 := (IsSm κ t i).FullSubcategory

def fgt : PC κ t i ⥤ SC κ t i where
  obj a := ⟨a.obj.T, by obtain ⟨V, hV⟩ := a.property; exact ⟨V, hV⟩⟩
  map f := ObjectProperty.homMk f.hom.1

def sec : SC κ t i ⥤ PC κ t i where
  obj T := ⟨⟨T.obj, ⊤, Or.inr rfl, by simp⟩, by obtain ⟨V, hV⟩ := T.property; exact ⟨V, hV⟩⟩
  map f := ObjectProperty.homMk ⟨f.hom, le_rfl⟩

abbrev OS : SC κ t i ⥤ CommAlgCat.{0} R := (IsSmall κ t (cov i)).ι ⋙ O κ t

abbrev OP : PC κ t i ⥤ CommAlgCat.{0} R := ((IsSm κ t i).ι ⋙ Pr.fgt κ t i) ⋙ O κ t

def nS : CoefMap (RingHom.id R) (OS κ t i) (OP κ t i) where
  G := fgt κ t i
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def kP : CoefMap (RingHom.id R) (OP κ t i) (OS κ t i) where
  G := sec κ t i
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def θP : fgt κ t i ⋙ sec κ t i ⟶ 𝟭 (PC κ t i) where
  app a := ObjectProperty.homMk ⟨𝟙 a.obj.T, le_top⟩
  naturality a b f :=
    ObjectProperty.hom_ext _ (Subtype.ext ((Category.comp_id f.hom.1).trans (Category.id_comp f.hom.1).symm))

def θS : sec κ t i ⋙ fgt κ t i ⟶ 𝟭 (SC κ t i) where
  app T := ObjectProperty.homMk (𝟙 T.obj)
  naturality _ _ f := ObjectProperty.hom_ext _ ((Category.comp_id f.hom).trans (Category.id_comp f.hom).symm)

theorem kn1 (c : H1 (OP κ t i)) : (nS κ t i).pull1 ((kP κ t i).pull1 c) = c := by
  rw [← CoefMap.pullCohomologyOne_comp, CoefMap.pullCohomologyOne_eq_of_natTrans _ (CoefMap.id _) (θP κ t i)
    (fun T b ↦ mp_id (O κ t) T.obj.T b), CoefMap.pullCohomologyOne_id]

theorem nk1 (c : H1 (OS κ t i)) : (kP κ t i).pull1 ((nS κ t i).pull1 c) = c := by
  rw [← CoefMap.pullCohomologyOne_comp, CoefMap.pullCohomologyOne_eq_of_natTrans _ (CoefMap.id _) (θS κ t i)
    (fun T b ↦ mp_id (O κ t) T.obj b), CoefMap.pullCohomologyOne_id]

theorem kn2 (c : H2 (OP κ t i)) : (nS κ t i).pull2 ((kP κ t i).pull2 c) = c := by
  rw [← CoefMap.pullCohomologyTwo_comp, CoefMap.pullCohomologyTwo_eq_of_natTrans _ (CoefMap.id _) (θP κ t i)
    (fun T b ↦ mp_id (O κ t) T.obj.T b), CoefMap.pullCohomologyTwo_id]

theorem nk2 (c : H2 (OS κ t i)) : (kP κ t i).pull2 ((nS κ t i).pull2 c) = c := by
  rw [← CoefMap.pullCohomologyTwo_comp, CoefMap.pullCohomologyTwo_eq_of_natTrans _ (CoefMap.id _) (θS κ t i)
    (fun T b ↦ mp_id (O κ t) T.obj b), CoefMap.pullCohomologyTwo_id]

theorem fac1 (c : H1 (O κ t)) : (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull1 c =
    (nS κ t i).pull1 ((CoefMap.restrict (O κ t) (IsSmall κ t (cov i)).ι).pull1 c) := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c; rfl

theorem fac2 (c : H2 (O κ t)) : (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull2 c =
    (nS κ t i).pull2 ((CoefMap.restrict (O κ t) (IsSmall κ t (cov i)).ι).pull2 c) := by
  obtain ⟨f, rfl⟩ := H2.mk_surjective _ c; rfl

end GlobalTheory.PDForm.SmallPairs

namespace GlobalTheory.PDForm

open SmallPairs

theorem pull_isSm_bijective (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y) :
    Function.Bijective (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull1 ∧
      Function.Bijective (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull2 := by
  have b1 := SmallDescent.pull1_bijective R I κ X t Y.affineOpens (cov i) (iSup_cov i)
  have b2 := small_descent_H2_bijective R I κ X t Y.affineOpens (cov i) (iSup_cov i)
  have n1 : Function.Bijective (nS κ t i).pull1 :=
    Function.bijective_iff_has_inverse.2 ⟨(kP κ t i).pull1, nk1 κ t i, kn1 κ t i⟩
  have n2 : Function.Bijective (nS κ t i).pull2 :=
    Function.bijective_iff_has_inverse.2 ⟨(kP κ t i).pull2, nk2 κ t i, kn2 κ t i⟩
  refine ⟨?_, ?_⟩
  · have e : ⇑(CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull1 =
        ⇑(nS κ t i).pull1 ∘ ⇑(CoefMap.restrict (O κ t) (IsSmall κ t (cov i)).ι).pull1 := funext (fac1 κ t i)
    rw [e]; exact n1.comp b1
  · have e : ⇑(CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull2 =
        ⇑(nS κ t i).pull2 ∘ ⇑(CoefMap.restrict (O κ t) (IsSmall κ t (cov i)).ι).pull2 := funext (fac2 κ t i)
    rw [e]; exact n2.comp b2

end GlobalTheory.PDForm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCohomologyRestrictAffinePointPairsBijStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.crystallineCohomology_restrict_affinePointPairs_bijective : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y), Function.Bijective (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull1 ∧ Function.Bijective (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull2 := by
  first | exact @GlobalTheory.PDForm.pull_isSm_bijective | exact GlobalTheory.PDForm.pull_isSm_bijective | (intros; apply GlobalTheory.PDForm.pull_isSm_bijective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictUpwardClosedSubcategoryPull1Bijective

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.Desc


open Classical in
theorem restrict_upwardClosed_subcategory_pull1_bijective : ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (P : ObjectProperty C), (∀ S S', (S ⟶ S') → P S → P S') →
    (∀ T, Desc.Sep F fun S (_ : T ⟶ S) ↦ P S) → (∀ T, Desc.Glue F fun S (_ : T ⟶ S) ↦ P S) →
    (∀ T, Desc.Van1 F fun S (_ : T ⟶ S) ↦ P S) → Function.Bijective (CoefMap.restrict F P.ι).pull1 := by
  intro R _ C _ F P hP sep glue van
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨f, rfl⟩ := H1.mk_surjective F c
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
    obtain ⟨g₀, hg⟩ := hc
    let g : ∀ S, P S → F.obj S := fun S hS ↦ g₀ ⟨S, hS⟩
    have hg' : ∀ (S S' : C) (hS : P S) (hS' : P S') (ψ : S ⟶ S'),
        g S' hS' - mp F ψ (g S hS) = f.1 S S' ψ := fun S S' hS hS' ψ ↦
      congrFun (congrFun (congrFun hg ⟨S, hS⟩) ⟨S', hS'⟩) (ObjectProperty.homMk ψ)
    have h1 : ∀ T : C, ∃ x : F.obj T, ∀ S (u : T ⟶ S) (hS : P S),
        mp F u x = g S hS - f.1 T S u := by
      intro T
      obtain ⟨x, hx⟩ := glue T (fun S u ↦ if hS : P S then g S hS - f.1 T S u else 0)
        fun S S' u ψ hS ↦ by
          have hS' := hP _ _ ψ hS
          simp only [dif_pos hS, dif_pos hS', map_sub]
          have k1 := Z1.comp f u ψ
          have k2 := hg' S S' hS hS' ψ
          linear_combination k2 - k1
      exact ⟨x, fun S u hS ↦ by rw [hx S u hS, dif_pos hS]⟩
    choose x hx using h1
    refine H1.mk_eq_zero.2 ⟨x, ?_⟩
    funext T T' φ
    rw [amitsur_d0_apply]
    refine (sub_eq_zero.1 (sep T' _ fun S u hS ↦ ?_)).symm
    have k1 := Z1.comp f φ u
    have k2 := hx T' S u hS
    have k3 := hx T S (φ ≫ u) hS
    rw [mp_comp] at k3
    simp only [map_sub]
    linear_combination k3 - k2 - k1
  · intro c
    obtain ⟨y, rfl⟩ := H1.mk_surjective _ c
    let z : ∀ S S', (S ⟶ S') → F.obj S' := fun S S' ψ ↦
      if h : P S then y.1 ⟨S, h⟩ ⟨S', hP _ _ ψ h⟩ (ObjectProperty.homMk ψ) else 0
    have hz : ∀ S S' S'' (ψ : S ⟶ S') (χ : S' ⟶ S''), P S →
        z S S'' (ψ ≫ χ) = mp F χ (z S S' ψ) + z S' S'' χ := by
      intro S S' S'' ψ χ hp
      have hp' := hP _ _ ψ hp
      simp only [z, dif_pos hp, dif_pos hp']
      exact y.2 (T := ⟨S, hp⟩) (T' := ⟨S', hp'⟩) (T'' := ⟨S'', hP _ _ χ hp'⟩)
        (ObjectProperty.homMk ψ) (ObjectProperty.homMk χ)
    have hzy : ∀ (S S' : P.FullSubcategory) (ψ : S ⟶ S'), z S.obj S'.obj ψ.hom = y.1 S S' ψ := by
      intro S S' ψ
      simp only [z, dif_pos S.property]
      rfl
    have h1 : ∀ T : C, ∃ b : ∀ S, (T ⟶ S) → F.obj S, (∀ S S' u ψ, P S →
        b S' (u ≫ ψ) - mp F ψ (b S u) = z S S' ψ) ∧ (P T → ∀ S u, b S u = z T S u) := by
      intro T
      by_cases hp : P T
      · exact ⟨fun S u ↦ z T S u, fun S S' u ψ _ ↦ by
          have := hz _ _ _ u ψ hp
          linear_combination this, fun _ _ _ ↦ rfl⟩
      · obtain ⟨b, hb⟩ := van T (fun S S' _ ψ ↦ z S S' ψ) fun S S' S'' u ψ χ h ↦ hz _ _ _ ψ χ h
        exact ⟨b, hb, fun h ↦ absurd h hp⟩
    choose b hb hb' using h1
    have h2 : ∀ T T' (φ : T ⟶ T'), ∃ x : F.obj T', ∀ S (u : T' ⟶ S), P S →
        mp F u x = b T S (φ ≫ u) - b T' S u := by
      intro T T' φ
      refine glue T' _ fun S S' u ψ hp ↦ ?_
      have k1 := hb T _ _ (φ ≫ u) ψ hp
      have k2 := hb T' _ _ u ψ hp
      simp only [map_sub, Category.assoc] at k1 ⊢
      linear_combination k1 - k2
    choose f hf using h2
    refine ⟨H1.mk F ⟨f, fun T T' T'' φ ψ ↦ sub_eq_zero.1 (sep T'' _ fun S u hp ↦ ?_)⟩, ?_⟩
    · have k1 := hf _ _ (φ ≫ ψ) S u hp
      have k2 := hf _ _ φ S (ψ ≫ u) hp
      have k3 := hf _ _ ψ S u hp
      simp only [map_sub, map_add (f := _), mp_comp, Category.assoc] at k1 k2 ⊢
      linear_combination k1 - k2 - k3
    · rw [CoefMap.pullCohomologyOne_class]
      congr 1
      refine Subtype.ext ?_
      funext S S' ψ
      have k1 := hf _ _ ψ.hom _ (𝟙 _) S'.property
      rw [hb' _ S.property, hb' _ S'.property, mp_id, Category.comp_id] at k1
      have k2 := hz _ _ _ (𝟙 S'.obj) (𝟙 S'.obj) S'.property
      rw [Category.id_comp, mp_id] at k2
      rw [← hzy]
      change f _ _ ψ.hom = _
      linear_combination k1 + k2

end GlobalTheory.CatCoh.Desc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCohomologyComputedOnAffinePairs

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDForm.AffPair

section

variable {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) {X : Scheme.{0}} (t : X ⟶ Sp R)
  {Y : Scheme.{0}} (i : X ⟶ Y)

def smAff : ObjectProperty (IsSm κ t i).FullSubcategory := fun S ↦ IsAffineOpen S.obj.U

theorem smAff_up (S S' : (IsSm κ t i).FullSubcategory) (f : S ⟶ S') (h : smAff κ t i S) :
    smAff κ t i S' := by
  rcases S'.obj.hU with h' | h'
  · exact h'
  · have e : S'.obj.U = S.obj.U := le_antisymm f.hom.2 (h' ▸ le_top)
    change IsAffineOpen S'.obj.U
    rw [e]
    exact h

abbrev coefSm : (IsSm κ t i).FullSubcategory ⥤ CommAlgCat.{0} R := (IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t

def toIter : EE κ t i ⥤ (smAff κ t i).FullSubcategory where
  obj a := ⟨⟨a.obj, ⟨⟨a.obj.U, a.property⟩, a.obj.mem⟩⟩, a.property⟩
  map f := ⟨⟨f.hom⟩⟩

def ofIter : (smAff κ t i).FullSubcategory ⥤ EE κ t i where
  obj a := ⟨a.obj.obj, a.property⟩
  map f := ⟨f.hom.hom⟩

def mapTo : CoefMap (RingHom.id R) ((smAff κ t i).ι ⋙ coefSm κ t i) (pE κ t i ⋙ O κ t) where
  G := toIter κ t i
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def mapOf : CoefMap (RingHom.id R) (pE κ t i ⋙ O κ t) ((smAff κ t i).ι ⋙ coefSm κ t i) where
  G := ofIter κ t i
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

theorem mapTo_pull1 : Function.Bijective (mapTo κ t i).pull1 := by
  refine Function.bijective_iff_has_inverse.2 ⟨(mapOf κ t i).pull1, fun c ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := H1.mk_surjective _ c; rfl
  · obtain ⟨a, rfl⟩ := H1.mk_surjective _ c; rfl

theorem mapTo_pull2 : Function.Bijective (mapTo κ t i).pull2 := by
  refine Function.bijective_iff_has_inverse.2 ⟨(mapOf κ t i).pull2, fun c ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := H2.mk_surjective _ c; rfl
  · obtain ⟨a, rfl⟩ := H2.mk_surjective _ c; rfl

end

end GlobalTheory.PDForm.AffPair

namespace GlobalTheory.PDForm


open AffPair in
theorem crystallineCohomology_computed_on_affinePairs : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y),
    (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) →
    ((Cx.single (Coef.ofAlg (O κ t))).resMap (pE κ t i)).PullbackBijectiveDegreesOneTwo := by
  intro R _ I κ X t Y i hY
  have ha := GlobalTheory.T.crystallineCohomology_restrict_affinePointPairs_bijective R I κ X t Y i
  have hc := GlobalTheory.T.affinePointPairs_comma_acyclic_degree_le_two.1 R I κ X t Y i hY
  have hc2 := GlobalTheory.T.affinePointPairs_comma_acyclic_degree_le_two.2 R I κ X t Y i hY
  have h1 : Function.Bijective (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull1 :=
    Desc.restrict_upwardClosed_subcategory_pull1_bijective R _ (coefSm κ t i) (smAff κ t i) (smAff_up κ t i)
      (fun T ↦ (hc T).1) (fun T ↦ (hc T).2.1) fun T ↦ (hc T).2.2
  have h2 : Function.Bijective (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull2 :=
    ⟨Desc.pull_restrict_small_injective (coefSm κ t i) (smAff κ t i) (smAff_up κ t i)
      (fun T ↦ (hc T).1) (fun T ↦ (hc T).2.1) fun T ↦ (hc T).2.2,
    Desc.descent_H2_surjective (coefSm κ t i) (smAff κ t i) (smAff_up κ t i)
      (fun T ↦ (hc T).1) (fun T ↦ (hc T).2.1) (fun T ↦ (hc T).2.2) hc2⟩
  refine GlobalTheory.T.algebra_coefficients_restriction_bijective R _ _ (O κ t) (pE κ t i) ?_ ?_
  · have h := (mapTo_pull1 κ t i).comp (h1.comp ha.1)
    have e : ⇑(CoefMap.restrict (O κ t) (pE κ t i)).pull1 = (mapTo κ t i).pull1 ∘
        (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull1 ∘
        (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull1 := by
      funext c
      obtain ⟨a, rfl⟩ := H1.mk_surjective _ c; rfl
    rw [e]
    exact h
  · have h := (mapTo_pull2 κ t i).comp (h2.comp ha.2)
    have e : ⇑(CoefMap.restrict (O κ t) (pE κ t i)).pull2 = (mapTo κ t i).pull2 ∘
        (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull2 ∘
        (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull2 := by
      funext c
      obtain ⟨a, rfl⟩ := H2.mk_surjective _ c; rfl
    rw [e]
    exact h

end GlobalTheory.PDForm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCohomologyComputedOnAffinePairsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.pullbackBijective12_resMap_of_affine_inter : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y), (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) → ((Cx.single (Coef.ofAlg (O κ t))).resMap (pE κ t i)).PullbackBijectiveDegreesOneTwo := by
  first | exact @GlobalTheory.PDForm.crystallineCohomology_computed_on_affinePairs | exact GlobalTheory.PDForm.crystallineCohomology_computed_on_affinePairs | (intros; apply GlobalTheory.PDForm.crystallineCohomology_computed_on_affinePairs <;> assumption)
end
end
