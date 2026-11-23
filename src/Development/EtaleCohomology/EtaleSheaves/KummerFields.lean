module

public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.KummerH0Surjection
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.ResMapNsmulHomotopy
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuPf

-- Source module: Development.EtaleCohomology.EtaleSheaves.KummerFields.H0Naturality

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H2CurveOrder.KummerH0Surjection
open CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafKumFieldPf.H0Naturality

set_option backward.isDefEq.respectTransparency false in
theorem resι_nat {F G : Shv ℤ} (φ : F ⟶ G) : resι ℤ F ≫ (resMap ℤ φ).f 0 = φ ≫ resι ℤ G := by
  have h := congrArg (fun f => HomologicalComplex.Hom.f f 0)
    (InjectiveResolution.desc_commutes φ (injectiveResolution G) (injectiveResolution F))
  simp only [HomologicalComplex.comp_f] at h
  simp only [resι, resMap, InjectiveResolution.ι'_f_zero, InjectiveResolution.cochainComplexXIso]
  rw [HomologicalComplex.extendMap_f _ _ (i := 0) (by rfl)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% h]
  first | rfl | simp | (congr 1)

theorem free_ext (X : Scheme.{0}) {I : Shv ℤ}
    (f g : (free ℤ).obj ((sch.obj X).obj (op (SimplexCategory.mk 0))) ⟶ I)
    (h : (f.hom.app (op X)).hom (freeGen ℤ _ X (𝟙 X)) = (g.hom.app (op X)).hom (freeGen ℤ _ X (𝟙 X))) : f = g := by
  have key : ∀ (η : (freeP ℤ).obj ((sch.obj X).obj (op (SimplexCategory.mk 0))) ⟶ I.obj) (U : Scheme.{0}) (x : U ⟶ X),
      (η.app (op U)).hom (ModuleCat.freeMk (ULift.up x)) =
        (I.obj.map x.op).hom ((η.app (op X)).hom (ModuleCat.freeMk (ULift.up (𝟙 X)))) := by
    intro η U x
    have := congrArg (fun m => m.hom (ModuleCat.freeMk (ULift.up (𝟙 X)))) (η.naturality x.op)
    refine Eq.trans ?_ this
    rw [ModuleCat.hom_comp]
    erw [LinearMap.comp_apply]
    congr 1
    erw [ModuleCat.free_map_apply]
    congr 2
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ I.2
  refine NatTrans.ext (funext fun U => ModuleCat.free_hom_ext fun ⟨x⟩ => ?_)
  have h1 := key (toSheafify _ _ ≫ f.hom) U.unop x
  have h2 := key (toSheafify _ _ ≫ g.hom) U.unop x
  refine h1.trans (h2.trans ?_).symm
  congr 1
  exact h.symm

theorem coc_ext (X : Scheme.{0}) (G : Shv ℤ) (a b : Cocycle ((chains ℤ).obj (sch.obj X)) (res ℤ G) 0)
    (h : ev a.1 0 0 (by simp) X (𝟙 X) = ev b.1 0 0 (by simp) X (𝟙 X)) : a = b := by
  apply Cocycle.ext
  apply Cochain.ext
  intro p q hpq
  obtain rfl : p = q := by omega
  rcases lt_trichotomy p 0 with hp | rfl | hp
  · apply IsZero.eq_of_tgt
    exact HomologicalComplex.isZero_extend_X _ _ _ (fun i => by show ((i:ℕ):ℤ) ≠ p; omega)
  · have e := free_ext X ((chainsXIso ℤ (sch.obj X) 0).inv ≫ a.1.v 0 0 (by simp))
      ((chainsXIso ℤ (sch.obj X) 0).inv ≫ b.1.v 0 0 (by simp)) h
    have := congrArg ((chainsXIso ℤ (sch.obj X) 0).hom ≫ ·) e
    simpa using this
  · apply IsZero.eq_of_src
    exact HomologicalComplex.isZero_extend_X _ _ _ (fun i => by show -((i:ℕ):ℤ) ≠ p; omega)

theorem ev_post (X : Scheme.{0}) {F G : Shv ℤ} (φ : F ⟶ G) (α : Cocycle ((chains ℤ).obj (sch.obj X)) (res ℤ F) 0) :
    ev (zcomp α (Cocycle.ofHom (resMap ℤ φ)) (add_zero 0)).1 0 0 (by simp) X (𝟙 X) =
      (((resMap ℤ φ).f 0).hom.app (op X)).hom (ev α.1 0 0 (by simp) X (𝟙 X)) := by
  simp only [ev, zcomp, Cocycle.mk, Cochain.comp_zero_cochain_v, Cocycle.ofHom, Cochain.ofHom_v]
  rfl

theorem etale_degree_zero_cohomology_natural_in_sheaf (hA9 : A9) : EtaleDegreeZeroCohomologyNaturallyIsoToSections := by
  intro _
  choose e he using fun F : Shv ℤ => (hA9 ℤ F).2
  refine ⟨e, ?_⟩
  intro F G φ X s
  obtain ⟨α, hα, hαv⟩ := (he F).2 X s
  obtain ⟨β, hβ, hβv⟩ := (he G).2 X (Sec.map φ s)
  rw [← hα, ← hβ]
  show CohomologyClass.mk (zcomp α (Cocycle.ofHom (resMap ℤ φ)) (add_zero 0)) = _
  congr 1
  apply coc_ext
  rw [hβv, ev_post, hαv]
  have := congrArg (fun m => (m.hom.app (op X)).hom s) (resι_nat φ)
  exact this
end H0Naturality
end LeafKumFieldPf
end E
end LateralTheory
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.KummerFields.GmSecSurj

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H2CurveOrder.LeafKumSeqPf LateralTheory.E.H2CurveOrder.KummerH0Surjection

namespace LateralTheory.E.LeafKumFieldPf.GmSecSurj

def unitsEquivHom (A : Type) [CommRing A] : (Multiplicative ℤ →* A) ≃ Aˣ where
  toFun f := (zpowersHom Aˣ).symm f.toHomUnits
  invFun u := (Units.coeHom A).comp (zpowersHom Aˣ u)
  left_inv f := by ext; simp
  right_inv u := by ext; simp

abbrev LR : CommRingCat.{0} := CommRingCat.of (AddMonoidAlgebra ℤ ℤ)

def homUnits (A : CommRingCat.{0}) : (LR ⟶ A) ≃ Aˣ :=
  ({ toFun := fun f => f.hom, invFun := CommRingCat.ofHom, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl } : (LR ⟶ A) ≃ (AddMonoidAlgebra ℤ ℤ →+* A)).trans <|
    (RingHom.equivIntAlgHom _ _).trans <| (AddMonoidAlgebra.lift ℤ A ℤ).symm.trans (unitsEquivHom A)

theorem homUnits_val (A : CommRingCat.{0}) (ψ : LR ⟶ A) :
    ((homUnits A ψ : Aˣ) : A) = ψ.hom (AddMonoidAlgebra.of ℤ ℤ (Multiplicative.ofAdd 1)) := by
  simp [homUnits, unitsEquivHom]
  rfl

theorem homUnits_nat {A B : CommRingCat.{0}} (ψ : LR ⟶ A) (h : A ⟶ B) :
    homUnits B (ψ ≫ h) = Units.map h.hom.toMonoidHom (homUnits A ψ) := by
  ext
  simp [homUnits_val]

abbrev P : Scheme.{0}ᵒᵖ ⥤ Type 1 := Scheme.Γ ⋙ unitsF ⋙ forget _

def repr : P.RepresentableBy (Spec LR) where
  homEquiv {X} := (ΓSpec.adjunction.homEquiv X (op LR)).symm.trans <|
    ({ toFun := fun φ => φ.unop, invFun := fun φ => φ.op, left_inv := fun _ => rfl, right_inv := fun _ => rfl } :
      (Scheme.Γ.rightOp.obj X ⟶ op LR) ≃ (LR ⟶ Γ(X, ⊤))).trans <| (homUnits _).trans <|
      Additive.ofMul.trans Equiv.ulift.symm
  homEquiv_comp {X X'} f g := by
    simp only [Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_left_symm]
    exact congrArg (fun u => ULift.up (Additive.ofMul u)) (homUnits_nat _ (Scheme.Γ.map f.op))

theorem isSheaf_P : Presieve.IsSheaf Scheme.etaleTopology.{0} P := by
  have : Scheme.etaleTopology.{0}.Subcanonical :=
    GrothendieckTopology.Subcanonical.of_le Scheme.etaleTopology_le_proetaleTopology
  have : P.IsRepresentable := repr.isRepresentable
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable P

theorem isSheaf_units : Presheaf.IsSheaf Scheme.etaleTopology.{0} (Scheme.Γ ⋙ unitsF) :=
  (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).mpr
    ((isSheaf_iff_isSheaf_of_type _ _).mpr isSheaf_P)

theorem LeafGmSecSurj_of : LateralTheory.E.H2CurveOrder.KummerH0Surjection.LeafGmSecSurj := by
  intro B _ y
  have := isIso_toSheafify Scheme.etaleTopology.{0} isSheaf_units
  let g := (toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ unitsF)).app (op (Spec (CommRingCat.of B)))
  refine ⟨((inv g).hom y).down, ?_⟩
  show g.hom ((inv g).hom y) = y
  change (inv g ≫ g).hom y = y
  rw [IsIso.inv_hom_id]
  rfl

end LateralTheory.E.LeafKumFieldPf.GmSecSurj
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.KummerFields

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafKumFieldPf

open LateralTheory.E.E4

theorem kumMu : LateralTheory.E.H2CurveOrder.LeafKumSeqPf.LeafKumMu := fun hy =>
  LateralTheory.E.H2CurveOrder.LeafKumMuPf.LeafKumMu_of hy.2.2.2.2.2.2.1 hy.2.2.2.2.2.2.2.2.1
    LateralTheory.E.H2CurveOrder.muUnits hy

theorem etale_kummer_sequence_degree_zero_global_sections : LateralTheory.E.H2CurveOrder.LeafKumSeqPf.KummerUnitsSurjectH0 := fun hy =>
  LateralTheory.E.H2CurveOrder.KummerH0Surjection.etale_kummer_degree_zero_cohomology_of_sections_and_units_surjective LateralTheory.E.H2CurveOrder.kumSecSurj
    (LateralTheory.E.LeafKumFieldPf.H0Naturality.etale_degree_zero_cohomology_natural_in_sheaf hy.2.2.2.2.2.2.2.1)
    LateralTheory.E.LeafKumFieldPf.GmSecSurj.LeafGmSecSurj_of hy

theorem kumSeq : LateralTheory.E.LeafKumCut.LeafKumSeq :=
  LateralTheory.E.H2CurveOrder.LeafKumSeqPf.LeafKumSeq_of kumMu etale_kummer_sequence_degree_zero_global_sections

end LateralTheory.E.LeafKumFieldPf
end
end
end
