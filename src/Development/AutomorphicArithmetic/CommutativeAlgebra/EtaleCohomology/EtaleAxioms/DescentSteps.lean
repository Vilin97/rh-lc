module

public import Development.EtaleCohomology.EtaleSheaves.DescentInduction
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
import Mathlib.Tactic.TypeStar
public import Development.EtaleCohomology.EtaleSheaves.longPf
public import Development.EtaleCohomology.EtaleSheaves.stupidPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheafStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyLongExactFirstOfInjectiveStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Development.EtaleCohomology.EtaleSheaves.DescentInduction
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Tactic.Linter.Style
import Development.EtaleCohomology.EtaleSheaves.inclPf
import Development.EtaleCohomology.EtaleSheaves.longPfSes
import Development.EtaleCohomology.EtaleSheaves.CxDescPf

-- Source module: Development.EtaleCohomology.EtaleSheaves.LevelIdentPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LevelIdentPf

def FreeSingleHomotopyEquivDiscreteChains : Prop := ∀ (R : Type) [CommRing R], ∃ e : ∀ P : PSh, HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)),
  (∀ P, sglι _ ≫ (e P).hom.f 0 = (chainsXIso R (disc.obj P) 0).inv) ∧
  ∀ {P Q : PSh} (f : P ⟶ Q), (e P).hom ≫ (chains R).map (disc.map f) =
    (CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (e Q).hom

variable {R : Type} [CommRing R]

theorem cpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem cpull_id (K I : Cx R) (n : ℤ) (x : CohomologyClass K I n) : cpull (𝟙 K) I n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem cpull_homotopy {K L : Cx R} {f g : K ⟶ L} (h : Homotopy f g) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    cpull f I n x = cpull g I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk (zcomp _ x _) = CohomologyClass.mk (zcomp _ x _)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨n - 1, by omega, n.negOnePow • (Cochain.ofHomotopy h).comp x.1 (by omega), ?_⟩
  rw [δ_units_smul, δ_comp _ _ (by omega) 0 (n + 1) n (by omega) (by omega) (by omega), δ_ofHomotopy]
  simp [zcomp, Cocycle.δ_eq_zero, Cochain.sub_comp, smul_smul, Int.units_mul_self]

theorem cpull_iso_bij {K L : Cx R} (e : HomotopyEquiv K L) (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull e.hom I n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cpull e.inv I n, fun x => ?_, fun x => ?_⟩
  · rw [← cpull_comp, cpull_homotopy e.homotopyInvHomId, cpull_id]
  · rw [← cpull_comp, cpull_homotopy e.homotopyHomInvId, cpull_id]

theorem sq_iff {A B C D : Type*} {a : B → D} {b : A → B} {c : C → D} {d : A → C}
    (w : ∀ x, a (b x) = c (d x)) (ha : Function.Bijective a) (hd : Function.Bijective d) :
    (Function.Bijective b ↔ Function.Bijective c) ∧ (Function.Injective b ↔ Function.Injective c) := by
  have w' : a ∘ b = c ∘ d := funext w
  obtain ⟨d', hd1, hd2⟩ := Function.bijective_iff_has_inverse.1 hd
  have hc : c = a ∘ b ∘ d' := by
    funext y; simp only [Function.comp_apply, w, hd2 y]
  have hd'b : Function.Bijective d' := Function.bijective_iff_has_inverse.2 ⟨d, hd2, hd1⟩
  refine ⟨⟨fun hb => hc ▸ ha.comp (hb.comp hd'b), fun hc' => ?_⟩, ⟨fun hb => hc ▸ ha.1.comp (hb.comp hd'b.1), fun hc' => ?_⟩⟩
  · have : a ∘ b = c ∘ d := w'
    have hab : Function.Bijective (a ∘ b) := this ▸ hc'.comp hd
    obtain ⟨a', ha1, ha2⟩ := Function.bijective_iff_has_inverse.1 ha
    have : b = a' ∘ (a ∘ b) := by funext x; simp [ha1 (b x)]
    rw [this]; exact (Function.bijective_iff_has_inverse.2 ⟨a, ha2, ha1⟩).comp hab
  · intro x y hxy
    apply hd.1; apply hc'
    rw [← w, ← w, hxy]

theorem chains_f {E E' : Spc} (f : E ⟶ E') (n : ℕ) : ((chains R).map f).f (-(n : ℤ)) =
    (chainsXIso R E n).hom ≫ (free R).map (f.app (op (SimplexCategory.mk n))) ≫ (chainsXIso R E' n).inv := by
  dsimp only [chains, chainsXIso, Functor.comp_map]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := n) rfl]
  rfl

theorem cpull_isoHom_bij {K L : Cx R} (i : K ≅ L) (I : Cx R) (n : ℤ) : Function.Bijective (cpull i.hom I n) :=
  cpull_iso_bij (HomotopyEquiv.ofIso i) I n

theorem pull_eq {E E' : Spc} (f : E ⟶ E') (F : Shv R) (n : ℤ) (x : H R E' F n) :
    pull R f F n x = cpull ((chains R).map f) (res R F) n x := rfl

theorem LevelIdent_of (hS : FreeSingleHomotopyEquivDiscreteChains) : LateralTheory.E.DescStepPf.LevelIdent := by
  intro R _ F E E' f p j
  obtain ⟨e, -, he⟩ := hS R
  let S := CochainComplex.singleFunctor (Shv R) 0
  let g := f.app (op (SimplexCategory.mk p))
  have sq1 : S.map (((chains R).map f).f (-(p : ℤ))) ≫ S.map (chainsXIso R E' p).hom =
      S.map (chainsXIso R E p).hom ≫ S.map ((free R).map g) := by
    rw [← S.map_comp, ← S.map_comp, chains_f]; simp [g]
  have w1 : ∀ x, cpull (S.map (chainsXIso R E p).hom) (res R F) j (cpull (S.map ((free R).map g)) (res R F) j x) =
      cpull (S.map (((chains R).map f).f (-(p : ℤ)))) (res R F) j (cpull (S.map (chainsXIso R E' p).hom) (res R F) j x) := by
    intro x; rw [← cpull_comp, ← cpull_comp, sq1]
  have w2 : ∀ x, cpull (e (E.obj (op (SimplexCategory.mk p)))).hom (res R F) j (pull R (disc.map g) F j x) =
      cpull (S.map ((free R).map g)) (res R F) j (cpull (e (E'.obj (op (SimplexCategory.mk p)))).hom (res R F) j x) := by
    intro x; rw [pull_eq, ← cpull_comp, ← cpull_comp, he g]
  obtain ⟨b1, i1⟩ := sq_iff w1 (cpull_isoHom_bij (S.mapIso (chainsXIso R E p)) _ _)
    (cpull_isoHom_bij (S.mapIso (chainsXIso R E' p)) _ _)
  obtain ⟨b2, i2⟩ := sq_iff w2 (cpull_iso_bij _ _ _) (cpull_iso_bij _ _ _)
  exact ⟨b2.trans b1, i2.trans i1⟩

end LateralTheory.E.LevelIdentPf
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.CochainComplexSingleFunctorZeroMapFZero

section

@[expose] public section

noncomputable section
open CategoryTheory Limits ZeroObject

namespace LateralTheory.E.trunc0Pf

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]

lemma isZero_tr (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] (i : ℤ) (hi : i ≠ 0) :
    IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE 0)).X i) := by
  rcases lt_or_gt_of_ne hi with h | h
  · apply HomologicalComplex.isZero_stupidTrunc_X
    intro j; simp; omega
  · exact (K.isZero_of_isStrictlyLE 0 i h).of_iso
      (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE 0) (i := i.toNat) (by simp; omega))

lemma cochainComplex_singleFunctor_zero_map_f_zero {A B : C} (f : A ⟶ B) :
    ((CochainComplex.singleFunctor C 0).map f).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).hom ≫ f ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 B).inv :=
  HomologicalComplex.single_map_f_self _ _ f

def eIso (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE 0) ≅ (CochainComplex.singleFunctor C 0).obj (K.X 0) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => if h : i = 0 then (by
        subst h
        exact K.stupidTruncXIso (ComplexShape.embeddingUpIntGE 0) (i := 0) (by simp) ≪≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X 0)).symm)
      else (isZero_tr K i h).iso (HomologicalComplex.isZero_single_obj_X _ 0 _ i h))
    (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      by_cases hj : j = 0
      · exact (isZero_tr K i (by omega)).eq_of_src _ _
      · exact (HomologicalComplex.isZero_single_obj_X _ 0 _ j hj).eq_of_tgt _ _)

lemma stupidTruncGEZeroIsoSingle_hom_f_zero (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] :
    (eIso K).hom.f 0 = (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE 0) (i := 0) (by simp)).hom ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X 0)).inv := by
  simp [eIso]

lemma nat {K L : CochainComplex C ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L) :
    HomologicalComplex.stupidTruncMap g (ComplexShape.embeddingUpIntGE 0) ≫ (eIso L).hom =
      (eIso K).hom ≫ (CochainComplex.singleFunctor C 0).map (g.f 0) := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases h : i = 0
  · subst h
    simp only [HomologicalComplex.comp_f, stupidTruncGEZeroIsoSingle_hom_f_zero, cochainComplex_singleFunctor_zero_map_f_zero, Category.assoc, Iso.inv_hom_id_assoc]
    erw [HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom_assoc]
  · exact (HomologicalComplex.isZero_single_obj_X _ 0 _ i h).eq_of_tgt _ _

theorem trunc0_of : LateralTheory.E.stupidPf.trunc0 := by
  intro R _ K L _ _ g
  exact ⟨eIso K, eIso L, nat g⟩

end LateralTheory.E.trunc0Pf
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.DescentInduction.Bounds

section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
namespace LateralTheory.E.DescStepPf

theorem bounds_le (R : Type) [CommRing R] (E : Spc) : ((chains R).obj E).IsStrictlyLE 0 := by
  show CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0
  infer_instance

theorem Bounds_holds : Bounds := fun R _ F E =>
  ⟨bounds_le R E, by unfold res; infer_instance,
    fun m => by unfold res; exact InjectiveResolution.instInjectiveXIntCochainComplex (injectiveResolution F) m⟩

theorem etale_descent_induction_of_levelwise_identity_and_complex_descent (hL : LevelIdent) (hX : CxDesc) : LateralTheory.E.t_E1Cut.DescStep :=
  DescStep_of Bounds_holds hL hX

end LateralTheory.E.DescStepPf
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.shiftPf

section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.shiftPf

theorem conj_iff {α β γ δ : Type*} (F : α → β) (G : γ → δ) (e1 : α ≃ γ) (e2 : β ≃ δ)
    (h : ∀ x, G (e1 x) = e2 (F x)) :
    (Function.Bijective F ↔ Function.Bijective G) ∧ (Function.Injective F ↔ Function.Injective G) := by
  have hG : G = e2 ∘ F ∘ e1.symm := funext fun y => by simpa using h (e1.symm y)
  have hF : F = e2.symm ∘ G ∘ e1 := funext fun x => by simp [h]
  refine ⟨⟨fun hb => ?_, fun hb => ?_⟩, ⟨fun hb => ?_, fun hb => ?_⟩⟩
  · rw [hG]; exact e2.bijective.comp (hb.comp e1.symm.bijective)
  · rw [hF]; exact e2.symm.bijective.comp (hb.comp e1.bijective)
  · rw [hG]; exact e2.injective.comp (hb.comp e1.symm.injective)
  · rw [hF]; exact e2.symm.injective.comp (hb.comp e1.injective)

section Cat
variable {C : Type*} [Category C]

abbrev pre {X X' : C} (u : X ⟶ X') (Y : C) : (X' ⟶ Y) → (X ⟶ Y) := fun h => u ≫ h

theorem pre_conj {W W' X X' : C} (u' : W ⟶ W') (u : X ⟶ X') (a : W ≅ X) (b : W' ≅ X')
    (h : u' ≫ b.hom = a.hom ≫ u) (Y : C) :
    (Function.Bijective (pre u Y) ↔ Function.Bijective (pre u' Y)) ∧
      (Function.Injective (pre u Y) ↔ Function.Injective (pre u' Y)) :=
  conj_iff _ _ ((Iso.homCongr b.symm (Iso.refl Y))) ((Iso.homCongr a.symm (Iso.refl Y))) (fun x => by
    simp only [pre, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    rw [← Category.assoc, h, Category.assoc])

theorem pre_target {X X' Y Y' : C} (u : X ⟶ X') (e : Y ≅ Y') :
    (Function.Bijective (pre u Y) ↔ Function.Bijective (pre u Y')) ∧
      (Function.Injective (pre u Y) ↔ Function.Injective (pre u Y')) :=
  conj_iff _ _ (Iso.homCongr (Iso.refl X') e) (Iso.homCongr (Iso.refl X) e) (fun x => by
    simp [pre, Iso.homCongr_apply])

theorem pre_shift [HasShift C ℤ] {X X' : C} (u : X ⟶ X') (p : ℤ) (Y : C) :
    (Function.Bijective (pre (u⟦p⟧') Y) ↔ Function.Bijective (pre u (Y⟦-p⟧))) ∧
      (Function.Injective (pre (u⟦p⟧') Y) ↔ Function.Injective (pre u (Y⟦-p⟧))) :=
  conj_iff _ _ ((shiftEquiv C p).toAdjunction.homEquiv X' Y) ((shiftEquiv C p).toAdjunction.homEquiv X Y) (fun x => by
    simp only [pre]
    exact ((shiftEquiv C p).toAdjunction.homEquiv_naturality_left u x).symm)

end Cat

variable {R : Type} [CommRing R]

abbrev Qt (R : Type) [CommRing R] := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)

theorem toHom_cpull {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    CohomologyClass.toHom (cpull f I n x) = (Qt R).map f ≫ CohomologyClass.toHom x := by
  obtain ⟨b, rfl⟩ := x.mk_surjective
  rw [cpull, cpre_mk, CohomologyClass.toHom_mk, CohomologyClass.toHom_mk, ← Functor.map_comp,
    ← Cocycle.equivHomShift_symm_precomp]
  congr 2

theorem cpull_iff {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ) :
    (Function.Bijective (cpull f I n) ↔ Function.Bijective (pre ((Qt R).map f) ((Qt R).obj (I⟦n⟧)))) ∧
      (Function.Injective (cpull f I n) ↔ Function.Injective (pre ((Qt R).map f) ((Qt R).obj (I⟦n⟧)))) :=
  conj_iff _ _ (CohomologyClass.homAddEquiv (K := L) (L := I) (n := n)).toEquiv
    (CohomologyClass.homAddEquiv (K := K) (L := I) (n := n)).toEquiv (fun x => by
      simp [toHom_cpull])

theorem main_iff (I : Cx R) {A B : Shv R} (φ : A ⟶ B) (P j : ℤ) :
    (Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - P)) ↔
      Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) (-P)).map φ) I j)) ∧
    (Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - P)) ↔
      Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) (-P)).map φ) I j)) := by
  let s0 := (CochainComplex.singleFunctor (Shv R) 0).map φ
  let sp := (CochainComplex.singleFunctor (Shv R) (-P)).map φ
  let E := (CochainComplex.singleFunctors (Shv R)).shiftIso P (-P) 0 (by omega)
  obtain ⟨b1, i1⟩ := cpull_iff sp I j
  obtain ⟨b2, i2⟩ := pre_conj ((Qt R).map sp) ((Qt R).map (s0⟦P⟧'))
    ((Qt R).mapIso (E.symm.app A)) ((Qt R).mapIso (E.symm.app B)) (by
      simp only [Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, ← Functor.map_comp]
      congr 1
      exact E.inv.naturality φ) ((Qt R).obj (I⟦j⟧))
  obtain ⟨b3, i3⟩ := pre_conj ((Qt R).map (s0⟦P⟧')) (((Qt R).map s0)⟦P⟧')
    (((Qt R).commShiftIso P).app _) (((Qt R).commShiftIso P).app _)
    (((Qt R).commShiftIso P).hom.naturality s0) ((Qt R).obj (I⟦j⟧))
  obtain ⟨b4, i4⟩ := pre_shift ((Qt R).map s0) P ((Qt R).obj (I⟦j⟧))
  obtain ⟨b5, i5⟩ := pre_target ((Qt R).map s0)
    ((((Qt R).commShiftIso (-P)).symm.app (I⟦j⟧)) ≪≫
      (Qt R).mapIso ((shiftFunctorAdd' (Cx R) j (-P) (j - P) (by omega)).symm.app I))
  obtain ⟨b6, i6⟩ := cpull_iff s0 I (j - P)
  exact ⟨b6.trans (b5.symm.trans (b4.symm.trans (b3.trans (b2.trans b1.symm)))),
    i6.trans (i5.symm.trans (i4.symm.trans (i3.trans (i2.trans i1.symm))))⟩

theorem shift_of : LateralTheory.E.CxDescPf.shift := by
  intro R _ I A B φ p j
  obtain ⟨hb, hi⟩ := main_iff I φ (p : ℤ) j
  exact ⟨hb.1, hi.1⟩

end LateralTheory.E.shiftPf
end
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleAxioms.DescentSteps

section

@[expose] public section

namespace UpperTheory.Et.EtaleDescentEtaleAxioms

theorem a0 : LateralTheory.E.LevelIdentPf.FreeSingleHomotopyEquivDiscreteChains := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf
theorem a1 : LateralTheory.E.DescStepPf.LevelIdent := LateralTheory.E.LevelIdentPf.LevelIdent_of a0
theorem a2 : LateralTheory.E.stupidPf.trunc0 := LateralTheory.E.trunc0Pf.trunc0_of
theorem a3 : LateralTheory.E.stupidPf.incl := LateralTheory.E.inclPf.incl_of
theorem a4 : LateralTheory.E.CxDescPf.stupid := LateralTheory.E.stupidPf.stupid_of a2 a3
theorem a5 : LateralTheory.E.longPf.LES := GlobalTheory.T.hypercohomology_longExact_first_of_injective
theorem a6 : LateralTheory.E.CxDescPf.long := LateralTheory.E.longPfSes.long_of a5
theorem a7 : LateralTheory.E.CxDescPf.shift := LateralTheory.E.shiftPf.shift_of
theorem a8 : LateralTheory.E.DescStepPf.CxDesc := LateralTheory.E.CxDescPf.CxDesc_of a4 a6 a7
theorem a9 : LateralTheory.E.t_E1Cut.DescStep := LateralTheory.E.DescStepPf.etale_descent_induction_of_levelwise_identity_and_complex_descent a1 a8

theorem intersectionNumber_baseChange : LateralTheory.E.t_E1Cut.DescStep := a9

end UpperTheory.Et.EtaleDescentEtaleAxioms
end
end
