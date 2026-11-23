module

public import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
public import Development.EtaleCohomology.EtaleSheaves.CupProductRingLaws
public import Development.EtaleCohomology.EtaleSheaves.ChernClassExistence
public import Development.EtaleCohomology.EtaleSheaves.ChernClassRootLocalization
public import Development.EtaleCohomology.EtaleSheaves.ChernClassEvaluation
import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsQthRootOfUnitWhenQInvertible
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
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Lemma
public import Development.EtaleCohomology.EtaleSheaves.ChernClassCocycleThird
import Development.EtaleCohomology.EtaleSheaves.ChernClassEvaluation
public import Development.EtaleCohomology.EtaleSheaves.ChernClassValueFirst
public import Development.EtaleCohomology.EtaleSheaves.ChernClassValueSecond
public import Development.EtaleCohomology.EtaleSheaves.FirstChernNaturality
import Mathlib.Tactic.Linter.Style
public import Development.EtaleCohomology.EtaleSheaves.LeafNatCupPf
public import Development.EtaleCohomology.EtaleSheaves.LeafPrimCoverPf
public import Development.EtaleCohomology.EtaleSheaves.LeafRootLocPf
public import Development.EtaleCohomology.EtaleSheaves.TwPairExists
public import Development.EtaleCohomology.EtaleSheaves.UnitExistence.CocycleOfSec
public import Development.EtaleCohomology.EtaleSheaves.UnitSections
public import Development.EtaleCohomology.TateTwists.EtaleKummerTorsorRootsOfUnityListTorsionExistsOf
public import Development.EtaleCohomology.TateTwists.HoldsOf
public import Development.EtaleCohomology.EtaleSheaves.LeafOneSpecPf

-- Source module: Development.EtaleCohomology.EtaleSheaves.ChernClassCocycleFirst

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernCocycleEdgeCoboundary


open LateralTheory.E.ChernClassRootLocalization in
theorem sec_dd (q : ℕ) {V : Scheme.{0}} (y : Sec ((res _ (tw q 1)).X 0) V) :
    Sec.map ((res _ (tw q 1)).d 1 2) (Sec.map ((res _ (tw q 1)).d 0 1) y) = 0 := by
  have h : (res _ (tw q 1)).d 0 1 ≫ (res _ (tw q 1)).d 1 2 = 0 := HomologicalComplex.d_comp_d _ _ _ _
  change ((((res _ (tw q 1)).d 0 1 ≫ (res _ (tw q 1)).d 1 2).hom.app (op V)).hom y) = 0
  rw [h]
  rfl

theorem etale_kummer_chern_cochain_coboundary_vanishes_on_edges_of_local_roots (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) : LateralTheory.E.ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnEdges := by
  intro q _ E L hi α hα U x
  have key : ∀ (V : Scheme.{0}) (x' : Sx E 1 V), ev (δ 2 3 α) 1 2 (by simp) V x' =
      Sec.map ((res _ (tw q 1)).d 1 2) (ev α 1 1 (by simp) V x') := by
    intro V x'
    have := (LateralTheory.E.ChernClassEvaluation.evDelta_pf (ZMod q) (I := res _ (tw q 1)) (n := 2) (m := 3) (by norm_num) α V).2
      0 1 2 (by simp) (by simp) x'
    rw [this]
    simp [hα.1]
  apply LateralTheory.E.ChernClassRootLocalization.sec_sep
  refine LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hi U x) fun V g hv => ?_
  obtain ⟨v, hv⟩ := hv
  rw [← LateralTheory.E.ChernClassRootLocalization.ev_res, key, hα.2.1 V _ v hv, sec_dd]
  exact (map_zero ((res _ (tw q 1)).X 2 |>.obj.map g.op).hom).symm

end LateralTheory.E.ChernCocycleEdgeCoboundary
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.ChernClassCocycleSecond

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernCocycleFaceFormulas

lemma δ0_eq : (SimplexCategory.δ (0 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 1 1 (by omega) := by
  ext i; fin_cases i <;> rfl

lemma δ2_eq : (SimplexCategory.δ (2 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 0 1 (by omega) := by
  ext i; fin_cases i <;> rfl

lemma face0 {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 0 = x.sub 1 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ; rw [δ0_eq]

lemma face2 {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 2 = x.sub 0 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ; rw [δ2_eq]

lemma glMat_face1 {U : Scheme.{0}} (y : Sx (ofCat (glCat 1)) 2 U) :
    glMat (y.face 1) = glMat (y.sub 1 1 (by omega)) * glMat (y.sub 0 1 (by omega)) := by
  let z : ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 := y
  have h1 : glMat (y.face 1) = z.map' 0 2 := rfl
  have h2 : glMat (y.sub 1 1 (by omega)) = z.map' 1 2 := rfl
  have h3 : glMat (y.sub 0 1 (by omega)) = z.map' 0 1 := rfl
  rw [h1, h2, h3, ← SingleObj.comp_as_mul, ← z.map'_comp 0 1 2]

lemma L_map {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} {m n : ℕ}
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (x : Sx E n U) :
    (L.app (op (SimplexCategory.mk m))).app (op U) ((E.map θ.op).app (op U) x) =
      ((ofCat (glCat 1)).map θ.op).app (op U) ((L.app (op (SimplexCategory.mk n))).app (op U) x) :=
  congrArg (fun φ => φ.app (op U) x) (L.naturality θ.op)

lemma lineUnit_face1 {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 2 U) :
    lineUnit L (x.face 1) = lineUnit L (x.sub 0 1 (by omega)) * lineUnit L (x.sub 1 1 (by omega)) := by
  have key := glMat_face1 ((L.app (op (SimplexCategory.mk 2))).app (op U) x)
  unfold lineUnit
  unfold Sx.face Sx.sub SimplicialObject.δ at *
  rw [L_map, L_map, L_map, key, map_mul, mul_comm]

open LateralTheory.E.ChernClassRootLocalization in
lemma etale_kummer_chern_cochain_coboundary_triangle_eq_zero_of_qth_roots (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1))
    (α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) (hα : LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α)
    (V : Scheme.{0}) (y : Sx E 2 V) (v w : (Γ(V, ⊤))ˣ) (hv : v ^ q = lineUnit L (y.sub 0 1 (by omega)))
    (hw : w ^ q = lineUnit L (y.sub 1 1 (by omega))) : ev (δ 2 3 α) 2 1 (by simp) V y = 0 := by
  have hd := (LateralTheory.E.ChernClassEvaluation.evDelta_pf (ZMod q) (show (2:ℤ) + 1 = 3 by norm_num) α V).2 1 0 1
    (by norm_num) (by norm_num) y
  have e0 : ev α 1 1 (by omega) V (y.face 0) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V w) :=
    hα.2.1 V _ w (by rw [face0]; exact hw)
  have e2 : ev α 1 1 (by omega) V (y.face 2) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V v) :=
    hα.2.1 V _ v (by rw [face2]; exact hv)
  have e1 : ev α 1 1 (by omega) V (y.face 1) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V (v * w)) :=
    hα.2.1 V _ (v * w) (by rw [lineUnit_face1, mul_pow, hv, hw])
  have e3 := hα.2.2 V y v w hv hw
  refine hd.trans ?_
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, add_zero]
  have e3' : ev α (1 + 1) 0 (by omega) V y = kumT q V v + kumT q V w - kumT q V (v * w) := e3
  have hn : (3 : ℤ).negOnePow = -1 := by rw [Int.negOnePow_odd]; decide
  rw [e3', e0, e1, e2, hn]
  simp only [Sec.map, map_add (f := _), map_sub]
  simp
  abel

open LateralTheory.E.ChernClassRootLocalization in
theorem etale_kummer_chern_cochain_coboundary_vanishes_on_triangles_of_local_r (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) : LateralTheory.E.ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTriangles := by
  intro q _ E L hi α hα U x
  apply sec_sep
  refine LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_and
    (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hi U (x.sub 0 1 (by omega)))
    (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hi U (x.sub 1 1 (by omega)))) fun V g hvw => ?_
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := hvw
  rw [← LateralTheory.EtaleFoundations.FirstChernUniqueness.sub_res] at hv hw
  rw [← ev_res]
  exact (etale_kummer_chern_cochain_coboundary_triangle_eq_zero_of_qth_roots q L α hα V _ v w hv hw).trans (map_zero ((_ : Sec _ U →ₗ[_] Sec _ V))).symm

end LateralTheory.E.ChernCocycleFaceFormulas
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.LeafEvMkPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafEvMkPf

variable {R : Type} [CommRing R]

def preLift {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (a U x) = a V (P.map g.op x)) :
    (freeP R).obj P ⟶ F.obj where
  app U := ModuleCat.ofHom (Finsupp.lift (F.obj.obj U) (ULift.{1} R) (ULift.{1} (P.obj U)) (fun y => a U.unop y.down))
  naturality := by
    intro U V g
    apply ModuleCat.free_hom_ext
    intro y'
    obtain ⟨y⟩ := y'
    have := ha V.unop U.unop g.unop y
    simp only [Sec.res, Quiver.Hom.op_unop, op_unop] at this
    dsimp [freeP]
    change (Finsupp.lift (F.obj.obj V) (ULift.{1} R) (ULift.{1} (P.obj V)) (fun y => a V.unop y.down))
        (Finsupp.mapDomain (fun x : ULift.{1} (P.obj U) => ULift.up (P.map g x.down)) (Finsupp.single (ULift.up y) 1)) =
      F.obj.map g ((Finsupp.lift (F.obj.obj U) (ULift.{1} R) (ULift.{1} (P.obj U)) (fun y => a U.unop y.down)) (Finsupp.single (ULift.up y) 1))
    rw [Finsupp.mapDomain_single, Finsupp.lift_apply, Finsupp.lift_apply, Finsupp.sum_single_index, Finsupp.sum_single_index]
    · simpa using this.symm
    all_goals simp

theorem preLift_app {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U) (ha) (U : Scheme.{0})
    (x : P.obj (op U)) : ((preLift a ha).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) = a U x := by
  show (Finsupp.lift (F.obj.obj (op U)) (ULift.{1} R) (ULift.{1} (P.obj (op U))) (fun y => a U y.down)) (Finsupp.single (ULift.up x) 1) = _
  rw [Finsupp.lift_apply, Finsupp.sum_single_index] <;> simp

def shLift {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (a U x) = a V (P.map g.op x)) :
    (free R).obj P ⟶ F :=
  ObjectProperty.homMk (sheafifyLift Scheme.etaleTopology (preLift a ha) F.property)

theorem shLift_gen {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U) (ha) (U : Scheme.{0})
    (x : P.obj (op U)) : ((shLift a ha).hom.app (op U)).hom (freeGen R P U x) = a U x := by
  unfold freeGen
  change ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ sheafifyLift Scheme.etaleTopology (preLift a ha) F.property).app (op U)).hom _ = _
  rw [toSheafify_sheafifyLift]
  exact preLift_app a ha U x

variable {E : Spc} {I : Cx R} {n : ℤ}

def comp (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) : ((chains R).obj E).X (-(p : ℤ)) ⟶ I.X s :=
  (chainsXIso R E p).hom ≫ shLift (P := E.obj (op (SimplexCategory.mk p))) (a p s h) (fun V U g x => ha p s h V U g x)

theorem comp_key (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p q : ℕ) (hq : q = p) (s : ℤ) (h : -(p : ℤ) + n = s) (h' : -(q : ℤ) + n = s)
    (e : ((chains R).obj E).X (-(p : ℤ)) = ((chains R).obj E).X (-(q : ℤ))) :
    (chainsXIso R E p).inv ≫ eqToHom e ≫ comp a ha q s h' =
      shLift (P := E.obj (op (SimplexCategory.mk p))) (a p s h) (fun V U g x => ha p s h V U g x) := by
  subst hq
  simp [comp]

theorem LeafEvMk_of : LateralTheory.E.ChernClassExistence.LeafEvMk := by
  intro R _ E I n a ha
  refine ⟨Cochain.mk fun i j hij => if hi : i ≤ 0 then
      eqToHom (congrArg (fun k => ((chains R).obj E).X k) (by omega : i = -(((-i).toNat : ℕ) : ℤ))) ≫
        comp a ha ((-i).toNat) j (by omega) else 0, ?_⟩
  intro p s h U x
  unfold ev
  rw [Cochain.mk_v, dite_eq_left (by omega), comp_key a ha p _ (by omega) s h]
  exact shLift_gen _ _ U x

end LateralTheory.E.LeafEvMkPf
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.LeafNatOnePf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafNatOnePf

variable {R : Type} [CommRing R]

theorem free_map_freeGen {P Q : PSh} (g : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map g).hom.app (op U)).hom (freeGen R P U x) = freeGen R Q U (g.app (op U) x) := by
  have h := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map g))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.coe_comp] at h
  unfold freeGen
  refine h.symm.trans (congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom y) ?_)
  exact ModuleCat.free_map_apply (R := ULift.{1} R) (uliftFunctor.{1}.map (g.app (op U))) (ULift.up.{1} x)

theorem chainsXIso_nat {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  unfold chainsXIso chains
  rw [Functor.comp_map, ComplexShape.Embedding.extendFunctor_map,
    HomologicalComplex.extendMap_f _ _ (i := p) (i' := -(p : ℤ)) rfl]
  erw [Iso.inv_hom_id_assoc]
  rfl

theorem ev_pull {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  unfold ev
  rw [Cochain.comp_v _ _ (zero_add n) (-(p : ℤ)) (-(p : ℤ)) s (by omega) (by omega), Cochain.ofHom_v,
    ← Category.assoc, chainsXIso_nat, Category.assoc]
  rw [← free_map_freeGen]
  rfl

theorem LeafNatOne_of (hOne : LateralTheory.E.CupProductRingLaws.LeafOneSpec) : LateralTheory.E.CupProductRingLaws.LeafNatOne := by
  intro q _ E E' f hE'
  have hE : Inv q E := fun U ⟨x⟩ => hE' U ⟨(f.app (op (SimplexCategory.mk 0))).app (op U) x⟩
  obtain ⟨⟨α, hα⟩, h'⟩ := hOne q E' hE'
  rw [h' α hα]
  let β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0 :=
    zcomp (Cocycle.ofHom ((chains (ZMod q)).map f)) α (zero_add 0)
  have hβ : LateralTheory.E.CupProductRingLaws.IsOneCocycle q E β := fun U x ζ => by
    rw [← hα U ((f.app (op (SimplexCategory.mk 0))).app (op U) x) ζ]
    exact ev_pull f α.1 0 0 _ U x
  rw [(hOne q E hE).2 β hβ]
  rfl

end LateralTheory.E.LeafNatOnePf
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.EtaleFirstChernClassRepresentedByChernCocycle

section

@[expose] public section

namespace LateralTheory.E.LeafA6nat_xy7V2Cut

theorem kumTExists : LateralTheory.E.CupProductRingLaws.LeafKumTExists := fun q _ =>
  ⟨_, LateralTheory.Fin.EtaleKummerTriangleExists.intersectionNumber_baseChange q⟩

theorem oneSpec : LateralTheory.E.CupProductRingLaws.LeafOneSpec :=
  LateralTheory.E.LeafOneSpecPf.LeafOneSpec_of
    (LateralTheory.E.LeafOneExistsPf.CocycleOfSec.LeafOneExists_of_unit LateralTheory.E.UnitSections.LeafUnitSec_of)
    LateralTheory.E.LeafPrimCoverPf.LeafPrimCover_of

theorem etaleFirstChernClass_represented_by_chern_cocycle : LateralTheory.E.CupProductRingLaws.EtaleFirstChernClassRepresentedByChernCocycle :=
  have hr := LateralTheory.E.LeafRootLocPf.LeafRootLoc_of
  LateralTheory.E.ChernClassRootLocalization.etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique
    (LateralTheory.E.ChernClassEvaluation.etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness LateralTheory.E.LeafEvMkPf.LeafEvMk_of
      (LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor.etale_kummer_chern_edge_values_exist_of_local_roots_and_kummer_torsor hr kumTExists) (LateralTheory.E.ChernClassTriangleValuesFromKummerTorsor.etale_kummer_chern_triangle_values_exist_of_local_roots_and_kummer_tor hr kumTExists)
      (LateralTheory.E.ChernCocycleEdgeCoboundary.etale_kummer_chern_cochain_coboundary_vanishes_on_edges_of_local_roots hr) (LateralTheory.E.ChernCocycleFaceFormulas.etale_kummer_chern_cochain_coboundary_vanishes_on_triangles_of_local_r hr) (LateralTheory.E.ChernCocycleFaceDegeneracyIdentities.etale_kummer_chern_cochain_coboundary_vanishes_on_tetrahedra_of_root_localization hr))
    hr

theorem natKum : LateralTheory.E.CupProductRingLaws.LeafNatKum := fun q _ =>
  ((LateralTheory.Fix.EtaleKummerClassExplicitCocycle.holds_of LateralTheory.Fin.EtaleKummerTriangleExists.intersectionNumber_baseChange) q).2.1

theorem goal_of : LateralTheory.E.D2.LeafA6nat := fun q _ =>
  ⟨LateralTheory.E.LeafNatCupPf.LeafNatCup_of LateralTheory.Fix.CupProductTensor.cupSpec q,
   LateralTheory.E.LeafNatOnePf.LeafNatOne_of oneSpec q,
   LateralTheory.E.FirstChernNaturality.etale_first_chern_class_natural_of_spec etaleFirstChernClass_represented_by_chern_cocycle q,
   natKum q⟩

end LateralTheory.E.LeafA6nat_xy7V2Cut
end
end
