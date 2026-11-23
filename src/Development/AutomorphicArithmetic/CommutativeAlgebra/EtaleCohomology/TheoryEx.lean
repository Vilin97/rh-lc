module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFacts
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TPullTMap
public import Mathlib.GroupTheory.FreeAbelianGroup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Mon
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceSnocCastSucc
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.EtaleIdempotents.ExistsCoefficientEquivCohomologyOfElements
public import Development.AutomorphicArithmetic.EtaleIdempotents.ExistsCohomologyZeroEquivSectionsNatural

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.VanishOfExact

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.CH
open GlobalTheory.CatH (face toLast)

namespace UpperTheory.Ru.crystallineComparison.Th

variable {C : Type 1} [Category.{0} C]

theorem fa_ext {X : Type 1} {A : AddCommGrpCat.{1}} {f g : AddCommGrpCat.of (FreeAddCommGroup X) ⟶ A}
    (h : ∀ x, f.hom (FreeAddCommGroup.of x) = g.hom (FreeAddCommGroup.of x)) : f = g := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
  induction x using FreeAddCommGroup.induction_on with
  | zero => simp
  | of x => exact h x
  | neg x ih => simpa using congrArg Neg.neg (h x)
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

variable (P : C ⥤ Type)

abbrev Gen (k : ℕ) (B : C) : Type 1 := Σ s : ComposableArrows P.Elements k, ((s.obj (Fin.last k)).1 ⟶ B)

def L (k : ℕ) : Coef C where
  obj B := AddCommGrpCat.of (FreeAddCommGroup (Gen P k B))
  map φ := AddCommGrpCat.ofHom (FreeAddCommGroup.map fun g => ⟨g.1, g.2 ≫ φ⟩)
  map_id B := fa_ext fun x => by simp
  map_comp φ ψ := fa_ext fun x => by simp

def gFace {k : ℕ} {B : C} (i : Fin (k + 2)) (g : Gen P (k + 1) B) : Gen P k B :=
  ⟨face i g.1, (toLast i g.1).1 ≫ g.2⟩

def dL (k : ℕ) : L P (k + 1) ⟶ L P k where
  app B := AddCommGrpCat.ofHom (FreeAddCommGroup.lift fun g => ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • FreeAddCommGroup.of (gFace P i g))
  naturality B B' φ := fa_ext fun g => by
    simp [L, gFace]

variable {P}

def tOf {K : Coef C} {k : ℕ} (f : Cn (elF P (zm K)) k) : L P k ⟶ K where
  app B := AddCommGrpCat.ofHom (FreeAddCommGroup.lift fun g => (K.map g.2).hom (f g.1))
  naturality B B' φ := fa_ext fun g => by
    simp [L]

def cOf {K : Coef C} {k : ℕ} (u : L P k ⟶ K) : Cn (elF P (zm K)) k :=
  fun s => (u.app (s.obj (Fin.last k)).1).hom (FreeAddCommGroup.of ⟨s, 𝟙 _⟩)

theorem L_map_of {B B' : C} (φ : B ⟶ B') {k : ℕ} (g : Gen P k B) :
    ((L P k).map φ).hom (FreeAddCommGroup.of g) = FreeAddCommGroup.of (⟨g.1, g.2 ≫ φ⟩ : Gen P k B') :=
  FreeAddCommGroup.map_of_apply _

theorem dL_of {k : ℕ} {B : C} (g : Gen P (k + 1) B) :
    ((dL P k).app B).hom (FreeAddCommGroup.of g) =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • (FreeAddCommGroup.of (gFace P i g) : (L P k).obj B) :=
  FreeAddCommGroup.lift_apply_of _ _

theorem tOf_of {K : Coef C} {k : ℕ} (f : Cn (elF P (zm K)) k) {B : C} (g : Gen P k B) :
    ((tOf f).app B).hom (FreeAddCommGroup.of g) = (K.map g.2).hom (f g.1) :=
  FreeAddCommGroup.lift_apply_of _ _

theorem cOf_tOf {K : Coef C} {k : ℕ} (f : Cn (elF P (zm K)) k) : cOf (tOf f) = f := by
  funext s
  refine (tOf_of f _).trans ?_
  simp only [K.map_id]
  rfl

theorem u_of {K : Coef C} {k : ℕ} (u : L P k ⟶ K) {B : C} (g : Gen P k B) :
    (u.app B).hom (FreeAddCommGroup.of g) = (K.map g.2).hom (cOf u g.1) := by
  obtain ⟨s, a⟩ := g
  have h2 : ((L P k).map a).hom (FreeAddCommGroup.of (⟨s, 𝟙 _⟩ : Gen P k _)) = FreeAddCommGroup.of (⟨s, a⟩ : Gen P k B) := by
    rw [L_map_of]; simp
  have h3 := congrArg (fun f => f.hom (FreeAddCommGroup.of (⟨s, 𝟙 _⟩ : Gen P k _))) (u.naturality a)
  refine Eq.trans ?_ h3
  exact (congrArg (u.app B).hom h2).symm

theorem tOf_cOf {K : Coef C} {k : ℕ} (u : L P k ⟶ K) : tOf (cOf u) = u := by
  ext B : 2
  exact fa_ext fun g => (tOf_of _ g).trans (u_of u g).symm

theorem d_apply' {K : Coef C} {k : ℕ} (f : Cn (elF P (zm K)) k) (s : ComposableArrows P.Elements (k + 1)) :
    d (elF P (zm K)) k f s = ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • (K.map (toLast i s).1).hom (f (face i s)) := rfl

theorem d_cOf {K : Coef C} {k : ℕ} (u : L P k ⟶ K) : d (elF P (zm K)) k (cOf u) = cOf (dL P k ≫ u) := by
  funext s
  rw [d_apply']
  change _ = (u.app _).hom (((dL P k).app _).hom (FreeAddCommGroup.of (⟨s, 𝟙 _⟩ : Gen P (k + 1) _)))

  rw [dL_of, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, u_of]
  simp [gFace]

theorem tOf_d {K : Coef C} {k : ℕ} (f : Cn (elF P (zm K)) k) : tOf (d (elF P (zm K)) k f) = dL P k ≫ tOf f := by
  ext B : 2
  refine fa_ext fun g => (tOf_of _ g).trans ?_
  change _ = ((tOf f).app B).hom (((dL P k).app B).hom (FreeAddCommGroup.of g))

  rw [d_apply', dL_of, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul, tOf_of]
  simp [gFace]

theorem tOf_zero {K : Coef C} {k : ℕ} : tOf (0 : Cn (elF P (zm K)) k) = 0 := by
  ext B : 2
  refine fa_ext fun g => (tOf_of _ g).trans ?_
  exact map_zero _

theorem dL_dL (k : ℕ) : dL P (k + 1) ≫ dL P k = 0 := by
  have h := tOf_d (d (elF P (zm (L P k))) k (cOf (𝟙 _)))
  rw [CrystallineSemistableComparison.CH.d_d, tOf_zero, tOf_d, tOf_cOf, Category.comp_id] at h
  exact h.symm

theorem vanish_of_exact (hex : ∀ k, (ShortComplex.mk (dL P (k + 1)) (dL P k) (dL_dL k)).Exact)
    (K : Coef C) (hK : Injective K) (j : ℕ) : Subsingleton (TH P K (j + 1)) := by
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ x : TH P K (j + 1), x = 0 by rw [h x, h y]
  intro x
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx (elF P (zm K))) (j + 1)).1 x
  rw [(CrystallineSemistableComparison.P.cls_surj (cx (elF P (zm K))) (j + 1)).2.1]
  have h0 : dL P (j + 1) ≫ tOf f = 0 := by
    rw [← tOf_d]
    exact (congrArg tOf hf).trans tOf_zero
  refine ⟨cOf ((hex j).descToInjective (tOf f) h0), ?_⟩
  refine (d_cOf _).trans ?_
  have := (hex j).comp_descToInjective (tOf f) h0
  simp only at this
  rw [this, cOf_tOf]

end UpperTheory.Ru.crystallineComparison.Th
end
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GFaceSnGCastSucc

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.CH
open GlobalTheory.CatH (face toLast)

namespace UpperTheory.Ru.crystallineComparison.Th

variable {C : Type 1} [Category.{0} C]

theorem exact_of_app (S : ShortComplex (Coef C))
    (h : ∀ B, Function.Exact (S.f.app B).hom (S.g.app B).hom) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  refine CategoryTheory.Functor.isZero _ fun B => ?_
  have h1 : (S.map ((evaluation C AddCommGrpCat.{1}).obj B)).Exact :=
    (ShortComplex.ab_exact_iff_function_exact _).2 (h B)
  rw [ShortComplex.exact_iff_isZero_homology] at h1
  exact h1.of_iso (S.mapHomologyIso ((evaluation C AddCommGrpCat.{1}).obj B)).symm

variable {P : C ⥤ Type}

def snG {m : ℕ} {B : C} (g : Gen P m B) (z : P.obj B) (h : (P.map g.2) (g.1.obj (Fin.last m)).2 = z) : Gen P (m + 1) B :=
  let a : g.1.obj (Fin.last m) ⟶ P.elementsMk B z := Functor.Elements.homMk g.2 h
  ⟨snoc g.1 a, (snε g.1 a).1⟩

theorem snG_eq {m : ℕ} {B : C} (g : Gen P m B) {z : P.obj B} (h : (P.map g.2) (g.1.obj (Fin.last m)).2 = z) :
    snG g z h = snG g _ rfl := by
  subst h; rfl

def sn {m : ℕ} {B : C} (g : Gen P m B) : Gen P (m + 1) B := snG g _ rfl

theorem gFace_snG_last {m : ℕ} {B : C} (g : Gen P m B) (z : P.obj B) (h : (P.map g.2) (g.1.obj (Fin.last m)).2 = z) :
    gFace P (Fin.last (m + 1)) (snG g z h) = g :=
  congrArg (fun p : (Σ t : ComposableArrows P.Elements m, t.obj (Fin.last m) ⟶ P.elementsMk B z) =>
    (⟨p.1, p.2.1⟩ : Gen P m B)) (gen_snoc_last g.1 (X := P.elementsMk B z) (Functor.Elements.homMk g.2 h))

theorem gFace_snG_castSucc {m : ℕ} {B : C} (g : Gen P (m + 1) B) (z : P.obj B) (h : (P.map g.2) (g.1.obj (Fin.last (m + 1))).2 = z)
    (i : Fin (m + 2)) (h' : (P.map (gFace P i g).2) ((gFace P i g).1.obj (Fin.last m)).2 = z) :
    gFace P i.castSucc (snG g z h) = snG (gFace P i g) z h' :=
  congrArg (fun p : (Σ t : ComposableArrows P.Elements (m + 1), t.obj (Fin.last (m + 1)) ⟶ P.elementsMk B z) =>
    (⟨p.1, p.2.1⟩ : Gen P (m + 1) B)) (gen_snoc_castSucc g.1 (X := P.elementsMk B z) (Functor.Elements.homMk g.2 h) i)

theorem gFace_sn_last {m : ℕ} {B : C} (g : Gen P m B) : gFace P (Fin.last (m + 1)) (sn g) = g := gFace_snG_last g _ rfl

theorem gFace_sn_castSucc {m : ℕ} {B : C} (g : Gen P (m + 1) B) (i : Fin (m + 2)) :
    gFace P i.castSucc (sn g) = sn (gFace P i g) := by
  have h' : (P.map (gFace P i g).2) ((gFace P i g).1.obj (Fin.last m)).2 = (P.map g.2) (g.1.obj (Fin.last (m + 1))).2 := by
    have e := (toLast i g.1).2
    change (P.map ((toLast i g.1).1 ≫ g.2)) _ = _
    rw [P.map_comp]
    exact congrArg (P.map g.2) e
  exact (gFace_snG_castSucc g _ rfl i h').trans (snG_eq _ h')

def hh (B : C) (m : ℕ) : (L P m).obj B →+ (L P (m + 1)).obj B := (FreeAddCommGroup.map sn : FreeAddCommGroup (Gen P m B) →+ _)

theorem hh_of (B : C) (m : ℕ) (g : Gen P m B) : hh B m (FreeAddCommGroup.of g) = FreeAddCommGroup.of (sn g) :=
  FreeAddCommGroup.map_of_apply _

def ofL {k : ℕ} {B : C} (g : Gen P k B) : (L P k).obj B := FreeAddCommGroup.of g

theorem d_hh_of (B : C) (k : ℕ) (g : Gen P (k + 1) B) :
    ((dL P (k + 1)).app B).hom (hh B (k + 1) (ofL g)) = hh B k (((dL P k).app B).hom (ofL g)) + (-1 : ℤ) ^ (k + 2) • ofL g := by
  unfold ofL

  rw [hh_of, dL_of, dL_of, Fin.sum_univ_castSucc, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hh_of, gFace_sn_castSucc]
    rfl
  · rw [gFace_sn_last]
    rfl

theorem d_hh (B : C) (k : ℕ) (y : (L P (k + 1)).obj B) :
    ((dL P (k + 1)).app B).hom (hh B (k + 1) y) = hh B k (((dL P k).app B).hom y) + (-1 : ℤ) ^ (k + 2) • y := by
  have key : AddCommGrpCat.ofHom (((dL P (k + 1)).app B).hom.comp (hh B (k + 1))) =
      AddCommGrpCat.ofHom ((hh B k).comp ((dL P k).app B).hom + (-1 : ℤ) ^ (k + 2) • AddMonoidHom.id ((L P (k + 1)).obj B)) := by
    exact fa_ext fun g => d_hh_of B k g
  exact congrArg (fun f => f.hom y) key

theorem exact_dL (k : ℕ) : (ShortComplex.mk (dL P (k + 1)) (dL P k) (dL_dL k)).Exact := by
  refine exact_of_app _ fun B y => ⟨fun hy => ?_, ?_⟩
  · refine ⟨(-1 : ℤ) ^ (k + 2) • hh B (k + 1) y, ?_⟩
    have e := d_hh B k y
    have hy' : ((dL P k).app B).hom y = 0 := hy
    rw [hy', map_zero, zero_add] at e
    change ((dL P (k + 1)).app B).hom _ = y
    rw [map_zsmul, e, smul_smul, ← mul_pow]
    simp
  · rintro ⟨x, rfl⟩
    exact congrArg (fun f => f.hom x) (congrArg (fun f => f.app B) (dL_dL (P := P) k))

theorem vanish (P : C ⥤ Type) (K : Coef C) (hK : Injective K) (j : ℕ) : Subsingleton (TH P K (j + 1)) :=
  vanish_of_exact exact_dL K hK j

end UpperTheory.Ru.crystallineComparison.Th
end
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TheoryEx

section

@[expose] public section

theorem UpperTheory.Ru.crystallineComparison.theoryEx :
    UpperTheory.Ru.crystallineComparison.TheoryEx := by
  intro C _
  obtain ⟨z, hz₁, hz₂⟩ := UpperTheory.exists_cohomology_zero_equiv_sections_natural C
  refine ⟨{ H := UpperTheory.Ru.crystallineComparison.Th.TH
            ab := fun _ _ _ => inferInstance
            pull := fun u F j => UpperTheory.Ru.crystallineComparison.Th.tPull u F j
            map := fun P _ _ α j => UpperTheory.Ru.crystallineComparison.Th.tMap P α j
            pull_map := fun u _ _ α j x => UpperTheory.Ru.crystallineComparison.Th.tPull_tMap u α j x
            δ := UpperTheory.Ru.crystallineComparison.Th.tδ
            pull_δ := fun u S h j x => UpperTheory.Ru.crystallineComparison.Th.tPull_tδ u S h j x
            ex₃ := UpperTheory.Ru.crystallineComparison.Th.ex₃
            ex₁ := UpperTheory.Ru.crystallineComparison.Th.ex₁
            zero := z
            zero_pull := hz₁
            zero_map := hz₂
            inj := UpperTheory.Ru.crystallineComparison.Th.vanish }, fun R _ F => ?_⟩
  obtain ⟨F', c, e, h₁, h₂⟩ := UpperTheory.exists_coefficient_equiv_cohomology_of_elements C R F
  exact ⟨F', c, e, h₁, h₂⟩
end
end
