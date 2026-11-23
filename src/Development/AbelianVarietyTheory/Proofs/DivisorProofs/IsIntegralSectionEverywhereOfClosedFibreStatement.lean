module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralElemNearFibreOfGenericPointStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenIntegralOfIntegralAtPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem chart_res_res {Y : Scheme.{0}} {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom x) =
      (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem chart_res_app {X Y : Scheme.{0}} (α : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    (Y.presheaf.map (homOfLE (α.preimage_mono h)).op).hom ((α.app U).hom x) =
      (α.app V).hom ((X.presheaf.map (homOfLE h).op).hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]; rfl

theorem isIntegralElem_of_square {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : C →+* D) (a : A →+* C) (b : B →+* D) (h : g.comp a = b.comp f) {x : B}
    (hx : f.IsIntegralElem x) : g.IsIntegralElem (b x) := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map a, hp.map a, ?_⟩
  rw [Polynomial.eval₂_map, h, ← Polynomial.hom_eval₂, hpx, map_zero]

theorem intAt_chart {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (ζ : X) :
    IntAt L α s ζ → ∀ (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → ζ ∈ W →
      ∃ c : Γ(X, W), ζ ∈ X.basicOpen c ∧ (α.app (X.basicOpen c)).hom.IsIntegralElem
        ((Y.presheaf.map (homOfLE (α.preimage_mono (X.basicOpen_le c))).op).hom (chartVal L α s j W hW)) := by
  intro hint j W hW hWa hζW
  obtain ⟨j', W', hW', hζW', hW'a, hint'⟩ := hint
  obtain ⟨c, hcle, hζc⟩ := hWa.exists_basicOpen_le (V := W ⊓ W') ⟨ζ, hζW, hζW'⟩ hζW
  refine ⟨c, hζc, ?_⟩
  have hBW : X.basicOpen c ≤ W := hcle.trans inf_le_left
  have hBW' : X.basicOpen c ≤ W' := hcle.trans inf_le_right
  have hBV : α ⁻¹ᵁ X.basicOpen c ≤ LB.wchart L (K := Fin 1) (fun _ => α) (fun _ => j) ⊓
      LB.wchart L (K := Fin 1) (fun _ => α) (fun _ => j') :=
    le_inf ((α.preimage_mono hBW).trans (locInt_le_chart L α j W hW))
      ((α.preimage_mono hBW').trans (locInt_le_chart L α j' W' hW'))
  have hBjj : X.basicOpen c ≤ L.U j ⊓ L.U j' := le_inf (hBW.trans hW) (hBW'.trans hW')
  have key := congrArg (Y.presheaf.map (homOfLE hBV).op).hom (s.compat (fun _ => j) (fun _ => j'))
  erw [chart_res_res, map_mul, chart_res_res] at key
  have ht : (Y.presheaf.map (homOfLE hBV).op).hom
      ((LB.LinComb L (K := Fin 1) (fun _ => α) (fun _ => (k : ℤ))).g (fun _ => j) (fun _ => j')).val =
      (α.app (X.basicOpen c)).hom (((X.presheaf.map (homOfLE hBjj).op).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j'))) ^ k) := by
    simp only [LB.LinComb, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val, res, pullU, Units.coe_map, map_pow]
    congr 1
    erw [Units.coe_map, Units.coe_map]
    erw [chart_res_res, ← chart_res_app α hBjj]
    rfl
  have hj' : (α.app (X.basicOpen c)).hom.IsIntegralElem
      ((Y.presheaf.map (homOfLE (α.preimage_mono hBW')).op).hom (chartVal L α s j' W' hW')) :=
    isIntegralElem_of_square (α.app W').hom (α.app (X.basicOpen c)).hom (X.presheaf.map (homOfLE hBW').op).hom
      (Y.presheaf.map (homOfLE (α.preimage_mono hBW')).op).hom (RingHom.ext fun x => (chart_res_app α hBW' x).symm) hint'
  rw [chartVal] at hj' ⊢
  erw [chart_res_res] at hj' ⊢
  erw [key, ht]
  exact RingHom.IsIntegralElem.mul _ (RingHom.isIntegralElem_map _) hj'

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenIntegralOfIntegralAtPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_basicOpen_integral_of_integral_at_point : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (ζ : X), IntAt L α s ζ → ∀ (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → ζ ∈ W → ∃ c : Γ(X, W), ζ ∈ X.basicOpen c ∧ (α.app (X.basicOpen c)).hom.IsIntegralElem ((Y.presheaf.map (homOfLE (α.preimage_mono (X.basicOpen_le c))).op).hom (chartVal L α s j W hW)) := by
  first | exact @GlobalTheory.Mum.intAt_chart | exact GlobalTheory.Mum.intAt_chart | (intros; apply GlobalTheory.Mum.intAt_chart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfIntegralAtFibreGenericPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.intAt_of_intAt_fibreGeneric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k) (x ζ : G.left), G.hom ζ = G.hom x → (∀ z, G.hom z = G.hom x → ζ ⤳ z) → IntAt L α s ζ → IntAt L α s x := by
  intro R _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s x ζ hζ hgen hint
  have hx : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := G.hom x) (U := ⊤) trivial
  obtain ⟨W, hW, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := L.U j ⊓ G.hom ⁻¹ᵁ U) ⟨hj, hxU⟩
  have hζW : ζ ∈ W := (hgen x rfl).mem_open W.isOpen hxW
  have hWj : W ≤ L.U j := fun z hz => (hWle hz).1
  have hWU : W ≤ G.hom ⁻¹ᵁ U := fun z hz => (hWle hz).2
  obtain ⟨c', hxc', hc'⟩ := GlobalTheory.T.isIntegralElem_near_fibre_of_generic_point R M G hsm hqc hgi Y α t hpb W hW U hU hWU (chartVal L α s j W hWj) x ζ hxW hζ hgen
    (GlobalTheory.T.exists_basicOpen_integral_of_integral_at_point L α k s ζ hint j W hWj hW hζW)
  refine ⟨j, G.left.basicOpen c', (G.left.basicOpen_le c').trans hWj, hxc', hW.basicOpen c', ?_⟩
  convert hc' using 1
  simp only [chartVal]
  erw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfIntegralAtFibreGenericPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.integral_of_integral_at_fibre_generic_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k) (x ζ : G.left), G.hom ζ = G.hom x → (∀ z, G.hom z = G.hom x → ζ ⤳ z) → IntAt L α s ζ → IntAt L α s x := by
  first | exact @GlobalTheory.Mum.intAt_of_intAt_fibreGeneric | exact GlobalTheory.Mum.intAt_of_intAt_fibreGeneric | (intros; apply GlobalTheory.Mum.intAt_of_intAt_fibreGeneric <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSectionEverywhereOfClosedFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isOpen_setOf_intAt {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) {k : ℕ} (s : SecK L α k) :
    IsOpen {x : X | IntAt L α s x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨j, W, hW, hx, hWa, hint⟩
  exact ⟨W, fun x' hx' => ⟨j, W, hW, hx', hWa, hint⟩, W.isOpen, hx⟩

theorem exists_fibre_generic {X S : Scheme.{0}} (f : X ⟶ S) [GeometricallyIrreducible f] (y : S) :
    ∃ ζ : X, f ζ = y ∧ ∀ z, f z = y → ζ ⤳ z := by
  refine ⟨f.fiberι y (genericPoint (f.fiber y)), ?_, ?_⟩
  · have : f.fiberι y (genericPoint (f.fiber y)) ∈ Set.range (f.fiberι y) := ⟨_, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  · intro z hz
    obtain ⟨z', rfl⟩ : z ∈ Set.range (f.fiberι y) := by rw [Scheme.Hom.range_fiberι]; exact hz
    exact (genericPoint_specializes z').map (f.fiberι y).continuous

theorem exists_specializes_closedPoint {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R)
    (y : M.S) : ∃ y₀, y ⤳ y₀ ∧ M.π y₀ = closedPoint R := by
  haveI := M.proper
  have hc : IsClosed (M.π '' closure {y}) := M.π.isClosedMap _ isClosed_closure
  have hm : M.π y ∈ M.π '' closure {y} := ⟨y, subset_closure rfl, rfl⟩
  obtain ⟨y₀, hy₀, e⟩ := (IsLocalRing.specializes_closedPoint (M.π y)).mem_closed hc hm
  exact ⟨y₀, specializes_iff_mem_closure.2 hy₀, e⟩

end GlobalTheory.Mum

theorem GlobalTheory.Mum.intAt_of_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), (∀ x : G.left, M.π (G.hom x) = closedPoint R → IntAt L α s x) → ∀ x : G.left, IntAt L α s x := by
  intro R _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s hcl x
  haveI := hsm; haveI := hgi
  by_contra hx
  obtain ⟨ζ, hζ, hζg⟩ := exists_fibre_generic G.hom (G.hom x)
  obtain ⟨y₀, hy₀, hy₀c⟩ := exists_specializes_closedPoint M (G.hom ζ)
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, G.hom g₀ = y₀ := by
    obtain ⟨g₀, hg₀, -⟩ := exists_fibre_generic G.hom y₀
    exact ⟨g₀, hg₀⟩
  obtain ⟨g, hg, hgg₀⟩ := Flat.generalizingMap G.hom (show G.hom ζ ⤳ G.hom g₀ from hg₀ ▸ hy₀)
  have hζg' : ζ ⤳ g := hζg g (hgg₀.trans hζ)
  have hnζ : ¬ IntAt L α s ζ := fun h => hx (GlobalTheory.T.integral_of_integral_at_fibre_generic_point R M G hsm hqc hgi L hL Y α t hpb k s x ζ hζ hζg h)
  have hclosed : IsClosed {z : G.left | ¬ IntAt L α s z} := (isOpen_setOf_intAt L α s).isClosed_compl
  have : ¬ IntAt L α s g₀ := (hζg'.trans hg).mem_closed hclosed hnζ
  exact this (hcl g₀ (by rw [hg₀, hy₀c]))
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSectionEverywhereOfClosedFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.isIntegralSection_everywhere_of_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), (∀ x : G.left, M.π (G.hom x) = closedPoint R → IntAt L α s x) → ∀ x : G.left, IntAt L α s x := by
  first | exact @GlobalTheory.Mum.intAt_of_closedFibre | exact GlobalTheory.Mum.intAt_of_closedFibre | (intros; apply GlobalTheory.Mum.intAt_of_closedFibre <;> assumption)
end
end
