module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueMemDominatingValuationSubringStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulIsIntegralElemOfForallDiscreteValuationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericChartFunctionsFractionsSmoothStatement
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtBasicOpenOfIntegralMulChartValue

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Mum

theorem intAt_of_integral_mul_basicOpen : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → ∀ (x : X) (d : Γ(X, W)), x ∈ X.basicOpen d → (α.app W).hom.IsIntegralElem ((α.app W).hom d * chartVal L α s j W hW) → IntAt L α s x := by
  intro X Y L α k s j W hW hWa x d hx hint
  have hle : X.basicOpen d ≤ W := X.basicOpen_le d
  have hW' : X.basicOpen d ≤ L.U j := hle.trans hW
  refine ⟨j, X.basicOpen d, hW', hx, hWa.basicOpen d, ?_⟩
  set ρX := (X.presheaf.map (homOfLE hle).op).hom with hρX
  set ρY := (Y.presheaf.map ((TopologicalSpace.Opens.map α.base).map (homOfLE hle)).op).hom with hρY
  have hnat : ∀ r, ρY ((α.app W).hom r) = (α.app (X.basicOpen d)).hom (ρX r) := by
    intro r
    have := congrArg (fun g => g.hom r) (Scheme.Hom.naturality α (homOfLE hle).op)
    simpa [ρX, ρY] using this.symm
  have hcv : chartVal L α s j (X.basicOpen d) hW' = ρY (chartVal L α s j W hW) := by
    simp only [chartVal, ρY]
    change _ = (Y.presheaf.map (homOfLE (locInt_le_chart L α j W hW)).op ≫
      Y.presheaf.map ((TopologicalSpace.Opens.map α.base).map (homOfLE hle)).op).hom _
    rw [← Functor.map_comp]
    rfl

  have hint' : (α.app (X.basicOpen d)).hom.IsIntegralElem (ρY ((α.app W).hom d * chartVal L α s j W hW)) := by
    obtain ⟨p, hp, hp0⟩ := hint
    refine ⟨p.map ρX, hp.map ρX, ?_⟩
    rw [Polynomial.eval₂_map]
    have : ((α.app (X.basicOpen d)).hom.comp ρX) = ρY.comp (α.app W).hom := by
      ext r; exact (hnat r).symm
    rw [this, ← Polynomial.hom_eval₂, hp0, map_zero]
  obtain ⟨u, hu⟩ : IsUnit (ρX d) := X.toRingedSpace.isUnit_res_basicOpen d
  have hmul : ρY ((α.app W).hom d * chartVal L α s j W hW) =
      (α.app (X.basicOpen d)).hom (u : Γ(X, X.basicOpen d)) * chartVal L α s j (X.basicOpen d) hW' := by
    rw [map_mul, hnat, hcv]
    congr 2
    exact hu.symm
  rw [hmul] at hint'
  have key : chartVal L α s j (X.basicOpen d) hW' =
      (α.app (X.basicOpen d)).hom ((u⁻¹ : (Γ(X, X.basicOpen d))ˣ) : Γ(X, X.basicOpen d)) *
        ((α.app (X.basicOpen d)).hom (u : Γ(X, X.basicOpen d)) * chartVal L α s j (X.basicOpen d) hW') := by
    rw [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]
  rw [key]
  exact RingHom.IsIntegralElem.mul _ (RingHom.isIntegralElem_map _) hint'

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtBasicOpenOfIntegralMulChartValueStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.integralAt_basicOpen_of_integral_mul_chartValue : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → ∀ (x : X) (d : Γ(X, W)), x ∈ X.basicOpen d → (α.app W).hom.IsIntegralElem ((α.app W).hom d * chartVal L α s j W hW) → IntAt L α s x := by
  first | exact @GlobalTheory.Mum.intAt_of_integral_mul_basicOpen | exact GlobalTheory.Mum.intAt_of_integral_mul_basicOpen | (intros; apply GlobalTheory.Mum.intAt_of_integral_mul_basicOpen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfSmoothGeomIrreducibleOverModificatio

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumInt

theorem isIntegral_of_smooth : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S),
    Smooth G.hom → GeometricallyIrreducible G.hom → Nonempty G.left → IsIntegral G.left := by
  intro R _ _ M G hsm hgi _
  haveI := M.integral
  haveI : IsReduced G.left := GlobalTheory.isReduced_of_smooth_of_isReduced G.hom
  haveI : IrreducibleSpace G.left := GeometricallyIrreducible.irreducibleSpace G.hom G.hom.isOpenMap
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end GlobalTheory.MumInt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfSmoothGeomIrreducibleOverModificatioStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.isIntegral_of_smooth_geomIrreducible_over_modification : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → GeometricallyIrreducible G.hom → Nonempty G.left → IsIntegral G.left := by
  first | exact @GlobalTheory.MumInt.isIntegral_of_smooth | exact GlobalTheory.MumInt.isIntegral_of_smooth | (intros; apply GlobalTheory.MumInt.isIntegral_of_smooth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfSmoothOverModification

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isLocallyNoetherian_of_smooth_over_modif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → IsLocallyNoetherian G.left := by
  intro R _ _ _ M G hG
  haveI : IsLocallyNoetherian (Sp R) := inferInstance
  haveI := M.proper
  haveI : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  haveI := hG
  exact LocallyOfFiniteType.isLocallyNoetherian G.hom

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfSmoothOverModificationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.isLocallyNoetherian_of_smooth_over_modification : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → IsLocallyNoetherian G.left := by
  first | exact @GlobalTheory.Mum.isLocallyNoetherian_of_smooth_over_modif | exact GlobalTheory.Mum.isLocallyNoetherian_of_smooth_over_modif | (intros; apply GlobalTheory.Mum.isLocallyNoetherian_of_smooth_over_modif <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtClosedFibreOfRegularAtAllTraits

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_chart_affineOpen {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S) (L : LB G.left)
    (hL : L.IsLB) (x : G.left) : ∃ (j : L.ι) (U : M.S.Opens) (W : G.left.Opens) (_ : W ≤ L.U j) (_ : W ≤ G.hom ⁻¹ᵁ U),
      x ∈ W ∧ IsAffineOpen W ∧ IsAffineOpen U := by
  obtain ⟨j, hj⟩ := exists_chart hL x
  obtain ⟨U, hUa, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := G.hom x) (U := ⊤) trivial
  obtain ⟨W, hWa, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := L.U j ⊓ G.hom ⁻¹ᵁ U) ⟨hj, hxU⟩
  exact ⟨j, U, W, fun y hy => (hWle hy).1, fun y hy => (hWle hy).2, hxW, hWa, hUa⟩

theorem intAt_closed_of_traitReg : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), TraitReg M G L s → ∀ x : G.left, M.π (G.hom x) = closedPoint R → IntAt L α s x := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s hs x hx
  obtain ⟨j, U, W, hW, hWU, hxW, hWa, hUa⟩ := exists_chart_affineOpen M G L hL x
  obtain ⟨hinj, hloc⟩ := GlobalTheory.T.generic_chart_functions_fractions_smooth R M G hsm Y α t hpb W U hWU hWa hUa
  haveI : IsIntegral G.left := GlobalTheory.T.isIntegral_of_smooth_geomIrreducible_over_modification R M G hsm hgi ⟨x⟩
  haveI : IsLocallyNoetherian G.left := GlobalTheory.T.isLocallyNoetherian_of_smooth_over_modification R M G hsm
  haveI : Nonempty W := ⟨⟨x, hxW⟩⟩
  haveI : IsNoetherianRing Γ(G.left, W) := IsLocallyNoetherian.component_noetherian ⟨W, hWa⟩
  let p : Ideal Γ(G.left, W) := RingHom.ker ((G.left.residue x).hom.comp (G.left.presheaf.germ W x hxW).hom)
  obtain ⟨d, hd, hi⟩ := GlobalTheory.T.exists_mul_isIntegralElem_of_forall_dvr Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) (α.app W).hom hinj hloc p (RingHom.ker_isPrime _)
    (chartVal L α s j W hW) (fun F _ β V hV h1 h2 =>
      GlobalTheory.T.chartValue_mem_dominating_valuationSubring R M G hsm hqc hgi L hL Y α t hpb k s hs j U W hW hWU hWa hUa x hxW hx F β V hV h1
        (fun c hc => h2 c (RingHom.mem_ker.2 hc)))
  refine GlobalTheory.T.integralAt_basicOpen_of_integral_mul_chartValue L α k s j W hW hWa x d ?_ hi
  rw [Scheme.mem_basicOpen _ _ _ hxW]
  have : (G.left.residue x).hom ((G.left.presheaf.germ W x hxW).hom d) ≠ 0 := fun h => hd (RingHom.mem_ker.2 h)
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 this

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtClosedFibreOfRegularAtAllTraitsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.integral_at_closedFibre_of_regular_at_all_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), TraitReg M G L s → ∀ x : G.left, M.π (G.hom x) = closedPoint R → IntAt L α s x := by
  first | exact @GlobalTheory.Mum.intAt_closed_of_traitReg | exact GlobalTheory.Mum.intAt_closed_of_traitReg | (intros; apply GlobalTheory.Mum.intAt_closed_of_traitReg <;> assumption)
end
end
