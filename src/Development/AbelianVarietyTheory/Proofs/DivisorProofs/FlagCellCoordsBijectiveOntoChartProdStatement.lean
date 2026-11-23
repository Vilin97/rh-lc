module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BearsFlagUnitriangularIffMemCellStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpUUniqueOfLower
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFlagBundleCellAndCoordsRegularStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackGramMatricesIndependentOfFrame

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellPointsExistsUniqueUnitriangular

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

theorem det_upU {K : Type} [Field K] {s : ℕ} (y : Low s → K) : (upU y).det = 1 := by
  have hb : (upU y).BlockTriangular id := fun a b (hab : b < a) => by
    simp only [upU, Matrix.of_apply, dif_neg (not_lt.2 hab.le), if_neg (ne_of_gt hab)]
  rw [Matrix.det_of_upperTriangular hb]
  exact Finset.prod_eq_one fun a _ => by simp [upU]

theorem pts_of {F : Type} [Field F] {X Y : Var F} {ι : Type} [Fintype ι] {m : ι → ℕ} {E : Fr (ratOf X) m 0}
    {E' : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hR : Refines E E' φ f) {A : Mat m X.Fn}
    {u : Cell m → Y.Fn} (hg : InCell E E' φ f A u (genericPoint Y.X)) {K : Type} [Field K] (x : Sp K ⟶ X.X)
    (hA : A ∈ E.S (x (IsLocalRing.closedPoint K))) (y₀ : Cell m → K)
    (hbears : ∀ p : Sp K ⟶ Y.X, A ∈ E.S (f (p (IsLocalRing.closedPoint K))) →
      (Bears E' φ A (upM y₀) p ↔ ∃ u' : Cell m → Y.Fn, upM u' * A.map φ ∈ E'.S (p (IsLocalRing.closedPoint K)) ∧
        ∀ j, (ratOf Y).val p (u' j) = y₀ j))
    (huniq : ∀ (s : ℕ) (y y' : Low s → Y.Fn) (b : Matrix (Fin s) (Fin s) Y.Fn), (∀ i j, i < j → b i j = 0) →
      upU y = b * upU y' → y = y') :
    ∃! p : Sp K ⟶ Y.X, p ≫ f = x ∧ InCell E E' φ f A u (p (IsLocalRing.closedPoint K)) ∧
      ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  have hPar : Par 0 ⊤ (upM y₀) := fun τ =>
    ⟨fun _ _ => trivial, by simp [upM, det_upU], trivial, fun _ _ hi => absurd hi (Nat.not_lt_zero _)⟩
  obtain ⟨p, ⟨hpf, hpB⟩, huq⟩ := hR.lifts K x A hA (upM y₀) hPar
  have hfz : f (p (IsLocalRing.closedPoint K)) = x (IsLocalRing.closedPoint K) := by
    rw [← hpf]; rfl
  have hA' : A ∈ E.S (f (p (IsLocalRing.closedPoint K))) := hfz ▸ hA
  obtain ⟨u', hu'S, hu'v⟩ := (hbears p hA').1 hpB
  have huu : u' = u := by
    have h1 := Fr.mem_genericPoint hu'S
    have hdA : ∀ τ, (A.map φ τ).det ≠ 0 := fun τ => by
      have := Mat.det_map A φ.toRingHom τ
      rw [show A.map φ.toRingHom = A.map φ from rfl] at this
      rw [this]; exact (map_ne_zero _).2 (Fr.det_ne hg.1 τ)
    have hdu : ∀ τ, (upM u τ).det ≠ 0 := fun τ => by simp [upM, det_upU]
    have hP := (Fr.mem_iff hg.2).1 h1
    rw [Mat.mul_inv_rev, ← mul_assoc, mul_assoc (upM u'), Mat.mul_inv hdA, mul_one] at hP
    have he : upM u' = (upM u' * (upM u)⁻¹) * upM u := by rw [mul_assoc, Mat.inv_mul hdu, mul_one]
    funext ⟨τ, s⟩
    have := huniq (m τ) (fun s => u' ⟨τ, s⟩) (fun s => u ⟨τ, s⟩) ((upM u' * (upM u)⁻¹) τ)
      (fun i j hij => (hP τ).2.2.2 i j i.2 hij) (congrFun he τ)
    exact congrFun this s
  subst huu
  refine ⟨p, ⟨hpf, ⟨hA', hu'S⟩, hu'v⟩, fun p' ⟨hp'f, ⟨h1, h2⟩, hv⟩ => huq p' ⟨hp'f, (hbears p' h1).2 ⟨u', h2, hv⟩⟩⟩

theorem cell_points_existsUnique : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (A : Mat m X.Fn) (u : Cell m → Y.Fn), InCell E E' φ f A u (genericPoint Y.X) → ∀ (K : Type) [Field K] (x : Sp K ⟶ X.X), A ∈ E.S (x (IsLocalRing.closedPoint K)) → ∀ y₀ : Cell m → K, ∃! p : Sp K ⟶ Y.X, p ≫ f = x ∧ InCell E E' φ f A u (p (IsLocalRing.closedPoint K)) ∧ ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  intro F _ X Y ι _ m E E' φ f hR A u hg K _ x hA y₀
  exact pts_of hR hg x hA y₀ (fun p hp => GlobalTheory.T.bearsFlag_unitriangular_iff_mem_cell F X Y ι m E E' φ f hR A K p hp y₀)
    (fun s y y' b hb h => upU_unique_of_lower Y.Fn s y y' b hb h)

end GlobalTheory.FlagCell2
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellPointsExistsUniqueUnitriangularStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.flag_cell_points_existsUnique_unitriangular : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (A : Mat m X.Fn) (u : Cell m → Y.Fn), InCell E E' φ f A u (genericPoint Y.X) → ∀ (K : Type) [Field K] (x : Sp K ⟶ X.X), A ∈ E.S (x (IsLocalRing.closedPoint K)) → ∀ y₀ : Cell m → K, ∃! p : Sp K ⟶ Y.X, p ≫ f = x ∧ InCell E E' φ f A u (p (IsLocalRing.closedPoint K)) ∧ ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  first | exact @GlobalTheory.FlagCell2.cell_points_existsUnique | exact GlobalTheory.FlagCell2.cell_points_existsUnique | (intros; apply GlobalTheory.FlagCell2.cell_points_existsUnique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellCoordsBijectiveOntoChartProd

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2

theorem pt_bsL_fb {n d : ℕ} {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (w : V n) : pt ε (bsL ε w) (fb ε w) = w := by
  ext a
  obtain ⟨x, rfl⟩ := ε.symm.surjective a
  rcases x with b | j <;> simp [pt, bsL_apply, fb]

theorem cellMap_image_eq : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), InCell E E' φ f A u (genericPoint Y.X) → ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m), IsOpen (cellSet E E' φ f hf c A u) ∧ Set.InjOn (cellMap ε f hf c u) (cellSet E E' φ f hf c A u) ∧ ∀ T : Set (CxPts X.str σ), T ⊆ c.e.source → (∀ x ∈ T, A ∈ E.S (under x)) → cellMap ε f hf c u '' (ptMap σ f hf ⁻¹' T ∩ cellSet E E' φ f hf c A u) = bsL ε ⁻¹' (c.e '' T) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR c A u hgen n ε
  have hO := GlobalTheory.T.isOpen_flagBundleCell_and_coords_regular F X Y ι m E E' φ f hR A u
  have hP := GlobalTheory.T.flag_cell_points_existsUnique_unitriangular F X Y ι m E E' φ f hR A u hgen
  have hval : ∀ y : CxPts Y.str σ, InCell E E' φ f A u (under y) → ∀ j,
      ratVal (u j) y = (ratOf Y).val y.1 (u j) :=
    fun y hy j => ratVal_eq_val_ratOf y (mem_O_ratOf.2 (hO.2 _ hy j))
  refine ⟨?_, ?_, ?_⟩
  · let W : Y.X.Opens := ⟨{y | InCell E E' φ f A u y}, hO.1⟩
    have e : cellSet E E' φ f hf c A u = ptsIn Y.str σ W ∩ ptMap σ f hf ⁻¹' c.e.source := by
      ext y
      simp only [cellSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, mem_ptsIn]
      rfl
    rw [e]
    exact (isOpen_ptsIn W).inter (c.e.open_source.preimage (Points.PtsOver.continuous_map f hf _))
  · intro y hy y' hy' h
    have h1 := congrArg (bsL ε) h
    have h2 := congrArg (fb ε) h
    simp only [cellMap, bsL_pt, fb_pt] at h1 h2
    have hx : ptMap σ f hf y = ptMap σ f hf y' := c.e.injOn hy.2 hy'.2 h1
    have hA : A ∈ E.S ((ptMap σ f hf y).1 (IsLocalRing.closedPoint ℂ)) := hy.1.1
    apply Subtype.ext
    exact (hP ℂ (ptMap σ f hf y).1 hA (fun j => ratVal (u j) y)).unique
      ⟨rfl, hy.1, fun j => (hval y hy.1 j).symm⟩
      ⟨congrArg Subtype.val hx.symm, hy'.1, fun j => (hval y' hy'.1 j).symm.trans (congrFun h2 j).symm⟩
  · intro S hS hA
    ext w
    constructor
    · rintro ⟨y, ⟨hyS, -⟩, rfl⟩
      exact ⟨ptMap σ f hf y, hyS, by simp only [cellMap, bsL_pt]⟩
    · rintro ⟨x, hxS, hxw⟩
      obtain ⟨p, ⟨hpf, hpc, hpv⟩, -⟩ := hP ℂ x.1 (hA x hxS) (fb ε w)
      have hps : p ≫ Y.str = spMap σ := by rw [← hf, ← Category.assoc, hpf, x.2]
      let y : CxPts Y.str σ := ⟨p, hps⟩
      have hyx : ptMap σ f hf y = x := Subtype.ext hpf
      refine ⟨y, ⟨by rw [Set.mem_preimage, hyx]; exact hxS, hpc, by rw [hyx]; exact hS hxS⟩, ?_⟩
      have hv : (fun j => ratVal (u j) y) = fb ε w := funext fun j => (hval y hpc j).trans (hpv j)
      simp only [cellMap, hyx, hxw, hv]
      exact pt_bsL_fb ε w

end GlobalTheory.FlagCell2
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellCoordsBijectiveOntoChartProdStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.flagCell_coords_bijective_onto_chart_prod : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), InCell E E' φ f A u (genericPoint Y.X) → ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m), IsOpen (cellSet E E' φ f hf c A u) ∧ Set.InjOn (cellMap ε f hf c u) (cellSet E E' φ f hf c A u) ∧ ∀ T : Set (CxPts X.str σ), T ⊆ c.e.source → (∀ x ∈ T, A ∈ E.S (under x)) → cellMap ε f hf c u '' (ptMap σ f hf ⁻¹' T ∩ cellSet E E' φ f hf c A u) = bsL ε ⁻¹' (c.e '' T) := by
  first | exact @GlobalTheory.FlagCell2.cellMap_image_eq | exact GlobalTheory.FlagCell2.cellMap_image_eq | (intros; apply GlobalTheory.FlagCell2.cellMap_image_eq <;> assumption)
end
end
