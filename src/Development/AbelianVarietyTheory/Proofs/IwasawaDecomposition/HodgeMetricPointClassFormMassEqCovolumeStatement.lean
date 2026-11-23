module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopPartHodgeMetricUniformisationImageStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComponentUniformisationArithmeticGroupInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMoebZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtEqOfPtOfFrameEq
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCurry
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulConjTransposeEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationImageBoundedDomainEqOpenPartStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationNullSetsToPointClassNullStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComponentUniformisationFibreArithmeticGroupRelat

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.UnifFibre

theorem fibre_gamma : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ∀ w ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ψ v = ψ w → ∃ γ ∈ gammaU (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ), moebI γ (unflat v) = unflat w := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ v hv w hw hvw
  have hjr : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right Dw.p Dw.q
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by
    have := (hU.2.1 k).1
    omega
  have hflat : ∀ u : (U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ, flat (unflat u) = u := by
    intro u; funext ⟨i, a, b⟩; rfl
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.TrueCx.FrameOnto.frame_onto E (Dw.p + Dw.q) Dw.p (U.X k) hjr (U.X k).Ψ
    (Equiv.refl _) hp (unflat v) hv
  obtain ⟨x', hx', hxw⟩ := GlobalTheory.TrueCx.FrameOnto.frame_onto E (Dw.p + Dw.q) Dw.p (U.X k) hjr (U.X k).Ψ
    (Equiv.refl _) hp (unflat w) hw
  have h1 := hψ ⟨x, hx⟩
  have h2 := hψ ⟨x', hx'⟩
  simp only at h1 h2
  rw [hxv, hflat] at h1
  rw [hxw, hflat] at h2
  have h3 : cxPt T.Z (U.un k ⟨x, hx⟩) = cxPt T.Z (U.un k ⟨x', hx'⟩) := by
    rw [← h1, ← h2, hvw]
  have h4 : (U.un k ⟨x, hx⟩).x = (U.un k ⟨x', hx'⟩).x := by
    have h5 := congrArg Subtype.val h3
    simp only [cxPt] at h5
    haveI := T.Z.jQ_open
    have h6 := (cancel_mono T.Z.jQ).1 h5
    have h7 := congrArg (· ≫ CategoryTheory.Limits.pullback.fst _ _) h6
    simp only [GlobalTheory.AllWt.ptF] at h7
    rwa [CategoryTheory.Limits.pullback.lift_fst, CategoryTheory.Limits.pullback.lift_fst] at h7
  obtain ⟨b, hb, hb0, hm, t, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor U hU hG k ⟨x, hx⟩ _ h4
  obtain ⟨γ, hγ, b', hb', heq⟩ := (hU.2.2.2.1 k k ⟨_, hm⟩ ⟨x', hx'⟩).1 ⟨t, ht⟩
  have hx'eq : x' = ReciprocityTheory.ChartRestriction.G.FD.rmul (ReciprocityTheory.ChartRestriction.G.FD.lact γ (ReciprocityTheory.ChartRestriction.G.FD.rmul x b)) b' :=
    eq_of_heq (Sigma.mk.inj_iff.1 heq).2
  refine ⟨GlobalTheory.TrueCx.toUpq (U.X k) hjr (Equiv.refl (U.X k).Ψ) γ, Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩, ?_⟩
  rw [← hxv, ← hxw, hx'eq, GlobalTheory.TrueCx.domPt_rmul _ _ _ hb', GlobalTheory.TrueCx.domPt_lact _ _ _ hp γ hm]
  rw [hp] at hb0
  rw [GlobalTheory.PointOfFrames.domPt_rmul_block _ _ _ _ b hb hb0]

end GlobalTheory.UnifFibre
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComponentUniformisationFibreArithmeticGroupRelatStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx


theorem _root_.GlobalTheory.T.componentUniformisation_fibre_arithmeticGroup_related : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ∀ w ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ψ v = ψ w → ∃ γ ∈ gammaU (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ), moebI γ (unflat v) = unflat w := by
  first | exact @GlobalTheory.UnifFibre.fibre_gamma | exact GlobalTheory.UnifFibre.fibre_gamma | (intros; apply GlobalTheory.UnifFibre.fibre_gamma <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComponentUniformisationBoundedDomainComple

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.LieBase.UnifExists

open Formalism.MJ ReciprocityTheory.ChartRestriction.G.AR.Up

theorem flat_inj {ι : Type} {p q : ℕ} {z z' : ι → Matrix (Fin p) (Fin q) ℂ} (h : flat z = flat z') : z = z' := by
  funext t a b
  exact congrFun h (t, a, b)

theorem exists_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∃ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL
  obtain ⟨hoi, hfj, -⟩ := hL
  haveI := hoi
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := first_index_eq_of_unfolded U hU rfl k
  have hle : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right Dw.p Dw.q
  have hrange : ∀ x : (U.X k).dom, Set.range (cxPt T.Z (U.un k x)).1 ⊆ Set.range j := by
    rintro x _ ⟨s, rfl⟩
    obtain ⟨y, hy⟩ := Φ.label k x s
    refine ⟨f y, ?_⟩
    show (f ≫ j) y = _
    rw [hfj]
    exact hy
  let lf : (U.X k).dom → CxPts X.str (σ.comp e.toRingHom) := fun x =>
    ⟨IsOpenImmersion.lift j (cxPt T.Z (U.un k x)).1 (hrange x), by
      rw [← hj, ← Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc, (cxPt T.Z (U.un k x)).2,
        ← Spec.map_comp]
      rfl⟩
  have hlf : ∀ x, cxOf e σ hj (lf x) = cxPt T.Z (U.un k x) := fun x =>
    Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  have hwell : ∀ x x' : (U.X k).dom,
      domPt (U.X k) hle (Equiv.refl (U.X k).Ψ) x.1 = domPt (U.X k) hle (Equiv.refl (U.X k).Ψ) x'.1 →
      cxPt T.Z (U.un k x) = cxPt T.Z (U.un k x') := by
    intro x x' h
    have h5 : ∀ τ, moeb (frameCo (U.X k) hle x.1 τ) 0 = moeb (frameCo (U.X k) hle x'.1 τ) 0 :=
      fun τ => congrFun h τ
    exact cxPt_congr (PointWell.pt_eq_of_block hU hσ k x x'
      (fun τ => PointWell.block_of_moeb_eq _ hle hp x.2 x'.2 τ (h5 τ))
      (fun τ => PointWell.block_of_moeb_eq _ hle hp x'.2 x.2 τ (h5 τ).symm))
  let x0 : (U.X k).dom := ⟨x0F (U.X k), IW.orth_mem_dom (U.X k) _ (isOrth_x0F (U.X k))⟩
  refine ⟨fun v => if h : ∃ x : (U.X k).dom,
      flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1) = v then lf h.choose else lf x0,
    fun x => ?_⟩
  have h : ∃ x' : (U.X k).dom, flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x'.1) =
      flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1) := ⟨x, rfl⟩
  simp only [dif_pos h]
  rw [hlf]
  exact hwell _ _ (flat_inj h.choose_spec)

end GlobalTheory.LieBase.UnifExists
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComponentUniformisationBoundedDomainCompleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx


theorem _root_.GlobalTheory.T.exists_componentUniformisation_boundedDomain_complexPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∃ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) := by
  first | exact @GlobalTheory.LieBase.UnifExists.exists_unif | exact GlobalTheory.LieBase.UnifExists.exists_unif | (intros; apply GlobalTheory.LieBase.UnifExists.exists_unif <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricPointClassFormMassEqCovolume

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.BaseVolume

theorem mass_openPart_eq_covol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 (ptsIn X.str (σ.comp e.toRingHom) (openPart j)) = ENNReal.ofReal (GlobalTheory.TrueCx.covol (U.X k)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL
  have hj' : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right _ _
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by have := (hU.2.1 k).1; omega
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_componentUniformisation_boundedDomain_complexPoints E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL
  have himg := GlobalTheory.T.uniformisation_image_boundedDomain_eq_openPart E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hfib := GlobalTheory.T.componentUniformisation_fibre_arithmeticGroup_related E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hinv := GlobalTheory.T.componentUniformisation_arithmeticGroup_invariant E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hdens := GlobalTheory.T.chernTopPart_hodgeMetric_uniformisation_image E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hnull := GlobalTheory.T.uniformisation_null_sets_to_pointClass_null E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  obtain ⟨FD, hFD⟩ := GlobalTheory.BoundedFundDomain.exists_isFD E (Dw.p + Dw.q) Dw.p (U.X k) hj' (U.X k).Ψ (Equiv.refl _) hp
  obtain ⟨hlt, hcov⟩ := GlobalTheory.FlagFibre.covol_eq_muD E (Dw.p + Dw.q) Dw.p (U.X k) hj' (U.X k).Ψ (Equiv.refl _) hp FD hFD
  obtain ⟨hFm, hFsub, hFcov, hFbad⟩ := hFD
  set μD := muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hμD
  set Bad := {v | v ∈ FD ∧ ∃ γ ∈ gammaU (U.X k) hj' (Equiv.refl (U.X k).Ψ), flat (moebI γ (unflat v)) ∈ FD ∧
    moebI γ (unflat v) ≠ unflat v} with hBad
  set B' := toMeasurable μD Bad with hB'
  have hB'0 : μD B' = 0 := by rw [hB', measure_toMeasurable]; exact hFbad
  have hfu : ∀ v : (U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ, flat (unflat v) = v := fun v => rfl
  have hinj : Set.InjOn ψ (FD \ B') := by
    intro v hv w hw hvw
    obtain ⟨γ, hγ, hγe⟩ := hfib v (hFsub hv.1) w (hFsub hw.1) hvw
    have hnb : v ∉ Bad := fun h => hv.2 (subset_toMeasurable _ _ h)
    have h1 : moebI γ (unflat v) = unflat v := by
      by_contra hne
      exact hnb ⟨hv.1, γ, hγ, by rw [hγe, hfu]; exact hw.1, hne⟩
    rw [← hfu v, ← hfu w, ← hγe, h1]
  have hD := hdens (FD \ B') (Set.diff_subset.trans hFsub) (hFm.diff (measurableSet_toMeasurable _ _)) hinj
  have hN := hnull (FD ∩ B') (Set.inter_subset_left.trans hFsub) (measure_mono_null Set.inter_subset_right hB'0)
  have hmF : μD (FD \ B') = μD FD := measure_diff_null hB'0
  have hsub : ψ '' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) ⊆ ψ '' (FD \ B') ∪ ψ '' (FD ∩ B') := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨γ, hγ, hγF⟩ := hFcov (unflat v) hv
    rw [← Set.image_union, Set.diff_union_inter, ← hinv γ hγ v hv]
    exact Set.mem_image_of_mem _ hγF
  have hsup : ψ '' (FD \ B') ⊆ ψ '' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) :=
    Set.image_mono (Set.diff_subset.trans hFsub)
  rw [← himg, hcov, ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hlt.ne, ← hmF, ← hD]
  refine le_antisymm ?_ (measure_mono hsup)
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ = _ := by rw [hN, add_zero]

end GlobalTheory.BaseVolume
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricPointClassFormMassEqCovolumeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame


theorem _root_.GlobalTheory.T.hodgeMetric_pointClassForm_mass_eq_covolume : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 (ptsIn X.str (σ.comp e.toRingHom) (openPart j)) = ENNReal.ofReal (GlobalTheory.TrueCx.covol (U.X k)) := by
  first | exact @GlobalTheory.BaseVolume.mass_openPart_eq_covol | exact GlobalTheory.BaseVolume.mass_openPart_eq_covol | (intros; apply GlobalTheory.BaseVolume.mass_openPart_eq_covol <;> assumption)
end
end
