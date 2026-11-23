module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenpartsFrameFamilyOverVariety
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineOpenSpreadStalkLieEigenspaceFrame

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

open CategoryTheory.Limits

namespace GlobalTheory.ShFam.StalkSpread

open GlobalTheory.LieLocFrame (res res_sum res_res)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)
open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_affine_isMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (X : Var F) (j : X.X ⟶ gen Z) (z : X.X) (φz : c.F →+* X.X.presheaf.stalk z) (fz : EigFrame Z φz (stalkPt X z ≫ j ≫ genι Z)) (W₀ : X.X.Opens), z ∈ W₀ → stalkPt X z ≫ j ≫ genStr Z = spMap φz → ∃ (W : X.X.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(X.X, W)) (fW : EigFrame Z φ (((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι Z)) (hz : z ∈ W), W ≤ W₀ ∧ ((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genStr Z = spMap φ ∧ (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v fW embτ basisIdx) (X.X.presheaf.germ W z hz).hom fz := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ X j z φz fz W₀ hz₀ hstr
  obtain ⟨U₀, hU₀, φ₀, f₀, hy₀, hs₀, -⟩ := GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z (j z)
  let gm₀ : Γ(gen Z, U₀) →+* X.X.presheaf.stalk z :=
    (X.X.presheaf.germ (j ⁻¹ᵁ U₀) z hy₀).hom.comp (j.app U₀).hom
  have hgm : ∀ (U : X.X.Opens) (hy : z ∈ U) (h : U ≤ j ⁻¹ᵁ U₀),
      (X.X.presheaf.germ U z hy).hom.comp (j.appLE U₀ U h).hom = gm₀ := fun U hy h =>
    RingHom.ext fun a => X.X.presheaf.germ_res_apply (homOfLE h) z hy _
  have hρ : ∀ (U : X.X.Opens) (hU : IsAffineOpen U) (h : U ≤ j ⁻¹ᵁ U₀),
      spMap (j.appLE U₀ U h).hom ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) =
        (show Sp Γ(X.X, U) ⟶ X.X from hU.fromSpec) ≫ j := fun U hU h =>
    IsAffineOpen.SpecMap_appLE_fromSpec j hU₀ hU h
  have hx₀ : spMap gm₀ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) = stalkPt X z ≫ j := by
    obtain ⟨U, hU, hy, h⟩ := exists_isAffineOpen_mem_and_subset (X := X.X) (U := j ⁻¹ᵁ U₀) (x := z) hy₀
    rw [← hgm U hy h, ← spMap_comp_spMap, Category.assoc, hρ U hU h, ← Category.assoc, Spread.spMap_germ]
    rfl
  have hs₀' : (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genStr Z = spMap φ₀ := hs₀
  have hφ₀ : gm₀.comp φ₀ = φz := by
    have h1 : spMap (gm₀.comp φ₀) = spMap φz := by
      rw [← spMap_comp_spMap, ← hs₀', ← Category.assoc, hx₀, Category.assoc, hstr]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have hx₁ : spMap gm₀ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genι Z =
      stalkPt X z ≫ j ≫ genι Z := by rw [← Category.assoc, hx₀, Category.assoc]
  obtain ⟨g, hg⟩ := Spread.exists_bc f₀ gm₀ hφ₀ hx₁
  choose A B hAB hA using Spread.exists_coord g fz
  obtain ⟨U, hU, hy, s, hle, hs⟩ := Spread.exists_affine_germs z (W := W₀ ⊓ j ⁻¹ᵁ U₀) ⟨hz₀, hy₀⟩
    (fun p : Bool × (Σ τ : E →+* ℂ, Fin (Dw.mult τ) × Fin (Dw.mult τ)) =>
      (cond p.1 (A p.2.1) (B p.2.1)) p.2.2.1 p.2.2.2)
  have h₀ : U ≤ j ⁻¹ᵁ U₀ := fun w hw => (hle hw).2
  let gm : Γ(X.X, U) →+* X.X.presheaf.stalk z := (X.X.presheaf.germ U z hy).hom
  let ρ : Γ(gen Z, U₀) →+* Γ(X.X, U) := (j.appLE U₀ U h₀).hom
  let A' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(X.X, U) :=
    fun τ => Matrix.of fun i k => s (true, ⟨τ, i, k⟩)
  let B' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(X.X, U) :=
    fun τ => Matrix.of fun i k => s (false, ⟨τ, i, k⟩)
  have hA' : ∀ τ i k, gm (A' τ i k) = A τ i k := fun τ i k => hs (true, ⟨τ, i, k⟩)
  have hB' : ∀ τ i k, gm (B' τ i k) = B τ i k := fun τ i k => hs (false, ⟨τ, i, k⟩)
  have hAB' : ∀ τ, B' τ * A' τ = 1 := fun τ => Matrix.ext fun i k => germ_injective_of_isIntegral X.X z hy (by
    show gm _ = gm _
    have := congrFun (congrFun (hAB τ) i) k

    simp only [Matrix.mul_apply, map_sum, map_mul, hA', hB', Matrix.one_apply] at this ⊢
    rw [this]
    split_ifs <;> simp)
  have hx₂ : spMap ρ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genι Z =
      ((show Sp Γ(X.X, U) ⟶ X.X from hU.fromSpec) ≫ j) ≫ genι Z := by rw [← Category.assoc, hρ U hU h₀]
  have hx₃ : spMap gm ≫ ((show Sp Γ(X.X, U) ⟶ X.X from hU.fromSpec) ≫ j) ≫ genι Z =
      stalkPt X z ≫ j ≫ genι Z := by
    rw [Category.assoc, ← Category.assoc, Spread.spMap_germ]
    rfl
  obtain ⟨g', hg'⟩ := Spread.exists_bc f₀ ρ rfl hx₂
  obtain ⟨fr, hfr⟩ := Spread.exists_change g' A' B' hAB'
  refine ⟨U, hU, ρ.comp φ₀, fr, hy, fun w hw => (hle hw).1, ?_, fun τ i => ?_⟩
  · rw [← hρ U hU h₀, Category.assoc, hs₀']
    exact spMap_comp_spMap φ₀ ρ
  · have hv : fz.vec τ i = res gm hx₃ (fr.vec τ i) := by
      rw [hfr, res_sum, hA]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hA', hg, hg', res_res ρ hx₂ gm hx₃ (hgm U hy h₀) hx₁]
    exact congrArg (fun v => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left) hv

end GlobalTheory.ShFam.StalkSpread
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineOpenSpreadStalkLieEigenspaceFrameStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)


theorem _root_.GlobalTheory.T.exists_affineOpen_spread_stalk_lieEigenspaceFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (X : Var F) (j : X.X ⟶ gen Z) (z : X.X) (φz : c.F →+* X.X.presheaf.stalk z) (fz : EigFrame Z φz (stalkPt X z ≫ j ≫ genι Z)) (W₀ : X.X.Opens), z ∈ W₀ → stalkPt X z ≫ j ≫ genStr Z = spMap φz → ∃ (W : X.X.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(X.X, W)) (fW : EigFrame Z φ (((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι Z)) (hz : z ∈ W), W ≤ W₀ ∧ ((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genStr Z = spMap φ ∧ (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v fW embτ basisIdx) (X.X.presheaf.germ W z hz).hom fz := by
  first | exact @GlobalTheory.ShFam.StalkSpread.exists_affine_isMap | exact GlobalTheory.ShFam.StalkSpread.exists_affine_isMap | (intros; apply GlobalTheory.ShFam.StalkSpread.exists_affine_isMap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineLieEigenFrameNearComplexPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NearFrame

theorem dualMap_comp_near {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) :=
  RingHom.ext fun x => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem exists_affine_frame_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), Tied e X j f₀ Eb A₀ → ∀ (y : CxPts X.str (σ.comp e.toRingHom)), ∀ A ∈ Eb.S (under y), ∃ (W : X.X.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(X.X, W)) (fW : EigFrame Z φ (((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι Z)), y ∈ ptsIn X.str (σ.comp e.toRingHom) W ∧ ∀ y' (hy' : y' ∈ ptsIn X.str (σ.comp e.toRingHom) W), (evHom hy').comp φ = σ ∧ ∃ g : EigFrame Z σ ((cxOf e σ hj y').1 ≫ genι Z), FrameAt e f₀ A₀ A y' g ∧ (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v fW embτ basisIdx) (evHom hy') g := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ X j f₀ Eb A₀ hj hT y A hA
  obtain ⟨φz, fz, hx0, hφ0, hv0⟩ := hT.2 (under y) A hA
  have inj := IsFractionRing.injective (X.X.presheaf.stalk (under y)) X.X.functionField
  have hgen : spMap (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) ≫ stalkPt X (under y) = genericPt X :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes _)
  have hstr : stalkPt X (under y) ≫ j ≫ genStr Z = spMap φz := by
    obtain ⟨p, hp⟩ := Spec.map_surjective (stalkPt X (under y) ≫ j ≫ genStr Z)
    have h1 : (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField).comp p.hom =
        (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField).comp φz := by
      refine EigLoc.spMap_inj ?_
      rw [← hφ0, ← TieBase.genericPt_str e X j hj, TieBase.spMap_trans, ← hgen]
      show _ ≫ Spec.map p = _
      rw [hp]
      simp only [Category.assoc]
    have h2 : p.hom = φz := RingHom.ext fun a => inj (RingHom.congr_fun h1 a)
    rw [← hp, ← h2]
    rfl
  obtain ⟨W, hW, φ, fW, hz, -, hWstr, hmap⟩ := GlobalTheory.T.exists_affineOpen_spread_stalk_lieEigenspaceFrame E H Dw l Xo c O β Z F X j (under y) φz fz ⊤ trivial hstr
  have hgerm : spMap (X.X.presheaf.germ W (under y) hz).hom ≫ (show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) =
      stalkPt X (under y) := hW.fromSpecStalk_eq_fromSpecStalk hz
  have hφz : φz = (X.X.presheaf.germ W (under y) hz).hom.comp φ := by
    refine EigLoc.spMap_inj ?_
    rw [TieBase.spMap_trans, ← hstr, ← hWstr, ← hgerm]
    simp only [Category.assoc]
  refine ⟨W, hW, φ, fW, mem_ptsIn.2 hz, fun y' hy' => ?_⟩
  have hz' : under y' ∈ W := mem_ptsIn.1 hy'
  have hp' : spMap (evHom hy') ≫ (show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) = y'.1 :=
    Points.specMap_valMap_fromSpec hW y'.1 hy'
  have ha : (evHom hy').comp φ = σ := by
    refine EigLoc.spMap_inj ?_
    rw [TieBase.spMap_trans, ← hWstr, ← (cxOf e σ hj y').2]
    show _ = (y'.1 ≫ j) ≫ genStr Z
    rw [← hp']
    simp only [Category.assoc]
  refine ⟨ha, ?_⟩
  obtain ⟨g, hg⟩ := EigFrame.exists_isMap fW (evHom hy') (φ' := σ) (x' := (cxOf e σ hj y').1 ≫ genι Z) ha.symm (by
    show (y'.1 ≫ j) ≫ genι Z = _
    rw [← hp']
    simp only [Category.assoc])
  refine ⟨g, ?_, hg⟩
  let germ' := (X.X.presheaf.germ W (under y') hz').hom
  let χ : X.X.presheaf.stalk (under y') →+* ℂ := (Scheme.stalkClosedPointTo (R := .of ℂ) y'.1).hom
  have hχ : χ.comp germ' = evHom hy' := by
    show _ = (Points.valMap y'.1 W hy').hom
    rw [← CommRingCat.hom_comp]
    congr 1
    rw [Scheme.germ_stalkClosedPointTo]
    rfl
  have hgerm' : spMap germ' ≫ (show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) = stalkPt X (under y') :=
    hW.fromSpecStalk_eq_fromSpecStalk hz'
  obtain ⟨fz', hfz'⟩ := EigFrame.exists_isMap fW germ' (φ' := germ'.comp φ)
    (x' := stalkPt X (under y') ≫ j ≫ genι Z) rfl (by rw [← hgerm']; simp only [Category.assoc])
  have hκ : (algebraMap (X.X.presheaf.stalk (under y')) X.X.functionField).comp germ' =
      (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField).comp (X.X.presheaf.germ W (under y) hz).hom :=
    RingHom.ext fun a => (algebraMap_germ hz' a).trans (algebraMap_germ hz a).symm
  refine ⟨germ'.comp φ, fz', χ, (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of ℂ) y'.1).symm, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hx0, ← hgerm, ← hgerm']
    simp only [← Category.assoc]
    rw [← TieBase.spMap_trans, ← TieBase.spMap_trans, hκ]
  · rw [hφ0, hφz, ← RingHom.comp_assoc, ← RingHom.comp_assoc, hκ]
  · intro τ i
    have e : (fun k => spMap (dualMap (algebraMap (X.X.presheaf.stalk (under y')) X.X.functionField)) ≫ fz'.v τ k) =
        fun k => spMap (dualMap (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField)) ≫ fz.v τ k := by
      funext k
      rw [hfz' τ k, hmap τ k, ← Category.assoc, ← Category.assoc, ← TieBase.spMap_trans, ← TieBase.spMap_trans,
        ← dualMap_comp_near, ← dualMap_comp_near, hκ]
    rw [e]
    exact hv0 τ i
  · intro τ i
    rw [hg τ i, hfz' τ i, ← Category.assoc, ← TieBase.spMap_trans, ← dualMap_comp_near, hχ]

end GlobalTheory.NearFrame
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineLieEigenFrameNearComplexPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)


theorem _root_.GlobalTheory.T.exists_affine_lieEigenFrame_near_complexPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), Tied e X j f₀ Eb A₀ → ∀ (y : CxPts X.str (σ.comp e.toRingHom)), ∀ A ∈ Eb.S (under y), ∃ (W : X.X.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(X.X, W)) (fW : EigFrame Z φ (((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι Z)), y ∈ ptsIn X.str (σ.comp e.toRingHom) W ∧ ∀ y' (hy' : y' ∈ ptsIn X.str (σ.comp e.toRingHom) W), (evHom hy').comp φ = σ ∧ ∃ g : EigFrame Z σ ((cxOf e σ hj y').1 ≫ genι Z), FrameAt e f₀ A₀ A y' g ∧ (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v fW embτ basisIdx) (evHom hy') g := by
  first | exact @GlobalTheory.NearFrame.exists_affine_frame_near | exact GlobalTheory.NearFrame.exists_affine_frame_near | (intros; apply GlobalTheory.NearFrame.exists_affine_frame_near <;> assumption)
end
end
