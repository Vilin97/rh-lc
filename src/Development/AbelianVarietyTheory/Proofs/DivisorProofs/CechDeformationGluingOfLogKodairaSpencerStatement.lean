module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelationStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.cechGluing_of_kodairaSpencer_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)), (∀ a, IsTanAtG t (LogKS.chart U) (v a)) → LogKS.IsKS t V U v D Θ → ∀ (K : Type) [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1), ⊤ ≤ x0 ⁻¹ᵁ V → ∀ (y1 : Sp (DualNumber K) ⟶ X) (hU' : ⊤ ≤ y1 ⁻¹ᵁ U.1), (∀ r, ev y1 U.1 hU' r = TrivSqZeroExt.inl (ev x0 U.1 hU r) + TrivSqZeroExt.inr (ev x0 U.1 hU (D r))) → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (ι : A.left ⟶ t.G.left) (ι' : A'.left ⟶ t.G.left) (i : A.left ⟶ A'.left) (u : Fin n → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A t.G x0 ι → IsGrpPullback A' t.G y1 ι' → i ≫ ι' = ι → (∀ a, (u a).left ≫ ι = spMap (dualMap (ev x0 U.1 hU)) ≫ v a) → ∀ (M : LB A.left), ⨆ k, M.U k = ⊤ → LBIso (t.PP.L.pull ι) M → GlobalTheory.CechKS.IsCechKS A A' i M u (Matrix.of fun a b => ev x0 U.1 hU (Θ a b)) := by
  first | exact @GlobalTheory.CechKS.isCechKS_of_isKS | exact GlobalTheory.CechKS.isCechKS_of_isKS | (intros; apply GlobalTheory.CechKS.isCechKS_of_isKS <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberReductionTangentFramedPoint

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.EpsRedFr

theorem epsRed_tangent_frX : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (D : Γ(TF.Y.X, U.1) → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1) (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (D r))) → GlobalTheory.DeRham.epsRed K ≫ y' = frX P := by
  intro E _ _ _ H Dw l Xo c TF U D K _ _ P hU y' hU' hy hev
  have h1 : ⊤ ≤ ((GlobalTheory.DeRham.epsRed K ≫ y') ≫ TF.Y.j) ⁻¹ᵁ U.1 := by
    rw [Category.assoc]; exact GlobalTheory.FlagMod.le_preimage_comp _ hU'
  have hfst : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap c.F (DualNumber K)) = algebraMap c.F K :=
    RingHom.ext fun r => by simp
  refine GlobalTheory.FlagMod.xF_ext (Y := TF.Y) ?_ (GlobalTheory.FlagMod.frX_snd P) ?_
  · rw [Category.assoc, hy, GlobalTheory.DeRham.epsRed, spMap_comp', hfst]
  · have e : ev ((GlobalTheory.DeRham.epsRed K ≫ y') ≫ TF.Y.j) U.1 h1 = ev (frX P ≫ TF.Y.j) U.1 hU := by
      have e0 : ev ((GlobalTheory.DeRham.epsRed K ≫ y') ≫ TF.Y.j) U.1 h1 =
          (TrivSqZeroExt.fstHom K K K).toRingHom.comp (ev (y' ≫ TF.Y.j) U.1 hU') := by
        rw [← GlobalTheory.FlagMod.ev_spMap _ (y' ≫ TF.Y.j) U.1 hU' (by rw [← Category.assoc]; exact h1)]
        exact GlobalTheory.FlagMod.ev_congr (Category.assoc _ _ _) _ _ _
      rw [e0]
      refine RingHom.ext fun r => ?_
      rw [RingHom.comp_apply, hev r]
      simp
    rw [← GlobalTheory.FlagMod.spMap_ev ((GlobalTheory.DeRham.epsRed K ≫ y') ≫ TF.Y.j) U.2 h1,
      ← GlobalTheory.FlagMod.spMap_ev (frX P ≫ TF.Y.j) U.2 hU, e]

end GlobalTheory.EpsRedFr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberReductionTangentFramedPointStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.dualNumberReduction_tangent_framedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (D : Γ(TF.Y.X, U.1) → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1) (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (D r))) → GlobalTheory.DeRham.epsRed K ≫ y' = frX P := by
  first | exact @GlobalTheory.EpsRedFr.epsRed_tangent_frX | exact GlobalTheory.EpsRedFr.epsRed_tangent_frX | (intros; apply GlobalTheory.EpsRedFr.epsRed_tangent_frX <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianPullbackFramedTangent

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FramedTransport

theorem exists_model_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1), IsBaseFrame TF U e v P hU → ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → GlobalTheory.DeRham.epsRed K ≫ y' = frX P → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G P.x π → IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' → i ≫ π' = π → (∀ σ k, (ub σ k).left ≫ π = P.u σ k) → ∃ (ι : A.left ⟶ TF.Y.t.G.left) (ι' : A'.left ⟶ TF.Y.t.G.left), IsGrpPullback A TF.Y.t.G (frX P ≫ TF.Y.j) ι ∧ IsGrpPullback A' TF.Y.t.G (y' ≫ TF.Y.j) ι' ∧ i ≫ ι' = ι ∧ (∀ σ k, (ub σ k).left ≫ ι = spMap (dualMap (ev (frX P ≫ TF.Y.j) U.1 hU)) ≫ v (e ⟨σ, k⟩)) ∧ LBIso (TF.Y.t.PP.L.pull ι) (Xo.univ.t.PP.L.pull π) ∧ ⨆ k, (Xo.univ.t.PP.L.pull π).U k = ⊤ := by
  intro E _ _ _ H Dw l Xo c TF U n e v K _ _ P hU hB y' hy' hred A _ A' _ π π' i ub hi hπ hπ' hiπ hub
  have hx : frX P ≫ pullback.fst _ _ = P.x := pullback.lift_fst _ _ _
  have hπ0 : IsGrpPullback A Xo.univ.t.G (frX P ≫ pullback.fst _ _) π := hπ.congr hx.symm rfl
  have w0 : π ≫ Xo.univ.t.G.hom = (A.hom ≫ frX P) ≫ pullback.fst _ _ := by
    rw [hπ0.1.w, Category.assoc]
  have w1 : π' ≫ Xo.univ.t.G.hom = (A'.hom ≫ y') ≫ pullback.fst _ _ := by
    rw [hπ'.1.w, Category.assoc]
  let lam := TF.Y.m0.cart.1.lift π (A.hom ≫ frX P) w0
  let lam' := TF.Y.m0.cart.1.lift π' (A'.hom ≫ y') w1
  have hl0 : lam ≫ TF.Y.m0.φ = π := TF.Y.m0.cart.1.lift_fst _ _ _
  have hl0' : lam' ≫ TF.Y.m0.φ = π' := TF.Y.m0.cart.1.lift_fst _ _ _
  have hs : lam ≫ TF.Y.oF.t.G.hom = A.hom ≫ frX P := TF.Y.m0.cart.1.lift_snd _ _ _
  have hs' : lam' ≫ TF.Y.oF.t.G.hom = A'.hom ≫ y' := TF.Y.m0.cart.1.lift_snd _ _ _
  have g1 : IsGrpPullback A TF.Y.oF.t.G (frX P) lam :=
    IsGrpPullback.cancel TF.Y.m0.cart (hπ0.congr rfl hl0.symm) hs
  have g1' : IsGrpPullback A' TF.Y.oF.t.G y' lam' :=
    IsGrpPullback.cancel TF.Y.m0.cart (hπ'.congr rfl hl0'.symm) hs'
  have hil : i ≫ lam' = lam := by
    apply TF.Y.m0.cart.1.hom_ext
    · rw [Category.assoc, hl0', hiπ, hl0]
    · rw [Category.assoc, hs', hs, ← Category.assoc, hi.1.w, Category.assoc, hred]
  obtain ⟨w, hw, -⟩ := TF.Y.m.lin
  obtain ⟨w0', hw0, -⟩ := TF.Y.m0.lin
  have i1 : LBIso (TF.Y.oF.t.PP.L.pull lam) (TF.Y.t.PP.L.pull (lam ≫ TF.Y.m.φ)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ lam lam rfl)
      (chartPullSame _ (fun _ => lam ≫ TF.Y.m.φ) (fun _ => TF.Y.m.φ) (fun _ => 1) lam (fun _ => rfl)) ⟨w, hw⟩
  have i2 : LBIso (TF.Y.oF.t.PP.L.pull lam) (Xo.univ.t.PP.L.pull (lam ≫ TF.Y.m0.φ)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ lam lam rfl)
      (chartPullSame _ (fun _ => lam ≫ TF.Y.m0.φ) (fun _ => TF.Y.m0.φ) (fun _ => 1) lam (fun _ => rfl)) ⟨w0', hw0⟩
  rw [hl0] at i2
  refine ⟨lam ≫ TF.Y.m.φ, lam' ≫ TF.Y.m.φ, g1.comp TF.Y.m.cart, g1'.comp TF.Y.m.cart, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hil]
  · intro σ k
    rw [← hB σ k]
    unfold frVec
    rw [FlagMod.toModel_left, ← Category.assoc]
    congr 1
    apply TF.Y.m0.cart.1.hom_ext
    · rw [Category.assoc, hl0, hub, FlagMod.liftTan_univ]
    · rw [Category.assoc, hs, ← Category.assoc, Over.w (ub σ k), FlagMod.liftTan_over]
      rfl
  · exact LBIso.trans (pull_isLB TF.Y.t.PP.isLB _) (pull_isLB TF.Y.oF.t.PP.isLB _)
      (pull_isLB Xo.univ.t.PP.isLB _) i1.symm i2
  · exact (pull_isLB Xo.univ.t.PP.isLB π).cover

end GlobalTheory.FramedTransport
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianPullbackFramedTangentStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.exists_semiAbelian_pullback_framed_tangent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1), IsBaseFrame TF U e v P hU → ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → GlobalTheory.DeRham.epsRed K ≫ y' = frX P → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G P.x π → IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' → i ≫ π' = π → (∀ σ k, (ub σ k).left ≫ π = P.u σ k) → ∃ (ι : A.left ⟶ TF.Y.t.G.left) (ι' : A'.left ⟶ TF.Y.t.G.left), IsGrpPullback A TF.Y.t.G (frX P ≫ TF.Y.j) ι ∧ IsGrpPullback A' TF.Y.t.G (y' ≫ TF.Y.j) ι' ∧ i ≫ ι' = ι ∧ (∀ σ k, (ub σ k).left ≫ ι = spMap (dualMap (ev (frX P ≫ TF.Y.j) U.1 hU)) ≫ v (e ⟨σ, k⟩)) ∧ LBIso (TF.Y.t.PP.L.pull ι) (Xo.univ.t.PP.L.pull π) ∧ ⨆ k, (Xo.univ.t.PP.L.pull π).U k = ⊤ := by
  first | exact @GlobalTheory.FramedTransport.exists_model_pullback | exact GlobalTheory.FramedTransport.exists_model_pullback | (intros; apply GlobalTheory.FramedTransport.exists_model_pullback <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeformationGluingOfLogKodairaSpencer

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechTransport

theorem cech_of_logKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1)), LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v D.1 Θ → ∀ (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1), IsBaseFrame TF U e v P hU → ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (D.1 r))) → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G P.x π → IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' → i ≫ π' = π → (∀ σ k, (ub σ k).left ≫ π = P.u σ k) → GlobalTheory.CechKS.IsCechKS A A' i (Xo.univ.t.PP.L.pull π) (fun a => ub (e.symm a).1 (e.symm a).2) (Matrix.of fun a b => ev (frX P ≫ TF.Y.j) U.1 hU (Θ a b)) := by
  intro E _ _ _ H Dw l Xo c TF U n e v hv D Θ hks K _ _ P hU hb y' hU' hy' hev A _ A' _ π π' i ub hi hπ hπ' hiπ hub
  have hred := GlobalTheory.T.dualNumberReduction_tangent_framedPoint E H Dw l Xo c TF U D.1 K P hU y' hU' hy' hev
  obtain ⟨ι, ι', h1, h2, h3, h4, h5, h6⟩ :=
    GlobalTheory.T.exists_semiAbelian_pullback_framed_tangent E H Dw l Xo c TF U n e v K P hU hb y' hy' hred A A' π π' i ub hi hπ hπ' hiπ hub
  have hint : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ LogKS.interior TF.Y := by
    intro x _
    exact ⟨(frX P).base x, rfl⟩
  exact GlobalTheory.T.cechGluing_of_kodairaSpencer_relation E H TF.Y.X TF.Y.t (LogKS.interior TF.Y) U n v D.1 Θ hv.1 hks K (frX P ≫ TF.Y.j) hU hint
    (y' ≫ TF.Y.j) hU' hev A A' ι ι' i _ hi h1 h2 h3
    (fun a => by simpa using h4 (e.symm a).1 (e.symm a).2) _ h6 h5

end GlobalTheory.CechTransport
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeformationGluingOfLogKodairaSpencerStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.cechDeformation_gluing_of_logKodairaSpencer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1)), LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v D.1 Θ → ∀ (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1), IsBaseFrame TF U e v P hU → ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (D.1 r))) → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G P.x π → IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' → i ≫ π' = π → (∀ σ k, (ub σ k).left ≫ π = P.u σ k) → GlobalTheory.CechKS.IsCechKS A A' i (Xo.univ.t.PP.L.pull π) (fun a => ub (e.symm a).1 (e.symm a).2) (Matrix.of fun a b => ev (frX P ≫ TF.Y.j) U.1 hU (Θ a b)) := by
  first | exact @GlobalTheory.CechTransport.cech_of_logKS | exact GlobalTheory.CechTransport.cech_of_logKS | (intros; apply GlobalTheory.CechTransport.cech_of_logKS <;> assumption)
end
end
