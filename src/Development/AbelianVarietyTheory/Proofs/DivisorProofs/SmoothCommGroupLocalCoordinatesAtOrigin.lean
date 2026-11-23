module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationFamilyCotangentBasisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorOfOriginDerivationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermOriginConstantSectionEqOriginStalkConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeStalkEvalAtOriginOriginStalkConstants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldApplyConstantEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.HodgeTateCharacterSystems
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivativeAtOriginAddTangentVectorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorEqOfTangentDerivativeAtOriginEqStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldEvalOriginEqTangentDerivativ

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section

namespace GlobalTheory.CoordsOrigin

variable {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}}

theorem valR_eq_germ (x : Sp A ⟶ X) (U : X.Opens) (hx : x (IsLocalRing.closedPoint A) ∈ U) (f : Γ(X, U)) :
    valR x U f = (X.presheaf.germ U _ hx ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of A) x).hom f := by
  have e : X.presheaf.germ U _ hx ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of A) x =
      x.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem x hx).ge ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  rw [e, valR, dite_eq_left (Scheme.preimage_eq_top_of_closedPoint_mem x hx).ge]
  rfl

end GlobalTheory.CoordsOrigin

namespace GlobalTheory.CoordsOrigin

variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]

theorem eta_hom : (η[G]).left ≫ G.hom = 𝟙 (Sp R) := Over.w (η[G])

theorem isTr_eta_tv (v : TanM (𝟙 (Sp R)) G) :
    IsTr G (RingHom.id R) (η[G]).left v (tv v).left := by
  have hη := eta_hom G
  refine ⟨1, Over.homMk (tv v).left ?_, ?_, ?_, ?_⟩
  · have := Over.w (tv v)
    simp only [Over.mk_hom, Category.comp_id] at this ⊢
    rw [this, hη, Category.comp_id]
  · rw [one_left]
    simp [hη]
  · have hd : dualMap (RingHom.id R) = RingHom.id (DualNumber R) := by
      ext x <;> simp [dualMap]
    simp [hd, spMap]
  · rw [_root_.one_mul]
    rfl

theorem evO_germ_of_isInv (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left) (hinv : IsInv G v dd) (O : G.left.Opens)
    (hO : origin G ∈ O) (f : Γ(G.left, O)) :
    evO G ((G.left.presheaf.germ O (origin G) hO).hom (dd O f)) =
      tanDer G v ((G.left.presheaf.germ O (origin G) hO).hom f) := by
  have hη := eta_hom G
  have hg : (η[G]).left ≫ G.hom = spMap (RingHom.id R) := by
    rw [hη]; simp [spMap]
  have hO' : (tv v).left (IsLocalRing.closedPoint (DualNumber R)) ∈ O := by
    rw [tv_closedPoint]; exact hO
  have htop : ⊤ ≤ (η[G]).left ⁻¹ᵁ O := (Scheme.preimage_eq_top_of_closedPoint_mem _ hO).ge
  have key := hinv.2 R (RingHom.id R) (η[G]).left (tv v).left O f hg htop (isTr_eta_tv G v)
  rw [valR_eq_germ _ O hO', valR_eq_germ (η[G]).left O hO] at key
  rw [tanDer_eq, evO]
  have e2 : G.left.presheaf.germ O (origin G) hO ≫
      (G.left.presheaf.stalkCongr (Inseparable.of_eq (tv_closedPoint G v).symm)).hom =
        G.left.presheaf.germ O _ hO' := by
    rw [TopCat.Presheaf.stalkCongr_hom]
    exact TopCat.Presheaf.germ_stalkSpecializes _ _ _
  rw [← CommRingCat.comp_apply, ← Category.assoc, e2]
  exact key.symm
end GlobalTheory.CoordsOrigin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldEvalOriginEqTangentDerivativStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

theorem _root_.GlobalTheory.T.invariantVectorField_eval_origin_eq_tangentDerivative : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left), IsInv G v dd → ∀ (O : G.left.Opens) (hO : origin G ∈ O) (f : Γ(G.left, O)), evO G ((G.left.presheaf.germ O (origin G) hO).hom (dd O f)) = tanDer G v ((G.left.presheaf.germ O (origin G) hO).hom f) := by
  first | exact @GlobalTheory.CoordsOrigin.evO_germ_of_isInv | exact GlobalTheory.CoordsOrigin.evO_germ_of_isInv | (intros; apply GlobalTheory.CoordsOrigin.evO_germ_of_isInv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginLocalRingNoetherianFreeUnitSectionConormal

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section

namespace GlobalTheory.CoordsOrigin
variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]

theorem constO_eq_strMap : constO G = (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.strMap G).hom := by
  ext r
  rw [GlobalTheory.HodgeTateCompare.strMap_eq]
  have h1 : (StructureSheaf.toStalk R (G.hom (origin G))).hom r =
      ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (G.hom (origin G)) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    rw [Scheme.ΓSpecIso_inv]
    rfl
  have h2 := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.Hom.germ_stalkMap G.hom ⊤ (origin G) trivial)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  change _ = (G.hom.stalkMap (origin G)).hom ((StructureSheaf.toStalk R (G.hom (origin G))).hom r)
  rw [h1, h2]
  simp [constO, Scheme.Hom.appLE]
  first
    | (erw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]; done)
    | (erw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]; rfl)
    | (rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]; rfl)
    | (simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]; rfl)

theorem free_finite_cotangent_of_eq [Smooth G.hom] (φ : R →+* G.left.presheaf.stalk (origin G))
    (hφ : φ = (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.strMap G).hom) :
    letI : Algebra R (G.left.presheaf.stalk (origin G)) := φ.toAlgebra
    Module.Free R (RingHom.ker (evO G)).Cotangent ∧ Module.Finite R (RingHom.ker (evO G)).Cotangent := by
  subst hφ
  obtain ⟨h1, h2⟩ := GlobalTheory.HodgeTateCompare.finite_projective_of_smooth (G := G)
  change Module.Free R (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Cotangent G) ∧ Module.Finite R (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Cotangent G)
  exact ⟨Module.free_of_flat_of_isLocalRing, h1⟩

end GlobalTheory.CoordsOrigin

theorem GlobalTheory.CoordsOrigin.noetherian_free_cotangent : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (G : Over (Sp R)) [GrpObj G], Smooth G.hom → IsNoetherianRing (G.left.presheaf.stalk (origin G)) ∧
      (letI : Algebra R (G.left.presheaf.stalk (origin G)) := (constO G).toAlgebra;
        Module.Free R (RingHom.ker (evO G)).Cotangent ∧ Module.Finite R (RingHom.ker (evO G)).Cotangent) := by
  intro R _ _ _ G _ hs
  haveI := hs
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  exact ⟨inferInstance, GlobalTheory.CoordsOrigin.free_finite_cotangent_of_eq G _ (GlobalTheory.CoordsOrigin.constO_eq_strMap G)⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginLocalRingNoetherianFreeUnitSectionConormalStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

theorem _root_.GlobalTheory.T.originLocalRing_noetherian_free_unitSectionConormal : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], Smooth G.hom → IsNoetherianRing (G.left.presheaf.stalk (origin G)) ∧ (letI : Algebra R (G.left.presheaf.stalk (origin G)) := (constO G).toAlgebra; Module.Free R (RingHom.ker (evO G)).Cotangent ∧ Module.Finite R (RingHom.ker (evO G)).Cotangent) := by
  first | exact @GlobalTheory.CoordsOrigin.noetherian_free_cotangent | exact GlobalTheory.CoordsOrigin.noetherian_free_cotangent | (intros; apply GlobalTheory.CoordsOrigin.noetherian_free_cotangent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivativeAtOriginSmulTangentVector

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section

namespace GlobalTheory.CoordsOrigin


set_option backward.isDefEq.respectTransparency false in
theorem stalkClosedPointTo_localMap_comp {X : Scheme.{0}} {A B : CommRingCat.{0}} [IsLocalRing A] [IsLocalRing B]
    (x : Spec A ⟶ X) (g : A ⟶ B) [IsLocalHom g.hom] (y : Spec B ⟶ X) (hy : y = Spec.map g ≫ x) (x₀ : X)
    (h₁ : x (IsLocalRing.closedPoint A) = x₀) (h₂ : y (IsLocalRing.closedPoint B) = x₀) :
    (X.presheaf.stalkCongr (Inseparable.of_eq h₂.symm)).hom ≫ Scheme.stalkClosedPointTo y =
      ((X.presheaf.stalkCongr (Inseparable.of_eq h₁.symm)).hom ≫ Scheme.stalkClosedPointTo x) ≫ g := by
  subst h₁
  have hy' : y = Spec.map (Scheme.stalkClosedPointTo x ≫ g) ≫ X.fromSpecStalk _ := by
    rw [hy, Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  clear hy
  subst hy'
  haveI : IsLocalHom (Scheme.stalkClosedPointTo x ≫ g).hom := by
    rw [CommRingCat.hom_comp]; infer_instance
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  simp only [TopCat.Presheaf.stalkCongr_hom, Category.assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc]
  exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (Scheme.stalkClosedPointTo x ≫ g) U _

theorem tanDer_smul : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (r : R) (v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)), tanDer G (r • v) f = r * tanDer G v f := by
  intro R _ _ G _ _ r v f
  have hl : IsLocalHom (CommRingCat.ofHom (epsMul r)).hom := ⟨fun a ha => (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (by
    simpa [epsMul] using (TrivSqZeroExt.isUnit_iff_isUnit_fst).1 ha)⟩
  have hy : (tv (r • v)).left = Spec.map (CommRingCat.ofHom (epsMul r)) ≫ (tv v).left := by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_smul, smT_left]
  have key := stalkClosedPointTo_localMap_comp (A := CommRingCat.of (DualNumber R)) (B := CommRingCat.of (DualNumber R))
    (tv v).left (CommRingCat.ofHom (epsMul r)) (tv (r • v)).left hy (origin G) (tv_closedPoint G v)
    (tv_closedPoint G (r • v))
  rw [tanDer_eq, tanDer_eq]
  refine (congrArg (fun φ => (φ.hom f).snd) key).trans ?_
  have hs : ∀ a : DualNumber R, (epsMul r a).snd = r * a.snd := fun a => by simp [epsMul]
  exact hs _

end GlobalTheory.CoordsOrigin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivativeAtOriginSmulTangentVectorStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

theorem _root_.GlobalTheory.T.tangentDerivativeAtOrigin_smul_tangentVector : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (r : R) (v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)), tanDer G (r • v) f = r * tanDer G v f := by
  first | exact @GlobalTheory.CoordsOrigin.tanDer_smul | exact GlobalTheory.CoordsOrigin.tanDer_smul | (intros; apply GlobalTheory.CoordsOrigin.tanDer_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCommGroupLocalCoordinatesAtOrigin

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

namespace GlobalTheory.CoordsOrigin

theorem coords_at_origin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ δ : Fin n → Derivation ℤ (G.left.presheaf.stalk (origin G)) (G.left.presheaf.stalk (origin G)), (∀ a O (hO : origin G ∈ O) f, δ a ((G.left.presheaf.germ O (origin G) hO).hom f) = (G.left.presheaf.germ O (origin G) hO).hom (dd a O f)) → ∃ z : Fin n → G.left.presheaf.stalk (origin G), (∀ i, evO G (z i) = 0) ∧ (∀ a i, evO G (δ a (z i)) = if a = i then 1 else 0) ∧ maximalIdeal (G.left.presheaf.stalk (origin G)) = (maximalIdeal R).map (constO G) ⊔ Ideal.span (Set.range z) := by
  intro R _ _ _ _ G _ _ hsm n v dd hinv δ hδ
  letI : Algebra R (G.left.presheaf.stalk (origin G)) := (constO G).toAlgebra
  obtain ⟨hN, hF, hFin⟩ := GlobalTheory.T.originLocalRing_noetherian_free_unitSectionConormal R G hsm
  have key : ∀ a f, evO G (δ a f) = tanDer G (v a) f := by
    intro a f
    obtain ⟨O, hx, g, rfl⟩ := G.left.presheaf.exists_germ_eq f
    rw [hδ a O hx g]
    exact GlobalTheory.T.invariantVectorField_eval_origin_eq_tangentDerivative R G (v a) (dd a) (hinv a) O hx g
  have hadd : ∀ a x y, tanDer G (v a) (x + y) = tanDer G (v a) x + tanDer G (v a) y := by
    intro a x y
    rw [← key, ← key, ← key, map_add (f := _), map_add (f := _)]
  have hmul : ∀ a x y, tanDer G (v a) (x * y) = evO G x * tanDer G (v a) y + evO G y * tanDer G (v a) x := by
    intro a x y
    rw [← key, ← key, ← key, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul]
  have hc : ∀ a r, tanDer G (v a) (algebraMap R _ r) = 0 := by
    intro a r
    rw [← key]
    show evO G (δ a (constO G r)) = 0
    rw [← GlobalTheory.GermConst.germ_constFn_origin R G ⊤ trivial r, hδ a ⊤ trivial,
      GlobalTheory.Heat.isInv_constFn R G (v a) (dd a) (hinv a) ⊤ r, map_zero, map_zero]
  let φ : TanM (𝟙 (Sp R)) G →+ (G.left.presheaf.stalk (origin G) → R) :=
    { toFun := fun w => tanDer G w
      map_zero' := funext fun f => by
        have h := GlobalTheory.T.tangentDerivativeAtOrigin_smul_tangentVector R G 0 0 f
        rwa [zero_smul, zero_mul] at h
      map_add' := fun u w => funext fun f => GlobalTheory.T.tangentDerivativeAtOrigin_add_tangentVector R G u w f }
  have hlin : ∀ (c : Fin n → R) f, tanDer G (∑ a, c a • v a) f = ∑ a, c a * tanDer G (v a) f := by
    intro c f
    have h1 : tanDer G (∑ a, c a • v a) f = φ (∑ a, c a • v a) f := rfl

    rw [h1, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => GlobalTheory.T.tangentDerivativeAtOrigin_smul_tangentVector R G (c a) (v a) f
  have hbasis : ∀ D : G.left.presheaf.stalk (origin G) → R, (∀ x y, D (x + y) = D x + D y) →
      (∀ x y, D (x * y) = evO G x * D y + evO G y * D x) → (∀ r, D (algebraMap R _ r) = 0) →
      ∃! c : Fin n → R, ∀ x, D x = ∑ a, c a * tanDer G (v a) x := by
    intro D h1 h2 h3
    obtain ⟨w, hw⟩ := GlobalTheory.T.exists_tangentVector_of_originDerivation R G D h1 h2 h3
    refine ⟨fun a => v.repr w a, ?_, ?_⟩
    · intro x
      rw [← hw x, ← hlin]
      congr 1
      exact (v.sum_repr w).symm
    · intro c hc'
      have hw' : ∑ a, c a • v a = w := GlobalTheory.T.tangentVector_eq_of_tangentDerivativeAtOrigin_eq R G _ _ fun f => by rw [hlin, hw, hc' f]
      funext a
      rw [← hw', v.repr_sum_self]
  obtain ⟨z, hz0, hz1, hz2⟩ := GlobalTheory.T.derivation_family_cotangent_basis R _ (evO G) (GlobalTheory.FormalOrigin.evO_constO R G) hF hFin n
    (fun a => tanDer G (v a)) hadd hmul hc hbasis
  exact ⟨z, hz0, fun a i => by rw [key]; exact hz1 a i, hz2⟩

end GlobalTheory.CoordsOrigin
end
end
