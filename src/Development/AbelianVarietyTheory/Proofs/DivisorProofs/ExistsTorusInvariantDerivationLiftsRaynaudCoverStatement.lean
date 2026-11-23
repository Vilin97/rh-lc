module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFormSec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDerivationExtendOfFormallySmooth
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoExtendsSemiAbelianDvrInducingFormal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldExtendingAffineDerivation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightPreservingLiftOfBaseDerivationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageProjectionAbelianPartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPreservingVectorFieldOnSmallerPreimagesStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationLiftRaynaudPreimageAffine

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LiftDer

theorem exists_lift_of_smooth (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) [Smooth f]
    (U : X.Opens) (hU : IsAffineOpen U) (D : Derivation ℤ R R) :
    ∃ δ : Γ(X, U) → Γ(X, U), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧
      ∀ r, δ (constFn f U r) = constFn f U (D r) := by
  let g : R →+* Γ(X, U) :=
    (f.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hg : g.Smooth := by
    refine RingHom.Smooth.comp (RingHom.Smooth.of_bijective ?_) ?_
    · exact ((Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm).bijective
    · exact HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
  letI : Algebra R Γ(X, U) := g.toAlgebra
  haveI : Algebra.FormallySmooth R Γ(X, U) := hg.formallySmooth
  obtain ⟨d, hadd, hmul, hc⟩ := GlobalTheory.KS.exists_derivation_extend_of_formallySmooth R Γ(X, U) Γ(X, U)
    (RingHom.id _) (fun r => g (D r)) (fun a b => by simp) (fun a b => by
      simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, RingHom.id_apply]
      rw [RingHom.algebraMap_toAlgebra])
  exact ⟨d, hadd, hmul, fun r => hc r⟩

theorem isAffineHom_q {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) : IsAffineHom Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have hc : IsAffineHom c.q.left := c.q_affine
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst Q.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  infer_instance

theorem smooth_H {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) : Smooth Y.H.hom := by
  have h1 : Smooth Y.q.left := Y.smooth_q
  have := Q.P.smoothDim
  have h2 : Smooth Q.P.A.hom := SmoothOfRelativeDimension.smooth Q.P.g _
  rw [← Over.w Y.q]
  infer_instance

theorem exists_lift_preimage : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R), ∃ δ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ ∀ r, δ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r) := by
  intro R _ _ Q O _ _ _ oa Y V D
  have := isAffineHom_q Y
  have := smooth_H Y
  exact exists_lift_of_smooth R Y.H.left Y.H.hom _ (V.2.preimage Y.q.left) D

end GlobalTheory.LiftDer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationLiftRaynaudPreimageAffineStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_derivation_lift_raynaud_preimage_affine : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R), ∃ δ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ ∀ r, δ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r) := by
  first | exact @GlobalTheory.LiftDer.exists_lift_preimage | exact GlobalTheory.LiftDer.exists_lift_preimage | (intros; apply GlobalTheory.LiftDer.exists_lift_preimage <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldExtendingAffineDerivationStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_vectorField_extending_affineDerivation : ∀ (Z : Scheme.{0}) (U : Z.Opens), IsAffineOpen U → ∀ δ : Γ(Z, U) → Γ(Z, U), (∀ a b, δ (a + b) = δ a + δ b) → (∀ a b, δ (a * b) = a * δ b + b * δ a) → ∃ d : Fld Z, IsField U d ∧ d U = δ := by
  first | exact @GlobalTheory.DerFieldExt.exists_field | exact GlobalTheory.DerFieldExt.exists_field | (intros; apply GlobalTheory.DerFieldExt.exists_field <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantLiftDerivationRaynaud

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.Heat.HxLift

theorem exists_invLift : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R), ∃ d : Fld Y.H.left, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V.1) d ∧ ∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f) := by
  intro R _ _ Q O _ _ _ oa Y V D
  obtain ⟨δ₀, h0a, h0m, h0c⟩ := GlobalTheory.T.exists_derivation_lift_raynaud_preimage_affine R Q O oa Y V D
  obtain ⟨δ, ha, hm, hc, hw⟩ := GlobalTheory.T.exists_weight_preserving_lift_of_base_derivation R Q O oa Y V D δ₀ h0a h0m h0c
  obtain ⟨d, hd, hdU⟩ := GlobalTheory.T.exists_vectorField_extending_affineDerivation Y.H.left _ (GlobalTheory.T.isAffineOpen_preimage_projection_abelianPart R Q O oa Y V) δ ha hm
  refine ⟨d, ⟨hd, fun O' hO' r => ?_⟩, ?_⟩
  · rw [← GlobalTheory.ZH.FormSec.res_constFn Y.H.hom hO' r, ← GlobalTheory.ZH.FormSec.res_constFn Y.H.hom hO' (D r),
      hd.2.2 _ _ hO' le_rfl, hdU, hc]
  · refine GlobalTheory.T.weight_preserving_vectorField_on_smaller_preimages R Q O oa Y V d hd (fun α f hf => ?_)
    rw [hdU]
    exact hw α f hf

end GlobalTheory.Heat.HxLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantLiftDerivationRaynaudStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_torusInvariant_lift_derivation_raynaud : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R), ∃ d : Fld Y.H.left, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V.1) d ∧ ∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f) := by
  first | exact @GlobalTheory.Heat.HxLift.exists_invLift | exact GlobalTheory.Heat.HxLift.exists_invLift | (intros; apply GlobalTheory.Heat.HxLift.exists_invLift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantDerivationLiftsRaynaudCover

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.HeatInvLift.exists_invLift_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (D : Derivation ℤ R R), ∃ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left), ⨆ i, V i = ⊤ ∧ (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) ∧ (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) ∧ ∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f)) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y D
  let J := {p : Dd.toPre.P.A.left.affineOpens × Dd.toPre.P.L.ι // p.1.1 ≤ Dd.toPre.P.L.U p.2}
  have H := fun i : J => GlobalTheory.T.exists_torusInvariant_lift_derivation_raynaud R Dd.toPre O oa Y i.1.1 D
  choose d hd using H
  refine ⟨J, fun i => i.1.1.1, fun i => i.1.2, d, ?_, fun i => i.2, fun i => (hd i).1, fun i α V' hV' f hf => ?_⟩
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ (⨆ k, Dd.toPre.P.L.U k) := by rw [Dd.toPre.P.isLB.cover]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVk⟩ :=
      Dd.toPre.P.A.left.isBasis_affineOpens.exists_subset_of_mem_open hk (Dd.toPre.P.L.U k).isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨V, hV⟩, k), hVk⟩, hxV⟩
  · have e : Y.q.left ⁻¹ᵁ (V' ⊓ i.1.1.1) = Y.q.left ⁻¹ᵁ V' := by
      rw [Scheme.Hom.preimage_inf]; exact inf_eq_left.2 hV'
    have key := (hd i).2 α (V' ⊓ i.1.1.1) inf_le_right
    rw [e] at key
    exact key f hf
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantDerivationLiftsRaynaudCoverStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_torusInvariant_derivationLifts_raynaudCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (D : Derivation ℤ R R), ∃ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left), ⨆ i, V i = ⊤ ∧ (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) ∧ (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) ∧ ∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f)) := by
  first | exact @GlobalTheory.HeatInvLift.exists_invLift_cover | exact GlobalTheory.HeatInvLift.exists_invLift_cover | (intros; apply GlobalTheory.HeatInvLift.exists_invLift_cover <;> assumption)
end
end
