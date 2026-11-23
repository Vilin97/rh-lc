module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantFieldConstCoeffs
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.SurjOfCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentKillingWeightZeroMapsToAbelianPartUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombination
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieBasisCoordinatesBijectiveTangent
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsResEqOfUnitInChart

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusTangentOfRaynaudTangentOverUnit

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

noncomputable section

namespace GlobalTheory.HeatMod.TorField

open TrivSqZeroExt (inl inr)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (coord coord_comp)

theorem exists_torTan_of_q : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (p : epsR R ⟶ Y.H), IsTangent p → p ≫ Y.q = 1 → ∃ ℓ : Q.X →+ R, p = GlobalTheory.HeatMod.TorField.torTan ℓ ≫ Y.i := by
  intro R _ _ Q O _ _ _ oa Y p hp hq
  have hmono : ∀ {T : Over (Sp R)} (a b : T ⟶ splitTorus (Sp R) (RayEv.Chr Q)), a ≫ Y.i = b ≫ Y.i → a = b :=
    fun a b h => Y.isKernel.hom_ext h (toUnit_unique _ _)
  have hw : p ≫ Y.q = toUnit _ ≫ η[Q.P.A] := by rw [hq, Hom.one_def]
  let t := Y.isKernel.lift p (toUnit _) hw
  have ht : t ≫ Y.i = p := Y.isKernel.lift_fst _ _ _
  have := Y.i_linear.isMonHom
  have htan : Chart.spMap (Chart.fstD R) ≫ t = 1 := hmono _ _ (by
    rw [Category.assoc, ht, MonObj.one_comp]; exact (Chart.isTan_iff p).2 hp)
  let a : RayEv.Chr Q → DualNumber R := fun χ =>
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom.hom ((coord t).hom (AddMonoidAlgebra.single χ 1))
  have hfst : ∀ χ, (a χ).fst = 1 := fun χ => by
    have e := congrArg (fun f => (coord f).hom (AddMonoidAlgebra.single χ 1)) htan
    simp only at e
    rw [coord_comp, Diag.coord_one, CommRingCat.hom_comp, RingHom.comp_apply, Chart.spMap_left] at e
    have nat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Chart.fstD R).toRingHom)
    have k := congrArg (fun f => f.hom ((coord t).hom (AddMonoidAlgebra.single χ 1))) nat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at k
    rw [e, map_one] at k
    exact k.symm
  have h0 : a 0 = 1 := by
    show (Scheme.ΓSpecIso _).hom.hom ((coord t).hom (AddMonoidAlgebra.single 0 1)) = 1
    rw [Diag.coord_single_zero, map_one]
  have hadd : ∀ x y, a (x + y) = a x * a y := fun x y => by
    show (Scheme.ΓSpecIso _).hom.hom ((coord t).hom (AddMonoidAlgebra.single (x + y) 1)) = _
    rw [Diag.coord_single_add, map_mul]
  have hform : ∀ χ, a χ = 1 + inr (a χ).snd := fun χ => by
    ext
    · rw [hfst χ]; simp
    · simp
  let ℓ : Q.X →+ R :=
    { toFun := fun χ => (a χ).snd
      map_zero' := (congrArg TrivSqZeroExt.snd h0).trans TrivSqZeroExt.snd_one
      map_add' := fun x y => (congrArg TrivSqZeroExt.snd (hadd x y)).trans (by
        rw [hform x, hform y]
        simp only [mul_add, add_mul, _root_.one_mul, _root_.mul_one, TrivSqZeroExt.inr_mul_inr, add_zero,
          TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_one, TrivSqZeroExt.snd_inr, zero_add]) }
  refine ⟨ℓ, ?_⟩
  rw [← ht]
  refine congrArg (· ≫ Y.i) (Diag.hom_ext fun χ => ?_)
  rw [torTan, Diag.coord_ofChar]
  show _ = (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + inr (a χ).snd)
  rw [← hform χ]
  show _ = (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom.hom ((coord t).hom (AddMonoidAlgebra.single χ 1)))
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

end GlobalTheory.HeatMod.TorField
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusTangentOfRaynaudTangentOverUnitStatement

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

theorem _root_.GlobalTheory.T.exists_torus_tangent_of_raynaud_tangent_over_unit : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (p : epsR R ⟶ Y.H), IsTangent p → p ≫ Y.q = 1 → ∃ ℓ : Q.X →+ R, p = GlobalTheory.HeatMod.TorField.torTan ℓ ≫ Y.i := by
  first | exact @GlobalTheory.HeatMod.TorField.exists_torTan_of_q | exact GlobalTheory.HeatMod.TorField.exists_torTan_of_q | (intros; apply GlobalTheory.HeatMod.TorField.exists_torTan_of_q <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecHomExtOfLocalizationAtPrimes

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

namespace GlobalTheory.SpecLocalExt

theorem hom_ext_of_localizationAtPrime : ∀ (A : Type) [CommRing A] (X : Scheme.{0}) (a b : Sp A ⟶ X), (∀ (P : Ideal A) [P.IsPrime], spMap (algebraMap A (Localization.AtPrime P)) ≫ a = spMap (algebraMap A (Localization.AtPrime P)) ≫ b) → a = b := by
  intro A _ X a b h
  refine GlobalTheory.hom_ext_of_isLocalRing fun B _ _ φ => ?_
  let P : Ideal A := (IsLocalRing.maximalIdeal B).comap φ
  haveI : P.IsPrime := Ideal.comap_isPrime φ (IsLocalRing.maximalIdeal B)
  have hu : ∀ y : P.primeCompl, IsUnit (φ y) := fun y => by
    by_contra hy
    exact y.2 ((IsLocalRing.mem_maximalIdeal _).2 hy)
  let ψ : Localization.AtPrime P →+* B := IsLocalization.lift hu
  have e : φ = ψ.comp (algebraMap A (Localization.AtPrime P)) := (IsLocalization.lift_comp hu).symm
  have h' := h P
  simp only [spMap] at h'
  rw [e, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc, h']

end GlobalTheory.SpecLocalExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecHomExtOfLocalizationAtPrimesStatement

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

theorem _root_.GlobalTheory.T.spec_hom_ext_of_localization_at_primes : ∀ (A : Type) [CommRing A] (X : Scheme.{0}) (a b : Sp A ⟶ X), (∀ (P : Ideal A) [P.IsPrime], spMap (algebraMap A (Localization.AtPrime P)) ≫ a = spMap (algebraMap A (Localization.AtPrime P)) ≫ b) → a = b := by
  first | exact @GlobalTheory.SpecLocalExt.hom_ext_of_localizationAtPrime | exact GlobalTheory.SpecLocalExt.hom_ext_of_localizationAtPrime | (intros; apply GlobalTheory.SpecLocalExt.hom_ext_of_localizationAtPrime <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddHomInvariantFieldKillsWeightZero

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
noncomputable section
namespace GlobalTheory.HeatMod.TorUniq
open GlobalTheory.ZH.CrdCalc (valR_res valR_spMap)
open ReciprocityTheory.ChartRestriction.G.Chart (sp)
open TrivSqZeroExt (inl inr)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (coord coord_comp)
open GlobalTheory.HeatMod.TorField

theorem exists_addHom_of_kills_wt_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ e : Fin n → R, (∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0) → ∃ ℓ : Q.X →+ R, ∀ (α : Q.X) (V : Q.P.A.left.Opens) f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = constFn Y.H.hom _ (ℓ α) * f := by
  intro R _ _ Q O _ _ _ oa Y n v dd hd e he
  obtain ⟨u, hb, hu⟩ := exists_isLieBasis v
  have hc : IsLieComb e u (GlobalTheory.SqZero.lieExp u (fun a => (TrivSqZeroExt.inr (e a) : DualNumber R)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) := (GlobalTheory.SqZero.isLieComb_iff_lieExp e _).2 rfl
  have ht := GlobalTheory.Reg.isTangent_of_isLieComb hb.1 hc
  have hq : GlobalTheory.SqZero.lieExp u (fun a => (TrivSqZeroExt.inr (e a) : DualNumber R)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) ≫ Y.q = 1 :=
    Over.OverMorphism.ext (GlobalTheory.T.spec_hom_ext_of_localization_at_primes _ _ _ _ fun P _ => GlobalTheory.T.tangent_killing_weight_zero_maps_to_abelianPart_unit R Q O oa Y n (fun a => v a) u hb.1 hu dd hd e he _ _)
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.exists_torus_tangent_of_raynaud_tangent_over_unit R Q O oa Y _ ht hq
  refine ⟨ℓ, fun α V f hf => ?_⟩
  show combF Y.H.hom dd e _ f = _
  refine sub_eq_zero.1 (Adjust.eq_zero_of_valR_points _ _ fun S _ g hg => ?_)
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) (g ≫ Y.H.hom)
  let φ : R →+* S := φ'.hom
  have hφ : g ≫ Y.H.hom = spMap φ := hφ'.symm
  letI : Algebra R S := φ.toAlgebra
  let z : sp (R₀ := R) S ⟶ Y.H := Over.homMk g hφ
  let ψ : DualNumber R →ₐ[R] DualNumber S := GlobalTheory.SqZero.dualMap (Algebra.ofId R S)
  have hψ : ∀ a : R, ψ (inr a) = inr (φ a) := fun a => GlobalTheory.SqZero.dualMap_inr _ _
  obtain ⟨a₁, a₂⟩ := valR_spMap (GlobalTheory.SqZero.inlS R S).toRingHom g _ hg
  obtain ⟨b₁, b₂⟩ := valR_prod hu hb.1 hd (fun i => ψ (inr (e i)))
    (fun _ _ => by rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) _ a₁ Finset.univ
  have E0 := congrArg (ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ ≫ ·) hℓ.symm
  simp only [GlobalTheory.SqZero.comp_lieExp, ← Category.assoc] at E0
  rw [GlobalTheory.SqZero.lieExp] at E0
  rw [← E0] at b₁ b₂
  have k := valR_torus_mul Y (S := DualNumber S) (φ := algebraMap R (DualNumber S)) (ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ ≫ torTan ℓ) _
    (coord_torTan ℓ ψ) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) hf a₁ b₁
  have a₃ : ∀ s, valR (A := DualNumber S) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z).left (Y.q.left ⁻¹ᵁ V) s = inl (valR g _ s) := a₂
  have k' := congrArg TrivSqZeroExt.snd ((b₂ f).symm.trans k)
  have hu' : ((Units.map ψ.toRingHom.toMonoidHom (epsUnit (ℓ α)) : (DualNumber S)ˣ) : DualNumber S) = 1 + inr (φ (ℓ α)) := by
    rw [← hψ, ← map_one ψ, ← map_add (f := _)]; rfl
  simp only [a₃, hψ, hu'] at k'

  rw [WtAlg.valR_sub' _ _ hg, WtAlg.valR_mul'' _ _ hg, Adjust.valR_const _ φ g hφ _ hg, combF,
  GlobalTheory.ZH.CrdCalc.valR_eq _ _ hg, map_sum, sub_eq_zero]
  simp only [← GlobalTheory.ZH.CrdCalc.valR_eq _ _ hg, WtAlg.valR_mul'' _ _ hg, Adjust.valR_const _ φ g hφ _ hg]
  simpa [TrivSqZeroExt.snd_sum, _root_.mul_comm] using k'

end GlobalTheory.HeatMod.TorUniq
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddHomInvariantFieldKillsWeightZeroStatement

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

theorem _root_.GlobalTheory.T.exists_addHom_invariantField_kills_weightZero : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ e : Fin n → R, (∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0) → ∃ ℓ : Q.X →+ R, ∀ (α : Q.X) (V : Q.P.A.left.Opens) f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = constFn Y.H.hom _ (ℓ α) * f := by
  first | exact @GlobalTheory.HeatMod.TorUniq.exists_addHom_of_kills_wt_zero | exact GlobalTheory.HeatMod.TorUniq.exists_addHom_of_kills_wt_zero | (intros; apply GlobalTheory.HeatMod.TorUniq.exists_addHom_of_kills_wt_zero <;> assumption)
end
end
