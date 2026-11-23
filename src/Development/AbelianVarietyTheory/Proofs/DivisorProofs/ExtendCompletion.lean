module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionRingHomExtPadicAlgClosureStatement
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFiniteTypeIntOfModel
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.Topology.Sheaves.Init
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueStalkHomPadicAlgClosureValuation
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvr
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFiniteTypeIntOfModelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical


theorem _root_.GlobalTheory.T.exists_affineOpen_finiteType_int_of_model : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), ∃ U : M.Z.Opens, IsAffineOpen U ∧ x ∈ U ∧ Algebra.FiniteType ℤ Γ(M.Z, U) := by
  first | exact @GlobalTheory.RatModel.exists_affineOpen_finiteType_int | exact GlobalTheory.RatModel.exists_affineOpen_finiteType_int | (intros; apply GlobalTheory.RatModel.exists_affineOpen_finiteType_int <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLocalHomAdicCompletionExtend

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem exists_isLocalHom_adicCompletion_extend (O : Type) [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] (V : Type) [CommRing V] [IsLocalRing V]
    [IsAdicComplete (maximalIdeal V) V] (ψ : O →+* V) (hψ : IsLocalHom ψ) :
    ∃ ev₀ : AdicCompletion (maximalIdeal O) O →+* V,
      IsLocalHom ev₀ ∧ ∀ a, ev₀ (algebraMap O _ a) = ψ a := by
  have h1 : maximalIdeal O ≤ (maximalIdeal V).comap ψ :=
    (IsLocalRing.maximalIdeal_comap ψ).ge
  have hn : ∀ n : ℕ, maximalIdeal O ^ n ≤ (maximalIdeal V ^ n).comap ψ := fun n =>
    (Ideal.pow_right_mono h1 n).trans (Ideal.le_comap_pow ψ n)
  let f : (n : ℕ) → AdicCompletion (maximalIdeal O) O →+* V ⧸ maximalIdeal V ^ n := fun n =>
    (Ideal.quotientMap _ ψ (hn n)).comp (AdicCompletion.evalₐ (maximalIdeal O) n : _ →+* _)
  have hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal V) hle).comp (f n) = f m := by
    intro m n hle
    refine RingHom.ext fun x => ?_
    obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective _ _ x
    simp only [f, RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk,
      Ideal.quotientMap_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    rw [Ideal.Quotient.eq, ← map_sub]
    apply hn m
    have := c.2 hle
    rw [SModEq.sub_mem] at this
    have h2 := neg_mem this
    simpa using h2
  have hev : ∀ a, IsAdicComplete.liftRingHom (maximalIdeal V) f hf (algebraMap O _ a) = ψ a := by
    intro a
    refine congrFun (IsHausdorff.funext' (maximalIdeal V)
      (f := fun a => IsAdicComplete.liftRingHom (maximalIdeal V) f hf (algebraMap O _ a))
      (g := fun a => ψ a) fun n b => ?_) a
    rw [IsAdicComplete.mk_liftRingHom]
    simp only [f, RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes]
    exact Ideal.quotientMap_mk
  refine ⟨IsAdicComplete.liftRingHom (maximalIdeal V) f hf, ?_, hev⟩
  apply ((IsLocalRing.local_hom_tfae _).out 1 3).mpr
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.comp_apply, hev]
  exact h1 ha

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLocalHomAdicCompletionExtendStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical


theorem _root_.GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_apply : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (V : Type) [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V] (ψ : O →+* V), IsLocalHom ψ → ∃ ev₀ : AdicCompletion (maximalIdeal O) O →+* V, IsLocalHom ev₀ ∧ ∀ a, ev₀ (algebraMap O _ a) = ψ a := by
  first | exact @GlobalTheory.exists_isLocalHom_adicCompletion_extend | exact GlobalTheory.exists_isLocalHom_adicCompletion_extend | (intros; apply GlobalTheory.exists_isLocalHom_adicCompletion_extend <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueStalkHomPadicAlgClosureValuationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical


theorem _root_.GlobalTheory.T.exists_unique_stalkHom_padicAlgClosure_valuation : ∀ (X : Scheme.{0}) (x : X) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) = x → ∃ φ : X.presheaf.stalk x →+* OO p, IsLocalHom φ ∧ spMap φ ≫ X.fromSpecStalk x = y ∧ ∀ g : X.presheaf.stalk x →+* OO p, spMap g ≫ X.fromSpecStalk x = y → g = φ := by
  first | exact @GlobalTheory.ValPt.exists_unique_stalk_hom | exact GlobalTheory.ValPt.exists_unique_stalk_hom | (intros; apply GlobalTheory.ValPt.exists_unique_stalk_hom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkNoetherianPadicImageFiniteExtension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory

theorem stalk_noetherian_and_finite_image :
    ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ x ∈ U, Algebra.FiniteType ℤ Γ(X, U) → ∀ (p : ℕ) [Fact p.Prime] (φ : X.presheaf.stalk x →+* OO p), IsNoetherianRing (X.presheaf.stalk x) ∧ ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ ∀ a, ((φ a : OO p) : PadicAlgCl p) ∈ K := by
  intro X U hU x hx hft p _ φ
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hloc := hU.isLocalization_stalk ⟨x, hx⟩
  haveI : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing ℤ Γ(X, U)
  refine ⟨IsLocalization.isNoetherianRing (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ this, ?_⟩
  let ψ : X.presheaf.stalk x →+* PadicAlgCl p := (OO p).subtype.comp φ
  let f : Γ(X, U) →+* PadicAlgCl p := ψ.comp (algebraMap Γ(X, U) (X.presheaf.stalk x))
  obtain ⟨s, hs⟩ := hft.out
  let K : IntermediateField ℚ_[p] (PadicAlgCl p) :=
    IntermediateField.adjoin ℚ_[p] ((s.image f : Finset (PadicAlgCl p)) : Set (PadicAlgCl p))
  refine ⟨K, ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin (fun y _ => Algebra.IsIntegral.isIntegral y)
  · have hgen : ∀ r : Γ(X, U), f r ∈ K := by
      intro r
      have hr : r ∈ Algebra.adjoin ℤ (s : Set Γ(X, U)) := by rw [hs]; trivial
      induction hr using Algebra.adjoin_induction with
      | mem y hy =>
        apply IntermediateField.subset_adjoin
        simp only [Finset.coe_image]
        exact Set.mem_image_of_mem f hy
      | algebraMap n =>
        have : f (algebraMap ℤ Γ(X, U) n) = (n : PadicAlgCl p) := by simp
        rw [this]; exact K.intCast_mem n
      | add a b _ _ ha hb => rw [map_add (f := _)]; exact K.add_mem ha hb
      | mul a b _ _ ha hb => rw [map_mul]; exact K.mul_mem ha hb
    intro a
    obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl a
    have hspec := IsLocalization.mk'_spec (X.presheaf.stalk x) r t
    have hunit : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) t) := IsLocalization.map_units _ t
    have hne : f t ≠ 0 := (hunit.map ψ).ne_zero
    have heq : ψ (IsLocalization.mk' (X.presheaf.stalk x) r t) =
        f r * (f t)⁻¹ := by
      have h2 := congrArg ψ hspec
      rw [map_mul] at h2
      change ψ _ * f t = f r at h2
      rw [← h2, _root_.mul_assoc, mul_inv_cancel₀ hne, _root_.mul_one]
    change ψ _ ∈ K
    rw [heq]
    exact K.mul_mem (hgen r) (K.inv_mem (hgen t))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkNoetherianPadicImageFiniteExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical


theorem _root_.GlobalTheory.T.stalk_noetherian_padicImage_finiteExtension : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ x ∈ U, Algebra.FiniteType ℤ Γ(X, U) → ∀ (p : ℕ) [Fact p.Prime] (φ : X.presheaf.stalk x →+* OO p), IsNoetherianRing (X.presheaf.stalk x) ∧ ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ ∀ a, ((φ a : OO p) : PadicAlgCl p) ∈ K := by
  first | exact @GlobalTheory.stalk_noetherian_and_finite_image | exact GlobalTheory.stalk_noetherian_and_finite_image | (intros; apply GlobalTheory.stalk_noetherian_and_finite_image <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendCompletion

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.ClassicalPt

theorem extend_completion : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z) (R : Type) [CommRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), y (cPt p) = x → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ev₀ : R →+* V) (i : V →+* OO p), IsAdicComplete (maximalIdeal V) V ∧ IsLocalHom ev₀ ∧ IsLocalHom i ∧ Function.Injective i ∧ spMap (i.comp ev₀) ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y ∧ ∀ ev : R →+* OO p, spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ev = i.comp ev₀ := by
  intro o' Ω _ _ _ _ M x R _ j hj p _ y hy
  obtain ⟨φ, hφl, hφ, hφu⟩ := GlobalTheory.T.exists_unique_stalkHom_padicAlgClosure_valuation M.Z x p y hy
  obtain ⟨U, hU, hxU, hft⟩ := GlobalTheory.T.exists_affineOpen_finiteType_int_of_model o' Ω M x
  obtain ⟨hN, K, hK, hφK⟩ := GlobalTheory.T.stalk_noetherian_padicImage_finiteExtension M.Z U hU x hxU hft p φ
  obtain ⟨hdvr, hcpl, -⟩ := GlobalTheory.intRing_complete_dvr p K hK
  obtain ⟨e, he⟩ := hj
  let i : GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K →+* OO p :=
    RingHom.codRestrict ((algebraMap K (PadicAlgCl p)).comp (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K).subtype) (OO p) (fun v => v.2)
  let ψK : M.Z.presheaf.stalk x →+* K :=
    RingHom.codRestrict ((OO p).subtype.comp φ) K (fun a => hφK a)
  let ψ : M.Z.presheaf.stalk x →+* GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K :=
    RingHom.codRestrict ψK (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) (fun a => (φ a).2)
  have hiψ : ∀ a, i (ψ a) = φ a := fun a => rfl
  have hil : IsLocalHom i := ⟨fun v hv => by
    obtain ⟨w, hw⟩ := hv.exists_right_inv
    have hw' : algebraMap K (PadicAlgCl p) (v : K) * (w : PadicAlgCl p) = 1 :=
      congrArg Subtype.val hw
    have h0 : (v : K) ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hw'
      exact zero_ne_one hw'
    refine isUnit_iff_exists_inv.2 ⟨⟨(v : K)⁻¹, ?_⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
    show algebraMap K (PadicAlgCl p) (v : K)⁻¹ ∈ OO p
    rw [map_inv₀, inv_eq_of_mul_eq_one_right hw']
    exact w.2⟩
  have hψl : IsLocalHom ψ := ⟨fun a ha => hφl.map_nonunit a (by rw [← hiψ]; exact ha.map i)⟩
  haveI := hN
  haveI := hcpl
  obtain ⟨ev', hev'l, hev'⟩ := GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_apply (M.Z.presheaf.stalk x) (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ψ hψl
  have hej : ∀ a, e.symm (j a) = algebraMap _ _ a := fun a => by rw [← he a, e.symm_apply_apply]
  let ev₀ : R →+* GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K := ev'.comp e.symm.toRingHom
  have hcomp : (i.comp ev₀).comp j = φ := RingHom.ext fun a => by
    show i (ev' (e.symm (j a))) = φ a
    rw [hej, hev', hiψ]
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K, inferInstance, inferInstance, hdvr, ev₀, i, hcpl, ?_, hil, ?_, ?_, ?_⟩
  · refine ⟨fun r hr => ?_⟩
    have h1 := hev'l.map_nonunit _ hr
    have h2 := h1.map e.toRingHom
    simpa using h2
  · intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext ((algebraMap K (PadicAlgCl p)).injective h)
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp, hφ]
  · intro ev hev
    have h1 : ev.comp j = φ := hφu _ (by
      rw [← hev, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
    have hf : (ev.comp e.toRingHom).comp (algebraMap _ _) = φ := RingHom.ext fun a => by
      rw [← h1]; simp [he]
    have h2 := GlobalTheory.T.adicCompletion_ringHom_ext_padicAlgClosure (M.Z.presheaf.stalk x) p (ev.comp e.toRingHom) ((i.comp ev₀).comp e.toRingHom)
      (by rw [hf]; exact hφl) (fun a => by
        have := congrArg (fun F => F a) hf
        have h3 := congrArg (fun F => F a) hcomp
        simp only [RingHom.comp_apply] at this h3
        change ev (e (algebraMap _ _ a)) = i (ev₀ (e (algebraMap _ _ a)))
        rw [he, h3, ← h1]
        rfl)
    refine RingHom.ext fun r => ?_
    have := congrArg (fun F => F (e.symm r)) h2
    simpa using this

end GlobalTheory.ClassicalPt
end
end
