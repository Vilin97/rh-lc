module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamFreeHodgeSequenceBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionOfDeRhamClassUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToH1StructureSurjectiveAbelian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeRhamClassOfRigidifiedExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeFiltrationToPDivOmegaLinearMapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCastOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiePairingCanonicalRigidifiedExtensionTangent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusCanonicalLiftPrimitiveHodgeStatement
public import Mathlib.Algebra.Module.Projective
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Mathlib.Algebra.WithConv
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaLevelBijectiveOfPowEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveHodgeToOmegaSpanModMaximalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfRangeSupSmulTopEqTop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiePairingCanonicalRigidifiedExtensionTangentStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lie_pairing_canonical_rigidified_extension_tangent :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A)
      (ψ : PrimitiveSubmodule A →ₗ[R] G.omega),
    (∀ c : PrimitiveSubmodule A, PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
    ∀ (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A)
      (hF : (⟨_, hβ⟩ : primDR A) ∈ PrimitiveSubmodule A) (x : G.Lie) (v : epsR R ⟶ A),
    t.LieCorr x v → x (ψ ⟨_, hF⟩) = tanVal v β :=
  @PtExt.lie_psi_cl_eq_tanVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieCompHodgeToOmegaEqLinearForm

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem exists_lie_comp_psi_eq :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → LieExact A →
    (∃ N' : Submodule R (primDR A), IsCompl (PrimitiveSubmodule A) N') →
    ∀ (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A)
      (ψ : PrimitiveSubmodule A →ₗ[R] G.omega),
    (∀ c : PrimitiveSubmodule A, GlobalTheory.PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
    ∀ l : Module.Dual R (PrimitiveSubmodule A), ∃ x : G.Lie, ∀ c, x (ψ c) = l c := by
  intro p _ R _ N hN A _ hab hLE hN' G t ψ hψ l
  obtain ⟨N', hc⟩ := hN'
  let h : HdR A := l ∘ₗ Submodule.projectionOnto (PrimitiveSubmodule A) N' hc
  obtain ⟨v, hv, -⟩ := hLE.1 h
  haveI := isAdicComplete_span_natCast_of_isNilpotent p R ⟨N, hN⟩
  obtain ⟨x, hx, -⟩ := t.existsUnique_lieCorr hv.1
  refine ⟨x, fun c => ?_⟩
  obtain ⟨⟨c, hc1⟩, hc2⟩ := c
  have hc3 : c ∈ F1 (A.hom ≫ 𝟙 _) := hc2
  rw [hodgeFiltration_eq_range] at hc3
  obtain ⟨β, rfl⟩ := hc3
  rw [GlobalTheory.T.lie_pairing_canonical_rigidified_extension_tangent p R N hN A hab G t ψ hψ β hc1 hc2 x v hx, ← hv.2 β hc1]
  change l (Submodule.projectionOnto (PrimitiveSubmodule A) N' hc ⟨_, hc1⟩) = _
  exact congrArg l (Submodule.projectionOnto_apply_left hc ⟨⟨_, hc1⟩, hc2⟩)

end GlobalTheory.PtExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieCompHodgeToOmegaEqLinearFormStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lie_comp_hodgeToOmega_eq_linearForm :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → LieExact A →
    (∃ N' : Submodule R (primDR A), IsCompl (PrimitiveSubmodule A) N') →
    ∀ (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A)
      (ψ : PrimitiveSubmodule A →ₗ[R] G.omega),
    (∀ c : PrimitiveSubmodule A, PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
    ∀ l : Module.Dual R (PrimitiveSubmodule A), ∃ x : G.Lie, ∀ c, x (ψ c) = l c :=
  @GlobalTheory.PtExt.exists_lie_comp_psi_eq
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfDualMapSurjectiveOfProjective

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem injective_of_dualMap_surjective_of_projective :
    ∀ (R : Type) [CommRing R] (M : Type 1) [AddCommGroup M] [Module R M] [Module.Projective R M]
      (N : Type) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N),
      Function.Surjective f.dualMap → Function.Injective f := by
  intro R _ M _ _ _ N _ _ f hf
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro m hm
  rw [LinearMap.mem_ker] at hm
  refine (Module.forall_dual_apply_eq_zero_iff R m).mp fun φ => ?_
  obtain ⟨ψ, rfl⟩ := hf φ
  simp [LinearMap.dualMap_apply, hm]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToRigidifiedExtensionBijectivePNilpotent

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem bijective_of_isCan_of_isNilpotent_of_hodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (L : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), (∀ c, IsCan t c (L c)) → Function.Bijective L := by
  intro hH p _ R _ hnil A _ g hA hg G t L hL
  obtain ⟨N, hN⟩ := hnil
  obtain ⟨hF, hHo, -⟩ := GlobalTheory.abelianDeRham_free_hodge_baseChange hH
  obtain ⟨hAll, -⟩ := hF R A g hA hg
  obtain ⟨hLie, hCompl, hFfin, hFproj, -⟩ := hHo R A g hA hg
  have hO : Function.Surjective (toH1O (A.hom ≫ 𝟙 _)) :=
    GlobalTheory.PtExt.toH1O_surjective_of_abelian hH R A g hA hg
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_hodgeFiltration_to_pDivOmega_linearMap p R N hN A hA G t

  haveI : Module.Finite R (Cot R (G.A N)) := .of_surjective _ (AugCot.d_surjective _)
  haveI : Module.Finite R G.omega :=
    .equiv (LinearEquiv.ofBijective _
      (PDivGroup.omegaLevel_bijective_of_pow_eq_zero p R N hN G N le_rfl)).symm
  haveI : Module.Projective R (PrimitiveSubmodule A) := hFproj

  have hψs : Function.Surjective ψ :=
    GlobalTheory.surjective_of_range_sup_smul_top_eq_top R _ G.omega ψ
      (GlobalTheory.T.primitive_hodge_to_omega_span_mod_maximal hH p R N hN A g hA hg G t ψ hψ)
  have hψi : Function.Injective ψ := by
    refine GlobalTheory.injective_of_dualMap_surjective_of_projective R _ G.omega ψ fun l => ?_
    obtain ⟨x, hx⟩ := GlobalTheory.T.exists_lie_comp_hodgeToOmega_eq_linearForm p R N hN A hA hLie hCompl G t ψ hψ l
    exact ⟨x, LinearMap.ext fun c => hx c⟩

  have hLF : ∀ c : PrimitiveSubmodule A, L c.1 = G.rigOfOmega (ψ c) := fun c =>
    GlobalTheory.PtExt.isCan_unique R A p G t c.1 hA _ _ (hL c.1) (hψ c)
  refine ⟨(injective_iff_map_eq_zero L).2 fun c hc => ?_, fun x => ?_⟩
  · have hcF : c ∈ PrimitiveSubmodule A :=
      GlobalTheory.T.mem_primitiveSubmodule_of_isCan_of_rigToExt_eq_zero p R N hN A hA G t c (L c) (hL c) (by rw [hc]; exact G.rigToExt.map_zero)
    have h1 : G.rigOfOmega (ψ ⟨c, hcF⟩) = 0 := by rw [← hLF ⟨c, hcF⟩]; exact hc
    have h2 : ψ ⟨c, hcF⟩ = 0 :=
      PDivGroup.rigOfOmega_injective_of_pow p R N hN G (by rw [h1, map_zero])
    have h3 : (⟨c, hcF⟩ : PrimitiveSubmodule A) = 0 := hψi (by rw [h2, map_zero])
    exact congrArg Subtype.val h3
  · obtain ⟨c, x', hcx', hx'⟩ := GlobalTheory.T.exists_deRham_class_of_rigidified_extension p R N hN A hA hAll hO G t x
    have hx'L : x' = L c := GlobalTheory.PtExt.isCan_unique R A p G t c hA _ _ hcx' (hL c)
    have hd : G.rigToExt (x - L c) = 0 := by
      exact (G.rigToExt.map_sub x (L c)).trans (sub_eq_zero.mpr (hx'L ▸ hx'.symm))
    obtain ⟨w, hw⟩ := (G.exact_rigOfOmega_rigToExt (x - L c)).1 hd
    obtain ⟨c₁, rfl⟩ := hψs w
    refine ⟨c + c₁.1, ?_⟩
    rw [map_add (f := _), hLF c₁, hw, add_sub_cancel]

end GlobalTheory.PtExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToRigidifiedExtensionBijectivePNilpotentStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.deRham_to_rigidified_extension_bijective_p_nilpotent : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (L : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), (∀ c, IsCan t c (L c)) → Function.Bijective L := by
  first | exact @GlobalTheory.PtExt.bijective_of_isCan_of_isNilpotent_of_hodgeDeRham | exact GlobalTheory.PtExt.bijective_of_isCan_of_isNilpotent_of_hodgeDeRham | (intros; apply GlobalTheory.PtExt.bijective_of_isCan_of_isNilpotent_of_hodgeDeRham <;> assumption)
end
end
