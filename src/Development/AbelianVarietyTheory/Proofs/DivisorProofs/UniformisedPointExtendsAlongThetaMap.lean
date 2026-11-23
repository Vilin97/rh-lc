module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNzOfPolAt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSectionNonzeroFibresLocalRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiRelOfExpT
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsIntegralUnitOfClosedFibreNonvanish
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsTwoPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSymmetricFunctionValuesInGroundFieldStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreExistsGeneratorStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Basify
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsFieldDetermineDescendStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapCoordsOfSymmetricThetaIsomorphicFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsIntegralUnitNormalLocalDoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTripleFibrePrincipallyPolarisedDimensio

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisationSectionNonvanishingClosedFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ExtNZ

theorem exists_sec_nz : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ t : SAB H (Sp R), Nonempty (PELUnif (IsLocalRing.maximalIdeal R) t) → ∃ σ : SecAt t.G t.PP.L (𝟙 (Sp R)), NZ t.G t.PP.L (𝟙 (Sp R)) σ := by
  intro E _ _ _ H R _ _ _ hB t ⟨P⟩
  haveI := t.comm
  haveI : GeometricallyConnected t.G.hom := t.semi.geomConnected
  haveI : IsNoetherianRing R := hB.1.1
  have hLaws := GlobalTheory.abelianSchemeLaws_all

  obtain ⟨th, hth, -⟩ := GlobalTheory.PsiRing.exists_basis_fibNZ hLaws.2.secTwist R P.D.toPre
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : P.D.toPre.SecB 1 0, ∀ (Z : Scheme.{0}) (r : Z ⟶ _) (z : Z) (J), Good P.D.toPre.P.L z J →
      sval th r z J = sval f₀ (r ≫ (snd (𝟙_ _) P.D.toPre.P.A).left) z J := by
    refine GlobalTheory.PsiExpansion.exists_sec_of_retract P.D.toPre.P.isLB _ _
      (GlobalTheory.PsiExpansion.snd_lift_unit P.D.toPre.P.A) (fun i => ?_) th
    fin_cases i
    · exact congrArg CommaMorphism.left (lift_snd (toUnit P.D.toPre.P.A) (𝟙 P.D.toPre.P.A))
    · refine congrArg CommaMorphism.left (show lift (toUnit P.D.toPre.P.A) (𝟙 P.D.toPre.P.A) ≫
        padd P.D.toPre.P.A (snd _ _) (toUnit _ ≫ P.D.toPre.c 0) = padd P.D.toPre.P.A (𝟙 _) (toUnit _ ≫ P.D.toPre.c 0) from ?_)
      simp only [padd, ← Category.assoc, comp_lift, lift_snd, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit P.D.toPre.P.A) (𝟙 P.D.toPre.P.A) ≫ toUnit _ ≫ P.D.toPre.c 0 = toUnit _ ≫ P.D.toPre.c 0 from ?_)
      rw [← Category.assoc, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit P.D.toPre.P.A) (𝟙 P.D.toPre.P.A) ≫ toUnit _ ≫ η[P.D.toPre.P.A] = toUnit _ ≫ η[P.D.toPre.P.A] from ?_)
      rw [← Category.assoc, comp_toUnit]
  obtain ⟨z₀, hz₀, hn₀⟩ := hth (IsLocalRing.closedPoint R)
  have hx : P.D.toPre.P.A.hom ((snd (𝟙_ (Over (Sp R))) P.D.toPre.P.A).left z₀) = IsLocalRing.closedPoint R :=
    (congrArg (fun q => q z₀) (Over.w (snd (𝟙_ (Over (Sp R))) P.D.toPre.P.A))).trans hz₀
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' P.D.toPre.P.isLB z₀
  have hu : IsUnit (sval th (𝟙 _) z₀ J) := (isUnit_sval_iff th (𝟙 _) z₀ hJ).2 hn₀
  rw [hf₀ _ _ z₀ J hJ, Category.id_comp] at hu
  have hxn := (isUnit_sval_iff f₀ _ z₀ hJ).1 hu

  obtain ⟨σ, fam, hfam0, hσ, hmem, -⟩ := GlobalTheory.ThetaUnit.exists_theta hLaws.1.globalFns hLaws.1.secBaseChange
    le_rfl P.U f₀ ⟨_, hx, hxn⟩
  have key : ∃ σ : H0 P.U.LG.L 1, ∃ g, t.G.hom g = IsLocalRing.closedPoint R ∧ g ∈ nonzeroLocus σ :=
    ⟨σ, GlobalTheory.ThetaUnit.exists_mem_nonzeroLocus le_rfl P.U.toUnifPre (hσ 0)
      (by rw [hfam0]; exact ⟨_, hx, hxn⟩) hmem⟩
  rw [P.bundle] at key
  obtain ⟨σ, g, hg, hn⟩ := key
  refine ⟨GlobalTheory.TorRef.upSec t.G σ, GlobalTheory.Ex.OnModel.toBase t.G g, ?_, ?_⟩
  · have a : GlobalTheory.Ex.OnModel.toBase t.G ≫ (fst (Over.mk (𝟙 (Sp R))) t.G).left = t.G.hom := by
      rw [GlobalTheory.Ex.OnModel.toBase, ← Over.comp_left, lift_fst]; rfl
    rw [← Scheme.Hom.comp_apply, a]
    exact hg
  · refine GlobalTheory.Ex.OnModel.mem_nonzeroLocus_pullTo σ _ _ ?_
    rw [← Scheme.Hom.comp_apply, GlobalTheory.Ex.OnModel.toBase_snd]
    exact hn

end GlobalTheory.UMin.ExtNZ
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisationSectionNonvanishingClosedFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_polarisation_section_nonvanishing_closed_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ t : SAB H (Sp R), Nonempty (PELUnif (IsLocalRing.maximalIdeal R) t) → ∃ σ : SecAt t.G t.PP.L (𝟙 (Sp R)), NZ t.G t.PP.L (𝟙 (Sp R)) σ := by
  first | exact @GlobalTheory.UMin.ExtNZ.exists_sec_nz | exact GlobalTheory.UMin.ExtNZ.exists_sec_nz | (intros; apply GlobalTheory.UMin.ExtNZ.exists_sec_nz <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpacePointOfUnitCoordinate

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

theorem exists_pCrd_of_isUnit : ∀ (o R : Type) [CommRing o] [CommRing R] (n : ℕ) (β : o →+* R) (v : Fin (n + 1) → R),
    (∃ j, IsUnit (v j)) → ∃ ξ : Sp R ⟶ PSpace o n, ξ ≫ PSpace.str o n = spMap β ∧ PCrd ξ v := by
  intro o R _ _ n β v ⟨j, hj⟩
  have hv : Ideal.span (Set.range v) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨j, rfl⟩) hj
  have hstr : GlobalTheory.ProjSpace.pt β v hv ≫ PSpace.str o n = spMap β := by
    rw [GlobalTheory.ProjSpace.pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C β v r
  refine ⟨GlobalTheory.ProjSpace.pt β v hv, hstr, ?_⟩
  have h1 := (GlobalTheory.ZM.ProjCoord.secCoord_iff (Equiv.refl _) (𝟙 _) β (GlobalTheory.ProjSpace.pt β v hv)
    (by rw [Category.comp_id, hstr]) v).2 ⟨hv, Category.comp_id _⟩
  have h2 := (GlobalTheory.ZM.RepBC.secCoord_pull (GlobalTheory.ProjSpace.O1 o n) (GlobalTheory.ProjSpace.coord o n) (𝟙 _) _ v).1 h1
  rwa [Category.comp_id] at h2

end GlobalTheory.UMin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpacePointOfUnitCoordinateStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_projectiveSpace_point_of_unit_coordinate : ∀ (o R : Type) [CommRing o] [CommRing R] (n : ℕ) (β : o →+* R) (v : Fin (n + 1) → R), (∃ j, IsUnit (v j)) → ∃ ξ : Sp R ⟶ PSpace o n, ξ ≫ PSpace.str o n = spMap β ∧ PCrd ξ v := by
  first | exact @GlobalTheory.UMin.exists_pCrd_of_isUnit | exact GlobalTheory.UMin.exists_pCrd_of_isUnit | (intros; apply GlobalTheory.UMin.exists_pCrd_of_isUnit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratesSectionsOfThetaSymmetricFunctionsNeZero

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.GenSym

theorem polFib_base {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) {g : ℕ} {R R' : Type}
    [CommRing R] [CommRing R'] {x : Sp R ⟶ S} (i : R →+* R') (h : PolFib G L g x) : PolFib G L g (spMap i ≫ x) := by
  obtain ⟨P, α, hg, hα, hPL⟩ := h
  obtain ⟨P', ψ, hg', hψ, hPL'⟩ := exists_isPolFibre polBaseChange_holds i P
  refine ⟨P', ψ ≫ α, hg'.trans hg, hψ.comp hα, ?_⟩
  exact LBIso.trans P'.isLB (pull_isLB P.isLB ψ) (pull_isLB hL _) hPL'.symm
    (LBIso.trans (pull_isLB P.isLB ψ) (pull_isLB (pull_isLB hL α) ψ) (pull_isLB hL _)
      (RigidBundleGlue.LBIso.pull hPL ψ) (GlobalTheory.UMin.FibMove.lbIso_pull_comp hL α ψ).symm)

theorem isGenSec_of_symAt : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left)
    (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (Ω : Type) [Field Ω] [CharZero Ω]
    (x : Sp Ω ⟶ S) (θ : SecAt G L x) (e : Fin N → Ω), Odd m → N = m ^ (4 * g) → PolFib G L g x →
    SymAt G L ρ m x θ e → (∃ j, e j ≠ 0) → IsGenSec G L ((1 : ℕ) : ℤ) θ := by
  intro S G _ _ L ρ hL hρ g m N Ω _ _ x θ e hm hN hpol hsym hne
  obtain ⟨⟨θ₁, h₁⟩, -⟩ := GlobalTheory.UMin.gen_of_polFib S G L hL g Ω x hpol
  obtain ⟨r, hr⟩ := (isGenSec_iff θ₁).1 h₁ (SecM.ofSec G θ)
  obtain ⟨a, rfl⟩ := (fnR x).surjective r
  by_cases ha : a = 0
  · exfalso
    subst ha
    let K := AlgebraicClosure Ω
    let i : Ω →+* K := algebraMap Ω K
    have hpol' : PolFib G L g (spMap i ≫ x) := polFib_base hL i hpol
    have hmK : (m : K) ≠ 0 := by
      have : m ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hm)
      exact_mod_cast this
    obtain ⟨pt, c, hl⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed S G L ρ hL hρ g m N K (spMap i ≫ x) (SecAt.pull G L θ₁ i) hm hmK hN hpol'
    have h0 : SecM.ofSec G (SecAt.pull G L θ i) = (0 : Γ((Over.mk (spMap i ≫ x)).left, ⊤)) •
        SecM.ofSec G (SecAt.pull G L θ₁ i) := by
      have q := congrArg (pl i rfl) hr
      rw [pl_smul, map_zero, map_zero, pl_ofSec, pl_ofSec] at q
      exact q
    have hl' : ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt (fun b => 0 * c b) := by
      refine ⟨hl.1, fun b => ?_, hl.2.2⟩
      have q := ThG.smul hL h0 (hl.2.1 b)
      simpa using q
    obtain ⟨j, hj⟩ := hne
    have q := hsym K i pt _ hl' j
    rw [(GlobalTheory.UMin.symTup_basic).1 K N c 0 j, zero_pow (Nat.factorial_ne_zero N), zero_mul] at q
    exact hj (i.injective (q.trans (map_zero i).symm))
  · refine (isGenSec_iff θ).2 fun s => ?_
    obtain ⟨r', hr'⟩ := (isGenSec_iff θ₁).1 h₁ s
    refine ⟨r' * fnR x a⁻¹, ?_⟩
    rw [hr', hr, smul_smul, _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, _root_.mul_one]

end GlobalTheory.UMin.GenSym
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratesSectionsOfThetaSymmetricFunctionsNeZeroStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.generates_sections_of_thetaSymmetricFunctions_ne_zero : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (x : Sp Ω ⟶ S) (θ : SecAt G L x) (e : Fin N → Ω), Odd m → N = m ^ (4 * g) → PolFib G L g x → SymAt G L ρ m x θ e → (∃ j, e j ≠ 0) → IsGenSec G L ((1 : ℕ) : ℤ) θ := by
  first | exact @GlobalTheory.UMin.GenSym.isGenSec_of_symAt | exact GlobalTheory.UMin.GenSym.isGenSec_of_symAt | (intros; apply GlobalTheory.UMin.GenSym.isGenSec_of_symAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointExtendsAlongThetaMap

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ExtP

theorem genericFibre_polAV : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c) (t : SAB H (Sp R)), GenOf Xo c y t → ∃ (P : PolAV (Sp (FractionRing R))) (α : P.A.left ⟶ Xo.univ.t.G.left) (α' : P.A.left ⟶ t.G.left), P.g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) ∧ IsGrpPullback P.A Xo.univ.t.G (y ≫ pullback.fst _ _) α ∧ LBIso P.L (Xo.univ.t.PP.L.pull α) ∧ IsGrpPullback P.A t.G (jK R) α' ∧ LBIso P.L (t.PP.L.pull α') := by
  intro E _ _ _ H Dw l Xo c R _ _ y t hy
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := hy
  have hw₁ : LBIso tK.PP.L (t.PP.L.pull m₁.cm.F) := by
    obtain ⟨w, hw, -⟩ := m₁.lin; exact ⟨w, hw⟩
  have hw₂ : LBIso tK.PP.L (Xo.univ.t.PP.L.pull m₂.cm.F) := by
    obtain ⟨w, hw, -⟩ := m₂.lin; exact ⟨w, hw⟩
  have hd := GlobalTheory.UMin.polFib_univ E H Dw l Xo c (FractionRing R) (𝟙 _ ≫ y ≫ pullback.fst _ _)
  obtain ⟨P, α₀, hgP, hpb₀, hL₀⟩ := ((GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback _ _ Xo.univ.t.G Xo.univ.t.PP.L tK.G tK.PP.L
    (y ≫ pullback.fst _ _) m₂.cm.F Xo.univ.t.PP.isLB tK.PP.isLB m₂.cart hw₂ _ (FractionRing R) (𝟙 _)).1).2 hd
  refine ⟨P, α₀ ≫ m₂.cm.F, α₀ ≫ m₁.cm.F, hgP, ?_, ?_, ?_, ?_⟩
  · have h := hpb₀.comp m₂.cart
    rwa [Category.id_comp] at h
  · exact LBIso.trans P.isLB (pull_isLB tK.PP.isLB α₀) (pull_isLB Xo.univ.t.PP.isLB _) hL₀
      (GlobalTheory.Ex.GenericFibre.lbIso_pull hw₂ α₀ rfl)
  · have h := hpb₀.comp m₁.cart
    rwa [Category.id_comp] at h
  · exact LBIso.trans P.isLB (pull_isLB tK.PP.isLB α₀) (pull_isLB t.PP.isLB _) hL₀
      (GlobalTheory.Ex.GenericFibre.lbIso_pull hw₁ α₀ rfl)

theorem extend_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ b : o →+* c.F, f ≫ PSpace.str o n = pullback.snd _ _ ≫ spMap b → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)), Nonempty (PELUnif (IsLocalRing.maximalIdeal R) t) → ∀ y : Sp (FractionRing R) ⟶ Xo.XF c, GenOf Xo c y t → ∀ σ : Sp R ⟶ Sp o, jK R ≫ σ = y ≫ pullback.snd _ _ ≫ spMap b → ∃ ξ : Sp R ⟶ PSpace o n, jK R ≫ ξ = y ≫ f ∧ ξ ≫ PSpace.str o n = σ := by
  intro E _ _ _ H Dw l Xo c o _ m n f hm h3 hmu hn hTh b hb R _ _ _ hR t hP y hy σ hσ
  haveI : IsNoetherianRing R := hR.1.1
  haveI : IsIntegrallyClosed R := hR.1.2.2.1
  haveI : CharZero R := hR.2
  haveI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  set g := Module.finrank ℚ E / 2 * (Dw.p + Dw.q) with hgdef
  obtain ⟨σ₀, hnz⟩ := GlobalTheory.T.exists_polarisation_section_nonvanishing_closed_fibre E H R hR t hP
  obtain ⟨P, α, α', hg, hpb, hL, hpb', hL'⟩ := genericFibre_polAV E H Dw l Xo c R y t hy
  have hpb₁ : IsGrpPullback P.A t.G (spMap (algebraMap R (FractionRing R)) ≫ 𝟙 (Sp R)) α' := by
    rw [Category.comp_id]; exact hpb'
  have hpf : PolFib t.G t.PP.L g (spMap (algebraMap R (FractionRing R)) ≫ 𝟙 (Sp R)) := ⟨P, α', hg, hpb₁, hL'⟩
  let θ := SecAt.pull t.G t.PP.L σ₀ (algebraMap R (FractionRing R))
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_theta_symmetric_function_values_in_ground_field (Sp R) t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen g m (n + 1) (FractionRing R)
    (spMap (algebraMap R (FractionRing R)) ≫ 𝟙 (Sp R)) θ hm hn hpf
  let β : o →+* R := (Spec.preimage σ).hom
  have hβ : spMap β = σ := Spec.map_preimage σ
  have hmR : IsUnit (m : R) := by simpa [β] using hmu.map β
  obtain ⟨e', he', j, hj⟩ := GlobalTheory.T.thetaSymmetricFunctions_integral_unit_normalLocalDomain E H (Sp R) t g m (n + 1) R (𝟙 _) σ₀ e hm h3 hmR hn hpf hnz he
  have hne : ∃ j, e j ≠ 0 := ⟨j, fun h0 => hj.ne_zero (IsFractionRing.injective R (FractionRing R)
    ((he' j).trans (h0.trans (map_zero _).symm)))⟩
  have hgen := GlobalTheory.T.generates_sections_of_thetaSymmetricFunctions_ne_zero (Sp R) t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen g m (n + 1) (FractionRing R) _ θ e hm hn hpf he hne
  have hcrd : PCrd (y ≫ f) e := GlobalTheory.T.thetaMap_coords_of_symmetric_theta_isomorphic_fibre Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig Xo.univ.t.PP.isLB
    Xo.univ.t.PP.rigGen g m n o (Xo.XF c) (pullback.fst _ _) f (Sp R) t.G t.PP.L t.PP.rig (FractionRing R) y
    (spMap (algebraMap R (FractionRing R)) ≫ 𝟙 (Sp R)) P α α' θ e hm hn hTh t.PP.isLB t.PP.rigGen hg hpb hL hpb₁ hL'
    hgen he
  obtain ⟨ξ, hξ1, hξ2⟩ := GlobalTheory.T.exists_projectiveSpace_point_of_unit_coordinate o R n β e' ⟨j, hj⟩
  refine ⟨ξ, ?_, hξ1.trans hβ⟩
  have hc1 : PCrd (jK R ≫ ξ) e := by
    have := (GlobalTheory.T.projectiveHomogeneousCoords_basic_properties).1 o R (FractionRing R) n ξ e' (algebraMap R (FractionRing R)) hξ2
    have ee : (fun j => algebraMap R (FractionRing R) (e' j)) = e := funext he'
    rw [ee] at this; exact this
  refine (GlobalTheory.T.projectiveHomogeneousCoords_field_determine_descend).1 o (FractionRing R) n (jK R ≫ ξ) (y ≫ f) e ?_ hc1 hcrd
  rw [Category.assoc, hξ1, hβ, Category.assoc, hb]; exact hσ

end GlobalTheory.UMin.ExtP
end
end
end
