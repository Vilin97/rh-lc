module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianReductionAlongIsogenyStrictHenselian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyPotentialSemiAbelianSplitTorusStatement
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionPullbackCartesianGroupSchemesStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimLeOfIsClosedImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Connected
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqOneOfPowEqOneOfCongrOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeSemiAbelianDvrNoSpecialTorusStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackOfGroupSchemeModelBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActExtendsSemiAbelianDvrStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomCharacterEndOfTorusExtensionActionStatement
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionAlgebraOrderNoSmallLattice

section

@[expose] public section

open NumberField

namespace GlobalTheory

theorem divAlg_clear_denominators {B : Type} [Ring B] [Algebra ℚ B] {O : Type} [Ring O]
    (ι : O →+* B) (v : B) (hv : v ∈ Submodule.span ℚ (Set.range ι)) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : O, ι c = (n : ℚ) • v := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨o, rfl⟩ := hx
    exact ⟨1, one_pos, o, by simp⟩
  | zero => exact ⟨1, one_pos, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n₁, hn₁, c₁, hc₁⟩ := hx
    obtain ⟨n₂, hn₂, c₂, hc₂⟩ := hy
    refine ⟨n₁ * n₂, Nat.mul_pos hn₁ hn₂, (n₂ : O) * c₁ + (n₁ : O) * c₂, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_natCast, map_natCast, hc₁, hc₂, ← nsmul_eq_mul,
      ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ n₂, ← Nat.cast_smul_eq_nsmul ℚ n₁, smul_smul,
      smul_smul, smul_add]
    push_cast
    rw [mul_comm (n₂ : ℚ) (n₁ : ℚ)]
  | smul q x _ hx =>
    obtain ⟨n, hn, c, hc⟩ := hx
    refine ⟨q.den * n, Nat.mul_pos q.den_pos hn, (q.num : O) * c, ?_⟩
    rw [map_mul, map_intCast, hc, smul_smul]
    rw [show ((q.num : B)) = algebraMap ℚ B (q.num : ℚ) by simp, ← Algebra.smul_def, smul_smul]
    congr 1
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring

theorem divAlg_smul_injective {B : Type} [Ring B] [Algebra ℚ B] {O : Type} [Ring O]
    (ι : O →+* B) (hunit : ∀ x : B, x ≠ 0 → IsUnit x) (hinj : Function.Injective ι)
    (hspan : Submodule.span ℚ (Set.range ι) = ⊤)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] (ρ : O →+* Module.End ℤ X)
    (x : X) (hx : x ≠ 0) (a : O) (ha : ρ a x = 0) : a = 0 := by
  by_contra h0
  have hιa : ι a ≠ 0 := fun h => h0 (hinj (by simpa using h))
  obtain ⟨u, hu⟩ := hunit _ hιa
  obtain ⟨n, hn, c, hc⟩ := divAlg_clear_denominators ι (↑u⁻¹ : B) (by rw [hspan]; trivial)
  have hca : c * a = (n : O) := by
    apply hinj
    rw [map_mul, hc, map_natCast, ← hu, Algebra.smul_mul_assoc, Units.inv_mul,
      Algebra.smul_def, mul_one]
    simp
  have h1 : ρ (c * a) x = 0 := by rw [map_mul, Module.End.mul_apply, ha, map_zero]
  rw [hca, map_natCast] at h1
  have h2 : (n : ℤ) • x = 0 := by
    rw [natCast_zsmul]
    simpa [Module.End.natCast_apply] using h1
  rcases smul_eq_zero.mp h2 with h | h
  · omega
  · exact hx h

end GlobalTheory

namespace GlobalTheory

theorem divAlg_order_no_small_lattice : ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B]
    (O : Type) [Ring O] (ι : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective ι →
    Submodule.span ℚ (Set.range ι) = ⊤ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (ρ : O →+* Module.End ℤ X), Module.finrank ℤ X < Module.finrank ℚ B →
    Module.finrank ℤ X = 0 := by
  intro B _ _ _ O _ ι hunit hinj hspan X _ _ _ ρ hlt
  by_contra hne
  have hnt : Nontrivial X := Module.nontrivial_of_finrank_pos (R := ℤ) (Nat.pos_of_ne_zero hne)
  obtain ⟨x, hx⟩ := exists_ne (0 : X)

  let φ : O →ₗ[ℤ] X := (AddMonoidHom.mk' (fun a => ρ a x) (by intro a b; simp)).toIntLinearMap
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact divAlg_smul_injective ι hunit hinj hspan ρ x hx a ha
  let ι' : O →ₗ[ℤ] B := ι.toAddMonoidHom.toIntLinearMap
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℚ (Set.range ι)
  rw [hspan] at hbspan
  let e := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan])
  choose f hf using fun i : b => hbsub i.2
  have li1 : LinearIndependent ℤ (fun i : b => (i : B)) := hbli.restrict_scalars' ℤ
  have li2 : LinearIndependent ℤ f := by
    apply LinearIndependent.of_comp ι'
    convert li1 using 1
    funext i
    exact hf i
  have li3 : LinearIndependent ℤ (φ ∘ f) := li2.map' φ (LinearMap.ker_eq_bot.mpr hφ)
  have hc := li3.cardinal_le_rank
  rw [Module.Basis.mk_eq_rank'' e, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at hc
  have := Nat.cast_le.mp hc
  omega

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionAlgebraOrderNoSmallLatticeStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.divisionAlgebra_order_no_small_lattice : ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (O : Type) [Ring O] (ι : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective ι → Submodule.span ℚ (Set.range ι) = ⊤ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (ρ : O →+* Module.End ℤ X), Module.finrank ℤ X < Module.finrank ℚ B → Module.finrank ℤ X = 0 := by
  first | exact @GlobalTheory.divAlg_order_no_small_lattice | exact GlobalTheory.divAlg_order_no_small_lattice | (intros; apply GlobalTheory.divAlg_order_no_small_lattice <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankTorusExtensionCharactersLeRelDim

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem finrank_torusExtension_le : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (E : TorusExtension G) (g : ℕ), SmoothOfRelativeDimension g G.hom → (letI := E.addCommGroup; Module.finrank ℤ E.X) ≤ g := by
  intro k _ G _ E g hG
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  letI := E.grpB
  haveI : IsSeparated E.B.hom := E.isAbelian.proper.toIsSeparated
  have hη : IsClosedImmersion (η : 𝟙_ (Over (Sp k)) ⟶ E.B).left := isClosedImmersion_of_comp_eq_id (Y := Sp k) E.B.hom _ (Over.w _)
  have hpb : IsPullback E.i.left (toUnit (splitTorus (Sp k) E.X)).left E.q.left (η : 𝟙_ (Over (Sp k)) ⟶ E.B).left :=
    E.isKernel.map (Over.forget _)
  have hi : IsClosedImmersion E.i.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip hη
  have pt : Sp k := Classical.choice inferInstance
  have hne : Nonempty (splitTorus (Sp k) E.X).left :=
    ⟨(η : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) E.X).left ((toUnit (Over.mk (𝟙 (Sp k)))).left pt)⟩
  exact relDim_le_of_isClosedImmersion k _ G E.i hi hne g _ hG (ReciprocityTheory.ChartRestriction.G.H1.torus_dim (Sp k) E.X)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankTorusExtensionCharactersLeRelDimStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.finrank_torusExtension_characters_le_relDim : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (E : TorusExtension G) (g : ℕ), SmoothOfRelativeDimension g G.hom → (letI := E.addCommGroup; Module.finrank ℤ E.X) ≤ g := by
  first | exact @GlobalTheory.finrank_torusExtension_le | exact GlobalTheory.finrank_torusExtension_le | (intros; apply GlobalTheory.finrank_torusExtension_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfDivisionAlgebraOrderActi

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.DivPotGood

theorem potGood_of_divisionAlgebra_action : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (jj : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective jj → Submodule.span ℚ (Set.range jj) = ⊤ → g < Module.finrank ℚ B → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro V K _ _ _ _ _ _ _ _ A _ g hA hg O _ act hact h1 hmul hadd B _ _ _ jj hdiv hinj hspan hgB
  obtain ⟨W, L, i1, i2, i3, i4, i5, i6, i7, i8, hcomp, hfin, hloc, hcpl, G, iG, hmod, hsa, ⟨E⟩⟩ :=
    GlobalTheory.T.abelianVariety_potential_semiAbelian_splitTorus V K A hA
  refine ⟨W, L, i1, i2, i3, i4, i5, i6, i7, i8, hcomp, hfin, hloc, hcpl, G, iG, hmod, ?_⟩

  set f : Sp L ⟶ Sp K := spMap (algebraMap K L)
  set A' := (Over.pullback f).obj A
  have hψ : IsGrpPullback A' A f (pullback.fst A.hom f) := isGrpPullback_pullback A f
  obtain ⟨act₁, ⟨h1a, h1b, h1c, h1d⟩, -⟩ := GlobalTheory.T.exists_ring_action_pullback_cartesian_group_schemes (Sp K) (Sp L) f A A' _ hψ O act hact h1 hmul hadd
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.isGrpPullback_of_group_scheme_model_base_change K W L A G hmod A' _ hψ
  obtain ⟨act₂, ⟨h2a, h2b, h2c, h2d⟩, -⟩ := GlobalTheory.T.exists_ring_action_extension_compatible W L G A' φ hsa hφ O act₁ h1a h1b h1c h1d
  have hres : IsGrpPullback (GlobalTheory.SS.spFibre G) G (spMap (IsLocalRing.residue W)) (pullback.fst G.hom _) :=
    isGrpPullback_pullback G _
  obtain ⟨act₃, ⟨h3a, h3b, h3c, h3d⟩, -⟩ :=
    GlobalTheory.T.exists_ring_action_pullback_cartesian_group_schemes _ _ (spMap (IsLocalRing.residue W)) G (GlobalTheory.SS.spFibre G) _ hres O act₂ h2a h2b h2c h2d
  haveI : IsCommMonObj (GlobalTheory.SS.spFibre G) := by
    haveI := hsa.comm
    infer_instance
  obtain ⟨ρ, -⟩ := GlobalTheory.T.ringHom_characterEnd_of_torusExtension_action _ (GlobalTheory.SS.spFibre G) E O act₃ h3a h3b h3c h3d

  obtain ⟨e, -⟩ := hmod
  haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have hA'g : SmoothOfRelativeDimension g A'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback A.hom f) hg
  have hGLg : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap W L))).obj G).hom := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_horiz_isIso (fst := e.hom.left) (snd := ((Over.pullback (spMap (algebraMap W L))).obj G).hom)
        (f := A'.hom) (g := 𝟙 _) ⟨by rw [Category.comp_id]; exact Over.w e.hom⟩) hA'g
  have hsc : GlobalTheory.SS.SmConn G := ⟨hsa.comm, hsa.smooth, hsa.separated, hsa.quasiCompact, hsa.geomConnected⟩
  have hsp : SmoothOfRelativeDimension g (GlobalTheory.SS.spFibre G).hom := GlobalTheory.IsogRed.relDim_spFibre (K := L) G hsc g hGLg
  have hle := GlobalTheory.T.finrank_torusExtension_characters_le_relDim _ (GlobalTheory.SS.spFibre G) E g hsp
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  have h0 : Module.finrank ℤ E.X = 0 := GlobalTheory.T.divisionAlgebra_order_no_small_lattice B O jj hdiv hinj hspan E.X ρ (lt_of_le_of_lt hle hgB)

  have hprop : IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom := by
    haveI : IsProper A.hom := hA.proper
    haveI : IsProper A'.hom := inferInstanceAs (IsProper (pullback.snd A.hom f))
    rw [← Over.w e.hom]
    infer_instance
  exact GlobalTheory.T.isAbelianScheme_semiAbelian_dvr_noSpecialTorus W L G hsa hprop E h0

end GlobalTheory.DivPotGood
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfDivisionAlgebraOrderActiStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.potentialGoodReduction_of_divisionAlgebra_order_action : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (jj : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective jj → Submodule.span ℚ (Set.range jj) = ⊤ → g < Module.finrank ℚ B → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  first | exact @GlobalTheory.DivPotGood.potGood_of_divisionAlgebra_action | exact GlobalTheory.DivPotGood.potGood_of_divisionAlgebra_action | (intros; apply GlobalTheory.DivPotGood.potGood_of_divisionAlgebra_action <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfDivisionAlgebraLeftActio

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
namespace GlobalTheory

theorem potModel_of_divAlg_leftAction : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (jj : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective jj → Submodule.span ℚ (Set.range jj) = ⊤ → g < Module.finrank ℚ B → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro V K _ _ _ _ _ _ _ _ A _ g hA hg O _ act hmon h1 hmul hadd B _ _ _ jj hunit hinj hspan hdim
  haveI : Module.Finite ℚ Bᵐᵒᵖ :=
    Module.Finite.equiv (MulOpposite.opLinearEquiv ℚ (M := B))
  refine GlobalTheory.T.potentialGoodReduction_of_divisionAlgebra_order_action V K A g hA hg Oᵐᵒᵖ (fun a => act a.unop) (fun a => hmon a.unop) h1
    (fun a b => hmul b.unop a.unop) (fun a b => hadd a.unop b.unop) Bᵐᵒᵖ (RingHom.op jj)
    ?_ ?_ ?_ ?_
  · intro x hx
    have hx' : x.unop ≠ 0 := by simpa using hx
    simpa using (hunit x.unop hx').op
  · intro a b h
    exact MulOpposite.unop_injective (hinj (MulOpposite.op_injective h))
  · have : Set.range (RingHom.op jj) = (MulOpposite.opLinearEquiv ℚ (M := B)) '' Set.range jj := by
      ext x; constructor
      · rintro ⟨a, rfl⟩; exact ⟨jj a.unop, ⟨a.unop, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩; exact ⟨MulOpposite.op a, rfl⟩
    rw [this, ← LinearEquiv.coe_coe, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  · rwa [(MulOpposite.opLinearEquiv ℚ (M := B)).symm.finrank_eq]

end GlobalTheory
end
end
