module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisationOfTraitUnifStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledCoverEmbeddingClosedFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalBundleModificationDescendsToGroupStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCpDescent
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointRangeEqFixedGroupImageStatement
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothModelNearClosedFibreEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulDescendsNearClosedFibreOfEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfDescendsNearClosedFibre
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTransStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.hasSemiAbelianUniformisation_of_finiteExt_trans : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')), Nonempty (IsPullDeg ρ D.toPre D'.toPre) → HasFin D' → HasFin D := by
  first | exact @GlobalTheory.Mum.hasFin_of_finExt | exact GlobalTheory.Mum.hasFin_of_finExt | (intros; apply GlobalTheory.Mum.hasFin_of_finExt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCpDescentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_cp_descent' : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G M.π β → ∀ L : LB G.left, L.IsLB → LBIso P'.L.L (L.pull β) → ∃ P : GlobalTheory.UU.CP G, P.L.L = L := by
  first | exact @GlobalTheory.Mum.exists_cp_descent | exact GlobalTheory.Mum.exists_cp_descent | (intros; apply GlobalTheory.Mum.exists_cp_descent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenThetaNonvanishingDescendedGroup

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_open_theta_descent : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), Surjective π → ∀ (G' : Over S) [GrpObj G'] (E : Emb π G') (N : Near π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → ∀ (L : LB G'.left), E.Theta L → ∀ (G : Over (Sp R)) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), β ≫ G.hom = G'.hom ≫ π → IsOpenImmersion i.left → N.u ≫ β = pullback.fst _ _ ≫ i.left → ∃ (θ : L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) ∧ ∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ k, g ∈ G'.left.basicOpen (θ.f k) := by
  intro R _ _ S π hπ G' _ E N fU l hl hlf L hT G β i hβ hi hu
  obtain ⟨θ, OY, ⟨y₀, hy₀⟩, hθ⟩ := hT
  haveI := E.imm
  obtain ⟨W, hW, hWY⟩ := (E.j.isEmbedding.isInducing.isOpen_iff).1 OY.isOpen
  have hrng := GlobalTheory.T.closedPoint_range_eq_fixedGroup_image R S π G' E
  have e1 : ∀ z, E.H.ι (l z) = N.u z := fun z => by rw [← Scheme.Hom.comp_apply, hl]
  have e2 : ∀ z, E.f (l z) = fU (pullback.fst N.U.hom π z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hlf, Scheme.Hom.comp_apply]
  have e3 : ∀ z, β (N.u z) = i.left (pullback.fst N.U.hom π z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hu, Scheme.Hom.comp_apply]
  have e4 : ∀ x, G.hom (β x) = π (G'.hom x) := fun x => by
    rw [← Scheme.Hom.comp_apply, hβ, Scheme.Hom.comp_apply]
  have hWj : ∀ y, y ∈ OY ↔ E.j y ∈ W := fun y => by
    show y ∈ (OY : Set E.Y.left) ↔ _
    rw [← hWY]; rfl
  refine ⟨θ, ⟨i.left '' (fU ⁻¹' W), i.left.isOpenEmbedding.isOpenMap _ (hW.preimage fU.continuous)⟩, ?_, ?_⟩
  · obtain ⟨g₀, hg₀c, hg₀f⟩ := hrng.2 hπ y₀
    obtain ⟨z, hz⟩ := N.all (E.H.ι g₀) hg₀c
    have hlz : l z = g₀ := E.H.ι.isOpenEmbedding.injective (by rw [e1, hz])
    refine ⟨i.left (pullback.fst N.U.hom π z), ⟨pullback.fst N.U.hom π z, ?_, rfl⟩, ?_⟩
    · show fU (pullback.fst N.U.hom π z) ∈ W
      rw [← e2 z, hlz, hg₀f]
      exact (hWj y₀).1 hy₀
    · rw [← e3, e4, hz]
      exact hg₀c
  · rintro g ⟨w, hw, hwg⟩ hc
    have hc' : π (G'.hom g) = closedPoint R := by rw [← e4]; exact hc
    obtain ⟨z, rfl⟩ := N.all g hc'
    have hzw : pullback.fst N.U.hom π z = w := i.left.isOpenEmbedding.injective (by rw [hwg, ← e3])
    have hc'' : π (G'.hom (E.H.ι (l z))) = closedPoint R := by rw [e1]; exact hc'
    obtain ⟨y, hy⟩ := hrng.1 (l z) hc''
    have hyO : y ∈ OY := (hWj y).2 (by rw [← hy, e2, hzw]; exact hw)
    obtain ⟨k, hk⟩ := hθ (l z) y hyO hc'' hy
    exact ⟨k, by rwa [e1] at hk⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenThetaNonvanishingDescendedGroupStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_open_thetaNonvanishing_descendedGroup : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), Surjective π → ∀ (G' : Over S) [GrpObj G'] (E : Emb π G') (N : Near π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → ∀ (L : LB G'.left), E.Theta L → ∀ (G : Over (Sp R)) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), β ≫ G.hom = G'.hom ≫ π → IsOpenImmersion i.left → N.u ≫ β = pullback.fst _ _ ≫ i.left → ∃ (θ : L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) ∧ ∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ k, g ∈ G'.left.basicOpen (θ.f k) := by
  first | exact @GlobalTheory.Mum.exists_open_theta_descent | exact GlobalTheory.Mum.exists_open_theta_descent | (intros; apply GlobalTheory.Mum.exists_open_theta_descent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfDescendsNearClosedFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.semiAbelian_descends_of_descends_near_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), IsSemiAbelian G ∧ IsGrpPullback G' G π β ∧ IsOpenImmersion i.left ∧ N.u ≫ β = pullback.fst _ _ ≫ i.left := by
  first | exact @GlobalTheory.Mum.descend_of_near | exact GlobalTheory.Mum.descend_of_near | (intros; apply GlobalTheory.Mum.descend_of_near <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfClosedFibreEmbedding

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem descend_of_emb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (E : Emb M.π G'), E.Theta P'.L.L → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (P : GlobalTheory.UU.CP G) (β : G'.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback G' G M.π β ∧ LBIso P'.L.L (P.L.L.pull β) := by
  intro R _ _ _ hR M G' _ _ hG' P' E hθ
  have : IsNoetherianRing R := hR.1
  have : IsIntegrallyClosed R := hR.2.2.1
  have hs : Surjective M.π := (Modif.appTop_bijective_surjective R M).2
  obtain ⟨N, fU, l, hl, hf⟩ := GlobalTheory.T.exists_smooth_model_near_closedFibre_embedding R hR M G' hG' E
  have hN : N.Law := GlobalTheory.T.mul_descends_near_closed_fibre_of_embedding R hR M G' hG' E N fU l hl hf
  obtain ⟨G, i1, i2, β, i, hG, hβ, hi, hu⟩ := GlobalTheory.T.semiAbelian_descends_of_descends_near_closedFibre R hR M.S M.π M.proper hs M.integral G' hG' N hN
  obtain ⟨θ, O, hO, hθO⟩ := GlobalTheory.T.exists_open_thetaNonvanishing_descendedGroup R M.S M.π hs G' E N fU l hl hf P'.L.L hθ G β i hβ.1.w hi hu
  obtain ⟨L, hL, hLi⟩ := GlobalTheory.T.cubicalBundle_modification_descends_to_group R hR M G' hG' P' G β hG hβ θ O hO hθO
  obtain ⟨P, rfl⟩ := GlobalTheory.T.exists_cp_descent' R hR M G' hG' P' G β hG hβ L hL hLi
  exact ⟨G, i1, i2, P, β, hG, hβ, hLi⟩

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfClosedFibreEmbeddingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.semiAbelian_descends_of_closedFibre_embedding : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (E : Emb M.π G'), E.Theta P'.L.L → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (P : GlobalTheory.UU.CP G) (β : G'.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback G' G M.π β ∧ LBIso P'.L.L (P.L.L.pull β) := by
  first | exact @GlobalTheory.Mum.descend_of_emb | exact GlobalTheory.Mum.descend_of_emb | (intros; apply GlobalTheory.Mum.descend_of_emb <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfLabelledCover

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.CoverFin

theorem semiAbelian_of_pull {S T : Scheme.{0}} {G : Over S} [GrpObj G] {f : T ⟶ S} {G' : Over T} [GrpObj G']
    [IsCommMonObj G'] {π : G'.left ⟶ G.left} (h : IsGrpPullback G' G f π) (hG : IsSemiAbelian G) : IsSemiAbelian G' := by
  obtain ⟨bc, hbc, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  haveI := hbc
  exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback f G hG)

theorem isLocalHom_of_comap {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] (φ : A →+* B)
    (h : (maximalIdeal B).comap φ = maximalIdeal A) : IsLocalHom φ := by
  refine ⟨fun a ha => ?_⟩
  by_contra hn
  have : a ∈ (maximalIdeal B).comap φ := by rw [h]; exact (mem_maximalIdeal a).2 hn
  exact (mem_maximalIdeal _).1 this ha

end GlobalTheory.Mum.CoverFin

open GlobalTheory.Mum.CoverFin

theorem GlobalTheory.Mum.hasFin_of_labCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)), Nonempty (LabCover D) → HasFin D := by
  intro R _ _ _ hB D ⟨C⟩
  obtain ⟨R', _, _, _, ρ, D', C', E, hρ, hD', hθ⟩ := GlobalTheory.T.exists_labelledCover_embedding_closedFibre R hB D C
  obtain ⟨G, _, _, P, β, hG, hβ, hL⟩ := GlobalTheory.T.semiAbelian_descends_of_closedFibre_embedding R' hρ.1 C'.toModif C'.G C'.semi C'.P E hθ
  haveI : IsNoetherianRing R' := hρ.1.1
  haveI : CharZero R := hB.2
  haveI : CharZero R' := charZero_of_injective_ringHom hρ.2.1
  obtain ⟨V, _, _, _, φ, hV, hφ, hm⟩ := GlobalTheory.PrimeUnif.exists_cdvr R' (maximalIdeal R')
  have hloc : IsLocalHom φ := isLocalHom_of_comap φ hm
  haveI : IsDiscreteValuationRing V := hV.1
  let fφ : FractionRing R' →+* FractionRing V :=
    IsLocalization.map (FractionRing V) φ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφ)
  have hfφ : ∀ r, fφ (algebraMap R' _ r) = algebraMap V _ (φ r) := fun r => IsLocalization.map_eq _ _
  haveI : IsProper C'.π := C'.proper
  obtain ⟨ξ, -, hξ⟩ := val_exists C'.π (spMap fφ ≫ C'.gp) (spMap φ) (by
    rw [Category.assoc, C'.gp_π]
    show spMap fφ ≫ spMap (algebraMap R' (FractionRing R')) = spMap (algebraMap V (FractionRing V)) ≫ spMap φ
    rw [← spMap_comp, ← spMap_comp]
    congr 1
    exact RingHom.ext fun r => hfφ r)
  obtain ⟨W', _, _, _, io, G'', _, _, β', D'', A'', U'', hD'', hW', hio, hfin, hβ', hL', -⟩ :=
    C'.trait V hV φ ξ hφ hloc hξ
  haveI : IsLocalHom io := hfin.to_isIntegral.isLocalHom hio
  have hcomp : IsGrpPullback G'' G (spMap (io.comp φ)) (β' ≫ β) :=
    (hβ'.comp hβ).congr (by rw [Category.assoc, hξ, spMap_comp]) rfl
  have h₂ : LBIso (C'.P.L.L.pull β') (P.L.L.pull (β' ≫ β)) :=
    LBIso.chartPull (chartPullPull C'.P.L.L β') (chartPullSame P.L.L _ _ _ β' fun _ => rfl) hL
  have hLc : LBIso U''.LG.L (P.L.L.pull (β' ≫ β)) :=
    LBIso.trans U''.LG.isLB (pull_isLB C'.P.L.isLB β') (pull_isLB P.L.isLB _) hL' h₂
  obtain ⟨R₁, _, _, _, ρ₁, D₁, G₁, _, _, β₁, A₁, U₁, hρ₁, hD₁, hβ₁, -⟩ :=
    GlobalTheory.T.exists_finiteExtension_uniformisation_of_trait_unif R' ⟨hρ.1, inferInstance⟩ D' G P hG W' hW' (io.comp φ) (hio.comp hφ) inferInstance G'' (β' ≫ β) D'' A'' U''
      hcomp hLc ⟨hD''⟩
  exact GlobalTheory.T.hasSemiAbelianUniformisation_of_finiteExt_trans R R' ρ hρ D D' hD'
    ⟨R₁, _, _, _, ρ₁, D₁, hρ₁, hD₁, G₁, _, _, A₁, semiAbelian_of_pull hβ₁ hG, ⟨U₁⟩⟩
end
end
end
