module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderScalarExtensionStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderBaseChangeGenericStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderComapHomStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingIsoFiniteStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenImmersionStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqTopOfEtaleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrderNoetherianStatement
public import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsCharacters
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrderNoetherianStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderValueEval
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueBtOrderEmbeddingStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueTangentDualNumber
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RelOfTorsion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueBtOrderEmbeddingStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MiTors
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualToInvariantDifferentials

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.BT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem valAt_sub_one {B : Type} [CommRing B] {X : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ X) (a : Γ(X, ⊤)) :
    valAt y ⊤ le_top (a - 1) = valAt y ⊤ le_top a - 1 := by
  simp [valAt]

theorem omega_isDerAtOne : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L), ∃ θ : Module.Dual R L →ₗ[R] omega (Γ.btOrder ⊤), (Function.Surjective θ ∧ ∀ (f : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L), θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent f ↔ Γ.IsDerAtOne i M N (f.1.1 : T → R) w) ∧ (∀ w, θ w = 0 ↔ ∃ u, w = N • u) ∧ ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M N χ w → θ w = dlogChar (Γ.btOrder ⊤) χ := by
  intro R _ _ _ _ T _ _ Γ S G _ _ x N i ht hsm L _ _ M
  obtain ⟨θ, hsurj, hker, hpin⟩ := Tan.omega_canon R T Γ S G x N i ht hsm L M
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.existsUnique_btOrder_embedding R T Γ
  have hex := fun e : L => (TanLift.tangent_mod_torsion R T Γ S G x N i ht L M e).exists
  have hsec : ∀ f : Γ.btOrder ⊤, ∃ s, Γ.HasValues s (f : T → R) := fun f =>
    ⟨j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ.btOrder ⊤))).inv.hom f), fun t =>
      ValEmb.valAt_pull j (Γ.pt t).left _ (hj.pt t) f⟩
  have pin : ∀ (f : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L),
      θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent f ↔ Γ.IsDerAtOne i M N (f.1.1 : T → R) w := by
    intro f w
    have h0 : (f.1.1 : T → R) 1 = 0 := f.2
    constructor
    · intro h
      obtain ⟨s, hs⟩ := hsec f.1
      refine ⟨s, hs, fun e => ?_⟩
      obtain ⟨v, a, b⟩ := hex e
      refine ⟨v, a, b, ?_⟩
      rw [(hpin f w s hs).1 h e v a b, h0]
      simp
    · rintro ⟨s, hs, hv⟩
      refine (hpin f w s hs).2 fun e v a b => ?_
      obtain ⟨v', a', b', c'⟩ := hv e
      obtain rfl := (TanLift.tangent_mod_torsion R T Γ S G x N i ht L M e).unique ⟨a, b⟩ ⟨a', b'⟩
      rw [c', h0]
      simp
  refine ⟨θ, ⟨hsurj, pin⟩, hker, ?_⟩
  rintro χ w ⟨s, hs, hv⟩
  have hχ : (fun t => ((χ t : Rˣ) : R)) ∈ Γ.btOrder ⊤ :=
    char_mem_hopfOrder R T _ (GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ) χ
  rw [OrderApi.dlogChar_of_mem _ χ hχ]
  refine (pin _ w).2 ⟨s - 1, fun t => ?_, fun e => ?_⟩
  · rw [valAt_sub_one, hs t]
    simp
  · obtain ⟨v, a, b, c⟩ := hv e
    refine ⟨v, a, b, ?_⟩
    rw [valAt_sub_one, c]
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp

end GlobalTheory.CompanionTheory.Ar.BT
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualToInvariantDifferentialsStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.exists_dual_to_invariant_differentials : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L), ∃ θ : Module.Dual R L →ₗ[R] omega (Γ.btOrder ⊤), (Function.Surjective θ ∧ ∀ (f : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L), θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent f ↔ Γ.IsDerAtOne i M N (f.1.1 : T → R) w) ∧ (∀ w, θ w = 0 ↔ ∃ u, w = N • u) ∧ ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M N χ w → θ w = dlogChar (Γ.btOrder ⊤) χ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.omega_isDerAtOne | exact GlobalTheory.CompanionTheory.Ar.BT.omega_isDerAtOne | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.omega_isDerAtOne <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEndomorphismLift

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.BT.TorsEnd

theorem endomorphism_restricts_to_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (a : G ⟶ G) [IsMonHom a], ∃ a' : Γ.G ⟶ Γ.G, IsMonHom a' ∧ a'.left ≫ i = i ≫ a.left :=
  @PositivityTheory.HtPt.Mi.torsion_end

end GlobalTheory.CompanionTheory.Ar.BT.TorsEnd
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEndomorphismLiftStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

theorem _root_.GlobalTheory.T.torsion_group_endomorphism_lift : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (a : G ⟶ G) [IsMonHom a], ∃ a' : Γ.G ⟶ Γ.G, IsMonHom a' ∧ a'.left ≫ i = i ≫ a.left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.TorsEnd.endomorphism_restricts_to_torsion | exact GlobalTheory.CompanionTheory.Ar.BT.TorsEnd.endomorphism_restricts_to_torsion | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.TorsEnd.endomorphism_restricts_to_torsion <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEtaleOfUnit

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem torsion_etale_of_isUnit : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → IsUnit (N : R) → Etale Γ.G.hom := by
  exact @PositivityTheory.HtPt.Mi.torsion_etale

end GlobalTheory.CompanionTheory.Ar.BT
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEtaleOfUnitStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

theorem _root_.GlobalTheory.T.torsion_group_etale_of_unit : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → IsUnit (N : R) → Etale Γ.G.hom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.torsion_etale_of_isUnit | exact GlobalTheory.CompanionTheory.Ar.BT.torsion_etale_of_isUnit | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.torsion_etale_of_isUnit <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupFiniteOfProper

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.BT.Tors

theorem nTorsion_finite_of_isProper : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → IsProper (pullback.snd G.hom x) → IsFinite Γ.G.hom :=
  @PositivityTheory.HtPt.Mi.torsion_finite

end GlobalTheory.CompanionTheory.Ar.BT.Tors
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupFiniteOfProperStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

theorem _root_.GlobalTheory.T.torsion_group_finite_of_proper : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → IsProper (pullback.snd G.hom x) → IsFinite Γ.G.hom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.Tors.nTorsion_finite_of_isProper | exact GlobalTheory.CompanionTheory.Ar.BT.Tors.nTorsion_finite_of_isProper | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.Tors.nTorsion_finite_of_isProper <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LemmaBTHolds

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

theorem lemmaBT_holds : LemmaBT := by
  unfold GlobalTheory.CompanionTheory.Ar.BT.LemmaBT
  intro R _ _ _ _ T _ _ Γ S G _ _ x N i hi hG
  refine ⟨GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ, ?_,
    fun hN => GlobalTheory.T.btOrder_eq_top_of_etale R T Γ
      (GlobalTheory.T.torsion_group_etale_of_unit R T Γ S G x N i hi hG hN), ?_, ?_,
    fun L _ _ M => GlobalTheory.T.exists_dual_to_invariant_differentials R T Γ S G x N i hi hG L M⟩
  · obtain ⟨j, hj, -⟩ := GlobalTheory.T.existsUnique_btOrder_embedding R T Γ
    obtain ⟨hoi, htr⟩ := GlobalTheory.T.btOrder_embedding_open_immersion R T Γ j hj
    refine ⟨j, hj, hoi, htr, fun hP => ?_⟩
    exact GlobalTheory.T.btOrder_embedding_iso_finite R T Γ j hj
      (GlobalTheory.T.torsion_group_finite_of_proper R T Γ S G x N i hi hP)
  · intro a _ α hα f hf
    obtain ⟨a', _, ha'⟩ := GlobalTheory.T.torsion_group_endomorphism_lift R T Γ S G x N i hi a
    refine GlobalTheory.T.btOrder_comap_hom R T Γ T Γ a' α (fun t => ?_) f hf
    obtain ⟨_, _, hcancel, _⟩ := hi
    apply hcancel
    rw [Over.comp_left, Category.assoc, ha', hα t]
  · intro R' _ _ _ Γ' F hF
    obtain ⟨hd, hΓ'⟩ :=
      GlobalTheory.T.btOrder_base_change_generic R T Γ R' Γ' F hF
    obtain ⟨-, e, he⟩ := GlobalTheory.T.hopf_order_scalar_extension R T R' _
      (GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ) hd
    rw [hΓ']
    exact ⟨e, he⟩

end GlobalTheory.CompanionTheory.Ar.BT
end
end
end
