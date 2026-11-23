module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackAlongStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformationHarrisTaylor
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
import Mathlib.RingTheory.WittVector.IsPoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFormallySmoothSquareZeroLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackCompStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfArtinianSquareZeroLiftingNoetherianBaseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfUniversalFirstOrderTaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformationHarrisTaylorStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.exists_universal_firstOrder_deformation_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ o : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ t), Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom)) ∧ ∀ o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t), Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, Nonempty (GlobalTheory.UPel.HT.ObjMap o' o (spMap (TrivSqZeroExt.map c).toRingHom)) := by
  first | (exact @GlobalTheory.HTUniv.main) | (exact GlobalTheory.HTUniv.main) | (intros; apply GlobalTheory.HTUniv.main  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTangentHarrisTaylorRepresentingFa

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.RepTangent

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := by
  simp only [spMap]; exact Spec.map_id _

theorem exists_univ_tangent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ F : RepFam b N, IsQProjOver F.s → Smooth F.s → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ F.X), ∃ u : Sp (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k)) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫ u = x ∧ u ≫ F.s = spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ x ≫ F.s ∧ ∀ v : Sp (DualNumber k) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ F.s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ F.s → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u := by
  intro p _ D R _ _ b N hN hNp F _ _ k _ _ x
  obtain ⟨o₀, ⟨m₀⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback_along p D R b N F.X (Sp k) F.s x F.univ
  obtain ⟨o, ⟨mo⟩, huniv⟩ := GlobalTheory.T.exists_universal_firstOrder_deformation_harrisTaylor p D R b N hN hNp k (x ≫ F.s) o₀
  obtain ⟨u, ⟨hu1, ⟨mu⟩⟩, -⟩ := F.rep _ _ o
  have hfst : spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫
      spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) = 𝟙 _ := by
    rw [spMap_comp_spMap]
    convert spMap_id' k
    ext a; simp
  refine ⟨u, ?_, hu1, ?_⟩
  · obtain ⟨f, -, hf⟩ := F.rep _ _ o₀
    have e1 := hf x ⟨rfl, ⟨m₀⟩⟩
    have e2 := hf (spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫ u)
      ⟨by rw [Category.assoc, hu1, ← Category.assoc, hfst, Category.id_comp], ⟨MapComp.comp mo mu⟩⟩
    exact e2.trans e1.symm
  · intro v hv1 hv2
    obtain ⟨o', ⟨m'⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback_along p D R b N F.X (Sp (DualNumber k)) F.s v F.univ
    have main : ∀ (s₁ : Sp (DualNumber k) ⟶ Sp R) (o' : Obj b N s₁), s₁ = v ≫ F.s → ObjMap o' F.univ v →
        ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u := by
      intro s₁ o' hs m'
      rw [hv2] at hs
      subst hs
      have h0 : Nonempty (ObjMap o₀ F.univ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v)) := by
        rw [hv1]; exact ⟨m₀⟩
      have m'' := (GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ o₀ o' F.univ _ v).2 h0 ⟨m'⟩
      obtain ⟨c, ⟨mc⟩, hc⟩ := huniv o' m''
      have hbase : ∀ c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k,
          (spMap (TrivSqZeroExt.map c).toRingHom ≫ u) ≫ F.s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ F.s := by
        intro c
        rw [Category.assoc, hu1, ← Category.assoc, spMap_comp_spMap]
        congr 2
        exact (TrivSqZeroExt.map c).comp_algebraMap
      refine ⟨c, ?_, ?_⟩
      · obtain ⟨f, -, hf⟩ := F.rep _ _ o'
        exact (hf v ⟨hv2, ⟨m'⟩⟩).trans (hf _ ⟨hbase c, ⟨MapComp.comp mc mu⟩⟩).symm
      · intro c' hc'
        apply hc
        rw [hc'] at m'
        exact (GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ o' o F.univ _ u).2 ⟨m'⟩ ⟨mu⟩
    exact main _ o' rfl m'

end GlobalTheory.UPel.HT.RepTangent
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTangentHarrisTaylorRepresentingFaStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_universal_tangent_harrisTaylor_representingFamily : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ F : RepFam b N, IsQProjOver F.s → Smooth F.s → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ F.X), ∃ u : Sp (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k)) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫ u = x ∧ u ≫ F.s = spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ x ≫ F.s ∧ ∀ v : Sp (DualNumber k) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ F.s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ F.s → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u := by
  first | (exact @GlobalTheory.UPel.HT.RepTangent.exists_univ_tangent) | (exact GlobalTheory.UPel.HT.RepTangent.exists_univ_tangent) | (intros; apply GlobalTheory.UPel.HT.RepTangent.exists_univ_tangent  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFormallySmoothSquareZeroLiftStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.harrisTaylor_formally_smooth_squareZero_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (A₁ A₀ : Type) [CommRing A₁] [CommRing A₀] [IsLocalRing A₁] [IsArtinianRing A₁] (π : A₁ →+* A₀) (β : R →+* A₁), Function.Surjective π → RingHom.ker π * RingHom.ker π = ⊥ → ∀ o : Obj b N (spMap (π.comp β)), ∃ o' : Obj b N (spMap β), Nonempty (ObjMap o o' (spMap π)) := by
  first | (exact @GlobalTheory.UPel.HT.obj_lift_sqZero) | (exact GlobalTheory.UPel.HT.obj_lift_sqZero) | (intros; apply GlobalTheory.UPel.HT.obj_lift_sqZero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem RepFam.smoothOfRelativeDimension : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ F : RepFam b N, IsQProjOver F.s → SmoothOfRelativeDimension (D.a * (D.n - 1)) F.s := by
  intro p _ D R _ _ b N hN hNp F hq
  have hlft : LocallyOfFiniteType F.s := by
    obtain ⟨M, i, hi, hqc, hi'⟩ := hq
    have := isProper_str R M
    rw [← hi']
    infer_instance
  have hsm : Smooth F.s := by
    refine GlobalTheory.T.smooth_of_artinian_squareZero_lifting_noetherian_base R F.X F.s hlft ?_
    intro C C₀ _ _ _ _ π hπ hker t x₀ hx
    obtain ⟨β, rfl⟩ : ∃ β : R →+* C, t = spMap β :=
      ⟨(Spec.preimage t).hom, by simp [spMap]⟩
    have hcomp : spMap π ≫ spMap β = spMap (π.comp β) := by
      simp [spMap, ← Spec.map_comp]
    have hs₀ : x₀ ≫ F.s = spMap (π.comp β) := by rw [hx, hcomp]
    obtain ⟨o₀, ⟨m₀⟩⟩ := GlobalTheory.T.exists_harrisTaylorObjectPullback p D R b N _ _ F.s _ F.univ x₀ hs₀
    obtain ⟨o', ⟨m'⟩⟩ := GlobalTheory.T.harrisTaylor_formally_smooth_squareZero_lift p D R b N hN hNp C C₀ π β hπ (by rw [← hker, pow_two]) o₀
    obtain ⟨x, ⟨hxs, ⟨mx⟩⟩, -⟩ := F.rep (Sp C) (spMap β) o'
    obtain ⟨mc⟩ := GlobalTheory.T.harrisTaylorObjectPullback_comp p D R b N _ _ _ _ _ _ o₀ o' F.univ (spMap π) x m' mx
    refine ⟨x, ?_, hxs⟩
    exact (F.rep (Sp C₀) (spMap (π.comp β)) o₀).unique
      ⟨by rw [Category.assoc, hxs, hcomp], ⟨mc⟩⟩ ⟨hs₀, ⟨m₀⟩⟩
  exact GlobalTheory.T.smoothOfRelativeDimension_of_universal_firstOrder_tangent R F.X F.s _ hsm (GlobalTheory.T.exists_universal_tangent_harrisTaylor_representingFamily p D R b N hN hNp F hq hsm)

end GlobalTheory.UPel.HT
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_repFam_of_isQProjOver : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ F : RepFam b N, IsQProjOver F.s → SmoothOfRelativeDimension (D.a * (D.n - 1)) F.s := by
  first | (exact @GlobalTheory.UPel.HT.RepFam.smoothOfRelativeDimension) | (exact GlobalTheory.UPel.HT.RepFam.smoothOfRelativeDimension) | (intros; apply GlobalTheory.UPel.HT.RepFam.smoothOfRelativeDimension  <;> assumption)
end
end
