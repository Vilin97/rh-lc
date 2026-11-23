module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsE8WeightedBundle
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ActionProductEqOne
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ActionRelativelyAmpleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8FibrationAlgebraicallyClosedField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizedSpecializationFieldStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ActionProductEqOneStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.e8_act_prod_eq_one : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ) (K : Type) [Field K] (P' : PolAV (Sp K))
  (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  letI := P'.isAb.comm
  act 0 * act 1 = 𝟙 P'.A ∧
  LBIso (cubeLB P'.A ![fst P'.A P'.A ≫ act 0, snd P'.A P'.A] P'.L) (cubeLB P'.A ![fst P'.A P'.A, snd P'.A P'.A ≫ act 1] P'.L) ∧
  LBIso P'.L (cubeLB P'.A ![𝟙 P'.A, act 0] P'.L) := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.PrimPic.e8_act_endomorphism_prod_eq_id | exact GlobalTheory.Poinc.Sep.E8Fibration.PrimPic.e8_act_endomorphism_prod_eq_id | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.PrimPic.e8_act_endomorphism_prod_eq_id <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8FibrationAlgebraicallyClosedFieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.e8_fibration_algebraically_closed_field : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ),
  ∃ Mat : Fin 2 → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ,
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ → (l : K) ≠ 0 →
  ∀ (P' : PolAV (Sp K)), P'.g = 8 * gQ →
  ∀ (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (pt : Fin (2 * (8 * gQ)) → (Out.baseOver (Sp K) ⟶ P'.A)),
    (∀ i, pt i ^ ((l ^ j) ^ 2) = 1) ∧
    (∀ (K' : Type) [Field K'] [IsAlgClosed K'] (x : Sp K' ⟶ Sp K) (y : Over.mk x ⟶ P'.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∃! c : Ix (8 * gQ) ((l ^ j) ^ 2), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp K)) ≫ pt i)
        (fun i => (c i).val) = y) ∧
    (∀ i i', Out.WeilIs P'.A P'.L (((l ^ j) ^ 2 : ℕ) : ℤ) (pt i) (pt i')
      (unitS (spMap k₀.subtype) bT.ζ ^ Out.stdSymp (8 * gQ) i i')) ∧
    ∀ (a : Fin 2) i, pt i ≫ act a = Out.linComb pt (fun i' => ((Mat a i' i : ZMod ((l ^ j) ^ 2))).val) := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.Lab.exists_symplectic_labels | exact GlobalTheory.Poinc.Sep.E8Fibration.Lab.exists_symplectic_labels | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.Lab.exists_symplectic_labels <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerEndomorphismActingByMatrix

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Poinc.Sep.E8Fibration.exists_monHom_actsBy : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)),
  E8Fibration.IsProd pr → ∀ m : Matrix (Fin 8) (Fin 8) ℤ, ∃ f : A ⟶ A, IsMonHom f ∧ E8Fibration.ActsBy pr f m := by
  intro S A B _ _ _ pr hP m
  letI cG : ∀ Z : Over S, CommGroup (Z ⟶ B) := fun Z => Hom.commGroup
  have mc : ∀ {T : Over S} (u v : T ⟶ A) (e : A ⟶ B), IsMonHom e → (u * v) ≫ e = (u ≫ e) * (v ≫ e) := by
    intro T u v e he
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]
  have pc : ∀ {T : Over S} (x : T ⟶ A) (a : Fin 8),
      x ≫ (∏ b, pr b ^ m a b : A ⟶ B) = ∏ b, (x ≫ pr b) ^ m a b := by
    intro T x a
    let φ : (A ⟶ B) →* (T ⟶ B) :=
      { toFun := fun u => x ≫ u, map_one' := MonObj.comp_one x, map_mul' := fun u v => MonObj.comp_mul x u v }
    have := map_prod φ (fun b => pr b ^ m a b) Finset.univ
    simp only [map_zpow] at this
    exact this
  obtain ⟨f, hf, -⟩ := hP.2 A (fun a => ∏ b, pr b ^ m a b)
  refine ⟨f, ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul f fun T x y => ?_, hf⟩
  refine (hP.2 T fun a => ((x * y) ≫ f) ≫ pr a).unique (fun a => rfl) fun a => ?_
  rw [mc _ _ _ (hP.1 a), Category.assoc, Category.assoc, Category.assoc, hf, pc, pc, pc,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [mc _ _ _ (hP.1 b), mul_zpow]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerEndomorphismActingByMatrixStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_eighth_power_endomorphism_acting_by_matrix : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)),
  E8Fibration.IsProd pr → ∀ m : Matrix (Fin 8) (Fin 8) ℤ, ∃ f : A ⟶ A, IsMonHom f ∧ E8Fibration.ActsBy pr f m := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.exists_monHom_actsBy | exact GlobalTheory.Poinc.Sep.E8Fibration.exists_monHom_actsBy | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.exists_monHom_actsBy <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefinementOddPrimeLocalization

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.E8Fibration

theorem eighthPowerFibre_thetaObj : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ), ∃ (J : Type) (_ : Finite J)
    (Mat : J → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ) (κ : ℕ) (w w' : J),
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    t.Shape Mat κ ∧ t.Prim w w' ∧
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) ∧
    ∀ (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ a, q ≫ ψ = (t.lab a).left := by
  intro W hW gQ
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.e8_act_linComb_relAmple W hW
  obtain ⟨Mat, hMat⟩ := GlobalTheory.T.e8_fibration_algebraically_closed_field W hW gQ
  refine ⟨Fin 2, inferInstance, Mat, κ, 0, 1, ?_⟩
  intro l hl hlo j hj V V₁ _ _ _ _ _ hCN hlu Q hQ ρ hρ D e hS K _ _ ev k₀ hk₀
  obtain ⟨P', ψ, B, _, M, pr, hg, hψ, hL, hB, hpr, hE, hpt⟩ := GlobalTheory.T.exists_polarized_specialization_field W gQ V V₁ Q hQ ρ hρ D e hS K ev
  haveI : IsCommMonObj B := hB.1.comm
  choose act hact1 hact2 using fun i : Fin 2 => GlobalTheory.T.exists_eighth_power_endomorphism_acting_by_matrix _ _ _ pr hpr (E8Fibration.actMat W i)
  have hlK : (l : K) ≠ 0 := by
    have := hlu.map ev
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨bT, pt, htor, hbij, hpair, hsh⟩ := hMat l hl hlo j hj K k₀ hk₀ hlK P' hg B M pr hB hpr hE act hact1 hact2
  let t : TObj (8 * gQ) ((l ^ j) ^ 2) (Fin 2) bT (spMap k₀.subtype) :=
    { A := P'.A, grp := P'.grp, ab := P'.isAb, dim := hg ▸ P'.smoothDim, L := P'.L, isLB := P'.isLB,
      rigid := P'.rigid, sym := P'.sym, ample := P'.ample, ktriv := P'.ktriv, pt := pt, torsion := htor,
      bij := hbij, pairing := hpair, act := act, hom := hact1 }
  refine ⟨bT, t, ψ, ?_, ?_, hψ, hL, ?_⟩
  · exact fun a => ⟨hsh a, hκ gQ K P' B M pr hB hpr hE act hact1 hact2 a⟩
  · exact GlobalTheory.T.e8_act_prod_eq_one W hW gQ K P' B M pr hB hpr hE act hact1 hact2
  · intro y hy q hq1 hq2
    obtain ⟨y', hy'1, hy'2⟩ := hpt _ y hy q hq1 hq2
    obtain ⟨c, hc, -⟩ := hbij K (𝟙 _) y' hy'2
    refine ⟨c, ?_⟩
    rw [← hy'1, ← hc]
    have h0 : (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) = 𝟙 _ := by
      ext; simp
    simp only [h0, Category.id_comp]
    rfl

end GlobalTheory.Poinc.Sep.E8Fibration
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefinementOddPrimeLocalizationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.sharp_refinement_odd_prime_localization : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ), ∃ (J : Type) (_ : Finite J)
    (Mat : J → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ) (κ : ℕ) (w w' : J),
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    t.Shape Mat κ ∧ t.Prim w w' ∧
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) ∧
    ∀ (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ a, q ≫ ψ = (t.lab a).left := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.eighthPowerFibre_thetaObj | exact GlobalTheory.Poinc.Sep.E8Fibration.eighthPowerFibre_thetaObj | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.eighthPowerFibre_thetaObj <;> assumption)
end
end
