module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusMemOfSepAtBTate
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsAgreeOverAlgClosedSubfield

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTauScaledGeneratorTorusMonomial

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.ScaleTorus

theorem unitOn_mul' {R : Type} [CommRing R] (x y : Rˣ) : unitOn (x * y) = unitOn x * unitOn y := by
  apply Units.ext
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (x : R) (y : R)

theorem isUnitTau_scaleGen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (C : MonoFam Xo c φ R) (N : ℕ) (s : Fin C.m ⊕ Fin N → R)
    (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar C.P.D.toPre.X)) (τ₀ : Gens C.P.D.toPre),
    (∀ i, s (.inl i) = C.s i) → (∀ i, (ε (.inl i) : LinearMap.BilinForm ℤ _) = C.δ i) →
    TauIn C.P.D.toPre τ₀ (fun k => s (finSumFinEquiv.symm k))
      (fun k => (l.M' : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) →
    ∀ (u : Fin N → Rˣ), (∀ k, (u k : R) = s (.inr k)) → ∀ a b,
      GlobalTheory.RigChart.IsUnitTau C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) a b
        (ReciprocityTheory.ChartRestriction.G.DVR.scaleGen
          (unitOn (∏ k, u k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b))) (τ₀ a b)) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ C N s ε τ₀ hs hε hτ u hu a b
  obtain ⟨hgen, k, hk, hval⟩ := hτ a b
  set w : Rˣ := ∏ k, u k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b) with hw
  let w' : (FractionRing R)ˣ := Units.map (algebraMap R (FractionRing R)).toMonoidHom w
  have hw' : (w' : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (s (.inr k)) ^
      ((l.M' : ℤ) • (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) a b := by
    simp only [w', hw, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.coe_map,
      LinearMap.smul_apply, smul_eq_mul, ← hu]
    rfl
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.scaleGen_isGen _ _ hgen, k * w'⁻¹, ?_, fun zz J hJ => ?_⟩
  · rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_inv_eq_iff_eq_mul₀ w'.ne_zero, hk, hw']
    refine (finSumFinEquiv.symm.prod_comp fun k => algebraMap R (FractionRing R) (s k) ^
      ((l.M' : ℤ) • (ε k : LinearMap.BilinForm ℤ C.P.D.toPre.X)) a b).trans ?_
    rw [Fintype.prod_sum_type]
    simp only [hs, hε]
  · have e₁ : val (ReciprocityTheory.ChartRestriction.G.DVR.scaleGen (unitOn w) (τ₀ a b)) (toUnit (TK R)).left zz J =
        gm (toUnit (TK R)).left zz ⊤ (unitOn w) * val (τ₀ a b) (toUnit (TK R)).left zz J :=
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ zz le_top (hJ.mem _ _) _) rfl)
    have e₂ : gm (toUnit (TK R)).left zz ⊤ (unitOn w) = gm (𝟙 (TK R).left) zz ⊤ (unitOn w') := by
      have e : (toUnit (TK R)).left = spMap (algebraMap R (FractionRing R)) := by simp
      rw [e]
      exact SepBModel.gm_spMap _ zz w
    have e₃ : gm (𝟙 (TK R).left) zz ⊤ (unitOn k) =
        gm (𝟙 (TK R).left) zz ⊤ (unitOn (k * w'⁻¹)) * gm (𝟙 (TK R).left) zz ⊤ (unitOn w') := by
      refine Eq.trans ?_ (map_mul _ _ _)
      refine congrArg _ (Eq.trans ?_ (unitOn_mul' _ _))
      rw [inv_mul_cancel_right]
    refine (hval zz J hJ).trans (Eq.trans ?_ (congrArg _ e₁.symm))
    rw [e₂, ← _root_.mul_assoc, ← e₃]

end GlobalTheory.UCanon.ScaleTorus
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTauScaledGeneratorTorusMonomialStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isUnitTau_scaledGenerator_torusMonomial : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (C : MonoFam Xo c φ R) (N : ℕ) (s : Fin C.m ⊕ Fin N → R)
    (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar C.P.D.toPre.X)) (τ₀ : Gens C.P.D.toPre),
    (∀ i, s (.inl i) = C.s i) → (∀ i, (ε (.inl i) : LinearMap.BilinForm ℤ _) = C.δ i) →
    TauIn C.P.D.toPre τ₀ (fun k => s (finSumFinEquiv.symm k))
      (fun k => (l.M' : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) →
    ∀ (u : Fin N → Rˣ), (∀ k, (u k : R) = s (.inr k)) → ∀ a b,
      GlobalTheory.RigChart.IsUnitTau C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) a b
        (ReciprocityTheory.ChartRestriction.G.DVR.scaleGen
          (unitOn (∏ k, u k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b))) (τ₀ a b)) := by
  first | exact @GlobalTheory.UCanon.ScaleTorus.isUnitTau_scaleGen | exact GlobalTheory.UCanon.ScaleTorus.isUnitTau_scaleGen | (intros; apply GlobalTheory.UCanon.ScaleTorus.isUnitTau_scaleGen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubfieldOfBilinFormBasisMonomials

section

@[expose] public section

namespace GlobalTheory

theorem mem_subfield_of_zpow_mem {K : Type} [Field K] (k₀ : Subfield K) [IsAlgClosed k₀]
    (u : Kˣ) (m : ℤ) (hm : m ≠ 0) (h : ((u ^ m : Kˣ) : K) ∈ k₀) : (u : K) ∈ k₀ := by
  have h1 : (u : K) ^ m.natAbs ∈ k₀ := by
    rw [Units.val_zpow_eq_zpow_val] at h
    rcases Int.natAbs_eq m with h2 | h2
    · rw [h2, zpow_natCast] at h; exact h
    · rw [h2, zpow_neg, zpow_natCast] at h
      simpa using k₀.inv_mem h
  have hint : IsIntegral k₀ (u : K) := by
    apply IsIntegral.of_pow (Int.natAbs_pos.mpr hm)
    exact isIntegral_algebraMap (R := k₀) (x := ⟨_, h1⟩)
  obtain ⟨y, hy⟩ := minpoly.mem_range_of_degree_eq_one k₀ (u : K)
    (IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible hint))
  rw [← hy]
  exact y.2

def monomialExponents {I : Type} [Fintype I] {K : Type} [Field K] (k₀ : Subfield K)
    (t : I → Kˣ) : Submodule ℤ (I → ℤ) :=
  AddSubgroup.toIntSubmodule
  { carrier := {v | ((∏ k, t k ^ v k : Kˣ) : K) ∈ k₀}
    zero_mem' := by simp [k₀.one_mem]
    add_mem' := by
      intro a b ha hb
      simp only [Set.mem_setOf_eq, Pi.add_apply, zpow_add, Finset.prod_mul_distrib,
        Units.val_mul] at *
      exact k₀.mul_mem ha hb
    neg_mem' := by
      intro a ha
      simp only [Set.mem_setOf_eq, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib,
        Units.val_inv_eq_inv_val] at *
      exact k₀.inv_mem ha }

theorem mem_monomialExponents {I : Type} [Fintype I] {K : Type} [Field K] (k₀ : Subfield K)
    (t : I → Kˣ) (v : I → ℤ) :
    v ∈ monomialExponents k₀ t ↔ ((∏ k, t k ^ v k : Kˣ) : K) ∈ k₀ := Iff.rfl

theorem mem_monomialExponents_of_smul {I : Type} [Fintype I] {K : Type} [Field K]
    (k₀ : Subfield K) [IsAlgClosed k₀] (t : I → Kˣ) (v : I → ℤ) (m : ℤ) (hm : m ≠ 0)
    (h : m • v ∈ monomialExponents k₀ t) : v ∈ monomialExponents k₀ t := by
  rw [mem_monomialExponents] at h ⊢
  apply mem_subfield_of_zpow_mem k₀ _ m hm
  convert h using 2
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_mul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem mem_subfield_of_bilinForm_monomials :
    ∀ (X : Type) [AddCommGroup X] (S : Submodule ℤ (LinearMap.BilinForm ℤ X)) (I : Type) [Fintype I]
    (ε : Module.Basis I ℤ S) (K : Type) [Field K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (n : ℤ), n ≠ 0 →
    ∀ (t : I → Kˣ), (∀ a b : X, ((∏ k, t k ^ (n * (ε k : LinearMap.BilinForm ℤ X) a b) : Kˣ) : K) ∈ k₀) →
    ∀ k, (t k : K) ∈ k₀ := by
  intro X _ S I _ ε K _ k₀ hk n hn t h k
  classical
  set P := monomialExponents k₀ t with hP
  have hv : ∀ a b : X, (fun k => (ε k : LinearMap.BilinForm ℤ X) a b) ∈ P := fun a b =>
    mem_monomialExponents_of_smul k₀ t _ n hn (h a b)
  haveI : NoZeroSMulDivisors ℤ ((I → ℤ) ⧸ P) := by
    refine ⟨fun {c x} hx => ?_⟩
    obtain ⟨v, rfl⟩ := P.mkQ_surjective x
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rw [← map_smul] at hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx ⊢
      exact mem_monomialExponents_of_smul k₀ t v c hc hx
  haveI : Module.Free ℤ ((I → ℤ) ⧸ P) := Module.free_of_finite_type_torsion_free'
  have key : P.mkQ (Pi.single k 1) = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff ℤ]
    intro φ
    have hz : ∑ j, φ (P.mkQ (Pi.single j 1)) • ε j = 0 := by
      apply Subtype.ext
      ext a b
      have h0 : φ (P.mkQ (fun k => (ε k : LinearMap.BilinForm ℤ X) a b)) = 0 := by
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).mpr (hv a b), map_zero]
      have h1 : (fun k => (ε k : LinearMap.BilinForm ℤ X) a b)
          = ∑ j, (ε j : LinearMap.BilinForm ℤ X) a b • (Pi.single j 1 : I → ℤ) := by
        funext i
        simp [Finset.sum_apply, Pi.single_apply]

      rw [h1, map_sum, map_sum] at h0
      simp only [map_smul, smul_eq_mul] at h0
      simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, ZeroMemClass.coe_zero, LinearMap.zero_apply]
      rw [← h0]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact Fintype.linearIndependent_iff.mp ε.linearIndependent _ hz k
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hP, mem_monomialExponents] at key
  convert key using 2
  rw [Finset.prod_eq_single k]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubfieldOfBilinFormBasisMonomialsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.mem_subfield_of_bilinForm_basis_monomials : ∀ (X : Type) [AddCommGroup X] (S : Submodule ℤ (LinearMap.BilinForm ℤ X)) (I : Type) [Fintype I]
    (ε : Module.Basis I ℤ S) (K : Type) [Field K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (n : ℤ), n ≠ 0 →
    ∀ (t : I → Kˣ), (∀ a b : X, ((∏ k, t k ^ (n * (ε k : LinearMap.BilinForm ℤ X) a b) : Kˣ) : K) ∈ k₀) →
    ∀ k, (t k : K) ∈ k₀ := by
  first | exact @GlobalTheory.mem_subfield_of_bilinForm_monomials | exact GlobalTheory.mem_subfield_of_bilinForm_monomials | (intros; apply GlobalTheory.mem_subfield_of_bilinForm_monomials <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsAgreeOverAlgClosedSubfieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.periodGenerators_agree_over_algClosedSubfield : ∀ (R : Type) [CommRing R] [IsDomain R]
    (Q : DegPre R) (τ₀ : Gens Q) (K : Type) [Field K] [IsAlgClosed K] (ev : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (W₀ : Type) [CommRing W₀] (ιb : W₀ →+* R), FromBase Q τ₀ ιb → (∀ a, ev (ιb a) ∈ k₀) →
    ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left))
      (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left)
      (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)),
      IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' Q.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ →
      w.IsGen →
      (∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) →
      ∀ (a b : Q.X) (τ₁ : LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1])),
        τ₁.IsGen → ∃ x : k₀ˣ, ∀ z J J₀, Good Q.P.L z J → Good M₀ z J₀ →
          val (τ₀ a b) (spMap ev) z J = lamUnit w c' a b z J J₀ *
            gm (𝟙 (Sp K)) z ⊤ (unitOn (Units.map k₀.subtype.toMonoidHom x)) * val τ₁ (spMap k₀.subtype) z J₀ := by
  first | exact @GlobalTheory.UCanon.BaseDescent.main | exact GlobalTheory.UCanon.BaseDescent.main | (intros; apply GlobalTheory.UCanon.BaseDescent.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPointRigidBoundaryFamilyOfRigidCoordinates

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtRigid

theorem pointRigid_of_hasRigidCoords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (C : MonoFam Xo c φ R), HasRigidCoords C → PointRigid C := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ C hC
  obtain ⟨N, s, ε, τ₀, hs, hε, hu, hτ, hPR⟩ := hC
  intro K _ _ ev k₀ hk hemb hsep
  apply hPR K ev k₀ hk hemb
  obtain ⟨h0, B₀, i₁, i₂, M₀, c₀, B', i₃, π₁, π₀, w, c', α, hB, hM, hp₁, hp₀, hw, hc, hrel⟩ := hsep
  refine ⟨fun i => by rw [hs]; exact h0 i, ⟨B₀, i₁, i₂, M₀, c₀, B', i₃, π₁, π₀, w, c', hB, hM, hp₁, hp₀, hw, hc⟩, ?_⟩
  intro W₀ _ ιb hFB hιb j
  let u : Fin N → Rˣ := fun k => (hu k).unit
  have hu' : ∀ k, (u k : R) = s (.inr k) := fun k => (hu k).unit_spec
  let t : Fin C.m ⊕ Fin N → Kˣ := Sum.elim (fun i => (α i)⁻¹) (fun k => Units.map ev.toMonoidHom (u k))
  have key : ∀ a b : C.P.D.toPre.X,
      ((∏ k, t k ^ ((l.M' : ℤ) * (ε k : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b) : Kˣ) : K) ∈ k₀ := by
    intro a b
    have hτ' := GlobalTheory.T.isUnitTau_scaledGenerator_torusMonomial Xo c φ R C N s ε τ₀ hs hε hτ u hu' a b
    obtain ⟨τ₁, hτ₁, hv⟩ := hrel a b _ hτ'
    obtain ⟨x, hx⟩ := GlobalTheory.T.periodGenerators_agree_over_algClosedSubfield R C.P.D.toPre τ₀ K ev k₀ hk W₀ ιb hFB hιb B₀ M₀ c₀ B' π₁ π₀ w c' hB hM hp₁ hp₀ hw hc
      a b τ₁ hτ₁
    let z : Sp K := IsLocalRing.closedPoint K
    choose J hJ using fun χ : Sp K ⟶ C.P.D.toPre.P.A.left => exists_chart C.P.D.toPre.P.isLB (χ z)
    choose J₀ hJ₀ using fun χ : Sp K ⟶ B₀.left => exists_chart hM (χ z)
    have gJ : Good C.P.D.toPre.P.L z J := hJ
    have gJ₀ : Good M₀ z J₀ := hJ₀
    have e₁ := hv z J J₀ gJ gJ₀
    have e₂ := hx z J J₀ gJ gJ₀
    have vs : ∀ (cc : Γ(Sp R, ⊤)ˣ), val (ReciprocityTheory.ChartRestriction.G.DVR.scaleGen cc (τ₀ a b)) (spMap ev) z J =
        gm (spMap ev) z ⊤ cc * val (τ₀ a b) (spMap ev) z J := fun cc =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ z le_top (gJ.mem _ _) cc) rfl)
    rw [vs, GlobalTheory.UChart.SepBModel.gm_spMap, e₂] at e₁
    set U' := Units.map ev.toMonoidHom (∏ k, u k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b))
    set x' := Units.map k₀.subtype.toMonoidHom x
    set A := ∏ i, α i ^ (((l.M' : ℤ) • C.δ i) a b)
    set L := lamUnit w c' a b z J J₀
    set V := val τ₁ (spMap k₀.subtype) z J₀
    have e₃ : gm (𝟙 (Sp K)) z ⊤ (unitOn U') * gm (𝟙 (Sp K)) z ⊤ (unitOn x') = gm (𝟙 (Sp K)) z ⊤ (unitOn A) := by
      have h₁ : gm (𝟙 (Sp K)) z ⊤ (unitOn U') * (L * gm (𝟙 (Sp K)) z ⊤ (unitOn x') * V) =
          (L * V) * (gm (𝟙 (Sp K)) z ⊤ (unitOn U') * gm (𝟙 (Sp K)) z ⊤ (unitOn x')) := by ac_rfl
      have h₂ : L * gm (𝟙 (Sp K)) z ⊤ (unitOn A) * V = (L * V) * gm (𝟙 (Sp K)) z ⊤ (unitOn A) := by ac_rfl
      rw [h₁, h₂] at e₁
      exact mul_left_cancel e₁
    have e₄ : U' * x' = A := GlobalTheory.UChart.SepBModel.gm_unitOn_inj z (by
      rw [show unitOn (U' * x') = unitOn U' * unitOn x' from map_mul _ _ _, map_mul]; exact e₃)
    have e₅ : (∏ k, t k ^ ((l.M' : ℤ) * (ε k : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b)) = x'⁻¹ := by
      rw [Fintype.prod_sum_type]
      have hA : (∏ i, t (.inl i) ^ ((l.M' : ℤ) * (ε (.inl i) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b)) = A⁻¹ := by
        simp only [t, Sum.elim_inl, hε, A, inv_zpow, Finset.prod_inv_distrib, LinearMap.smul_apply, smul_eq_mul]
      have hU : (∏ k, t (.inr k) ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b)) = U' := by
        simp only [t, Sum.elim_inr, U', map_prod, map_zpow]
      rw [hA, hU, ← e₄, mul_inv_rev, inv_mul_cancel_right]
    rw [e₅]
    exact (x⁻¹ : k₀ˣ).val.2
  have := GlobalTheory.T.mem_subfield_of_bilinForm_basis_monomials C.P.D.toPre.X (balForms H.bar C.P.D.toPre.X) (Fin C.m ⊕ Fin N) ε K k₀ hk (l.M')
    (by exact_mod_cast (level_pos l).ne') t key (.inr j)
  simpa [t, u] using this

end GlobalTheory.PtRigid
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPointRigidBoundaryFamilyOfRigidCoordinatesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isPointRigidBoundaryFamily_of_rigidCoordinates : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (C : MonoFam Xo c φ R), HasRigidCoords C → PointRigid C := by
  first | exact @GlobalTheory.PtRigid.pointRigid_of_hasRigidCoords | exact GlobalTheory.PtRigid.pointRigid_of_hasRigidCoords | (intros; apply GlobalTheory.PtRigid.pointRigid_of_hasRigidCoords <;> assumption)
end
end
