module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Hermitian
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeLiftOfLevelSectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelPeriodOfSymplecticBasisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBasisCongrLevelModStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyNearbyPeriodsSameComponent
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SqOfCalculus
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertUnimodularRiemannForm

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.PolUnif

theorem hermForm_self_im {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (x : Fin g → ℂ) :
    (hermForm Hm x x).im = 0 := by
  have h := hH.im_star_dotProduct_mulVec_self (star x)
  rw [star_star] at h
  exact h

theorem exists_unif_riemannForm : ∀ (h : ℕ) (P : Out.PolAV (Sp ℂ)), P.g = h → ∃ (u : HolUnif P.A P.L h) (Hm : Matrix (Fin h) (Fin h) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), u.IsAH Hm χ ∧ (∀ x y : u.Λ, (Ef x y : ℝ) = (hermForm Hm x y).im) ∧ Function.Bijective Ef ∧ (∀ x, Ef x x = 0) ∧ Module.Free ℤ u.Λ ∧ Module.Finite ℤ u.Λ ∧ Module.finrank ℤ u.Λ = 2 * h ∧ ∀ (n : ℕ) (x y : u.Λ) (e : ℂˣ), 0 < n → (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef x y : ℂ) / n) → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (x : Fin h → ℂ))) (u.ex ((n : ℂ)⁻¹ • (y : Fin h → ℂ))) (unitOn e) := by
  intro h P hg
  subst hg
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, hbij, hW⟩ := GlobalTheory.thetaUnifAV_all P rig hrig
  haveI : DiscreteTopology u.Λ := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  refine ⟨u, Hm, χ, Ef, hAH, hE, hbij, fun x => ?_, ZLattice.module_free ℝ u.Λ, ZLattice.module_finite ℝ u.Λ, ?_, hW⟩
  · have h1 := hE x x
    rw [hermForm_self_im hAH.1] at h1
    exact_mod_cast h1
  · rw [ZLattice.rank ℝ u.Λ, Module.finrank_pi_fintype]
    simp [mul_comm]

end GlobalTheory.PolUnif
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertUnimodularRiemannFormStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

theorem _root_.GlobalTheory.T.exists_appellHumbert_unimodular_riemannForm : ∀ (h : ℕ) (P : Out.PolAV (Sp ℂ)), P.g = h → ∃ (u : HolUnif P.A P.L h) (Hm : Matrix (Fin h) (Fin h) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), u.IsAH Hm χ ∧ (∀ x y : u.Λ, (Ef x y : ℝ) = (hermForm Hm x y).im) ∧ Function.Bijective Ef ∧ (∀ x, Ef x x = 0) ∧ Module.Free ℤ u.Λ ∧ Module.Finite ℤ u.Λ ∧ Module.finrank ℤ u.Λ = 2 * h ∧ ∀ (n : ℕ) (x y : u.Λ) (e : ℂˣ), 0 < n → (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef x y : ℂ) / n) → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (x : Fin h → ℂ))) (u.ex ((n : ℂ)⁻¹ • (y : Fin h → ℂ))) (unitOn e) := by
  first | exact @GlobalTheory.PolUnif.exists_unif_riemannForm | exact GlobalTheory.PolUnif.exists_unif_riemannForm | (intros; apply GlobalTheory.PolUnif.exists_unif_riemannForm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolUnifCompLinearEquivExists

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.KeyFam

theorem holUnif_transport_linearEquiv : ∀ (h : ℕ) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L h) (T : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ)), ∃ u' : HolUnif A L h, (∀ z, u'.ex z = u.ex (T z)) ∧ ∀ z, z ∈ u'.Λ ↔ T z ∈ u.Λ := by
  intro h A _ L u T
  have hc : Continuous T := T.toContinuousLinearEquiv.continuous
  have hd : Differentiable ℂ T := T.toContinuousLinearEquiv.differentiable
  let Λ' : Submodule ℤ (Fin h → ℂ) := u.Λ.comap ((T.restrictScalars ℤ).toLinearMap)
  have hmem : ∀ z, z ∈ Λ' ↔ T z ∈ u.Λ := fun z => Iff.rfl
  have hdisc : DiscreteTopology Λ' := by
    haveI := u.discrete
    let f : Λ' → u.Λ := fun z => ⟨T z, (hmem z).1 z.2⟩
    have hf : Continuous f := (hc.comp continuous_subtype_val).subtype_mk _
    have hi : Function.Injective f := fun a b hab =>
      Subtype.ext (T.injective (congrArg Subtype.val hab))
    exact DiscreteTopology.of_continuous_injective hf hi
  have hfull : Submodule.span ℝ (Λ' : Set (Fin h → ℂ)) = ⊤ := by
    have h1 : (Λ' : Set (Fin h → ℂ)) = (T.symm.restrictScalars ℝ).toLinearMap '' (u.Λ : Set (Fin h → ℂ)) := by
      ext z
      constructor
      · intro hz
        exact ⟨T z, hz, by simp⟩
      · rintro ⟨w, hw, rfl⟩
        refine (hmem _).2 ?_
        simpa using hw
    rw [h1, ← Submodule.map_span, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact (T.symm.restrictScalars ℝ).surjective
  refine ⟨{ ex := fun z => u.ex (T z)
            ex_add := fun z w => by rw [map_add (f := _), u.ex_add]
            ex_onto := u.ex_onto.comp T.surjective
            Λ := Λ'
            ker := fun z => u.ker (T z)
            discrete := hdisc
            full := hfull
            hol := fun U f => ⟨(u.hol U f).1.preimage hc,
              (u.hol U f).2.comp hd.differentiableOn (fun _ hz => hz)⟩
            fr := fun i z => u.fr i (T z)
            fr_hol := fun i => (u.fr_hol i).comp hd.differentiableOn (fun _ hz => hz)
            fr_ne := fun i z hz => u.fr_ne i (T z) hz
            fr_compat := fun i j z hz => u.fr_compat i j (T z) hz }, fun _ => rfl, hmem⟩

end GlobalTheory.KeyFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolUnifCompLinearEquivExistsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

theorem _root_.GlobalTheory.T.holUnif_comp_linearEquiv_exists : ∀ (h : ℕ) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L h) (T : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ)), ∃ u' : HolUnif A L h, (∀ z, u'.ex z = u.ex (T z)) ∧ ∀ z, z ∈ u'.Λ ↔ T z ∈ u.Λ := by
  exact @GlobalTheory.KeyFam.holUnif_transport_linearEquiv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSquareRootWeilPairingStandard

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.SqRootPairing

theorem eq_of_sq_eq_of_odd {G : Type} [CommGroup G] {k : ℕ} (hk : Odd k) {a b : G} (ha : a ^ k = 1) (hb : b ^ k = 1)
    (h : a ^ 2 = b ^ 2) : a = b := by
  obtain ⟨m, rfl⟩ := hk
  rw [pow_succ, pow_mul] at ha hb
  rw [h] at ha
  exact mul_left_cancel (ha.trans hb.symm)

theorem weilIs_down {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hp : IsGrpPullback G' G f φ) (hw : LBIso L' (L.pull φ)) (T : Over S') (g : T.left ⟶ S) (hg : g = T.hom ≫ f)
    (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G) (c : Γ(T.left, ⊤)ˣ) (ex : x₀.left = x.left ≫ φ)
    (ey : y₀.left = y.left ≫ φ) (h : Out.WeilIs G L k x₀ y₀ c) : Out.WeilIs G' L' k x y c := by
  subst hg
  exact (weilIs_grpPullback_of_comm _ _ _ _ _ _ _ _ hL hL' hp hw T k x y x₀ y₀ c ex ey).2 h

theorem pow_eq_one (hL : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {k n : ℕ} {T : Over S}
    {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (H : Out.WeilIs P.A P.L k x y c) (hx : x ^ n = 1) : c ^ n = 1 := by
  have key : ∀ l : ℕ, Out.WeilIs P.A P.L k (x ^ (l + 1)) y (c ^ (l + 1)) := fun l => by
    induction l with
    | zero => rw [zero_add, pow_one, pow_one]; exact H
    | succ l ih => rw [pow_succ, pow_succ c]; exact (hL.weil S P k T).2.1 _ _ _ _ _ ih H
  have := key n
  rw [pow_succ, hx, _root_.one_mul] at this
  have e := CommutatorPairing.weilIs_unique hL.globalFns P.isAb P.isLB this H
  rwa [pow_succ, mul_eq_right] at e

theorem weilIs_lev_of_sqOf : ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (S : Scheme.{0}) (s : S ⟶ Sp K) (c : SiegPre h k ζ s) (p : Sp ℂ ⟶ S) (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ c.A.left) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → p ≫ s = spMap σ → SqOf P c p φ → (∀ a, (lev a).left ≫ φ = p ≫ (c.lev a).left) → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ k = 1) → ∀ (a b : Fin h ⊕ Fin h → ℤ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / k) → Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn e) := by
  intro h k K _ ζ σ S s c p P φ lev hk3 hk hζ hp hsq hlev _ tors a b e he
  obtain ⟨hpb, -, φ₂, sq, iso⟩ := hsq
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let z : ℂˣ := Units.mk0 (σ ζ) (by rw [hζ]; exact Complex.exp_ne_zero _)
  have hz : (z : ℂ) = σ ζ := rfl
  have hzk : z ^ k = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hz, hζ, ← Complex.exp_nat_mul, mul_div_cancel₀ _ hk0, Complex.exp_neg,
      Complex.exp_two_pi_mul_I, inv_one, Units.val_one])
  have hez : e = z ^ omegaStd a b := Units.ext (by
    rw [Units.val_zpow_eq_zpow_val, hz, hζ, ← Complex.exp_int_mul, he]
    congr 1
    ring)
  have lam : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  have dg : ((abelian₂ P.A P.L).pull (lift (𝟙 P.A) (𝟙 P.A)).left).IsLB := LB.isLB_linComb lam _ _
  have dc : (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left).IsLB := LB.isLB_linComb c.isLB _ _
  have w₀ := (c.geom ℂ p σ z hp hz).2.2 a b
  have pt : ∀ a, (toUnit (Over.mk p) ≫ c.lev a).left = (lev a).left ≫ φ := fun a => by
    rw [hlev, Over.comp_left, Over.toUnit_left]
    rfl
  have w₁ := weilIs_down dc dg hpb (SiegelPull.diag_iso sq iso) (𝟙_ (Over (Sp ℂ))) p (Category.id_comp p).symm k
    (lev a) (lev b) _ _ _ (pt a) (pt b) w₀
  obtain ⟨c₀, hc₀, -⟩ := (hL.weil _ P k (𝟙_ (Over (Sp ℂ)))).1 (lev a) (lev b) (tors a) (tors b)
  have w₂ := SiegelOfPolarised.weilIs_of_lbIso_pow hL.globalFns P.isAb P.isLB dg
    (SiegelOfPolarised.lbIso_diag hL P) hc₀
  have e₂ := CommutatorPairing.weilIs_unique hL.globalFns P.isAb dg w₂ w₁
  have up : ∀ (u : ℂˣ) (n : ℕ), unitOn (u ^ n) = unitOn u ^ n := fun u n => map_pow _ _ _
  have e₁ : c₀ = unitOn e := by
    refine eq_of_sq_eq_of_odd hk (pow_eq_one hL P hc₀ (tors a)) ?_ (e₂.trans ?_)
    · refine (up e k).symm.trans ?_
      rw [hez, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzk, one_zpow]
      exact map_one _
    · refine Eq.trans ?_ (up e 2)
      rw [hez, mul_comm, zpow_mul, zpow_ofNat]
  exact e₁ ▸ hc₀

end GlobalTheory.SqRootPairing
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSquareRootWeilPairingStandardStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

theorem _root_.GlobalTheory.T.siegel_square_root_weil_pairing_standard : ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (S : Scheme.{0}) (s : S ⟶ Sp K) (c : SiegPre h k ζ s) (p : Sp ℂ ⟶ S) (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ c.A.left) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → p ≫ s = spMap σ → SqOf P c p φ → (∀ a, (lev a).left ≫ φ = p ≫ (c.lev a).left) → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ k = 1) → ∀ (a b : Fin h ⊕ Fin h → ℤ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / k) → Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn e) := by
  first | exact @GlobalTheory.SqRootPairing.weilIs_lev_of_sqOf | exact GlobalTheory.SqRootPairing.weilIs_lev_of_sqOf | (intros; apply GlobalTheory.SqRootPairing.weilIs_lev_of_sqOf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodTorusComplexPointSiegelFamily

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.SiegelPtAt

theorem sqrt_at_point (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ) (hk : 3 ≤ k)
    (hζ : σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k)) (p : Sp ℂ ⟶ F.X) :
    ∃ (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ F.univ.A.left), SqOf P F.univ p φ := by
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hζ' : IsUnit ζ := IsUnit.mk0 _ fun e => Complex.exp_ne_zero _ (by rw [← hζ, e, map_zero])
  obtain ⟨R, _, π, p₁, Q₁, φ₁, -, rfl, hQ₁, -⟩ := GlobalTheory.SiegelNearby.exists_etale_sqrt hL σ F (by omega) hζ' p
  obtain ⟨P, ψ, hpb⟩ := GlobalTheory.SiegelNearby.exists_polPB hL.polBaseChange Q₁ p₁
  exact ⟨P, ψ ≫ φ₁, (sqOf_calculus h k K ζ _ _ _ F.s F.univ π).1 p₁ Q₁ P φ₁ ψ hQ₁ hpb⟩

theorem levels_pull {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (c : SiegPre h k ζ s) (p : Sp ℂ ⟶ S) (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ c.A.left) (hsq : SqOf P c p φ) :
    ∃ lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A),
      (∀ a, (lev a).left ≫ φ = p ≫ (c.lev a).left) ∧ (∀ a b, lev (a + b) = lev a * lev b) ∧
        ∀ a, lev a ^ k = 1 := by
  choose l hl hl' using fun a => GlobalTheory.SiegelNearby.exists_section_pull hsq.1 (c.lev a) k (c.lev_tors a)
  refine ⟨l, hl', fun a b => ?_, hl⟩
  have key := hsq.1.2 (𝟙_ (Over (Sp ℂ))) (l a) (l b) (toUnit _ ≫ c.lev a) (toUnit _ ≫ c.lev b)
    (by rw [Over.comp_left, GlobalTheory.SiegelNearby.toUnit_left, hl']; exact congrArg (· ≫ _) (Category.id_comp p))
    (by rw [Over.comp_left, GlobalTheory.SiegelNearby.toUnit_left, hl']; exact congrArg (· ≫ _) (Category.id_comp p))
  rw [← MonObj.comp_mul, ← c.lev_add, Over.comp_left, GlobalTheory.SiegelNearby.toUnit_left] at key
  apply Over.OverMorphism.ext
  apply hsq.1.1.hom_ext
  · rw [hl', ← key]; exact (Category.id_comp _).symm
  · rw [Over.w, Over.w]

theorem perLev_of_level (h k : ℕ) (P : Out.PolAV (Sp ℂ)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A))
    (hg : P.g = h) (hk : 0 < k) (add : ∀ a b, lev (a + b) = lev a * lev b) (tors : ∀ a, lev a ^ k = 1)
    (weil : ∀ (a b : Fin h ⊕ Fin h → ℤ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / k) →
      Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn e)) :
    ∃ τ : Matrix (Fin h) (Fin h) ℂ, PerLev P τ k lev := by
  obtain ⟨u, Hm, χ, Ef, hAH, hEf, hbij, halt, hfree, hfin, hrank, hW⟩ := GlobalTheory.T.exists_appellHumbert_unimodular_riemannForm h P hg
  obtain ⟨l, hl, hdvd⟩ := GlobalTheory.T.exists_lattice_lift_of_level_section h k P lev u Ef hk add tors weil (fun x y e he => hW k x y e hk he)
  obtain ⟨B, hB, hBl⟩ := GlobalTheory.T.exists_symplectic_basis_congr_level_mod h k u.Λ Ef l hk hrank halt hbij hdvd
  let v : Fin h ⊕ Fin h → (Fin h → ℂ) := fun i => (B (Pi.single i 1) : Fin h → ℂ)
  have hv : ∀ i j, (hermForm Hm (v i) (v j)).im =
      (omegaStd (Pi.single i 1 : Fin h ⊕ Fin h → ℤ) (Pi.single j 1) : ℝ) := fun i j => by
    rw [← hEf, hB]
  obtain ⟨τ, T, hs, hp, hT⟩ := GlobalTheory.T.exists_siegel_period_of_symplectic_basis h Hm v hAH.1 hAH.2.1 hv
  obtain ⟨u', hex, hΛ⟩ := GlobalTheory.T.holUnif_comp_linearEquiv_exists h P.A P.L u T
  have hBa : ∀ a, (B a : Fin h → ℂ) = ∑ i, a i • v i := fun a => by
    conv_lhs => rw [show a = ∑ i, a i • (Pi.single i 1 : Fin h ⊕ Fin h → ℤ) by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]

    simp only [v, map_sum, map_zsmul, Submodule.coe_sum, Submodule.coe_smul]
  refine ⟨τ, hg, hs, hp, u', fun z => ?_, fun n a b e hn he => ?_, fun a => ?_⟩
  · rw [hΛ]
    constructor
    · intro hz
      obtain ⟨a, ha⟩ := B.surjective ⟨T z, hz⟩
      refine ⟨a, T.injective ?_⟩
      rw [hT, ← hBa, ha]
    · rintro ⟨a, rfl⟩
      rw [hT, ← hBa]
      exact (B a).2
  · have := hW n (B a) (B b) e hn (by rw [hB]; exact he)
    rwa [hex, hex, map_smul, map_smul, hT, hT, ← hBa, ← hBa]
  · rw [hl, hex, map_smul, hT, ← hBa]
    obtain ⟨m, hm⟩ := hBl a
    have e : ((l a : u.Λ) : Fin h → ℂ) = (B a : Fin h → ℂ) + (k : ℂ) • (m : Fin h → ℂ) := by
      rw [← sub_eq_iff_eq_add', ← Submodule.coe_sub, hm, Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℂ]
      norm_cast
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    rw [e, smul_add, smul_smul, inv_mul_cancel₀ hk', one_smul, u.ex_add, (u.ker _).2 m.2, _root_.mul_one]

theorem exists_ptAt : ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ p : Sp ℂ ⟶ F.X, p ≫ F.s = spMap σ → ∃ τ : Matrix (Fin h) (Fin h) ℂ, PtAt F.univ p τ := by
  intro h k K _ ζ σ F _ hk hodd hζ p hp
  obtain ⟨P, φ, hsq⟩ := sqrt_at_point h k K ζ σ F hk hζ p
  obtain ⟨lev, hlev, add, tors⟩ := levels_pull F.univ p P φ hsq
  have weil := GlobalTheory.T.siegel_square_root_weil_pairing_standard h k K ζ σ F.X F.s F.univ p P φ lev hk hodd hζ hp hsq hlev add tors
  obtain ⟨τ, hτ⟩ := perLev_of_level h k P lev hsq.2.1 (by omega) add tors weil
  exact ⟨τ, P, lev, φ, hτ, hsq, hlev⟩

end GlobalTheory.SiegelPtAt
end
end
