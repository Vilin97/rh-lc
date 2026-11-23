module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyEndCharpolySpecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDegreeIntegerCombinationIsHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativePolynomialFunctionEqNormFormStatement
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneTheoryVEqVerschiebungInjectiveStatement
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNormProdAevalEq
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompEqZeroOfNotIsIsogeny
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPadicIntCharpolyCommuteFrobeniusSemilinearStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTowerAndHeightEqTwoDim
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetAevalEqProdArootsCharpolyStatement
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAevalEqProdArootsStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.deg_aeval_end_eq_prod_aroots : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] (R : Polynomial ℤ), algebraMap ℚ Ω (deg (A := A) (B := A) (Polynomial.aeval f R).asHom : ℚ) = ((((charpoly f).map (Int.castRingHom ℚ)).aroots Ω).map (fun a => Polynomial.aeval a R)).prod := by
  intro K _ A f Ω _ _ _ R
  obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f
  refine GlobalTheory.T.multiplicative_polynomialFunction_eq_normForm Ω A.dim
    (fun F => (deg (Polynomial.aeval f F).asHom : ℚ))
    ((charpoly f).map (Int.castRingHom ℚ)) ?_ ?_ ?_ ?_ ?_ R
  · intro F G
    have h := (isIsogeny_comp_iff_and_deg_comp K A A A
      (Polynomial.aeval f G).asHom (Polynomial.aeval f F).asHom rfl rfl).2
    change (deg (Polynomial.aeval f (F * G)).asHom : ℚ) =
      (deg (Polynomial.aeval f F).asHom : ℚ) * (deg (Polynomial.aeval f G).asHom : ℚ)
    rw [map_mul, End.mul_asHom, h, Nat.cast_mul, mul_comm]
  · intro n u
    obtain ⟨Φ, hΦ, hΦev⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous K A A rfl n
      (fun i => (Polynomial.aeval f (u i)).asHom)
    refine ⟨Φ, hΦ, fun m => ?_⟩
    rw [hΦev m]
    change _ = (deg (End.addEquiv (Polynomial.aeval f (∑ i, m i • u i))) : ℚ)
    simp only [map_sum, map_zsmul, End.addEquiv_apply]
  · exact hm.map _
  · rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _)]
    exact hd
  · intro n
    have e : Polynomial.aeval f (Polynomial.C n - Polynomial.X) = (n : End A) - f := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, eq_intCast]
    change ((charpoly f).map (Int.castRingHom ℚ)).eval (n : ℚ) =
      (deg (Polynomial.aeval f (Polynomial.C n - Polynomial.X)).asHom : ℚ)
    rw [Polynomial.eval_intCast_map, Int.cast_id, hev n, e, map_natCast]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNormProdAevalEqStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eq_of_norm_prod_aeval_eq' : ∀ (l : ℕ) [Fact l.Prime] (P Q : Polynomial ℚ_[l]), P.Monic → Q.Monic → P.natDegree = Q.natDegree → (∀ F : Polynomial ℤ, ‖((P.aroots (PadicAlgCl l)).map (fun a => Polynomial.aeval a F)).prod‖ = ‖((Q.aroots (PadicAlgCl l)).map (fun a => Polynomial.aeval a F)).prod‖) → P = Q := by
  first | exact @GlobalTheory.PadicRootNorm.eq_of_norm_prod_aeval_eq | exact GlobalTheory.PadicRootNorm.eq_of_norm_prod_aeval_eq | (intros; apply GlobalTheory.PadicRootNorm.eq_of_norm_prod_aeval_eq; all_goals assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTowerAndHeightEqTwoDimStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_torsionTower_and_height_eq_two_dim : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A : AbVar k), (∃ G : PDivGroup p k, Nonempty (G.TorsionTower A.X)) ∧ ∀ (G : PDivGroup p k) (t : G.TorsionTower A.X), G.height = 2 * A.dim := by
  first | exact @GlobalTheory.AVTower.exists_tower_and_height_eq | exact GlobalTheory.AVTower.exists_tower_and_height_eq | (intros; apply GlobalTheory.AVTower.exists_tower_and_height_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdAevalPadicRootsCharpolyEqDet

section

@[expose] public section

namespace GlobalTheory
open Polynomial

theorem aeval_int_eq_eval₂ {A : Type} [Ring A] [inst : Algebra ℤ A] (x : A) (R : ℤ[X]) :
    @aeval ℤ A _ _ inst x R = eval₂ (Int.castRingHom A) x R := by
  rw [aeval_def]
  congr 1
  exact RingHom.ext_int _ _

theorem prod_aeval_aroots_padic_eq_det : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [IsDomain S] (N : Type) [AddCommGroup N] [Module S N] [Module.Free S N] [Module.Finite S N] (ψ : ℤ_[p] →+* S) (u : N →ₗ[S] N) (P : Polynomial ℤ_[p]) (R : Polynomial ℤ) (d : ℤ_[p]), Function.Injective ψ → P.map ψ = u.charpoly → LinearMap.det (Polynomial.aeval u R) = ψ d → (((P.map (algebraMap ℤ_[p] ℚ_[p])).aroots (PadicAlgCl p)).map (fun a => Polynomial.aeval a R)).prod = algebraMap ℚ_[p] (PadicAlgCl p) (d : ℚ_[p]) := by
  intro p _ S _ _ N _ _ _ _ ψ u P R d hψ hP hd
  let K := FractionRing S
  have hg : Function.Injective ((algebraMap S K).comp ψ) :=
    (IsFractionRing.injective S K).comp hψ
  let ψ' : ℚ_[p] →+* K := IsFractionRing.lift hg
  have hψ' : ψ'.comp (algebraMap ℤ_[p] ℚ_[p]) = (algebraMap S K).comp ψ :=
    IsLocalization.lift_comp _
  let Ω := AlgebraicClosure K
  letI : Algebra ℚ_[p] Ω := ((algebraMap K Ω).comp ψ').toAlgebra
  have hΩ : algebraMap ℚ_[p] Ω = (algebraMap K Ω).comp ψ' := rfl
  let j : PadicAlgCl p →ₐ[ℚ_[p]] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hj : Function.Injective j := j.toRingHom.injective
  let uK : Module.End K (TensorProduct S K N) := u.baseChange K
  have key := GlobalTheory.T.det_aeval_eq_prod_aroots_charpoly' K Ω (TensorProduct S K N) uK (R.map (Int.castRingHom K))
  have hF : ∀ {A : Type} [Ring A] [Algebra K A] (x : A), aeval x (R.map (Int.castRingHom K)) = aeval x R := by
    intro A _ _ x
    rw [← algebraMap_int_eq, aeval_map_algebraMap]
  simp only [hF] at key
  have hbc : aeval uK R = (aeval u R).baseChange K := by
    have := aeval_algHom_apply (Module.End.baseChangeHom S K N).toRingHom.toIntAlgHom u R
    exact this
  rw [hbc, LinearMap.det_baseChange, hd] at key
  have hch : uK.charpoly.aroots Ω = (P.map (algebraMap ℤ_[p] ℚ_[p])).aroots Ω := by
    rw [LinearMap.charpoly_baseChange, ← hP, aroots_def, aroots_def, map_map, map_map, map_map, hΩ]
    simp only [RingHom.comp_assoc, hψ']
  rw [hch] at key
  apply hj
  set Q := P.map (algebraMap ℤ_[p] ℚ_[p])
  have hroots : Q.aroots Ω = (Q.aroots (PadicAlgCl p)).map j := by
    have h := (IsAlgClosed.splits (Q.map (algebraMap ℚ_[p] (PadicAlgCl p)))).roots_map (j : PadicAlgCl p →+* Ω)
    rw [map_map, AlgHom.comp_algebraMap] at h
    rw [aroots_def, aroots_def, h]
    rfl
  rw [hroots, Multiset.map_map] at key
  rw [map_multiset_prod, Multiset.map_map, AlgHom.commutes]
  simp only [aeval_int_eq_eval₂] at key ⊢
  have e1 : ∀ a : PadicAlgCl p, j (eval₂ (Int.castRingHom _) a R) = eval₂ (Int.castRingHom Ω) (j a) R := by
    intro a
    change (j : PadicAlgCl p →+* Ω) (eval₂ (Int.castRingHom _) a R) = _
    rw [Polynomial.hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _
  simp only [Function.comp_def, e1] at key ⊢
  refine key.symm.trans ?_
  rw [hΩ, RingHom.comp_apply]
  congr 1
  exact (RingHom.congr_fun hψ' d).symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdAevalPadicRootsCharpolyEqDetStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.prod_aeval_padicRoots_charpoly_eq_det : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [IsDomain S] (N : Type) [AddCommGroup N] [Module S N] [Module.Free S N] [Module.Finite S N] (ψ : ℤ_[p] →+* S) (u : N →ₗ[S] N) (P : Polynomial ℤ_[p]) (R : Polynomial ℤ) (d : ℤ_[p]), Function.Injective ψ → P.map ψ = u.charpoly → LinearMap.det (Polynomial.aeval u R) = ψ d → (((P.map (algebraMap ℤ_[p] ℚ_[p])).aroots (PadicAlgCl p)).map (fun a => Polynomial.aeval a R)).prod = algebraMap ℚ_[p] (PadicAlgCl p) (d : ℚ_[p]) := by
  first | exact @GlobalTheory.prod_aeval_aroots_padic_eq_det | exact GlobalTheory.prod_aeval_aroots_padic_eq_det | (intros; apply GlobalTheory.prod_aeval_aroots_padic_eq_det <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyMapEq

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.CharpolyAV

section Rho

variable {p : ℕ} [Fact p.Prime] (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]
  {A : AbVar k} {G : PDivGroup p k} (t : G.TorsionTower A.X)

def rho : End A →+ Module.End (WittVector p k) (T.M G) :=
  AddMonoidHom.mk' (fun g => T.map (t.map t g.asHom.hom)) fun g h => by
    have hfun := base_functor_props p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
    haveI : IsMonHom (g.asHom.hom * h.asHom.hom) := inferInstanceAs (IsMonHom (g + h).asHom.hom)
    show T.map (t.map t (g.asHom.hom * h.asHom.hom)) = _
    rw [TorsionTower.map_mul]
    exact hfun.2.2.1 _ _

theorem rho_apply (g : End A) : rho T t g = T.map (t.map t g.asHom.hom) := rfl

theorem rho_pow (f : End A) (n : ℕ) : rho T t (f ^ n) = rho T t f ^ n := by
  have hfun := base_functor_props p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, rho_apply]
    show T.map (t.map t (𝟙 A.X)) = _
    rw [TorsionTower.map_id]
    exact hfun.1
  | succ n ih =>
    rw [pow_succ, pow_succ', ← ih, rho_apply, rho_apply, rho_apply]
    show T.map (t.map t (f.asHom.hom ≫ (f ^ n).asHom.hom)) = _
    rw [TorsionTower.map_comp t t t]
    exact hfun.2.1 _ _

theorem rho_aeval (f : End A) (R : Polynomial ℤ) :
    rho T t (Polynomial.aeval f R) = Polynomial.aeval (rho T t f) R := by
  induction R using Polynomial.induction_on' with
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, eq_intCast (algebraMap ℤ (End A)),
      eq_intCast (algebraMap ℤ (Module.End (WittVector p k) (T.M G))), ← zsmul_eq_mul, ← zsmul_eq_mul, map_zsmul, rho_pow]

end Rho

theorem charpoly_map_eq : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (A : AbVar k) (G : PDivGroup p k) (t : G.TorsionTower A.X)
    [Module.Free (WittVector p k) (T.M G)] [Module.Finite (WittVector p k) (T.M G)] (f : End A),
    (T.map (t.map t f.asHom.hom)).charpoly = (GlobalTheory.AV.AbVar.charpoly f).map (Int.castRingHom (WittVector p k)) := by
  intro p _ T k _ _ _ A G t _ _ f
  have hfun := base_functor_props p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
  have hFc : ∀ (g : End A) (x : T.M G), T.map (t.map t g.asHom.hom) (T.F G x) = T.F G (T.map (t.map t g.asHom.hom) x) :=
    fun g x => hfun.2.2.2.2.2.2.1 _ x
  have hFinj : Function.Injective (T.F G) := (GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective p T k G).1
  let ψ : ℤ_[p] →+* WittVector p k :=
    (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom
  have hψ : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow, map_natCast] at hx
    have hu : IsUnit (ψ (PadicInt.unitCoeff hx0 : ℤ_[p])) := (Units.isUnit _).map ψ
    have hpn : ((p : WittVector p k)) ^ x.valuation ≠ 0 := pow_ne_zero _ (WittVector.p_nonzero p k)
    exact hpn ((hu.mul_right_eq_zero).1 hx)
  have hrank : Module.finrank (WittVector p k) (T.M G) = 2 * A.dim :=
    hfun.2.2.2.2.2.2.2.1.trans ((GlobalTheory.T.exists_torsionTower_and_height_eq_two_dim p k A).2 G t)
  obtain ⟨P, hPm, hP⟩ := GlobalTheory.T.exists_padicInt_charpoly_commute_frobeniusSemilinear p k (T.M G) (T.F G) ψ (T.map (t.map t f.asHom.hom)) hFinj (hFc f)
  obtain ⟨⟨hQm, hQdeg, -⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec k A f
  have hPdeg : P.natDegree = 2 * A.dim := by
    rw [← hPm.natDegree_map ψ, hP, LinearMap.charpoly_natDegree, hrank]
  have key : P.map (algebraMap ℤ_[p] ℚ_[p]) = (charpoly f).map (Int.castRingHom ℚ_[p]) := by
    refine GlobalTheory.T.eq_of_norm_prod_aeval_eq' p _ _ (hPm.map _) (hQm.map _) ?_ ?_
    · rw [hPm.natDegree_map, hQm.natDegree_map, hPdeg, hQdeg]
    · intro R
      obtain ⟨PR, -, hPR⟩ := GlobalTheory.T.exists_padicInt_charpoly_commute_frobeniusSemilinear p k (T.M G) (T.F G) ψ
        (T.map (t.map t (Polynomial.aeval f R).asHom.hom)) hFinj (hFc _)
      set d : ℤ_[p] := (-1) ^ Module.finrank (WittVector p k) (T.M G) * PR.coeff 0 with hd_def
      have hd : LinearMap.det (T.map (t.map t (Polynomial.aeval f R).asHom.hom)) = ψ d := by
        rw [LinearMap.det_eq_sign_charpoly_coeff, ← hPR, Polynomial.coeff_map, hd_def, map_mul, map_pow,
          map_neg, map_one]
      have habs := GlobalTheory.Dieu.AbsDet.norm_det_eq_norm_deg p T k A G t ψ (Polynomial.aeval f R) d hd
      have hd' : LinearMap.det (Polynomial.aeval (T.map (t.map t f.asHom.hom)) R) = ψ d := by
        rw [← hd]; exact congrArg LinearMap.det (rho_aeval T t f R).symm
      rw [GlobalTheory.T.prod_aeval_padicRoots_charpoly_eq_det p (WittVector p k) (T.M G) ψ _ P R d hψ hP hd']
      have hQ : (charpoly f).map (Int.castRingHom ℚ_[p]) =
          ((charpoly f).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℚ_[p]) := by
        rw [Polynomial.map_map]; congr 1 <;> exact RingHom.ext_int _ _
      have h2 := GlobalTheory.T.deg_aeval_end_eq_prod_aroots k A f (PadicAlgCl p) R
      rw [hQ, Polynomial.aroots_map]
      erw [← h2]
      rw [PadicAlgCl.norm_extends, map_natCast, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends]
      rw [PadicInt.padic_norm_e_of_padicInt, habs]
      rw [← PadicInt.padic_norm_e_of_padicInt]; push_cast; rfl
  have hP' : P = (charpoly f).map (Int.castRingHom ℤ_[p]) := by
    apply Polynomial.map_injective (algebraMap ℤ_[p] ℚ_[p]) (IsFractionRing.injective ℤ_[p] ℚ_[p])
    rw [key, Polynomial.map_map]; congr 1 <;> exact RingHom.ext_int _ _
  rw [← hP, hP', Polynomial.map_map]; congr 1 <;> exact RingHom.ext_int _ _

end GlobalTheory.Dieu.CharpolyAV
end
end
end
