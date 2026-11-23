module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsPtJ
public import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.DualLiftInjective
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsJetChartCoordinatesNilpotentStatement
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
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
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointAddSqZeroEqProdMulTangentStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartCut

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsJetPointsOfIsLieBasis

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetPoint

open GlobalTheory.SqZero

variable {R : Type} [CommRing R]

theorem jetTruncR_surjective (κ : Type) (m : ℕ) : Function.Surjective (jetTruncR R κ m) := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ p, rfl⟩

theorem jetAug_comp_jetTruncR (κ : Type) (m : ℕ) :
    (jetAug R κ m).comp (jetTruncR R κ m) = jetAug R κ (m + 1) :=
  jet_ext fun j => by
    rw [jetAug_zR]
    exact jetAug_zR (R := R) m j

theorem ker_jetTruncR_isNilpotent (κ : Type) (m : ℕ) :
    IsNilpotent (RingHom.ker (jetTruncR R κ m)) := by
  have hle : RingHom.ker (jetTruncR R κ m) ≤ RingHom.ker (jetAug R κ (m + 1)) := by
    intro a ha
    have ha' : jetTruncR R κ m a = 0 := ha
    change jetAug R κ (m + 1) a = 0
    rw [← jetAug_comp_jetTruncR, AlgHom.comp_apply, ha', map_zero]
  refine ⟨m + 1 + 1, ?_⟩
  rw [Ideal.zero_eq_bot, ← le_bot_iff, ← ker_jetAug_pow (R := R) κ (m + 1)]
  exact Ideal.pow_right_mono hle _

theorem jetZeroR_comp_jetTruncR (κ : Type) (m : ℕ) :
    (jetZeroR R κ m).comp (jetTruncR R κ m) = jetZeroR R κ (m + 1) :=
  jet_ext fun _ => rfl

theorem zR_zero_eq_zero {κ : Type} (j : κ) : zR (R := R) 0 j = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (by
    rw [zero_add, pow_one]
    exact Ideal.subset_span ⟨j, rfl⟩)

theorem zR_one_mul_self {κ : Type} (j : κ) : zR (R := R) 1 j * zR (R := R) 1 j = 0 :=
  mul_eq_zero_of_sq (ker_jetAug_pow (R := R) κ 1) (zR_mem_ker 1 j) (zR_mem_ker 1 j)

end GlobalTheory.JetPoint

namespace GlobalTheory

open SqZero JetPoint

theorem exists_jetPoints_of_isLieBasis :
    ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v → ∃ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) ∧ (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) ∧ (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) := by
  intro R _ G _ _ hG d v hv
  have htan : ∀ i, IsTan (v i) := fun i => (isTan_iff _).2 (hv.1 i)
  choose L hL using fun m => ptsMap_surjective_of_isNilpotent (G := G) hv (jetTruncR R (Fin d) m)
    (jetTruncR_surjective _ m) (ker_jetTruncR_isNilpotent _ m)
  let x₁ : sp (R₀ := R) (JetR R (Fin d) 1) ⟶ G :=
    lieExp v (fun j => zR (R := R) 1 j) zR_one_mul_self
  let y : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) (m + 1)) ⟶ G :=
    fun m => Nat.rec (motive := fun m => sp (R₀ := R) (JetR R (Fin d) (m + 1)) ⟶ G) x₁
      (fun k z => L (k + 1) z) m
  let x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G :=
    fun m => Nat.casesOn (motive := fun m => sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) m 1 y
  have h₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m := by
    rintro (_ | m)
    · change spMap _ ≫ lieExp v _ _ = 1
      rw [comp_lieExp, lieExp]
      exact Finset.prod_eq_one fun i _ => epsTo_zero_comp (htan i) _ (zR_zero_eq_zero i) _
    · exact hL (m + 1) (y m)
  refine ⟨x, h₁, fun m => ?_, fun j => ?_⟩
  · induction m with
    | zero => exact comp_one' _
    | succ m ih => rw [← jetZeroR_comp_jetTruncR, ← spMap_comp, Category.assoc, h₁, ih]
  · change spMap _ ≫ lieExp v _ _ = _
    rw [comp_lieExp, lieExp, Finset.prod_eq_single j]
    · have : ∀ (t : DualNumber R) (ht : t * t = 0), t = DualNumber.eps →
          epsTo R t ht = AlgHom.id R _ := fun t ht e =>
        DualNumber.algHom_ext (by rw [epsTo_eps, e]; rfl)
      rw [this _ _ (by rw [dualLift_zR, Pi.single_eq_same]; rfl), spMap_id]
      exact Category.id_comp _
    · intro i _ hi
      exact epsTo_zero_comp (htan i) _
        (by rw [dualLift_zR, Pi.single_eq_of_ne hi, TrivSqZeroExt.inr_zero]) _
    · simp

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetChartCoordinatesUniqueCommGroup

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open SqZero

theorem jetCoord_eq_of_sub_mem {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (hG : Smooth G.hom) {d : ℕ} {v : Fin d → (epsR R ⟶ G)}
    (hv : IsLieBasis v) {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G}
    (hx₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m)
    (hx₂ : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1)
    (hx₃ : ∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j)
    {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (J : Ideal A)
    (hJ : J * RingHom.ker aug = ⊥) (hJ' : J ≤ RingHom.ker aug) {m : ℕ}
    (ψ ψ' : JetR R (Fin d) m →ₐ[R] A) (hψ : aug.comp ψ = jetAug R (Fin d) m)
    (hψ' : aug.comp ψ' = jetAug R (Fin d) m) (hδ : ∀ j, ψ' (zR m j) - ψ (zR m j) ∈ J)
    (h : spMap ψ ≫ x m = spMap ψ' ≫ x m) : ψ = ψ' := by
  have hJ2 : J ^ 2 = ⊥ := by
    rw [← le_bot_iff, pow_two, ← hJ]
    exact Ideal.mul_mono_right hJ'
  let c : Fin d → J := fun j => ⟨_, hδ j⟩
  have hc : ∀ j, (c j : A) * (c j : A) = 0 := fun j => mul_eq_zero_of_sq hJ2 (c j).2 (c j).2
  have he : ∀ j, epsTo R (c j : A) (hc j) (TrivSqZeroExt.inr 1) = c j := fun j => epsTo_eps _ _
  have key := GlobalTheory.T.jetPoint_add_sqZero_eq_prod_mul_tangent R G hG d v hv x hx₁ hx₂ hx₃ A aug J hJ hJ' m ψ ψ' hψ hψ'
    (fun j => epsTo R (c j : A) (hc j)) (fun j => by rw [he]; exact (c j).2)
    (fun j => by rw [he]; exact (add_sub_cancel _ _).symm)
  rw [← h] at key
  have h1 : lieExp v (fun j => (c j : A)) hc = 1 := mul_eq_right.1 key.symm
  have h0 : c = 0 := by
    apply (expHom_bijective hv hJ2).1
    rw [map_zero]
    exact congrArg Additive.ofMul (Subtype.ext h1)
  refine jet_ext fun j => ?_
  have : ψ' (zR m j) - ψ (zR m j) = 0 := congrArg Subtype.val (congrFun h0 j)
  exact (sub_eq_zero.1 this).symm

theorem jetCoord_unique (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] (hG : Smooth G.hom) (d : ℕ) (v : Fin d → (epsR R ⟶ G)) (hv : IsLieBasis v)
    (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G)
    (hx₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m)
    (hx₂ : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1)
    (hx₃ : ∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j)
    (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ)
    (hN : (RingHom.ker aug) ^ (m + 1) = ⊥) (ψ ψ' : JetR R (Fin d) m →ₐ[R] A)
    (hψ : aug.comp ψ = jetAug R (Fin d) m) (hψ' : aug.comp ψ' = jetAug R (Fin d) m)
    (h : spMap ψ ≫ x m = spMap ψ' ≫ x m) : ψ = ψ' := by
  set N := RingHom.ker aug with hNdef
  have main : ∀ k j, ψ' (zR m j) - ψ (zR m j) ∈ N ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro j
      rw [zero_add, pow_one, hNdef, RingHom.mem_ker, map_sub, ← AlgHom.comp_apply,
        ← AlgHom.comp_apply, hψ, hψ', sub_self]
    | succ k ih =>
      let q : A →ₐ[R] A ⧸ N ^ (k + 1 + 1) := Ideal.Quotient.mkₐ R _
      have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective R _
      let aug' : (A ⧸ N ^ (k + 1 + 1)) →ₐ[R] R := Ideal.Quotient.liftₐ _ aug
        (fun a ha => Ideal.pow_le_self (by omega) ha)
      have haug : aug'.comp q = aug := AlgHom.ext fun _ => rfl
      have hker : RingHom.ker aug' = N.map q := by
        apply le_antisymm
        · intro a ha
          obtain ⟨b, rfl⟩ := hq a
          exact Ideal.mem_map_of_mem _ ha
        · exact Ideal.map_le_iff_le_comap.2 fun a ha => ha
      have e := jetCoord_eq_of_sub_mem hG hv hx₁ hx₂ hx₃ aug' ((N ^ (k + 1)).map q)
        (by rw [hker, ← Ideal.map_mul, ← pow_succ]; exact Ideal.map_quotient_self _)
        (by rw [hker]; exact Ideal.map_mono (Ideal.pow_le_self (by omega)))
        (q.comp ψ) (q.comp ψ') (by rw [← AlgHom.comp_assoc, haug, hψ])
        (by rw [← AlgHom.comp_assoc, haug, hψ'])
        (fun j => by
          rw [AlgHom.comp_apply, AlgHom.comp_apply, ← map_sub]
          exact Ideal.mem_map_of_mem _ (ih j))
        (by rw [← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc, h])
      intro j
      exact Ideal.Quotient.eq.1 (AlgHom.congr_fun e (zR m j)).symm
  refine jet_ext fun j => ?_
  have := main m j
  rw [hN, Ideal.mem_bot] at this
  exact (sub_eq_zero.1 this).symm

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetChartCoordinatesUniqueCommGroupStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.jetChart_coordinates_unique_commGroup : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v → ∀ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) → (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) → (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) → ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ), (RingHom.ker aug) ^ (m + 1) = ⊥ → ∀ ψ ψ' : JetR R (Fin d) m →ₐ[R] A, aug.comp ψ = jetAug R (Fin d) m → aug.comp ψ' = jetAug R (Fin d) m → spMap ψ ≫ x m = spMap ψ' ≫ x m → ψ = ψ' := by
  first | exact @GlobalTheory.jetCoord_unique | exact GlobalTheory.jetCoord_unique | (intros; apply GlobalTheory.jetCoord_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsUnivChartOfIsLieBasis

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_isUnivChart_of_isLieBasis :
    ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G],
      Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v →
      ∃ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), IsUnivChart G d x ∧
        (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) := by
  intro R _ G _ _ hG d v hv
  obtain ⟨x, h₁, h₂, h₃⟩ := GlobalTheory.exists_jetPoints_of_isLieBasis R G hG d v hv
  refine ⟨x, ⟨h₁, h₂, ?_⟩, h₃⟩
  intro A _ _ aug m hm y hy
  obtain ⟨ψ, hψ, hyψ⟩ := GlobalTheory.T.exists_jetChart_coordinates_nilpotent R G hG d v hv x h₁ h₂ h₃ A aug m hm y hy
  refine ⟨ψ, ⟨hψ, hyψ⟩, ?_⟩
  rintro ψ' ⟨hψ', hyψ'⟩
  exact GlobalTheory.T.jetChart_coordinates_unique_commGroup R G hG d v hv x h₁ h₂ h₃ A aug m hm ψ' ψ hψ' hψ (hyψ'.symm.trans hyψ)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsChartGOfBasis

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (FGLaw)
open scoped CategoryTheory.Obj

namespace GlobalTheory.ChartData

open GlobalTheory.ChartJet (Q gen sq_gen)

theorem mk_psTrunc {S : Type} [CommRing S] {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    ChartJet.pj m f = Ideal.Quotient.mk _ (psTrunc m f - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m f))) := by
  have co : ∀ e : κ →₀ ℕ, e.degree < m + 1 → (psTrunc m f).coeff e = MvPowerSeries.coeff e f := fun e he => by
    have hm : e ∈ degLE m := Finset.mem_filter.2 ⟨Finset.mem_image.2
      ⟨fun i => ⟨e i, lt_of_le_of_lt (Finsupp.le_degree i e) he⟩, Finset.mem_univ _, by ext i; simp⟩, Nat.le_of_lt_succ he⟩
    rw [psTrunc, MvPolynomial.coeff_sum, Finset.sum_eq_single e (fun b _ hb => by rw [MvPolynomial.coeff_monomial, if_neg hb])
      (fun h => absurd hm h), MvPolynomial.coeff_monomial, if_pos rfl]
  have c0 : MvPolynomial.constantCoeff (psTrunc m f) = 0 := (co 0 (by simp)).trans hf
  rw [c0, map_zero, sub_zero]
  exact ChartJet.pj_eq_mk.2 fun e he => (co e he).symm

theorem jetMap_zR {S : Type} [CommRing S] {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (h) (s : κ) :
    (jetMap φ h : Jet S κ m →ₐ[S] Jet S κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X s)) = Ideal.Quotient.mk _ (φ s) := by
  show Ideal.Quotient.mkₐ S _ (MvPolynomial.aeval φ (MvPolynomial.X s)) = _
  rw [MvPolynomial.aeval_X]; rfl

theorem subst_zR {S : Type} [CommRing S] {d n : ℕ} (m : ℕ) (p : Q S d n) (s : Fin 1 × Fin d) :
    jetSubstP m (fun s : Fin 1 × Fin d => psTrunc m (p.1 s.2)) (Chart.zR m s) = ChartJet.pj m (p.1 s.2) :=
  (jetMap_zR m _ _ s).trans (mk_psTrunc m _ (p.2 _)).symm

theorem copy_zR {S : Type} [CommRing S] {d n : ℕ} (m : ℕ) (i : Fin n) (s : Fin 1 × Fin d) :
    jetCopy (S := S) d m i (Chart.zR m s) = ChartJet.pj m ((gen i : Q S d n).1 s.2) :=
  (jetMap_zR m _ _ s).trans (ChartJet.pj_X m (i, s.2)).symm



theorem exists_isChartG_of_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)), (∀ ℓ, IsTanAtG t x0 (tg ℓ)) → (∀ w, IsTanAtG t x0 w → ∃! a : κ → S, IsCombAtG t x0 (m := Fintype.card κ) (fun i => tg ((Fintype.equivFin κ).symm i)) (fun i => a ((Fintype.equivFin κ).symm i)) w) → ∃ (d : ℕ) (G : FGLaw S d) (A : Germ.OAct (𝓞 E) G) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), d = Fintype.card κ ∧ (∀ ℓ (j : Fin d), uvec ℓ j = if (j : ℕ) = (Fintype.equivFin κ ℓ : ℕ) then 1 else 0) ∧ IsChartG t x0 d G.F A.act tg uvec x := by
  classical
  intro E _ _ _ H X0 t S _ x0 κ _ tg htan hb
  have hp := isGrpPullback_pullback t.G x0
  have := t.semi.smooth
  have : Smooth ((Over.pullback x0).obj t.G).hom :=
    smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  let φ := pullback.fst t.G.hom x0
  let up : ∀ w : Sp (DualNumber S) ⟶ t.G.left, w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x0 →
      (epsR S ⟶ (Over.pullback x0).obj t.G) := fun w h => Over.homMk (pullback.lift w _ h) (pullback.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ φ = w := fun w h => pullback.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp S)} {u v : T ⟶ (Over.pullback x0).obj t.G}, u.left ≫ φ = v.left ≫ φ → u = v := fun h =>
    Over.OverMorphism.ext (pullback.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp S), (1 : T ⟶ (Over.pullback x0).obj t.G).left ≫ φ = (1 : Over.mk (T.hom ≫ x0) ⟶ t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))
  have tan : ∀ w : epsR S ⟶ (Over.pullback x0).obj t.G, IsTangent w ↔ IsTanAtG t x0 (w.left ≫ φ) := fun w => by
    have e : (1 : Chart.sp (R₀ := S) S ⟶ (Over.pullback x0).obj t.G).left ≫ φ = (1 : Over.mk x0 ⟶ t.G).left :=
      (one _).trans (congrArg (· ≫ (η[t.G]).left) (show Spec.map (CommRingCat.ofHom (RingHom.id S)) ≫ x0 = x0 by simp))
    rw [← Chart.isTan_iff]
    refine ⟨fun h => ⟨Over.w (pushPt hp.1.w w), ?_⟩, fun h => inj ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ φ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEpsG x0 ⟶ t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → S) (v : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)) w,
      IsLieComb c v w ↔ IsCombAtG t x0 (fun i => (v i).left ≫ φ) c (w.left ≫ φ) := fun c v w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => pushPt hp.1.w (u i), fun i => (congrArg (· ≫ φ) (hu i)).trans (Category.assoc _ _ _), (pr u).symm⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => up (u i).left (Over.w _), fun i => pullback.hom_ext ?_ ?_, inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (Over.w (Chart.spMap (Chart.scaleD (c i)))).symm
      · have : u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEpsG x0 ⟶ t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEpsG x0 ⟶ t.G) => (List.ofFn q).prod.left) this
  let e := Fintype.equivFin κ
  let v : Fin (Fintype.card κ) → (epsR S ⟶ (Over.pullback x0).obj t.G) := fun i => up (tg (e.symm i)) (htan _).1
  have hv : (fun i => (v i).left ≫ φ) = fun i => tg (e.symm i) := funext fun i => hup _ _
  have hB : IsLieBasis v := ⟨fun i => (tan _).2 (by rw [hup]; exact htan _), fun w hw => by
    obtain ⟨a, ha, hu⟩ := hb _ ((tan w).1 hw)
    refine ⟨fun i => a (e.symm i), (comb _ _ _).2 (hv ▸ ha), fun c hc => ?_⟩
    have := hu (fun l => c (e l)) (by simpa only [e, Equiv.apply_symm_apply] using hv ▸ (comb _ _ _).1 hc)
    funext i; rw [← this]; simp⟩
  obtain ⟨x, hx, hxv'⟩ := GlobalTheory.exists_isUnivChart_of_isLieBasis S ((Over.pullback x0).obj t.G) this _ v hB
  have hxv := fun j => (hxv' j).symm
  obtain ⟨F, A, hF, hA⟩ := ChartJet.exists_series hx (OAct.pullback x0 t.G t.act)
  have sub : ∀ {n} m (p : Q S (Fintype.card κ) n) (g : Jet S (Fin 1 × Fin (Fintype.card κ)) m →ₐ[S] Jet S (Fin n × _) m),
      (∀ s, g (Chart.zR m s) = ChartJet.pj m (p.1 s.2)) →
      homAt x0 g ≫ pushPt hp.1.w (ChartJet.ptJ x m (gen 0)) = pushPt hp.1.w (ChartJet.ptJ x m p) := fun m p g hg => by
    have e₁ : g = ChartJet.jQ m ![p] := Chart.jet_ext fun s => (hg s).trans (by
      obtain ⟨i, j⟩ := s
      obtain rfl := Subsingleton.elim i 0
      exact (ChartJet.jS_zR m (fun s : Fin 1 × _ => ((![p] : Fin 1 → _) s.1).1 s.2) (fun s => ((![p] : Fin 1 → _) s.1).2 s.2)
        (0, j)).symm)
    have e₂ := ChartJet.ptJ_sq x m ![p] (gen 0)
    rw [sq_gen, ← e₁] at e₂
    exact Over.OverMorphism.ext ((Category.assoc _ _ _).symm.trans (congrArg (fun q => q.left ≫ φ) e₂))
  have sp := fun {n} m (p : Q S (Fintype.card κ) n) => subst_zR m p
  have cp : ∀ {n} m (i : Fin n), jptG t x0 _ (fun m => pushPt hp.1.w (ChartJet.ptJ x m (gen 0))) m i =
      pushPt hp.1.w (ChartJet.ptJ x m (gen i)) := fun m i => sub m (gen i) _ (copy_zR m i)
  refine ⟨_, F, A, fun l => Pi.single (e l) 1, fun m => pushPt hp.1.w (ChartJet.ptJ x m (gen 0)), rfl,
    fun l j => by simp only [Pi.single_apply, Fin.ext_iff, e], fun m => ?_, fun m => ?_,
    fun m => ?_, fun m a => ?_, fun l => ?_, fun w => ?_⟩
  · exact Over.OverMorphism.ext ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q.left ≫ φ) (ChartJet.ptJ_aug hx m (gen 0))).trans (one _)))
  · exact Over.OverMorphism.ext ((Category.assoc _ _ _).symm.trans
      (congrArg (fun q => q.left ≫ φ) (ChartJet.ptJ_trunc hx m (gen 0))))
  · rw [cp, cp]
    exact (sub m ⟨F.F, F.const⟩ _ (sp m _)).trans ((congrArg _ (hF m)).trans (map_mul (pushHom hp _) _ _))
  · refine Eq.trans ?_ ((sub m ⟨A.act a, A.const a⟩ _ (sp m _)).trans (congrArg _ (hA a m))).symm
    exact Over.OverMorphism.ext ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (pullback.lift_fst _ _ _ : ((OAct.pullback x0 t.G t.act).act a).left ≫ φ = φ ≫ (t.act.act a).left).symm).trans
      (Category.assoc _ _ _).symm))
  · have h := (comb _ _ _).1 (ChartJet.comb_single hx hxv (e l))
    rw [hup, Equiv.symm_apply_apply] at h
    convert h using 2 with j
    let T : Chart.JetR S (Fin 1 × Fin (Fintype.card κ)) 1 →ₐ[S] DualNumber S := (jetTan ((0 : Fin 1), j) :
      Jet S (Fin 1 × Fin (Fintype.card κ)) (0 + 1) →ₐ[S] DualNumber S)
    have e₁ : T.comp (ChartJet.jP 1 (gen 0 : Q S _ 1)) = Chart.dualLift (Pi.single j 1) := Chart.jet_ext fun i => by
      rw [AlgHom.comp_apply, ChartJet.jP_zR, Chart.dualLift_zR]
      refine (congrArg T (ChartJet.pj_X 1 ((0 : Fin 1), i))).trans ?_
      show MvPolynomial.aeval (fun i => if i = ((0 : Fin 1), j) then (DualNumber.eps : DualNumber S) else 0)
        (MvPolynomial.X ((0 : Fin 1), i)) = _
      rw [MvPolynomial.aeval_X]
      by_cases hij : i = j
      · subst hij; rw [if_pos rfl, Pi.single_eq_same]; rfl
      · rw [if_neg (fun h => hij (Prod.ext_iff.1 h).2), Pi.single_eq_of_ne hij, TrivSqZeroExt.inr_zero]
    have e₂ : Chart.spMap T ≫ ChartJet.ptJ x 1 (gen 0) = v j := by
      rw [hxv, ← e₁, ← Chart.spMap_comp, Category.assoc]; rfl
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun q => q.left ≫ φ) e₂)
  · refine ⟨fun l => w (e l), fun j => ?_, fun a ha => funext fun l => ?_⟩
    · rw [Finset.sum_eq_single (e.symm j) (fun b _ hb => by
        rw [Pi.single_eq_of_ne (fun h => hb (by rw [h, Equiv.symm_apply_apply])), mul_zero]) (by simp)]
      simp
    · rw [← ha, Finset.sum_eq_single l (fun b _ hb => by
        rw [Pi.single_eq_of_ne (fun h => hb (e.injective h).symm), mul_zero]) (by simp)]
      simp

end GlobalTheory.ChartData
end
end
end
