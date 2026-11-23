module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupToPadicPointsDegreeOneEqUnitaryPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQrOneBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ClassFieldTheory.LocalClassField.HerbrandA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMapInjectivity
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgEquivExtendingPadicAlgCl

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open scoped TensorProduct
open scoped Classical

namespace GlobalTheory.LKTrip

theorem exists_algEquiv_extending_padicAlgCl {p : ℕ} [Fact p.Prime]
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (φ : E →ₐ[ℚ_[p]] PadicAlgCl p) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ x : E, σ x = φ x := by
  refine ⟨AlgEquiv.ofBijective (φ.liftNormal (PadicAlgCl p))
    (Algebra.IsAlgebraic.algHom_bijective _), fun x => ?_⟩
  exact φ.liftNormal_commutes (PadicAlgCl p) x

theorem HTGroup.sum_finrank_Fw_eq_finrank_Kq {p : ℕ} [Fact p.Prime] (G : HTGroup p) :
    ∑ w : Fin G.m, Module.finrank ℚ_[p] (G.Fw w) = Module.finrank G.Kq G.F := by
  letI : Algebra G.Kq (PadicAlgCl p) := ((algebraMap ℚ_[p] (PadicAlgCl p)).comp G.u).toAlgebra
  haveI : FiniteDimensional G.Kq G.F := Module.Finite.of_restrictScalars_finite ℚ G.Kq G.F
  let f : (Σ w : Fin G.m, (G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p)) → (G.F →ₐ[G.Kq] PadicAlgCl p) := fun a =>
    { (a.2 : G.Fw a.1 →+* PadicAlgCl p).comp (G.embW a.1) with
      commutes' := fun x => by
        have h : G.embW a.1 (x : G.F) = algebraMap ℚ_[p] (G.Fw a.1) (G.u x) :=
          Subtype.ext (G.emb_over a.1 x)
        change a.2 (G.embW a.1 (x : G.F)) = algebraMap ℚ_[p] (PadicAlgCl p) (G.u x)
        rw [h, AlgHom.commutes] }
  have hf : ∀ a x, f a x = a.2 (G.embW a.1 x) := fun _ _ => rfl
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨w, φ⟩ ⟨w', ψ⟩ h
      have h' : ∀ x, φ (G.embW w x) = ψ (G.embW w' x) := fun x => by
        rw [← hf ⟨w, φ⟩, h, hf]
      obtain ⟨σ, hσ⟩ := exists_algEquiv_extending_padicAlgCl _ φ
      obtain ⟨τ, hτ⟩ := exists_algEquiv_extending_padicAlgCl _ ψ
      obtain rfl : w = w' := by
        refine G.emb_inj w w' (σ.trans τ.symm) (RingHom.ext fun x => ?_)
        change τ.symm (σ (G.emb w x)) = G.emb w' x
        rw [AlgEquiv.symm_apply_eq]
        exact (hσ (G.embW w x)).trans ((h' x).trans (hτ (G.embW w' x)).symm)
      obtain rfl : φ = ψ := by
        refine IntermediateField.adjoin_algHom_ext ℚ_[p] ?_
        rintro _ ⟨x, rfl⟩
        exact h' x
      rfl
    · intro τ
      obtain ⟨w, σ, h⟩ := G.emb_all (τ : G.F →+* PadicAlgCl p) (fun x => τ.commutes x)
      refine ⟨⟨w, (σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p).comp (G.Fw w).val⟩, AlgHom.ext fun x => ?_⟩
      exact (DFunLike.congr_fun h x).symm
  have hc := Fintype.card_of_bijective hbij
  rw [Fintype.card_sigma, AlgHom.card] at hc
  simpa only [AlgHom.card] using hc

theorem HTGroup.two_mul_sum_finrank_Fw (p : ℕ) [Fact p.Prime] (G : HTGroup p) :
    2 * ∑ w : Fin G.m, Module.finrank ℚ_[p] (G.Fw w) = Module.finrank ℚ G.F := by
  rw [G.sum_finrank_Fw_eq_finrank_Kq, ← G.hKq.1]
  exact Module.finrank_mul_finrank ℚ G.Kq G.F

end GlobalTheory.LKTrip
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicPointsSimilitudeGLProductBijective

section

@[expose] public section

open GlobalTheory.LKTrip
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LKTrip.HTGroup.LocPBij

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

theorem starT_starT (x : ℚ_[p] ⊗[ℚ] G.C) :
    (starT G.star ℚ_[p] (starT G.star ℚ_[p] x).unop).unop = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => rw [starT_tmul, starT_tmul, G.star_star]
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]

theorem starT_algebraMap (a : ℚ_[p]) :
    (starT G.star ℚ_[p] (algebraMap ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) a)).unop = algebraMap ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) a := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, starT_tmul, map_one,
    MulOpposite.unop_one]

theorem starT_mul (x y : ℚ_[p] ⊗[ℚ] G.C) :
    (starT G.star ℚ_[p] (x * y)).unop = (starT G.star ℚ_[p] y).unop * (starT G.star ℚ_[p] x).unop := by
  rw [map_mul, MulOpposite.unop_mul]

def starL : ℚ_[p] ⊗[ℚ] G.C →ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] G.C where
  toFun x := (starT G.star ℚ_[p] x).unop
  map_add' x y := by rw [map_add (f := _), MulOpposite.unop_add]
  map_smul' a x := by
    rw [Algebra.smul_def, starT_mul, starT_algebraMap, RingHom.id_apply, Algebra.smul_def]
    exact (Algebra.commutes _ _).symm

def psiL : ℚ_[p] ⊗[ℚ] G.C →ₗ[ℚ_[p]]
    ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) × ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) :=
  LinearMap.prod (LinearMap.pi fun i => (G.locW i).toLinearMap)
    ((LinearMap.pi fun i => (G.locW i).toLinearMap).comp (starL G))

theorem psiL_injective : Function.Injective (psiL G) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  exact GlobalTheory.HTGroupLocInj.locW_inj G x (fun i => congrFun (congrArg Prod.fst hx) i)
    (fun i => congrFun (congrArg Prod.snd hx) i)

theorem finrank_eq : Module.finrank ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) = Module.finrank ℚ_[p]
    (((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) × ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i))) := by
  rw [Module.finrank_baseChange, ← Module.finrank_mul_finrank ℚ G.F G.C, G.rankC, Module.finrank_prod,
    Module.finrank_pi_fintype]
  simp only [Module.finrank_matrix, Fintype.card_fin]
  rw [← HTGroup.two_mul_sum_finrank_Fw p G, ← Finset.mul_sum]
  ring

theorem psiL_bijective : Function.Bijective (psiL G) := by
  haveI : ∀ i, FiniteDimensional ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) := fun i => inferInstance
  exact ⟨psiL_injective G,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (finrank_eq G)).1 (psiL_injective G)⟩

end GlobalTheory.LKTrip.HTGroup.LocPBij

theorem GlobalTheory.LKTrip.HTGroup.bijective_locP : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Function.Bijective G.localization₂ := by
  intro p _ G
  have key : ∀ d : ℚ_[p] ⊗[ℚ] G.C, (starT G.star ℚ_[p] d).unop = d → (∀ i, G.locW i d = 0) → d = 0 :=
    fun d hd h0 => GlobalTheory.HTGroupLocInj.locW_inj G d h0 (fun i => by rw [hd]; exact h0 i)
  constructor
  · rintro ⟨⟨x, c⟩, hx⟩ ⟨⟨y, d⟩, hy⟩ h
    have hx' : (x : ℚ_[p] ⊗[ℚ] G.C) * (starT G.star ℚ_[p] x).unop = algebraMap ℚ_[p] _ (c : ℚ_[p]) := hx
    have hy' : (y : ℚ_[p] ⊗[ℚ] G.C) * (starT G.star ℚ_[p] y).unop = algebraMap ℚ_[p] _ (d : ℚ_[p]) := hy
    have hc : c = d := congrArg Prod.fst h
    subst hc
    have hu := fun i => congrFun (congrArg Prod.snd h) i
    have sx : (starT G.star ℚ_[p] x).unop = ((x⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) * algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← hx', ← mul_assoc, Units.inv_mul, one_mul]
    have sy : (starT G.star ℚ_[p] y).unop = ((y⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) * algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← hy', ← mul_assoc, Units.inv_mul, one_mul]
    have hw : ∀ i, G.locW i x = G.locW i y := fun i => congrArg Units.val (hu i)
    have hwi : ∀ i, G.locW i ((x⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) = G.locW i ((y⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) := by
      intro i
      have := congrArg (fun u => ((u⁻¹ : (Matrix (Fin G.n) (Fin G.n) (G.Fw i))ˣ) : Matrix (Fin G.n) (Fin G.n) (G.Fw i))) (hu i)
      exact this
    have hxy : x = y := by
      apply Units.ext
      apply GlobalTheory.LKTrip.HTGroup.LocPBij.psiL_injective G
      refine Prod.ext (funext hw) (funext fun i => ?_)
      show G.locW i (starT G.star ℚ_[p] x).unop = G.locW i (starT G.star ℚ_[p] y).unop
      rw [sx, sy, map_mul, map_mul, hwi]
    subst hxy
    rfl
  · rintro ⟨c, a⟩
    obtain ⟨x, hx⟩ := (GlobalTheory.LKTrip.HTGroup.LocPBij.psiL_bijective G).2
      (fun i => ((a i : GL (Fin G.n) (G.Fw i)) : Matrix (Fin G.n) (Fin G.n) (G.Fw i)),
       fun i => algebraMap ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) (c : ℚ_[p]) *
        (((a i)⁻¹ : GL (Fin G.n) (G.Fw i)) : Matrix (Fin G.n) (Fin G.n) (G.Fw i)))
    have h1 : ∀ i, G.locW i x = a i := fun i => congrFun (congrArg Prod.fst hx) i
    have h2 : ∀ i, G.locW i (starT G.star ℚ_[p] x).unop = algebraMap ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) (c : ℚ_[p]) *
        (((a i)⁻¹ : GL (Fin G.n) (G.Fw i)) : Matrix (Fin G.n) (Fin G.n) (G.Fw i)) := fun i => congrFun (congrArg Prod.snd hx) i
    have hyy := GlobalTheory.LKTrip.HTGroup.LocPBij.starT_starT G x
    have hxy : x * (starT G.star ℚ_[p] x).unop = algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← sub_eq_zero]
      apply key
      · rw [map_sub, MulOpposite.unop_sub, GlobalTheory.LKTrip.HTGroup.LocPBij.starT_mul, hyy,
          GlobalTheory.LKTrip.HTGroup.LocPBij.starT_algebraMap]
      · intro i
        rw [map_sub, map_mul, h1, h2, AlgHom.commutes, Algebra.left_comm, Units.mul_inv, mul_one, sub_self]
    have hyx : (starT G.star ℚ_[p] x).unop * x = algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← sub_eq_zero]
      apply key
      · rw [map_sub, MulOpposite.unop_sub, GlobalTheory.LKTrip.HTGroup.LocPBij.starT_mul, hyy,
          GlobalTheory.LKTrip.HTGroup.LocPBij.starT_algebraMap]
      · intro i
        rw [map_sub, map_mul, h1, h2, AlgHom.commutes, mul_assoc, Units.inv_mul, mul_one, sub_self]
    let u : (ℚ_[p] ⊗[ℚ] G.C)ˣ := ⟨x, algebraMap ℚ_[p] _ ((c⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * (starT G.star ℚ_[p] x).unop,
      by rw [Algebra.left_comm, hxy, ← map_mul, Units.inv_mul, map_one],
      by rw [mul_assoc, hyx, ← map_mul, Units.inv_mul, map_one]⟩
    refine ⟨⟨(u, c), hxy⟩, Prod.ext rfl (funext fun i => Units.ext (h1 i))⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicPointsSimilitudeGLProductBijectiveStatement

section

@[expose] public section

open GlobalTheory.LKTrip

theorem _root_.GlobalTheory.T.padicPoints_similitude_GL_product_bijective : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Function.Bijective G.localization₂ := by
  first | (exact @GlobalTheory.LKTrip.HTGroup.bijective_locP) | (exact GlobalTheory.LKTrip.HTGroup.bijective_locP) | (intros; apply GlobalTheory.LKTrip.HTGroup.bijective_locP  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryCentralizerOfCommutePadicPointsSpli

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

theorem GlobalTheory.TorCls.centraliser_at_p : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β → ∀ (y₀ : grp G β) (c : Gr G 1), c * toP1 G β y₀ = toP1 G β y₀ * c → ∃ z : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ, InT G ℚ_[p] β (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) z ∧ psiP G z = c :=
  fun p _ G β hβ y₀ c hc => GlobalTheory.TorCls.AtP.atp_of_bijective G (GlobalTheory.T.padicPoints_similitude_GL_product_bijective p G) β hβ y₀ c hc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryCentralizerOfCommutePadicPointsSpliStatement

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.exists_unitaryCentralizer_of_commute_padicPoints_split : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β → ∀ (y₀ : grp G β) (c : Gr G 1), c * toP1 G β y₀ = toP1 G β y₀ * c → ∃ z : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ, InT G ℚ_[p] β (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) z ∧ psiP G z = c := by
  first | exact @GlobalTheory.TorCls.centraliser_at_p | exact GlobalTheory.TorCls.centraliser_at_p | (intros; apply GlobalTheory.TorCls.centraliser_at_p <;> assumption)
end
end
