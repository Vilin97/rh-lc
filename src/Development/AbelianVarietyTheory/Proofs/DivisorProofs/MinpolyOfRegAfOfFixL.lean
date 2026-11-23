module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHaarMeasureScaling
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.FieldTheory.Perfect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqDegCentralSimpleCommCentraliseStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeSignatureOnePreservesPosDefFormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacter

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalEqZeroOfSqEqZeroOfPosDefSimilitude

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.SimNormSq

open Polynomial

theorem commute_aeval_of_commute {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {x y : A} (h : Commute y x) (p : R[X]) : Commute y (aeval x p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_right hq
  | monomial n a =>
    rw [aeval_monomial]; exact (Algebra.commute_algebraMap_right a y).mul_right (h.pow_right n)

theorem eq_zero_of_conjTranspose_mul_mul_eq_zero {n : ℕ} {H A : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosDef) (h : Aᴴ * H * A = 0) : A = 0 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [Matrix.zero_mulVec]
  by_contra hne
  have hpos := hH.dotProduct_mulVec_pos hne
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h,
    Matrix.zero_mulVec, dotProduct_zero] at hpos
  exact lt_irrefl _ hpos

end GlobalTheory.SimNormSq

namespace GlobalTheory

open Polynomial

theorem aeval_eq_zero_of_mul_self_eq_zero_of_similitude :
    ∀ (n : ℕ) (H M : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), H.PosDef → 0 < s →
      Mᴴ * H * M = (s : ℂ) • H → ∀ P : Polynomial ℂ,
        Polynomial.aeval M P * Polynomial.aeval M P = 0 → Polynomial.aeval M P = 0 := by
  intro n H M s hH hs hM P hP
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hHinv : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hdet
  have hHinv' : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hdet
  have hHh : Hᴴ = H := hH.1
  have hHih : (H⁻¹)ᴴ = H⁻¹ := by rw [conjTranspose_nonsing_inv, hHh]
  have hc : ∀ A : Matrix (Fin n) (Fin n) ℂ, H⁻¹ * (H * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hHinv, Matrix.one_mul]
  have hc' : ∀ A : Matrix (Fin n) (Fin n) ℂ, H * (H⁻¹ * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hHinv', Matrix.one_mul]
  have hM' : Mᴴ * (H * M) = (s : ℂ) • H := by rw [← Matrix.mul_assoc]; exact hM
  set D := H⁻¹ * Mᴴ * H with hD
  have hDM : D * M = (s : ℂ) • 1 := by
    rw [hD]; simp only [Matrix.mul_assoc]; rw [hM', Matrix.mul_smul, hHinv]
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hMD : M * D = (s : ℂ) • 1 := by
    have h1 : ((s : ℂ)⁻¹ • D) * M = 1 := by
      rw [Matrix.smul_mul, hDM, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    have h2 := mul_eq_one_comm.mp h1
    rw [Matrix.mul_smul] at h2
    calc M * D = (s : ℂ) • ((s : ℂ)⁻¹ • (M * D)) := by
          rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]
      _ = (s : ℂ) • 1 := by rw [h2]
  have hcomm : Commute D M := by
    show D * M = M * D
    rw [hDM, hMD]
  have hall : ∀ Y, Commute Y M → Commute Y (aeval M P) := fun Y hY =>
    SimNormSq.commute_aeval_of_commute hY P
  have hDW := hall D hcomm
  generalize hW : aeval M P = W at hP hDW ⊢
  have key : Commute (H⁻¹ * Wᴴ * H) M := by
    have h1 : Wᴴ * (H * (M * H⁻¹)) = H * (M * (H⁻¹ * Wᴴ)) := by
      have h0 := congrArg conjTranspose hDW.eq
      simp only [hD, conjTranspose_mul, conjTranspose_conjTranspose, hHh, hHih,
        Matrix.mul_assoc] at h0
      exact h0
    show H⁻¹ * Wᴴ * H * M = M * (H⁻¹ * Wᴴ * H)
    calc H⁻¹ * Wᴴ * H * M = H⁻¹ * (Wᴴ * (H * (M * H⁻¹))) * H := by
          simp only [Matrix.mul_assoc, hHinv, Matrix.mul_one]
      _ = H⁻¹ * (H * (M * (H⁻¹ * Wᴴ))) * H := by rw [h1]
      _ = M * (H⁻¹ * Wᴴ * H) := by
          simp only [Matrix.mul_assoc, hc]
  have hXW : Commute (H⁻¹ * Wᴴ * H) W := by
    have h4 := hall _ key
    rwa [hW] at h4
  have hX : (H⁻¹ * Wᴴ * H * W)ᴴ * H * (H⁻¹ * Wᴴ * H * W) = 0 := by
    calc (H⁻¹ * Wᴴ * H * W)ᴴ * H * (H⁻¹ * Wᴴ * H * W)
        = Wᴴ * H * (W * (H⁻¹ * Wᴴ * H)) * W := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, hHh, hHih,
            Matrix.mul_assoc, hc]
      _ = Wᴴ * H * ((H⁻¹ * Wᴴ * H) * W) * W := by rw [← hXW.eq]
      _ = 0 := by simp only [Matrix.mul_assoc, hP, Matrix.mul_zero]
  have hX0 := SimNormSq.eq_zero_of_conjTranspose_mul_mul_eq_zero hH hX
  have hW2 : Wᴴ * H * W = 0 := by
    have h3 : H * (H⁻¹ * Wᴴ * H * W) = Wᴴ * H * W := by simp only [Matrix.mul_assoc, hc']
    rw [← h3, hX0, Matrix.mul_zero]
  exact SimNormSq.eq_zero_of_conjTranspose_mul_mul_eq_zero hH hW2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalEqZeroOfSqEqZeroOfPosDefSimilitudeStatement

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

theorem _root_.GlobalTheory.T.aeval_eq_zero_of_sq_eq_zero_of_posDef_similitude : ∀ (n : ℕ) (H M : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), H.PosDef → 0 < s → Mᴴ * H * M = (s : ℂ) • H → ∀ P : Polynomial ℂ, Polynomial.aeval M P * Polynomial.aeval M P = 0 → Polynomial.aeval M P = 0 := by
  first | (exact @GlobalTheory.aeval_eq_zero_of_mul_self_eq_zero_of_similitude) | (exact GlobalTheory.aeval_eq_zero_of_mul_self_eq_zero_of_similitude) | (intros; apply GlobalTheory.aeval_eq_zero_of_mul_self_eq_zero_of_similitude  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolySeparableOfNoSqZeroPolynomialImage

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.LKCx

theorem minpoly_separable_of_sq_zero_free
    (F C : Type) [Field F] [Ring C] [IsSimpleRing C] [Algebra F C] [FiniteDimensional F C]
    (n : ℕ) (σ : F →+* ℂ) (ψ : C →+* Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    (hψ : ∀ x : F, ψ (algebraMap F C x) = Matrix.scalar (Fin n) (σ x)) (c : C)
    (hc : ∀ P : Polynomial ℂ, Polynomial.aeval (ψ c) P * Polynomial.aeval (ψ c) P = 0 →
      Polynomial.aeval (ψ c) P = 0) :
    (minpoly F c).Separable := by
  haveI : CharZero F := (RingHom.charZero_iff σ.injective).2 inferInstance
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hinj : Function.Injective ψ := ψ.injective
  have hcomp : ψ.comp (algebraMap F C) = (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ)).comp σ := by
    ext x
    simp only [RingHom.comp_apply, hψ, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
    rfl
  have hev : ∀ Q : Polynomial F, ψ (Polynomial.aeval c Q) = Polynomial.aeval (ψ c) (Q.map σ) := by
    intro Q
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp, Polynomial.aeval_def,
      Polynomial.eval₂_map]
  have hint : IsIntegral F c := IsIntegral.of_finite F c
  have hm0 : minpoly F c ≠ 0 := minpoly.ne_zero hint
  rw [PerfectField.separable_iff_squarefree]
  intro g hg
  obtain ⟨h, hh⟩ := hg
  have hQ : Polynomial.aeval c (g * h) = 0 := by
    apply hinj
    rw [map_zero, hev]
    apply hc
    rw [← hev, ← map_mul, ← map_mul]
    have : g * h * (g * h) = minpoly F c * h := by rw [hh]; ring
    rw [this, map_mul, minpoly.aeval, zero_mul, map_zero]
  have hdvd : minpoly F c ∣ g * h := minpoly.dvd F c hQ
  have hgh0 : g * h ≠ 0 := by
    intro h0
    apply hm0
    rw [hh, mul_assoc, h0, mul_zero]
  rw [hh, mul_assoc] at hdvd
  have : g * (g * h) ∣ 1 * (g * h) := by rwa [one_mul]
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hgh0).1 this)

end GlobalTheory.LKCx
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolySeparableOfNoSqZeroPolynomialImageStatement

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

theorem _root_.GlobalTheory.T.minpoly_separable_of_no_sq_zero_polynomial_image : ∀ (F C : Type) [Field F] [Ring C] [IsSimpleRing C] [Algebra F C] [FiniteDimensional F C] (n : ℕ) (σ : F →+* ℂ) (ψ : C →+* Matrix (Fin n) (Fin n) ℂ), 0 < n → (∀ x : F, ψ (algebraMap F C x) = Matrix.scalar (Fin n) (σ x)) → ∀ c : C, (∀ P : Polynomial ℂ, Polynomial.aeval (ψ c) P * Polynomial.aeval (ψ c) P = 0 → Polynomial.aeval (ψ c) P = 0) → (minpoly F c).Separable := by
  first | (exact @GlobalTheory.LKCx.minpoly_separable_of_sq_zero_free) | (exact GlobalTheory.LKCx.minpoly_separable_of_sq_zero_free) | (intros; apply GlobalTheory.LKCx.minpoly_separable_of_sq_zero_free  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularElementSeparableMinpoly

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx

theorem commute_units_conj {A : Type*} [Monoid A] (U : Aˣ) {a e : A} (h : Commute a e) :
    Commute ((U : A) * a * ↑U⁻¹) ((U : A) * e * ↑U⁻¹) := by
  unfold Commute SemiconjBy at *
  calc (U : A) * a * ↑U⁻¹ * ((U : A) * e * ↑U⁻¹) = U * (a * e) * ↑U⁻¹ := by
        simp only [mul_assoc, Units.inv_mul_cancel_left]
    _ = U * (e * a) * ↑U⁻¹ := by rw [h]
    _ = _ := by simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem comm_of_conj {A : Type*} [Monoid A] (U : Aˣ) (e : A)
    (h : ∀ a b : A, Commute a ((U : A) * e * ↑U⁻¹) → Commute b ((U : A) * e * ↑U⁻¹) → Commute a b)
    (a b : A) (ha : Commute a e) (hb : Commute b e) : Commute a b := by
  have h1 := h _ _ (commute_units_conj U ha) (commute_units_conj U hb)
  have h2 := commute_units_conj U⁻¹ h1
  have e1 : ∀ z : A, ((U⁻¹ : Aˣ) : A) * ((U : A) * z * ↑U⁻¹) * ↑(U⁻¹)⁻¹ = z := by
    intro z; simp [mul_assoc]
  rwa [e1, e1] at h2

variable {p : ℕ} [Fact p.Prime]

theorem ubc_val_eq (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t)
    (y : grp G β) (h : G.GAf) (w : AwayP p) :
    ∃ U : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
    ((ubcMap (AfP.eval w) (h⁻¹ * toAfF G β x t hx y * h)).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      (U : w.1.adicCompletion ℚ ⊗[ℚ] G.C) * ((1 : w.1.adicCompletion ℚ) ⊗ₜ (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) *
        ((U⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
  set φ : AfP p ⊗[ℚ] G.C →ₐ[ℚ] w.1.adicCompletion ℚ ⊗[ℚ] G.C :=
    Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) with hφ
  have hm : ((ubcMap (AfP.eval w) (toAfF G β x t hx y)).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      φ x * ((1 : w.1.adicCompletion ℚ) ⊗ₜ (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * φ ↑x⁻¹ := by
    show φ ((x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ↑x⁻¹) = _
    rw [map_mul, map_mul]
    congr 2
  refine ⟨((ubcMap (AfP.eval w) h).1.1)⁻¹ * Units.map φ.toMonoidHom x, ?_⟩
  rw [map_mul, map_mul, map_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, Units.val_mul, _root_.mul_inv_rev, inv_inv]
  rw [hm]
  simp only [Units.coe_map, MonoidHom.coe_coe, mul_assoc]
  rw [Units.coe_map_inv]
  rfl

end GlobalTheory.LKCx

namespace GlobalTheory.LKCx

end GlobalTheory.LKCx
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyOfRegAfOfFixL

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

theorem GlobalTheory.LKCx.minpoly_of_regAf_of_fixL : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (β : G.Cˣ), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y : grp G β) (h : G.GAf) (z : PosV G v β), FixL G v β y z.1 → RegAf G (h⁻¹ * toAfF G β x t hx y * h) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable := by
  intro p _ G v hv β hβ hR x t hx y h z hfix hreg
  have hcomm : ∀ a b : G.C, Commute a (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) →
      Commute b (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) → Commute a b := by
    obtain ⟨w, hw⟩ := hreg
    obtain ⟨U, hU⟩ := ubc_val_eq G β x t hx y h w
    rw [hU] at hw
    intro a b ha hb
    let ι : G.C →ₐ[ℚ] w.1.adicCompletion ℚ ⊗[ℚ] G.C := Algebra.TensorProduct.includeRight
    have hinj : Function.Injective ι :=
      Algebra.TensorProduct.includeRight_injective (algebraMap ℚ (w.1.adicCompletion ℚ)).injective
    have e : ι (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
        (1 : w.1.adicCompletion ℚ) ⊗ₜ (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := rfl
    have ha' := ha.map ι
    have hb' := hb.map ι
    rw [e] at ha' hb'
    have hab := comm_of_conj U _ hw (ι a) (ι b) ha' hb'
    exact hinj (by rw [map_mul, map_mul]; exact hab.eq)
  obtain ⟨-, -, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G v β hβ hR
  have hsim := GlobalTheory.LKCx.grp_similitude_herm p G v β y
  have hs : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by exact_mod_cast y.2.2
  obtain ⟨c0, hc0⟩ := hfix
  obtain ⟨H, hH, hHM⟩ := GlobalTheory.T.similitude_signature_one_preserves_posDef_form G.n (G.gram v) (herm G v β) (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ)
    (G.gram_herm v) Z _ (G.gram_det v) hv hZ hs (by rw [Complex.ofReal_ratCast]; exact hsim) z.1 c0 z.2 hc0
  have hsq := GlobalTheory.T.aeval_eq_zero_of_sq_eq_zero_of_posDef_similitude G.n H _ _ hH hs hHM
  have hsep := GlobalTheory.T.minpoly_separable_of_no_sq_zero_polynomial_image G.F G.C G.n v.embedding (G.psi v) G.n_pos (G.psi_F v) _ hsq
  exact ⟨GlobalTheory.T.natDegree_minpoly_eq_deg_centralSimple_commCentraliser G.F G.C G.n G.rankC _ hsep hcomm, hsep⟩
end
end
