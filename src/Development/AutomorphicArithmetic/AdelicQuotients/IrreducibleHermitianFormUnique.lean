module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AutomorphicArithmetic.AdelicQuotients.InvariantSesquilinearFormEqSmulOfIrreducible
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
public import Mathlib.MeasureTheory.Group.Integral

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsOrthonormalBasisSesquilinear

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Qh52.exists_orthonormal_basis_sesquilinear :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V]
    [FiniteDimensional ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ (a b : V), ((B : V → V →ₗ⋆[ℂ] ℂ) b : V → ℂ) a = Star.star (((B : V → V →ₗ⋆[ℂ] ℂ) a : V → ℂ) b)) →
      (∀ (a : V), a ≠ (0 : V) → (0 : ℝ) < (((B : V → V →ₗ⋆[ℂ] ℂ) a : V → ℂ) a).re) →
        ∃ (e : Fin (Module.finrank ℂ V) → V),
          (∀ (i : Fin (Module.finrank ℂ V)), ((B : V → V →ₗ⋆[ℂ] ℂ) (e i) : V → ℂ) (e i) = (1 : ℂ)) ∧
            (∀ (x y : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) y =
                  ∑ i : Fin (Module.finrank ℂ V),
                    ((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) (e i) * ((B : V → V →ₗ⋆[ℂ] ℂ) (e i) : V → ℂ) y) ∧
              ∀ (x y : V),
                ‖((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) y‖ ^ (2 : ℕ) ≤
                  (((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) x).re * (((B : V → V →ₗ⋆[ℂ] ℂ) y : V → ℂ) y).re := by
  intro V _ _ _ B hs hp
  let c : InnerProductSpace.Core ℂ V :=
    { inner := fun x y => B y x
      conj_inner_symm := fun x y => (hs x y).symm
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · simp [h]
        · exact (hp x h).le
      add_left := fun x y z => map_add (B z) x y
      smul_left := fun x y r => by simp
      definite := fun x h => by
        by_contra hx
        have h1 := hp x hx
        have h2 : B x x = 0 := h
        rw [h2] at h1
        simp at h1 }
  letI : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  have hB : ∀ x y : V, B x y = inner ℂ y x := fun _ _ => rfl
  let b := stdOrthonormalBasis ℂ V
  refine ⟨b, fun i => ?_, fun x y => ?_, fun x y => ?_⟩
  · rw [hB]
    exact b.inner_eq_one i
  · simp only [hB]
    rw [← b.sum_inner_mul_inner y x]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · simp only [hB]
    have h := inner_mul_inner_self_le (𝕜 := ℂ) y x
    rw [norm_inner_symm x y] at h
    rw [sq, mul_comm (inner ℂ x x).re]
    exact h
end
end

-- Source module: Development.AutomorphicArithmetic.AdelicQuotients.IrreducibleHermitianFormUnique

section

@[expose] public section

open MeasureTheory

private lemma exists_orthonormal_basis_sesquilinear {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hh : ∀ a b, B b a = star (B a b))
    (hp : ∀ a, a ≠ 0 → 0 < (B a a).re) :
    ∃ e : Fin (Module.finrank ℂ V) → V,
      (∀ i, B (e i) (e i) = 1) ∧ (∀ x y, B x y = ∑ i, B x (e i) * B (e i) y) ∧
      (∀ x y, ‖B x y‖ ^ 2 ≤ (B x x).re * (B y y).re) :=
  _root_.UpperTheory.Reformulated.B.Qh52.exists_orthonormal_basis_sesquilinear B hh hp

theorem UpperTheory.irreducible_hermitian_form_unique :
    ∀ {G V : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] (ρ : G →* Module.End ℂ V)
      (_hI : ∀ W : Submodule ℂ V, (∀ g, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤)
      (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (_hh : ∀ a b, B b a = star (B a b)) (_hp : ∀ a, a ≠ 0 → 0 < (B a a).re)
      (_hinv : ∀ g a b, B (ρ g a) (ρ g b) = B a b) (_hm : ∀ a b, Measurable fun g => B (ρ g a) b) (a b c d : V),
      ∫ g, B (ρ g a) b * star (B (ρ g c) d) ∂μ = ((μ.real Set.univ / (Module.finrank ℂ V : ℝ) : ℝ) : ℂ) * B a c * star (B b d) := by
  intro G V _ _ _ μ _ _ _ _ _ _ ρ hI B hh hp hinv hm a b c d
  obtain ⟨e, he1, hpar, hcs⟩ := exists_orthonormal_basis_sesquilinear B hh hp
  have hshift : ∀ (h g : G) (x y : V), B (ρ g x) (ρ h y) = B (ρ (h⁻¹ * g) x) y := by
    intro h g x y
    rw [← hinv h (ρ (h⁻¹ * g) x) y, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have hbd : ∀ (x y : V) (g : G), ‖B (ρ g x) y‖ ≤ Real.sqrt ((B x x).re * (B y y).re) := by
    intro x y g
    apply Real.le_sqrt_of_sq_le
    have := hcs (ρ g x) y
    rwa [hinv] at this
  have hint : ∀ x y z w : V, Integrable (fun g => B (ρ g x) y * star (B (ρ g z) w)) μ := by
    intro x y z w
    refine Integrable.of_bound (C := Real.sqrt ((B x x).re * (B y y).re) * Real.sqrt ((B z z).re * (B w w).re)) ?_ ?_
    · exact ((hm x y).mul (continuous_star.measurable.comp (hm z w))).aestronglyMeasurable
    · filter_upwards with g
      rw [norm_mul, norm_star]
      exact mul_le_mul (hbd _ _ _) (hbd _ _ _) (norm_nonneg _) (Real.sqrt_nonneg _)
  let S : V → V → ℂ := fun y w => ∫ g, B (ρ g a) y * star (B (ρ g c) w) ∂μ
  have hS1 : ∀ w w' y, S y (w + w') = S y w + S y w' := by
    intro w w' y
    simp only [S, map_add (f := _), star_add, mul_add]
    exact integral_add (hint _ _ _ _) (hint _ _ _ _)
  have hS2 : ∀ (r : ℂ) w y, S y (r • w) = r * S y w := by
    intro r w y
    have : ∀ g, B (ρ g a) y * star (B (ρ g c) (r • w)) = r * (B (ρ g a) y * star (B (ρ g c) w)) := by
      intro g
      simp [map_smulₛₗ]
      ring
    simp only [S, this]
    exact integral_const_mul _ _
  have hS3 : ∀ w y y', S (y + y') w = S y w + S y' w := by
    intro w y y'
    simp only [S, map_add (f := _), add_mul]
    exact integral_add (hint _ _ _ _) (hint _ _ _ _)
  have hS4 : ∀ (r : ℂ) w y, S (r • y) w = star r * S y w := by
    intro r w y
    have : ∀ g, B (ρ g a) (r • y) * star (B (ρ g c) w) = star r * (B (ρ g a) y * star (B (ρ g c) w)) := by
      intro g
      simp [map_smulₛₗ]
      ring
    simp only [S, this]
    exact integral_const_mul _ _
  let B₁ : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun w y => S y w)
      (fun w w' y => hS1 w w' y) (fun r w y => hS2 r w y)
      (fun w y y' => hS3 w y y') (fun r w y => hS4 r w y)
  have hB₁ : ∀ w y, B₁ w y = S y w := fun _ _ => rfl
  have hB₁inv : ∀ h w y, B₁ (ρ h w) (ρ h y) = B₁ w y := by
    intro h w y
    simp only [hB₁, S, hshift]
    exact integral_mul_left_eq_self (μ := μ) (fun g => B (ρ g a) y * star (B (ρ g c) w)) h⁻¹
  obtain ⟨lam, hlam⟩ := UpperTheory.invariant_sesquilinearForm_eq_smul_of_irreducible ρ hI B hh hp hinv B₁ hB₁inv
  have hsum : lam * (Module.finrank ℂ V : ℂ) = ((μ.real Set.univ : ℝ) : ℂ) * B a c := by
    have h1 : ∑ i, S (e i) (e i) = lam * (Module.finrank ℂ V : ℂ) := by
      have : ∀ i, S (e i) (e i) = lam := by
        intro i
        rw [← hB₁, hlam, he1, mul_one]
      simp [this, mul_comm]
    have h2 : ∑ i, S (e i) (e i) = ∫ _g : G, B a c ∂μ := by
      simp only [S]
      rw [← integral_finsetSum _ (fun i _ => hint _ _ _ _)]
      congr 1
      funext g
      rw [← hinv g a c, hpar (ρ g a) (ρ g c)]
      exact Finset.sum_congr rfl fun i _ => by rw [hh (ρ g c) (e i)]
    rw [← h1, h2, integral_const]
    simp
  have hn : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have hfin : (∫ g, B (ρ g a) b * star (B (ρ g c) d) ∂μ) = S b d := rfl
  rw [hfin, ← hB₁, hlam, hh b d]
  have hlam' : lam = ((μ.real Set.univ : ℝ) : ℂ) * B a c / (Module.finrank ℂ V : ℂ) := by
    rw [eq_div_iff hn, hsum]
  rw [hlam']
  push_cast
  ring
end
end
