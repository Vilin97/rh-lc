module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCoreDefs
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

-- Source module: Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.CompLmulMapId

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

variable {K H : Type} [Field K] [CommRing H] [Algebra K H]

theorem comp_lmul_map_id (ε : H →ₐ[K] K) (f : H →ₐ[K] H) (t : H ⊗[K] H) :
    f (Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (AlgHom.id K H) ((Algebra.ofId K H).comp ε) t)) =
      Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map f ((Algebra.ofId K H).comp ε) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, AlgHom.id_apply,
      AlgHom.comp_apply, Algebra.ofId_apply, map_mul, AlgHom.commutes]
  | add s t hs ht => simp only [map_add (f := _), hs, ht]

theorem counit_pw (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) (hL : CounitL Δ ε) (hR : CounitR Δ ε) (n : ℕ) :
    ε.comp (pw Δ ε n) = ε := by
  induction n with
  | zero => ext x; simp [pw]
  | succ n ih =>
    ext x
    have key : ∀ t : H ⊗[K] H,
        ε (Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H) t)) =
          ε (Algebra.TensorProduct.lmul' K
            (Algebra.TensorProduct.map ((Algebra.ofId K H).comp ε) (AlgHom.id K H) t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_mul,
          AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.commutes, AlgHom.id_apply]
        rw [← AlgHom.comp_apply ε (pw Δ ε n), ih]
        simp
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
    have hx := DFunLike.congr_fun hL x
    simp only [CounitL, AlgHom.comp_apply, AlgHom.id_apply] at hx
    show ε (Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H) (Δ x))) = ε x
    rw [key, hx]

theorem pw_sub_mem (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) (hL : CounitL Δ ε) (hR : CounitR Δ ε) (n : ℕ)
    {x : H} (hx : x ∈ RingHom.ker ε) : pw Δ ε n x - (n : H) * x ∈ RingHom.ker ε ^ 2 := by
  have hx0 : ε x = 0 := hx
  set e : H →ₐ[K] H := (Algebra.ofId K H).comp ε with he
  have gen : ∀ f : H →ₐ[K] H, ε.comp f = ε → ∀ t : H ⊗[K] H,
      Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map f (AlgHom.id K H) t) -
        Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map e (AlgHom.id K H) t) -
        Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map f e t) +
        Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map e e t) ∈ RingHom.ker ε ^ 2 := by
    intro f hf t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, AlgHom.id_apply, he,
        AlgHom.comp_apply, Algebra.ofId_apply]
      have e1 : f a * b - algebraMap K H (ε a) * b - f a * algebraMap K H (ε b) +
          algebraMap K H (ε a) * algebraMap K H (ε b) =
          (f a - algebraMap K H (ε a)) * (b - algebraMap K H (ε b)) := by ring
      rw [e1, pow_two]
      refine Ideal.mul_mem_mul ?_ ?_
      · rw [RingHom.mem_ker, map_sub, ← AlgHom.comp_apply, hf, AlgHom.commutes]; simp
      · rw [RingHom.mem_ker, map_sub, AlgHom.commutes]; simp
    | add s t hs ht =>
      simp only [map_add (f := _)]
      convert Ideal.add_mem _ hs ht using 1
      ring
  induction n with
  | zero => simp [pw, hx0]
  | succ n ih =>
    have h1 := gen (pw Δ ε n) (counit_pw Δ ε hL hR n) (Δ x)
    have hLx := DFunLike.congr_fun hL x
    have hRx := DFunLike.congr_fun hR x
    simp only [CounitL, CounitR, AlgHom.comp_apply, AlgHom.id_apply] at hLx hRx
    rw [← comp_lmul_map_id ε (pw Δ ε n), ← comp_lmul_map_id ε e, hRx, hLx] at h1
    have hex : e x = 0 := by simp [he, hx0]
    rw [hex, add_zero] at h1
    have h2 := Ideal.add_mem _ h1 ih
    have hp : pw Δ ε (n + 1) x =
        Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H) (Δ x)) := rfl
    rw [hp]
    convert h2 using 1
    push_cast
    ring

end PositivityTheory.PrwZar.Qi
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCharP

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

variable {K H : Type} [Field K] [CommRing H] [Algebra K H]

theorem pw_charP (p : ℕ) [Fact p.Prime] [CharP K p] (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K)
    (hL : CounitL Δ ε) (hR : CounitR Δ ε) (hmul : ∀ a b : ℕ, pw Δ ε (a * b) = (pw Δ ε a).comp (pw Δ ε b))
    (r : ℕ) {x : H} (hx : x ∈ RingHom.ker ε) : pw Δ ε (p ^ r) x ∈ RingHom.ker ε ^ (2 ^ r) := by
  induction r generalizing x with
  | zero =>
    rw [pow_zero, pow_zero, pow_one, RingHom.mem_ker]
    have h := AlgHom.congr_fun (counit_pw Δ ε hL hR 1) x
    rw [AlgHom.comp_apply] at h
    rw [h]
    exact RingHom.mem_ker.1 hx
  | succ r ih =>
    have hp : (p : H) = 0 := by
      rw [← map_natCast (algebraMap K H), CharP.cast_eq_zero K p, map_zero]
    have h2 : pw Δ ε p x ∈ RingHom.ker ε ^ 2 := by
      have := pw_sub_mem Δ ε hL hR p hx
      rwa [hp, zero_mul, sub_zero] at this
    have hcomp : pw Δ ε (p ^ (r + 1)) = (pw Δ ε (p ^ r)).comp (pw Δ ε p) := by
      rw [pow_succ]
      exact hmul _ _
    rw [hcomp, AlgHom.comp_apply]
    have hmap : Ideal.map (pw Δ ε (p ^ r)) (RingHom.ker ε) ≤ RingHom.ker ε ^ (2 ^ r) :=
      Ideal.map_le_iff_le_comap.2 fun z hz => ih hz
    have hy : pw Δ ε (p ^ r) (pw Δ ε p x) ∈ Ideal.map (pw Δ ε (p ^ r)) (RingHom.ker ε ^ 2) :=
      Ideal.mem_map_of_mem _ h2
    rw [Ideal.map_pow] at hy
    have h3 := Ideal.pow_right_mono hmap 2 hy
    rwa [← pow_mul, ← pow_succ] at h3

end PositivityTheory.PrwZar.Qi
end
end
end
