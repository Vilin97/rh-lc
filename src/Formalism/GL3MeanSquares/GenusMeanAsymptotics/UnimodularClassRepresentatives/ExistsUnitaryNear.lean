module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsLocUnif
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.PolNatDegreeLe
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsInvOneAdd

section

@[expose] public section

open Matrix

namespace Formalism.HermitianLattices.Ext.L3.HU

variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem Cayley.exists_det_one_add (hS : IsLocUnif S ϖ) {M : Matrix n n K} (hM : Ent S M) :
    ∃ s ∈ S, (1 + ϖ • M).det = 1 + ϖ * s := by
  obtain ⟨M₀, rfl⟩ := hM.exists_map
  let ϖ₀ : S := ⟨ϖ, hS.mem⟩
  refine ⟨((Matrix.trace M₀ + (Matrix.det (1 + (Polynomial.X : Polynomial S) •
      M₀.map Polynomial.C)).divX.divX.eval ϖ₀ * ϖ₀ : S) : K), SetLike.coe_mem _, ?_⟩
  have hmap : (1 : Matrix n n K) + ϖ • M₀.map S.subtype = S.subtype.mapMatrix (1 + ϖ₀ • M₀) := by
    ext i j
    by_cases h : i = j <;> simp [h, ϖ₀]
  rw [hmap, ← RingHom.map_det, Matrix.det_one_add_smul ϖ₀ M₀]
  simp only [map_add (f := _), map_mul, map_one, map_pow, Subring.coe_subtype]
  simp only [Subring.coe_add, Subring.coe_mul, ϖ₀]
  ring

theorem Cayley.exists_inv_one_add (hS : IsLocUnif S ϖ) {M : Matrix n n K} (hM : Ent S M) :
    ∃ Q : Matrix n n K, Ent S Q ∧ (1 + ϖ • M) * Q = 1 := by
  obtain ⟨s, hs, hdet⟩ := Cayley.exists_det_one_add hS hM
  obtain ⟨hne, hinv⟩ := hS.rad s hs
  have hA : Ent S (1 + ϖ • M) := Ent.add Ent.one (Ent.smul hS.mem hM)
  refine ⟨(1 + ϖ * s)⁻¹ • (1 + ϖ • M).adjugate, Ent.smul hinv hA.adjugate, ?_⟩
  rw [Matrix.mul_smul, Matrix.mul_adjugate, hdet, smul_smul, inv_mul_cancel₀ hne, one_smul]

theorem exists_cayley (hS : IsLocUnif S ϖ) {H E : Matrix n n K} (hH : Hᴴ = H) (hHS : Ent S H)
    (hES : Ent S E) {e l N : ℕ} (hHE : H * E = ϖ ^ e • (1 : Matrix n n K)) (hN : 2 * l + e + 1 ≤ N)
    {X Z W' : Matrix n n K} (hX : Ent S X) (hZ : Ent S Z) (hXZ : Xᴴ * H * X = H + ϖ ^ N • Z)
    {c : K} (hc : c ∈ S) (hcc : c + star c = 1) (hW' : Ent S W')
    (hWW : (c • (1 : Matrix n n K) + star c • X) * W' = ϖ ^ l • (1 : Matrix n n K)) :
    ∃ G D : Matrix n n K, Ent S D ∧ Gᴴ * H * G = H ∧ G = X + ϖ ^ (N - 2 * l - e) • D := by
  classical
  set j := N - 2 * l - e with hj
  have hj1 : 1 ≤ j := by omega
  have hNj : N = j + e + 2 * l := by omega
  have hϖ0 : ϖ ≠ 0 := hS.ne
  have hstar : ∀ k : ℕ, star (ϖ ^ k) = ϖ ^ k := fun k => by rw [star_pow, hS.fix]
  have hcs : star c ∈ S := hS.star_mem c hc
  obtain ⟨A, hA⟩ : ∃ A : Matrix n n K, A = c • (1 : Matrix n n K) + star c • X := ⟨_, rfl⟩
  rw [← hA] at hWW
  have hAent : Ent S A := by
    rw [hA]
    exact Ent.add (Ent.smul hc Ent.one) (Ent.smul hcs hX)
  have hWA : W' * A = ϖ ^ l • (1 : Matrix n n K) := by
    have hne : ϖ ^ l ≠ 0 := pow_ne_zero _ hϖ0
    have h1 : A * ((ϖ ^ l)⁻¹ • W') = 1 := by
      rw [Matrix.mul_smul, hWW, smul_smul, inv_mul_cancel₀ hne, one_smul]
    have h2 : ((ϖ ^ l)⁻¹ • W') * A = 1 := mul_eq_one_comm.mp h1
    rw [Matrix.smul_mul] at h2
    calc W' * A = ϖ ^ l • ((ϖ ^ l)⁻¹ • (W' * A)) := by
          rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
      _ = ϖ ^ l • (1 : Matrix n n K) := by rw [h2]
  have hAW : ∀ M : Matrix n n K, Aᴴ * (W'ᴴ * M) = ϖ ^ l • M := by
    intro M
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hWA, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hstar, Matrix.smul_mul, Matrix.one_mul]
  have hHE' : ∀ M : Matrix n n K, H * (E * M) = ϖ ^ e • M := by
    intro M
    rw [← Matrix.mul_assoc, hHE, Matrix.smul_mul, Matrix.one_mul]
  have hZh : Zᴴ = Z := by
    have h1 : (Xᴴ * H * X)ᴴ = Xᴴ * H * X := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH,
        Matrix.mul_assoc]
    rw [hXZ, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hH, hstar] at h1
    exact smul_right_injective _ (pow_ne_zero N hϖ0) (add_left_cancel h1)
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : Matrix n n K, D₁ = E * (W'ᴴ * (Z * W')) := ⟨_, rfl⟩
  have hD₁ent : Ent S D₁ := by
    rw [hD₁]
    exact Ent.mul hES (Ent.mul (Ent.conjTranspose hS.star_mem hW') (Ent.mul hZ hW'))
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : Matrix n n K, Δ = (c * ϖ ^ j) • (D₁ * A) := ⟨_, rfl⟩
  have key1 : Aᴴ * (H * Δ) = (c * ϖ ^ N) • Z := by
    rw [hΔ, hD₁]
    simp only [Matrix.mul_smul, Matrix.mul_assoc]
    rw [hHE']
    simp only [Matrix.mul_smul]
    rw [hAW, hWA]
    simp only [Matrix.mul_smul, Matrix.mul_one, smul_smul]
    congr 1
    rw [hNj]
    ring
  have key2 : Δᴴ * (H * A) = (star c * ϖ ^ N) • Z := by
    have h : Δᴴ * (H * A) = (Aᴴ * (H * Δ))ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH,
        Matrix.mul_assoc]
    rw [h, key1, Matrix.conjTranspose_smul, hZh, star_mul', hstar]
  have hAh : Aᴴ = star c • (1 : Matrix n n K) + c • Xᴴ := by
    rw [hA, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, star_star]
  have k1 : star c • (H * Δ) + c • (Xᴴ * (H * Δ)) = (c * ϖ ^ N) • Z := by
    rw [← key1, hAh, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
  have k2 : c • (Δᴴ * H) + star c • (Δᴴ * (H * X)) = (star c * ϖ ^ N) • Z := by
    rw [← key2, hA, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.mul_one]
  have k0 : Xᴴ * (H * X) = H + ϖ ^ N • Z := by rw [← Matrix.mul_assoc, hXZ]
  have hTR : (X - c • Δ)ᴴ * H * (X - c • Δ) = (1 + star c • Δ)ᴴ * H * (1 + star c • Δ) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, star_star, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc]
    rw [k0]
    linear_combination (norm := module) -k1 - k2 - hcc • (ϖ ^ N • Z)
  have hMent : Ent S ((star c * c * ϖ ^ (j - 1)) • (D₁ * A)) :=
    Ent.smul (mul_mem (mul_mem hcs hc) (_root_.pow_mem hS.mem _)) (Ent.mul hD₁ent hAent)
  obtain ⟨Q, hQent, hRQ⟩ := Cayley.exists_inv_one_add hS hMent
  have hjj : ϖ * ϖ ^ (j - 1) = ϖ ^ j := by
    rw [← pow_succ']
    congr 1
    omega
  have hR : (1 : Matrix n n K) + ϖ • ((star c * c * ϖ ^ (j - 1)) • (D₁ * A)) =
      1 + star c • Δ := by
    rw [hΔ, smul_smul, smul_smul]
    congr 2
    rw [← hjj]
    ring
  rw [hR] at hRQ
  have hRQ' : Q + star c • (Δ * Q) = 1 := by
    have h := hRQ
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul] at h
    exact h
  refine ⟨(X - c • Δ) * Q, -(star c * c) • (X * (D₁ * (A * Q))) - (c * c) • (D₁ * (A * Q)), ?_, ?_, ?_⟩
  · exact Ent.sub (Ent.smul (neg_mem (mul_mem hcs hc)) (Ent.mul hX (Ent.mul hD₁ent (Ent.mul hAent hQent))))
      (Ent.smul (mul_mem hc hc) (Ent.mul hD₁ent (Ent.mul hAent hQent)))
  · rw [Matrix.conjTranspose_mul]
    calc Qᴴ * (X - c • Δ)ᴴ * H * ((X - c • Δ) * Q)
        = Qᴴ * ((X - c • Δ)ᴴ * H * (X - c • Δ)) * Q := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * ((1 + star c • Δ)ᴴ * H * (1 + star c • Δ)) * Q := by rw [hTR]
      _ = ((1 + star c • Δ) * Q)ᴴ * H * ((1 + star c • Δ) * Q) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = H := by rw [hRQ]; simp
  · calc (X - c • Δ) * Q = X * (Q + star c • (Δ * Q)) - star c • (X * (Δ * Q)) - c • (Δ * Q) := by
          simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
          abel
      _ = X + ϖ ^ j • (-(star c * c) • (X * (D₁ * (A * Q))) - (c * c) • (D₁ * (A * Q))) := by
          rw [hRQ', Matrix.mul_one, hΔ]
          simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
          module

end Formalism.HermitianLattices.Ext.L3.HU
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.StepIdentity

section

@[expose] public section

open Matrix

namespace Formalism.HermitianLattices.Ext.L3.HU

variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Newton

theorem det_one_add (hϖ : ϖ ∈ S) {M : Matrix n n K} (hM : Ent S M) :
    ∃ s ∈ S, (1 + ϖ • M).det = 1 + ϖ * s := by
  obtain ⟨M₀, rfl⟩ := hM.exists_map
  set w : S := ⟨ϖ, hϖ⟩ with hw
  obtain ⟨c, h⟩ : ∃ c : S, (1 + w • M₀).det = 1 + M₀.trace * w + c * w ^ 2 :=
    ⟨_, Matrix.det_one_add_smul w M₀⟩
  refine ⟨((M₀.trace + c * w : S) : K), Subtype.prop _, ?_⟩
  have key : (1 + ϖ • M₀.map S.subtype) = S.subtype.mapMatrix (1 + w • M₀) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hw]
    · simp [Matrix.one_apply_ne hij, hw]
  have h2 : (1 + M₀.trace * w + c * w ^ 2 : S) = 1 + w * (M₀.trace + c * w) := by ring
  rw [key, ← RingHom.map_det, h, h2]
  simp [hw]

theorem step_identity (P H X Y Y' Z V V' : Matrix n n K) (a b : K)
    (hG : P * H * X = H + (a * b) • Z) (hHY : H * Y = b • V') (hYH : Y' * H = b • V)
    (hV : V + V' = Z) :
    (P - a • (Y' * P)) * H * (X - a • (X * Y)) =
      H + (a * a * b) • (-(Z * Y) - Y' * Z + Y' * V' + a • (Y' * Z * Y)) := by
  have e1 : P - a • (Y' * P) = (1 - a • Y') * P := by rw [sub_mul, one_mul, smul_mul_assoc]
  have e2 : X - a • (X * Y) = X * (1 - a • Y) := by rw [mul_sub, mul_one, mul_smul_comm]
  have e3 : (1 - a • Y') * P * H * (X * (1 - a • Y)) = (1 - a • Y') * (P * H * X) * (1 - a • Y) := by
    simp only [Matrix.mul_assoc]
  have hYHY : Y' * H * Y = b • (Y' * V') := by
    rw [Matrix.mul_assoc, hHY, mul_smul_comm]
  have hV2 : V = Z - V' := eq_sub_of_add_eq hV
  rw [e1, e2, e3, hG]
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
  simp only [← Matrix.mul_assoc, hYHY]
  simp only [← Matrix.mul_assoc, hHY, hYH, hV2]
  simp only [Matrix.mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
  module

theorem step (hS : IsLocUnif S ϖ) {H E : Matrix n n K} (hH : Hᴴ = H) (hES : Ent S E) {e k : ℕ}
    (hHE : H * E = ϖ ^ e • (1 : Matrix n n K)) (hk : e + 1 ≤ k)
    {X Z : Matrix n n K} (hX : Ent S X) (hZ : Ent S Z) (hXZ : Xᴴ * H * X = H + ϖ ^ k • Z) :
    ∃ D Z' : Matrix n n K, Ent S D ∧ Ent S Z' ∧
      (X + ϖ ^ (k - e) • D)ᴴ * H * (X + ϖ ^ (k - e) • D) = H + ϖ ^ (k + 1) • Z' := by
  obtain ⟨τ, hτ, hτ1⟩ := hS.tr
  have hstar : ∀ m : ℕ, star (ϖ ^ m) = ϖ ^ m := fun m => by rw [star_pow, hS.fix]
  have hZH : Zᴴ = Z := by
    have h1 : (Xᴴ * H * X)ᴴ = Xᴴ * H * X := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc]
    rw [hXZ, conjTranspose_add, hH, conjTranspose_smul, hstar] at h1
    have h2 : ϖ ^ k • Zᴴ = ϖ ^ k • Z := add_left_cancel h1
    exact smul_right_injective _ (pow_ne_zero k hS.ne) h2
  have hYent : Ent S (E * (τ • Z)) := hES.mul (Ent.smul hτ hZ)
  have hYc : Ent S (E * (τ • Z))ᴴ := Ent.conjTranspose hS.star_mem hYent
  have hab : ϖ ^ (k - e) * ϖ ^ e = ϖ ^ k := by rw [← pow_add, Nat.sub_add_cancel (by omega : e ≤ k)]
  have hG : Xᴴ * H * X = H + (ϖ ^ (k - e) * ϖ ^ e) • Z := by rw [hab]; exact hXZ
  have hHY : H * (E * (τ • Z)) = ϖ ^ e • (τ • Z) := by
    rw [← Matrix.mul_assoc, hHE, smul_mul_assoc, one_mul]
  have hEH : Eᴴ * H = ϖ ^ e • (1 : Matrix n n K) := by
    have h3 := congrArg conjTranspose hHE
    rw [conjTranspose_mul, hH, conjTranspose_smul, conjTranspose_one, hstar] at h3
    exact h3
  have hYH : (E * (τ • Z))ᴴ * H = ϖ ^ e • (star τ • Z) := by
    rw [conjTranspose_mul, Matrix.mul_assoc, hEH, conjTranspose_smul, hZH, mul_smul_comm, mul_one]
  have hV : star τ • Z + τ • Z = Z := by rw [← add_smul, add_comm, hτ1, one_smul]
  have hid := Newton.step_identity Xᴴ H X (E * (τ • Z)) (E * (τ • Z))ᴴ Z (star τ • Z) (τ • Z)
    (ϖ ^ (k - e)) (ϖ ^ e) hG hHY hYH hV
  refine ⟨-(X * (E * (τ • Z))), ϖ ^ (k - e - 1) • (-(Z * (E * (τ • Z))) - (E * (τ • Z))ᴴ * Z +
    (E * (τ • Z))ᴴ * (τ • Z) + ϖ ^ (k - e) • ((E * (τ • Z))ᴴ * Z * (E * (τ • Z)))), (hX.mul hYent).neg,
    Ent.smul (S.pow_mem hS.mem _) ((((hZ.mul hYent).neg.sub (hYc.mul hZ)).add
      (hYc.mul (Ent.smul hτ hZ))).add (Ent.smul (S.pow_mem hS.mem _) ((hYc.mul hZ).mul hYent))), ?_⟩
  have e1 : X + ϖ ^ (k - e) • -(X * (E * (τ • Z))) = X - ϖ ^ (k - e) • (X * (E * (τ • Z))) := by
    rw [smul_neg, ← sub_eq_add_neg]
  have e2 : (X - ϖ ^ (k - e) • (X * (E * (τ • Z))))ᴴ =
      Xᴴ - ϖ ^ (k - e) • ((E * (τ • Z))ᴴ * Xᴴ) := by
    rw [conjTranspose_sub, conjTranspose_smul, hstar, conjTranspose_mul]
  have hp : ϖ ^ (k - e) * ϖ ^ (k - e) * ϖ ^ e = ϖ ^ (k + 1) * ϖ ^ (k - e - 1) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [e1, e2, hid, smul_smul, hp]

end Newton

theorem det_unit (hS : IsLocUnif S ϖ) {H E : Matrix n n K} (hH : Hᴴ = H) (hHS : Ent S H)
    (hES : Ent S E) {e k : ℕ} (hHE : H * E = ϖ ^ e • (1 : Matrix n n K)) (hk : e + 1 ≤ k)
    {X Z : Matrix n n K} (hX : Ent S X) (hZ : Ent S Z) (hXZ : Xᴴ * H * X = H + ϖ ^ k • Z) :
    X.det ≠ 0 ∧ X.det⁻¹ ∈ S := by
  have hW : Ent S (ϖ ^ (k - e - 1) • (Z * E)) := Ent.smul (S.pow_mem hS.mem _) (hZ.mul hES)
  obtain ⟨s, hs, hdet⟩ := Newton.det_one_add hS.mem hW
  have hmat : Xᴴ * H * X * E = ϖ ^ e • (1 + ϖ • (ϖ ^ (k - e - 1) • (Z * E))) := by
    rw [hXZ, add_mul, hHE, smul_mul_assoc, smul_add, smul_smul, smul_smul, ← pow_succ, ← pow_add,
      show e + 1 + (k - e - 1) = k by omega]
  have h1 := congrArg Matrix.det hmat
  rw [det_mul, det_mul, det_mul, det_smul, hdet, det_conjTranspose] at h1
  have h2 := congrArg Matrix.det hHE
  rw [det_mul, det_smul, det_one, mul_one] at h2
  have hc : (ϖ ^ e) ^ Fintype.card n ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hS.ne)
  have h3 : star X.det * X.det = 1 + ϖ * s := by
    apply mul_right_cancel₀ hc
    linear_combination h1 - star X.det * X.det * h2
  obtain ⟨hne, hinv⟩ := hS.rad s hs
  have hX0 : X.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h3
    exact hne h3.symm
  have hsX : star X.det ≠ 0 := star_ne_zero.mpr hX0
  refine ⟨hX0, ?_⟩
  have e4 : X.det⁻¹ = star X.det * (1 + ϖ * s)⁻¹ := by
    rw [← h3, mul_inv, ← mul_assoc, mul_inv_cancel₀ hsX, one_mul]
  rw [e4]
  exact S.mul_mem (hS.star_mem _ hX.det) hinv

theorem exists_newton (hS : IsLocUnif S ϖ) {H E : Matrix n n K} (hH : Hᴴ = H) (hHS : Ent S H)
    (hES : Ent S E) {e k : ℕ} (hHE : H * E = ϖ ^ e • (1 : Matrix n n K)) (hk : e + 1 ≤ k)
    {X Z : Matrix n n K} (hX : Ent S X) (hZ : Ent S Z) (hXZ : Xᴴ * H * X = H + ϖ ^ k • Z) (N : ℕ) :
    ∃ D Z' : Matrix n n K, Ent S D ∧ Ent S Z' ∧
      (X + ϖ ^ (k - e) • D)ᴴ * H * (X + ϖ ^ (k - e) • D) = H + ϖ ^ N • Z' := by
  have key : ∀ j : ℕ, ∃ D Z' : Matrix n n K, Ent S D ∧ Ent S Z' ∧
      (X + ϖ ^ (k - e) • D)ᴴ * H * (X + ϖ ^ (k - e) • D) = H + ϖ ^ (k + j) • Z' := by
    intro j
    induction j with
    | zero => exact ⟨0, Z, Ent.zero, hZ, by simpa using hXZ⟩
    | succ j ih =>
      obtain ⟨D, Z', hD, hZ', hEq⟩ := ih
      obtain ⟨D₁, Z'', hD₁, hZ'', hEq'⟩ := Newton.step hS hH hES hHE (by omega : e + 1 ≤ k + j)
        (hX.add (Ent.smul (S.pow_mem hS.mem _) hD)) hZ' hEq
      refine ⟨D + ϖ ^ j • D₁, Z'', hD.add (Ent.smul (S.pow_mem hS.mem _) hD₁), hZ'', ?_⟩
      have e1 : X + ϖ ^ (k - e) • (D + ϖ ^ j • D₁) =
          X + ϖ ^ (k - e) • D + ϖ ^ (k + j - e) • D₁ := by
        rw [smul_add, smul_smul, ← pow_add, add_assoc, show k - e + j = k + j - e by omega]
      rw [e1, hEq', show k + (j + 1) = k + j + 1 by omega]
  obtain ⟨D, Z', hD, hZ', hEq⟩ := key N
  refine ⟨D, ϖ ^ k • Z', hD, Ent.smul (S.pow_mem hS.mem _) hZ', ?_⟩
  rw [hEq, smul_smul, ← pow_add, add_comm k N]

end Formalism.HermitianLattices.Ext.L3.HU
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsUnitaryNear

section

@[expose] public section

open Matrix

namespace Formalism.HermitianLattices.Ext.L3.HU

variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem exists_unitary_near [CharZero K] (hS : IsLocUnif S ϖ) {H E : Matrix n n K} (hH : Hᴴ = H)
    (hHS : Ent S H) (hES : Ent S E) {e k : ℕ} (hHE : H * E = ϖ ^ e • (1 : Matrix n n K))
    (hk : e + 1 ≤ k) {X Z : Matrix n n K} (hX : Ent S X) (hZ : Ent S Z)
    (hXZ : Xᴴ * H * X = H + ϖ ^ k • Z) :
    ∃ G G' D : Matrix n n K, Ent S G ∧ Ent S G' ∧ Ent S D ∧ G * G' = 1 ∧ Gᴴ * H * G = H ∧
      G = X + ϖ ^ (k - e) • D := by
  obtain ⟨l, hl⟩ := exists_node (K := K) hS n
  obtain ⟨D1, Z1, hD1, hZ1, hX1⟩ := exists_newton hS hH hHS hES hHE hk hX hZ hXZ (k + 2 * l)
  have hpk : ϖ ^ (k - e) ∈ S := pow_mem hS _
  have hX1S : Ent S (X + ϖ ^ (k - e) • D1) := hX.add (hD1.smul hpk)
  have hk1 : e + 1 ≤ k + 2 * l := by omega
  obtain ⟨hd1, hd1S⟩ := det_unit hS hH hHS hES hHE hk1 hX1S hZ1 hX1
  obtain ⟨c, hc, hcc, W', hW', hWW⟩ := hl _ hX1S hd1 hd1S
  have hN : 2 * l + e + 1 ≤ k + 2 * l := by omega
  obtain ⟨G, D2, hD2, hG, hGe⟩ :=
    exists_cayley hS hH hHS hES hHE hN hX1S hZ1 hX1 hc hcc hW' hWW
  have hexp : k + 2 * l - 2 * l - e = k - e := by omega
  rw [hexp] at hGe
  have hGS : Ent S G := by
    rw [hGe]
    exact hX1S.add (hD2.smul hpk)
  have hG0 : Gᴴ * H * G = H + ϖ ^ k • (0 : Matrix n n K) := by
    rw [smul_zero, add_zero]
    exact hG
  obtain ⟨hd, hdS⟩ := det_unit hS hH hHS hES hHE hk hGS Ent.zero hG0
  refine ⟨G, G.det⁻¹ • G.adjugate, D1 + D2, hGS, hGS.adjugate.smul hdS, hD1.add hD2, ?_, hG, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, inv_mul_cancel₀ hd, one_smul]
  · rw [hGe, smul_add, add_assoc]

end Formalism.HermitianLattices.Ext.L3.HU
end
end
