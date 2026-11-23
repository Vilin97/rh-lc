module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HasDerivAtMexpCommAddBracket
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPbB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.TypeStar
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPbA

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

theorem dpb_sylv (f : W →ₗ[ℝ] V) (g : V →ₗ[ℝ] W) :
    LinearMap.det (1 + f ∘ₗ g : V →ₗ[ℝ] V) = LinearMap.det (1 + g ∘ₗ f : W →ₗ[ℝ] W) := by
  classical
  let bV := Module.finBasis ℝ V
  let bW := Module.finBasis ℝ W
  rw [← LinearMap.det_toMatrix bV, ← LinearMap.det_toMatrix bW, map_add (f := _), map_add (f := _),
    LinearMap.toMatrix_comp bV bW bV, LinearMap.toMatrix_comp bW bV bW, LinearMap.toMatrix_one,
    LinearMap.toMatrix_one]
  exact Matrix.det_one_add_mul_comm _ _

theorem dpb_ring {R : Type*} [Ring R] (a p q : R) (h0 : p * q = 0) (hc : p * a = a * p) :
    (1 + a * p) * (1 + a * q) = 1 + a * (p + q) := by
  have h : a * p * (a * q) = 0 := by
    rw [mul_assoc, ← mul_assoc p a q, hc, mul_assoc, h0, mul_zero, mul_zero]
  calc (1 + a * p) * (1 + a * q) = 1 + a * p + a * q + a * p * (a * q) := by noncomm_ring
    _ = 1 + a * (p + q) := by rw [h, add_zero, mul_add, add_assoc]

theorem det_one_add_compression (a p q r s ι κ N C : Module.End ℝ V) (E : W →ₗ[ℝ] V) (P : V →ₗ[ℝ] W)
    (hpq : p + q = 1) (hpq0 : p * q = 0) (hpa : p * a = a * p)
    (hNC : N * C = a) (hCN : C * N = a) (hpN : p * N = N * q)
    (hrs : r + s = q) (hrs0 : r * s = 0) (hra : r * a = a * r)
    (hι : ι * κ = 1) (hιa : ι * a = a * ι) (hιr : ι * r = s * ι)
    (hEP : E ∘ₗ P = r) :
    LinearMap.det (1 + a) = LinearMap.det (1 + P ∘ₗ a ∘ₗ E : W →ₗ[ℝ] W) ^ 4 := by
  have hsy : ∀ X Y : Module.End ℝ V, LinearMap.det (1 + X * Y) = LinearMap.det (1 + Y * X) :=
    fun X Y => dpb_sylv X Y
  have hA : 1 + a = (1 + a * p) * (1 + a * q) := by rw [dpb_ring a p q hpq0 hpa, hpq, mul_one]
  have hq : q = 1 - p := eq_sub_of_add_eq' hpq
  have hqa : q * a = a * q := by rw [hq, sub_mul, mul_sub, one_mul, mul_one, hpa]
  have hB1 : a * p = N * (q * C) := by rw [← hpa, ← hNC, ← mul_assoc, hpN, mul_assoc]
  have hB2 : q * C * N = a * q := by rw [mul_assoc, hCN, hqa]
  have hB : LinearMap.det (1 + a * p) = LinearMap.det (1 + a * q) := by
    rw [hB1, hsy N (q * C), hB2]
  have hC : 1 + a * q = (1 + a * r) * (1 + a * s) := by rw [dpb_ring a r s hrs0 hra, hrs]
  have hs : s = ι * r * κ := by rw [hιr, mul_assoc, hι, mul_one]
  have hD1 : 1 + a * s = ι * (1 + a * r) * κ := by
    rw [hs, mul_add, add_mul, mul_one, hι, ← mul_assoc ι a r, hιa]
    simp only [mul_assoc]
  have hdet : LinearMap.det ι * LinearMap.det κ = 1 := by rw [← map_mul, hι, map_one]
  have hD : LinearMap.det (1 + a * s) = LinearMap.det (1 + a * r) := by
    rw [hD1, map_mul, map_mul]
    calc LinearMap.det ι * LinearMap.det (1 + a * r) * LinearMap.det κ
        = LinearMap.det (1 + a * r) * (LinearMap.det ι * LinearMap.det κ) := by ring
      _ = LinearMap.det (1 + a * r) := by rw [hdet, mul_one]
  have hE : LinearMap.det (1 + P ∘ₗ a ∘ₗ E : W →ₗ[ℝ] W) = LinearMap.det (1 + a * r) := by
    have h := dpb_sylv E (P ∘ₗ a)
    have h2 : E ∘ₗ (P ∘ₗ a) = a * r := by
      show (E ∘ₗ P) ∘ₗ a = a * r
      rw [hEP, ← hra]
      rfl
    rw [h2] at h
    exact h.symm
  rw [hA, map_mul, hB, hC, map_mul, hD, hE]
  ring

theorem dpb_abs (t θ α ι N C : Module.End ℝ V) (E : W →ₗ[ℝ] V) (P : V →ₗ[ℝ] W)
    (hθ : ∀ v, θ (θ v) = v) (hα : ∀ v, α (α v) = v) (hθα : ∀ v, θ (α v) = α (θ v))
    (htθ : ∀ v, θ (t v) = t (θ v)) (htα : ∀ v, α (t v) = t (α v))
    (hNC : ∀ v, N (C v) = t v - v) (hCN : ∀ v, C (N v) = t v - v) (hθN : ∀ v, θ (N v) = -N (θ v))
    (hι : ∀ v, ι (ι v) = -v) (hιt : ∀ v, ι (t v) = t (ι v)) (hιθ : ∀ v, θ (ι v) = ι (θ v))
    (hια : ∀ v, α (ι v) = -ι (α v))
    (hEP : ∀ v, E (P v) = (1 / 4 : ℝ) • (v + α v - θ v - α (θ v))) (hPE : ∀ w, P (E w) = w) :
    LinearMap.det t = LinearMap.det (P ∘ₗ t ∘ₗ E : W →ₗ[ℝ] W) ^ 4 := by
  have key := det_one_add_compression (t - 1) ((1 / 2 : ℝ) • (1 + θ)) ((1 / 2 : ℝ) • (1 - θ))
    ((1 / 4 : ℝ) • (1 + α - θ - α * θ)) ((1 / 4 : ℝ) • (1 - α - θ + α * θ)) ι (-ι) N C E P
    (by ext v; simp; module)
    (by ext v; simp [hθ]; try module)
    (by ext v; simp [htθ]; try module)
    (by ext v; simp [hNC]) (by ext v; simp [hCN])
    (by ext v; simp [hθN]; try module)
    (by ext v; simp; module)
    (by ext v; simp [hθ, hα, hθα]; try module)
    (by ext v; simp [htθ, htα]; try module)
    (by ext v; simp [hι])
    (by ext v; simp [hιt])
    (by ext v; simp [hιθ, hια]; try module)
    (by ext v; simp [hEP])
  have e1 : (1 : Module.End ℝ V) + (t - 1) = t := by abel
  have e2 : (1 + P ∘ₗ (t - 1) ∘ₗ E : W →ₗ[ℝ] W) = P ∘ₗ t ∘ₗ E := by
    ext w; simp [hPE]
  rwa [e1, e2] at key

end ReciprocityTheory.ChartRestriction.DS
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPbC

section

@[expose] public section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def dpbE (ε : Fin n → Bool) : (PCoord ε → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := pmat
  map_add' z w := by
    ext a b
    simp only [pmat, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c z := by
    ext a b
    simp only [pmat, Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

def dpbP (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (PCoord ε → ℂ) where
  toFun W ab := (1 / 2 : ℝ) • (W ab.1.1 ab.1.2 + star (W ab.1.2 ab.1.1))
  map_add' W W' := by
    ext ab
    simp only [Matrix.add_apply, Pi.add_apply, star_add]
    module
  map_smul' c W := by
    ext ab
    simp only [Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply, star_smul, star_trivial]
    module

theorem dpbP_herm {ε : Fin n → Bool} {W : Matrix (Fin n) (Fin n) ℂ} (hW : Wᴴ = W) (ab : PCoord ε) :
    dpbP ε W ab = W ab.1.1 ab.1.2 := by
  have h : star (W ab.1.2 ab.1.1) = W ab.1.1 ab.1.2 := by
    have := congrFun (congrFun hW ab.1.1) ab.1.2
    simpa [Matrix.conjTranspose_apply] using this
  simp only [dpbP, LinearMap.coe_mk, AddHom.coe_mk]
  rw [h, Complex.real_smul]
  push_cast
  ring

theorem dpbP_E {ε : Fin n → Bool} (w : PCoord ε → ℂ) : dpbP ε (dpbE ε w) = w := by
  funext ab
  obtain ⟨⟨a, b⟩, hab, hne⟩ := ab
  have h1 : ¬ (a < b ∧ ε b ≠ ε a) := fun h => absurd h.1 (not_lt.mpr hab.le)
  simp only [dpbP, dpbE, LinearMap.coe_mk, AddHom.coe_mk, pmat, dif_pos (And.intro hab hne), dif_neg h1,
    star_star]
  rw [Complex.real_smul]
  push_cast
  ring

theorem dpb_JWJ (ε : Fin n → Bool) (W : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Jm ε * W * Jm ε) a b = if ε a = ε b then W a b else -W a b := by
  simp only [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal]
  cases ε a <;> cases ε b <;> simp

theorem dpbE_P {ε : Fin n → Bool} (W : Matrix (Fin n) (Fin n) ℂ) :
    dpbE ε (dpbP ε W) = (1 / 4 : ℝ) • (W + Wᴴ - Jm ε * W * Jm ε - (Jm ε * W * Jm ε)ᴴ) := by
  ext a b
  simp only [dpbE, dpbP, LinearMap.coe_mk, AddHom.coe_mk, pmat, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.conjTranspose_apply, dpb_JWJ]
  by_cases hε : ε a = ε b
  · have h1 : ¬ (b < a ∧ ε a ≠ ε b) := fun h => h.2 hε
    have h2 : ¬ (a < b ∧ ε b ≠ ε a) := fun h => h.2 hε.symm
    rw [dif_neg h1, dif_neg h2, if_pos hε, if_pos hε.symm]
    simp
  · rw [if_neg hε, if_neg (Ne.symm hε)]
    rcases lt_trichotomy a b with h | h | h
    · have h1 : ¬ (b < a ∧ ε a ≠ ε b) := fun h' => absurd h'.1 (not_lt.mpr h.le)
      rw [dif_neg h1, dif_pos (And.intro h (Ne.symm hε))]
      simp only [Complex.real_smul]
      push_cast
      simp only [star_add, star_mul', star_star, star_div₀, star_one, star_ofNat, star_neg]
      ring
    · exact absurd (h ▸ rfl) hε
    · rw [dif_pos (And.intro h hε)]
      simp only [star_neg, Complex.real_smul]
      push_cast
      ring

theorem dpb_JYJ {ε : Fin n → Bool} (y : PCoord ε → ℂ) : Jm ε * pmat y * Jm ε = -pmat y := by
  ext a b
  rw [dpb_JWJ]
  split_ifs with h
  · have : pmat y a b = 0 := by simp [pmat, h]
    rw [Matrix.neg_apply, this, neg_zero]
  · rw [Matrix.neg_apply]

theorem dpb_shc_neg (u : ℝ) : shc (-u) = shc u := by
  unfold shc
  by_cases h : u = 0
  · simp [h]
  · rw [if_neg (neg_ne_zero.mpr h), if_neg h, Real.sinh_neg, neg_div_neg_eq]

theorem dpb_shc_fac : (fun u : ℝ => u * ((shc u - 1) / u)) = fun u => shc u - 1 := by
  funext u
  unfold shc
  by_cases h : u = 0
  · simp [h]
  · rw [if_neg h]
    field_simp

theorem dpb_theta_ad {J Y : Matrix (Fin n) (Fin n) ℂ} (hJ : J * J = 1) (hY : J * Y * J = -Y)
    (W : Matrix (Fin n) (Fin n) ℂ) : J * (Y * W - W * Y) * J = -(Y * (J * W * J) - (J * W * J) * Y) := by
  have key : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (J * A * J) * (J * B * J) = J * (A * B) * J := by
    intro A B
    calc (J * A * J) * (J * B * J) = J * A * (J * J) * B * J := by simp only [Matrix.mul_assoc]
      _ = J * (A * B) * J := by rw [hJ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.sub_mul, ← key Y W, ← key W Y, hY]
  simp only [neg_mul, mul_neg]
  abel

theorem dpb_det {ε : Fin n → Bool} {U : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → ℝ} (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1) (hY : Jm ε * (U * dpbD x * Uᴴ) * Jm ε = -(U * dpbD x * Uᴴ)) :
    LinearMap.det (dpbL U x shc) = LinearMap.det (dpbP ε ∘ₗ dpbL U x shc ∘ₗ dpbE ε) ^ 4 := by
  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJh : (Jm ε)ᴴ = Jm ε := by
    rw [Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    change star (if ε a then (1 : ℂ) else -1) = (if ε a then 1 else -1)
    split_ifs <;> simp
  have hJJv : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  let θ : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => Jm ε * W * Jm ε
      map_add' := fun W W' => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c W => by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let α : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => Wᴴ
      map_add' := fun W W' => Matrix.conjTranspose_add W W'
      map_smul' := fun c W => by simp [Matrix.conjTranspose_smul] }
  let ι : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => Complex.I • W
      map_add' := fun W W' => smul_add _ _ _
      map_smul' := fun c W => by simp only [RingHom.id_apply]; exact smul_comm _ _ _ }
  let N : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => (U * dpbD x * Uᴴ) * W - W * (U * dpbD x * Uᴴ)
      map_add' := fun W W' => by simp only [Matrix.mul_add, Matrix.add_mul]; abel
      map_smul' := fun c W => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_sub] }
  let C : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) := dpbL U x (fun u => (shc u - 1) / u)
  have hsub : dpbH U x (fun u => u * ((shc u - 1) / u)) = dpbH U x (fun u => shc u - 1) := by
    rw [dpb_shc_fac]
  refine dpb_abs (dpbL U x shc) θ α ι N C (dpbE ε) (dpbP ε) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro v
    show Jm ε * (Jm ε * v * Jm ε) * Jm ε = v
    simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one, hJJv]
  · intro v
    show (vᴴ)ᴴ = v
    exact Matrix.conjTranspose_conjTranspose v
  · intro v
    show Jm ε * vᴴ * Jm ε = (Jm ε * v * Jm ε)ᴴ
    simp only [Matrix.conjTranspose_mul, hJh, Matrix.mul_assoc]
  · intro v
    show Jm ε * dpbH U x shc v * Jm ε = dpbH U x shc (Jm ε * v * Jm ε)
    exact dpbH_theta hU hU' hJJ hJh hY shc dpb_shc_neg v
  · intro v
    show (dpbH U x shc v)ᴴ = dpbH U x shc vᴴ
    exact dpbH_conjTranspose U x shc dpb_shc_neg v
  · intro v
    show (U * dpbD x * Uᴴ) * dpbH U x (fun u => (shc u - 1) / u) v -
      dpbH U x (fun u => (shc u - 1) / u) v * (U * dpbD x * Uᴴ) = dpbH U x shc v - v
    rw [dpbH_ad_left x hU, hsub, dpbH_sub_one x hU']
  · intro v
    show dpbH U x (fun u => (shc u - 1) / u) ((U * dpbD x * Uᴴ) * v - v * (U * dpbD x * Uᴴ)) =
      dpbH U x shc v - v
    rw [dpbH_ad_right x hU, hsub, dpbH_sub_one x hU']
  · intro v
    show Jm ε * ((U * dpbD x * Uᴴ) * v - v * (U * dpbD x * Uᴴ)) * Jm ε =
      -((U * dpbD x * Uᴴ) * (Jm ε * v * Jm ε) - (Jm ε * v * Jm ε) * (U * dpbD x * Uᴴ))
    exact dpb_theta_ad hJJ hY v
  · intro v
    show Complex.I • (Complex.I • v) = -v
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  · intro v
    show Complex.I • dpbH U x shc v = dpbH U x shc (Complex.I • v)
    exact (dpbH_smul U x shc Complex.I v).symm
  · intro v
    show Jm ε * (Complex.I • v) * Jm ε = Complex.I • (Jm ε * v * Jm ε)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  · intro v
    show (Complex.I • v)ᴴ = -(Complex.I • vᴴ)
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I, neg_smul]
  · intro v
    exact dpbE_P v
  · intro w
    exact dpbP_E w

end ReciprocityTheory.ChartRestriction.DS
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ShcAdC

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def shcAdC {ε : Fin n → Bool} (y : PCoord ε → ℂ) (w : PCoord ε → ℂ) : PCoord ε → ℂ :=
  fun ab => shcAd y (pmat w) ab.1.1 ab.1.2

theorem detPb {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    LinearMap.det ((fderiv ℝ (shcAd y) 0 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) =
      (LinearMap.det ((fderiv ℝ (shcAdC y) 0 : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
        (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))) ^ 4 := by
  set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
    with hUdef
  have hU : Uᴴ * U = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.1
  have hU' : U * Uᴴ = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.2
  have hY : U * dpbD (pev y) * Uᴴ = pmat y := (pmat_isHermitian y).spectral_theorem.symm
  have e1 : shcAd y = LinearMap.toContinuousLinearMap (dpbL U (pev y) shc) := rfl
  have e2 : shcAdC y = LinearMap.toContinuousLinearMap (dpbP ε ∘ₗ dpbL U (pev y) shc ∘ₗ dpbE ε) := by
    funext w ab
    refine (dpbP_herm (W := dpbH U (pev y) shc (pmat w)) ?_ ab).symm
    rw [dpbH_conjTranspose U _ shc dpb_shc_neg, (pmat_isHermitian w).eq]
  rw [e1, e2, ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact dpb_det hU hU' (by rw [hY]; exact dpb_JYJ y)

end ReciprocityTheory.ChartRestriction.DS
end
end
end
