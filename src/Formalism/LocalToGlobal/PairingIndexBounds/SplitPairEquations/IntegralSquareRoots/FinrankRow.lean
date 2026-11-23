module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstUniqueOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.GMConjTranspose
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.MemStandardThetaLatticeIffAdelicIdeal

section

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def rowE (D : D7) (N N' : ℕ) : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] (Fin N' → TaylorLogMetric.VC D N 1) where
  toFun z := fun i τ _ j => z τ i j
  invFun w := fun τ i j => w i τ 0 j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv w := by
    funext i τ a j
    rw [Subsingleton.elim a 0]

def colE (D : D7) (N N' : ℕ) : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] (Fin N → TaylorLogMetric.VC D N' 1) where
  toFun z := fun j τ _ i => z τ i j
  invFun w := fun τ i j => w j τ 0 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv w := by
    funext i τ a j
    rw [Subsingleton.elim a 0]

theorem form_row (A : ℝ) (N N' : ℕ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' x y = ∑ i, Ker.formV A D.what₂.Tau N 1 (rowE D N N' x i) (rowE D N N' y i) := by
  simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, rowE, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.univ_unique, Finset.sum_singleton]
  rw [← Finset.sum_div, Finset.sum_comm]

theorem form_col (A : ℝ) (N N' : ℕ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' x y = ∑ j, Ker.formV A D.what₂.Tau N' 1 (colE D N N' x j) (colE D N N' y j) := by
  simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, colE, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.univ_unique, Finset.sum_singleton]
  rw [← Finset.sum_div]
  congr 1
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun τ _ => Finset.sum_comm

theorem formV_pos {A : ℝ} (hA : 0 < A) (n : Type) [Fintype n] (N N' : ℕ) : IsPosDef (Ker.formV A n N N') := by
  intro x hx
  have e : (Ker.formV A n N N' x x).re = (∑ τ, ∑ i, ∑ j, Complex.normSq (x τ i j)) / A := by
    simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, Complex.mul_conj]
    rw [← Complex.ofReal_re ((∑ τ, ∑ i, ∑ j, Complex.normSq (x τ i j)) / A)]
    push_cast
    rfl
  rw [e]
  refine div_pos ?_ hA
  obtain ⟨τ, i, j, h⟩ : ∃ τ i j, x τ i j ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hx (funext fun τ => funext fun i => funext fun j => hno τ i j)
  calc 0 < Complex.normSq (x τ i j) := Complex.normSq_pos.mpr h
    _ ≤ ∑ j, Complex.normSq (x τ i j) :=
        Finset.single_le_sum (f := fun j => Complex.normSq (x τ i j)) (fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, Complex.normSq (x τ i j) :=
        Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (x τ i j))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ τ, ∑ i, ∑ j, Complex.normSq (x τ i j) :=
        Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, Complex.normSq (x τ i j))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ τ)

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Ker.Base D cc δ)

include B in
theorem area_pos' : 0 < TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂ := by
  have := B.areaOK
  unfold Ker.Base.AreaOK at this
  show 0 < TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)
  rw [this]
  exact Formalism.L2.Th1.F.areaPos_thm B.L

abbrev La0 (_B : Ker.Base D cc δ) (N N' : ℕ) : AddSubgroup (TaylorLogMetric.VC D N N') :=
  TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')

theorem mem_standardThetaLattice_iff_adelicIdeal (N N' : ℕ) (x : TaylorLogMetric.VC D N N') : x ∈ La0 B N N' ↔ ∀ i j, (fun τ => x τ i j) ∈ B.lamM := by
  have := B.lat0OK N N'
  unfold Ker.Base.Lat0OK at this
  show x ∈ TaylorLogMetric.La D B.tor _ _ ↔ _
  rw [this]
  rfl

theorem lat_row (N N' : ℕ) (x : TaylorLogMetric.VC D N N') : x ∈ La0 B N N' ↔ ∀ i, rowE D N N' x i ∈ La0 B N 1 := by
  simp only [mem_standardThetaLattice_iff_adelicIdeal]
  exact ⟨fun h i _ j => h i j, fun h i j => h i 0 j⟩

theorem lat_col (N N' : ℕ) (x : TaylorLogMetric.VC D N N') : x ∈ La0 B N N' ↔ ∀ j, colE D N N' x j ∈ La0 B N' 1 := by
  simp only [mem_standardThetaLattice_iff_adelicIdeal]
  exact ⟨fun h j _ i => h i j, fun h i j => h j 0 i⟩

theorem neg_one_zpow_sum {ι : Type} (s : Finset ι) (m : ι → ℤ) : (-1 : ℂ) ^ (∑ i ∈ s, m i) = ∏ i ∈ s, (-1 : ℂ) ^ m i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (by norm_num), ih]

theorem al_prod {ι : Type} [Fintype ι] {N N' M M' : ℕ} (x : TaylorLogMetric.VC D N N') (y : ι → TaylorLogMetric.VC D M M')
    (hf : TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x x = ∑ i, TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) (y i) (y i))
    (hq : ∀ i, ∃ m : ℤ, Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) (y i) (y i)).re = (m : ℝ)) :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x = ∏ i, TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (y i) := by
  choose m hm using hq
  have h : Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x x).re = ((∑ i, m i : ℤ) : ℝ) := by
    rw [hf, Complex.re_sum, Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun i _ => hm i
  unfold TaylorLogMetric.al
  rw [h, round_intCast, neg_one_zpow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hm i, round_intCast]

theorem al_row (hS : B.StdOK) (N N' : ℕ) (x : TaylorLogMetric.VC D N N') (hx : x ∈ La0 B N N') :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x = ∏ i, TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (rowE D N N' x i) :=
  al_prod x _ (form_row _ N N' x x) fun i => B.qInt0 hS N 1 _ ((lat_row B N N' x).1 hx i)

theorem al_col (hS : B.StdOK) (N N' : ℕ) (x : TaylorLogMetric.VC D N N') (hx : x ∈ La0 B N N') :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x = ∏ j, TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (colE D N N' x j) :=
  al_prod x _ (form_col _ N N' x x) fun j => B.qInt0 hS N' 1 _ ((lat_col B N N' x).1 hx j)

end Formalism.L2.PairingIndexBounds.Eq.J
end
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.FinrankRow

section

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def phiU {N N' : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) :
    TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N' :=
  phiL (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (Matrix.mem_unitaryGroup_iff'.mp γ.2) (Matrix.mem_unitaryGroup_iff.mp γ.2)
    (Matrix.mem_unitaryGroup_iff'.mp γ'.2) (Matrix.mem_unitaryGroup_iff.mp γ'.2)

def cjU {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix.unitaryGroup (Fin n) D.host.E :=
  ⟨(star (γ : Matrix (Fin n) (Fin n) D.host.E))ᵀ, by
    rw [Matrix.mem_unitaryGroup_iff]
    have h : star ((star (γ : Matrix (Fin n) (Fin n) D.host.E))ᵀ) = (γ : Matrix (Fin n) (Fin n) D.host.E)ᵀ := by
      ext i j
      simp [Matrix.star_apply, Matrix.transpose_apply]
    rw [h, ← Matrix.transpose_mul, Matrix.mem_unitaryGroup_iff.mp γ.2, Matrix.transpose_one]⟩

theorem map_row {N N' : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E) (x : TaylorLogMetric.VC D N N') (i : Fin N') :
    rowE D N N' (phiU γ 1 x) i = phiU γ 1 (rowE D N N' x i) := by
  funext τ a j
  show (gM (1 : Matrix (Fin N') (Fin N') D.host.E) τ * Matrix.of (x τ) * (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) i j =
    (gM (1 : Matrix (Fin 1) (Fin 1) D.host.E) τ * Matrix.of (rowE D N N' x i τ) *
      (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) a j
  rw [gM_one, gM_one, Matrix.one_mul, Matrix.one_mul, Matrix.mul_apply, Matrix.mul_apply]
  rfl

theorem map_col {N N' : ℕ} (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (x : TaylorLogMetric.VC D N N') (j : Fin N) :
    colE D N N' (phiU 1 γ' x) j = phiU (cjU γ') 1 (colE D N N' x j) := by
  funext τ a i
  show (gM (γ' : Matrix (Fin N') (Fin N') D.host.E) τ * Matrix.of (x τ) * (gM (1 : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) i j =
    (gM (1 : Matrix (Fin 1) (Fin 1) D.host.E) τ * Matrix.of (colE D N N' x j τ) *
      (gM ((star (γ' : Matrix (Fin N') (Fin N') D.host.E))ᵀ) τ)ᴴ) a i
  rw [gM_one, gM_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  show TaylorLogMetric.embT D τ ((γ' : Matrix (Fin N') (Fin N') D.host.E) i k) * x τ k j =
    x τ k j * star (TaylorLogMetric.embT D τ (star ((γ' : Matrix (Fin N') (Fin N') D.host.E) i k)))
  rw [embT_star', star_star, mul_comm]

theorem det_gM {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) : (gM M τ).det = TaylorLogMetric.embT D τ M.det :=
  ((TaylorLogMetric.embT D τ).map_det M).symm

theorem gM_sub {n : ℕ} (A C : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) : gM (A - C) τ = gM A τ - gM C τ := by
  ext i j
  simp [gM]

theorem nofix {N N' : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E)
    (hγ : (1 - (γ : Matrix (Fin N) (Fin N) D.host.E)).det ≠ 0) (y : TaylorLogMetric.VC D N N') (h : (phiU γ 1).symm y = y) : y = 0 := by
  funext τ
  have h1 : (gM (1 : Matrix (Fin N') (Fin N') D.host.E) τ)ᴴ * Matrix.of (y τ) * gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ =
      Matrix.of (y τ) := congrFun h τ
  rw [gM_one, Matrix.conjTranspose_one, Matrix.one_mul] at h1
  have h2 : Matrix.of (y τ) * gM (1 - (γ : Matrix (Fin N) (Fin N) D.host.E)) τ = 0 := by
    rw [gM_sub, gM_one, Matrix.mul_sub, Matrix.mul_one, h1, sub_self]
  have hu : IsUnit (gM (1 - (γ : Matrix (Fin N) (Fin N) D.host.E)) τ).det := by
    rw [det_gM]
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero _).mpr hγ)
  have h3 := Matrix.mul_nonsing_inv_cancel_right _ (Matrix.of (y τ)) hu
  rw [h2, Matrix.zero_mul] at h3
  exact h3.symm

theorem det_cjU {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) D.host.E) :
    ((cjU γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E).det =
      star (γ : Matrix (Fin n) (Fin n) D.host.E).det := by
  show ((star (γ : Matrix (Fin n) (Fin n) D.host.E))ᵀ).det = _
  rw [Matrix.det_transpose, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]

theorem ne_cjU {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) D.host.E)
    (hγ : (1 - (γ : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0) :
    (1 - ((cjU γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0 := by
  have h : (1 - ((cjU γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) =
      (star (1 - (γ : Matrix (Fin n) (Fin n) D.host.E)))ᵀ := by
    rw [star_sub, star_one, Matrix.transpose_sub, Matrix.transpose_one]
    rfl
  rw [h, Matrix.det_transpose, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]
  exact star_ne_zero.mpr hγ

theorem det_row {N : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E) :
    LinearMap.det ((phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1) : TaylorLogMetric.VC D N 1 →ₗ[ℂ] TaylorLogMetric.VC D N 1) =
      ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det) := by
  let g : D.what₂.Tau → (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) := fun τ =>
    Matrix.toLin' (((gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ)ᵀ)
  let f : D.what₂.Tau → (Fin 1 → Fin N → ℂ) →ₗ[ℂ] (Fin 1 → Fin N → ℂ) := fun τ =>
    LinearMap.pi fun a => (g τ).comp (LinearMap.proj a)
  have e : ((phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1) : TaylorLogMetric.VC D N 1 →ₗ[ℂ] TaylorLogMetric.VC D N 1) =
      LinearMap.pi fun τ => (f τ).comp (LinearMap.proj τ) := by
    refine LinearMap.ext fun x => ?_
    funext τ a j
    show (gM (1 : Matrix (Fin 1) (Fin 1) D.host.E) τ * Matrix.of (x τ) * (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) a j =
      (((gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ)ᵀ *ᵥ (x τ a)) j
    rw [gM_one, Matrix.one_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [e, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun τ _ => ?_
  show LinearMap.det (LinearMap.pi fun a => (g τ).comp (LinearMap.proj a)) = _
  rw [LinearMap.det_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, LinearMap.det_toLin',
    Matrix.det_transpose, Matrix.det_conjTranspose, det_gM, embT_star']

theorem finrank_row (N : ℕ) : Module.finrank ℂ (TaylorLogMetric.VC D N 1) = Fintype.card D.what₂.Tau * N := by
  simp [Module.finrank_pi_fintype]

end Formalism.L2.PairingIndexBounds.Eq.J
end
end
end
