module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import ReciprocityTheory.DualLattices.FischerAdjointStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.LinearAlgebra.Matrix.Block
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryGroupIntertwinerOfHighestWeightPolyStatement
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsJointHighestWeightLeadingMinorProduct

section

@[expose] public section

noncomputable section

open MvPolynomial Matrix

namespace GlobalTheory.CompactHowe.Minors

variable {N n : ℕ}

def IsBorelVec (hn : n ≤ N) (ν : Fin N → ℕ) (Δ : MvPolynomial (Fin N × Fin n) ℂ) : Prop :=
  Δ ≠ 0 ∧ ∀ (h : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin n) (Fin n) ℂ),
    (∀ i j, j < i → h i j = 0) → (∀ i j, j < i → g i j = 0) →
      subst2 h g Δ = ((∏ b, h b b ^ ν b) * ∏ a, g a a ^ ν (Fin.castLE hn a)) • Δ

theorem isBorelVec_one (hn : n ≤ N) : IsBorelVec hn (fun _ => 0) 1 :=
  ⟨one_ne_zero, fun h g _ _ => by simp⟩

theorem IsBorelVec.mul {hn : n ≤ N} {ν μ : Fin N → ℕ} {Δ Γ : MvPolynomial (Fin N × Fin n) ℂ}
    (h1 : IsBorelVec hn ν Δ) (h2 : IsBorelVec hn μ Γ) : IsBorelVec hn (fun b => ν b + μ b) (Δ * Γ) := by
  refine ⟨mul_ne_zero h1.1 h2.1, fun h g hh hg => ?_⟩
  rw [map_mul, h1.2 h g hh hg, h2.2 h g hh hg, smul_mul_smul_comm]
  congr 1
  simp only [pow_add, Finset.prod_mul_distrib]
  ring

theorem not_range_castLE {k m : ℕ} (hk : k ≤ m) (i : Fin m) (hi : i ∉ Set.range (Fin.castLE hk)) : k ≤ (i : ℕ) := by
  by_contra hc
  exact hi ⟨⟨i, by omega⟩, Fin.ext rfl⟩

theorem sum_castLE {M : Type*} [AddCommMonoid M] {k m : ℕ} (hk : k ≤ m) (f : Fin m → M)
    (hf : ∀ i : Fin m, k ≤ (i : ℕ) → f i = 0) : ∑ i, f i = ∑ i : Fin k, f (Fin.castLE hk i) :=
  (Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ f
    (fun i hi => hf i (not_range_castLE hk i hi)) fun _ => rfl).symm

theorem prod_pow_ite {k m : ℕ} (hk : k ≤ m) (c : Fin m → ℂ) :
    ∏ i, c i ^ (if (i : ℕ) < k then 1 else 0) = ∏ i : Fin k, c (Fin.castLE hk i) :=
  (Fintype.prod_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _
    (fun i hi => by rw [if_neg (not_lt.2 (not_range_castLE hk i hi)), pow_zero])
    fun i => by simp).symm

def block (hn : n ≤ N) {k : ℕ} (hk : k ≤ n) : Matrix (Fin k) (Fin k) (MvPolynomial (Fin N × Fin n) ℂ) :=
  Matrix.of fun i j => X (Fin.castLE (hk.trans hn) i, Fin.castLE hk j)

theorem det_block_ne_zero (hn : n ≤ N) {k : ℕ} (hk : k ≤ n) : (block hn hk).det ≠ 0 := by
  intro h0
  have h1 := (eval (fun p : Fin N × Fin n => if (p.1 : ℕ) = (p.2 : ℕ) then (1 : ℂ) else 0)).map_det (block hn hk)
  have h2 : (eval (fun p : Fin N × Fin n => if (p.1 : ℕ) = (p.2 : ℕ) then (1 : ℂ) else 0)).mapMatrix (block hn hk) = 1 := by
    ext i j
    simp [block, Matrix.one_apply, Fin.ext_iff]
  rw [h2, h0] at h1
  simp at h1

theorem det_lead {k m : ℕ} (hk : k ≤ m) (g : Matrix (Fin m) (Fin m) ℂ) (hg : ∀ i j, j < i → g i j = 0) :
    (g.submatrix (Fin.castLE hk) (Fin.castLE hk)).det = ∏ i : Fin k, g (Fin.castLE hk i) (Fin.castLE hk i) := by
  rw [Matrix.det_of_upperTriangular]
  · rfl
  · intro i j hij
    exact hg _ _ hij

theorem isBorelVec_det (hn : n ≤ N) {k : ℕ} (hk : k ≤ n) :
    IsBorelVec hn (fun b => if (b : ℕ) < k then 1 else 0) (block hn hk).det := by
  refine ⟨det_block_ne_zero hn hk, fun h g hh hg => ?_⟩
  have key : (subst2 h g).mapMatrix (block hn hk) =
      ((C : ℂ →+* _).mapMatrix (h.submatrix (Fin.castLE (hk.trans hn)) (Fin.castLE (hk.trans hn))))ᵀ * block hn hk *
        (C : ℂ →+* _).mapMatrix (g.submatrix (Fin.castLE hk) (Fin.castLE hk)) := by
    ext1 i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, block, Matrix.of_apply, subst2_X, Matrix.mul_apply,
      Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.submatrix_apply, Finset.sum_mul]
    rw [sum_castLE (hk.trans hn), Finset.sum_comm]
    · rw [sum_castLE hk]
      · refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
        rw [map_mul]; ring
      · intro l hl
        refine Finset.sum_eq_zero fun m _ => ?_
        rw [hg l _ (by rw [Fin.lt_def]; have := j.2; simp only [Fin.val_castLE]; omega)]
        simp
    · intro l hl
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [hh l _ (by rw [Fin.lt_def]; have := i.2; simp only [Fin.val_castLE]; omega)]
      simp
  rw [AlgHom.map_det, key, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, ← RingHom.map_det,
    det_lead _ _ hh, det_lead _ _ hg, prod_pow_ite (hk.trans hn) (fun b => h b b)]
  simp only [Fin.val_castLE]
  rw [prod_pow_ite hk (fun b => g b b), smul_eq_C_mul, map_mul]
  ring

theorem exists_isBorelVec (hn : n ≤ N) (M : ℕ) : ∀ ν : Fin N → ℕ, (∀ b, ν b ≤ M) → Antitone ν →
    (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → ∃ Δ, IsBorelVec hn ν Δ := by
  classical
  induction M with
  | zero =>
    intro ν hM _ _
    obtain rfl : ν = fun _ => 0 := funext fun b => Nat.le_zero.1 (hM b)
    exact ⟨1, isBorelVec_one hn⟩
  | succ M ih =>
    intro ν hM ha h0
    obtain ⟨Γ, hΓ⟩ := ih (fun b => ν b - 1) (fun b => by have := hM b; omega)
      (fun a b hab => Nat.sub_le_sub_right (ha hab) 1) (fun b hb => by simp [h0 b hb])
    have hex : ∃ k : ℕ, ∀ b : Fin N, k ≤ (b : ℕ) → ν b = 0 := ⟨n, h0⟩
    have hk : Nat.find hex ≤ n := Nat.find_min' hex h0
    refine ⟨(block hn hk).det * Γ, ?_⟩
    have := (isBorelVec_det hn hk).mul hΓ
    convert this using 2 with b
    split_ifs with hb
    · have h1 := Nat.find_min hex hb
      push Not at h1
      obtain ⟨c, hc, hc0⟩ := h1
      have : ν c ≤ ν b := ha (Fin.le_def.2 hc)
      omega
    · have := Nat.find_spec hex b (not_lt.1 hb)
      omega

theorem exists_highestWeight (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (ha : Antitone ν)
    (h0 : ∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) :
    ∃ Δ : MvPolynomial (Fin N × Fin n) ℂ, Δ ≠ 0 ∧
      (∀ h g, ReciprocityTheory.PGsh.IsUpperUnitri h → ReciprocityTheory.PGsh.IsUpperUnitri g → subst2 h g Δ = Δ) ∧
      ∀ (d : Fin N → ℂ) (e : Fin n → ℂ), subst2 (Matrix.diagonal d) (Matrix.diagonal e) Δ =
        ((∏ b, d b ^ ν b) * ∏ a, e a ^ ν (Fin.castLE hn a)) • Δ := by
  obtain ⟨Δ, h1, h2⟩ := exists_isBorelVec hn (∑ b, ν b) ν
    (fun b => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)) ha h0
  refine ⟨Δ, h1, fun h g hh hg => ?_, fun d e => ?_⟩
  · rw [h2 h g hh.2 hg.2]
    simp [hh.1, hg.1]
  · rw [h2 _ _ (fun i j hij => Matrix.diagonal_apply_ne _ hij.ne') (fun i j hij => Matrix.diagonal_apply_ne _ hij.ne')]
    simp

end GlobalTheory.CompactHowe.Minors

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsJointHighestWeightLeadingMinorProductStatement

section

@[expose] public section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_jointHighestWeight_leadingMinorProduct : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → ∃ Δ : MvPolynomial (Fin N × Fin n) ℂ, Δ ≠ 0 ∧ (∀ h g, ReciprocityTheory.PGsh.IsUpperUnitri h → ReciprocityTheory.PGsh.IsUpperUnitri g → subst2 h g Δ = Δ) ∧ ∀ (d : Fin N → ℂ) (e : Fin n → ℂ), subst2 (Matrix.diagonal d) (Matrix.diagonal e) Δ = ((∏ b, d b ^ ν b) * ∏ a, e a ^ ν (Fin.castLE hn a)) • Δ := by
  first | exact @GlobalTheory.CompactHowe.Minors.exists_highestWeight | exact GlobalTheory.CompactHowe.Minors.exists_highestWeight | (intros; apply GlobalTheory.CompactHowe.Minors.exists_highestWeight <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTensorTypesIntertwinerMatrixPolynomials

section

@[expose] public section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompactHoweJoint

theorem exists_bilinear {G G' H H' P : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H']
    [AddCommGroup P] [Module ℂ P] (S : Set G) (S' : Set G') (τ : G → H →ₗ[ℂ] H) (τ' : G' → H' →ₗ[ℂ] H')
    (a : G → P →ₗ[ℂ] P) (b : G' → P →ₗ[ℂ] P) (hab : ∀ g h x, a g (b h x) = b h (a g x))
    (hirr : ∀ U : Submodule ℂ H, (∀ g ∈ S, ∀ v ∈ U, τ g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (hirr' : ∀ U : Submodule ℂ H', (∀ g ∈ S', ∀ v ∈ U, τ' g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (L : H →ₗ[ℂ] P) (L' : H' →ₗ[ℂ] P) (hL : ∀ g ∈ S, ∀ u, L (τ g u) = a g (L u))
    (hL' : ∀ h ∈ S', ∀ u, L' (τ' h u) = b h (L' u)) (v₀ : H) (v₀' : H') (h0 : L v₀ = L' v₀')
    (hne : L v₀ ≠ 0) :
    ∃ Ψ : H' →ₗ[ℂ] H →ₗ[ℂ] P, Ψ ≠ 0 ∧ ∀ h ∈ S', ∀ g ∈ S, ∀ v' v, Ψ (τ' h v') (τ g v) = b h (a g (Ψ v' v)) := by
  let 𝓗 : Submodule ℂ (H →ₗ[ℂ] P) :=
    { carrier := {A | ∀ g ∈ S, ∀ u, A (τ g u) = a g (A u)}
      add_mem' := fun {A B} hA hB g hg u => by
        simp only [LinearMap.add_apply, map_add (f := _), hA g hg u, hB g hg u]
      zero_mem' := fun g _ u => by simp
      smul_mem' := fun c A hA g hg u => by
        simp only [LinearMap.smul_apply, map_smul, hA g hg u] }
  have hv₀ : v₀ ≠ 0 := fun h => hne (by rw [h, map_zero])
  have hv₀' : v₀' ≠ 0 := fun h => hne (by rw [h0, h, map_zero])
  let ev : 𝓗 →ₗ[ℂ] P := (LinearMap.applyₗ v₀).comp 𝓗.subtype
  have hev : ∀ A : 𝓗, ev A = (A : H →ₗ[ℂ] P) v₀ := fun _ => rfl
  have hinj : Function.Injective ev := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro A hA
    rcases hirr (LinearMap.ker (A : H →ₗ[ℂ] P)) (fun g hg v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [A.2 g hg v, hv, map_zero]) with h | h
    · exact absurd ((Submodule.eq_bot_iff _).1 h v₀ hA) hv₀
    · exact Subtype.ext (LinearMap.ker_eq_top.1 h)
  have hstab : ∀ h, ∀ A ∈ 𝓗, (b h).comp A ∈ 𝓗 := fun h A hA g hg u => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hA g hg u, hab]
  have hrange : ∀ v', L' v' ∈ LinearMap.range ev := by
    rcases hirr' ((LinearMap.range ev).comap L') (fun h hh v hv => by
      obtain ⟨A, hA⟩ := hv
      refine ⟨⟨(b h).comp A, hstab h _ A.2⟩, ?_⟩
      rw [hL' h hh, ← hA]
      rfl) with h | h
    · exact absurd ((Submodule.eq_bot_iff _).1 h v₀' ⟨⟨L, hL⟩, h0⟩) hv₀'
    · intro v'
      have : v' ∈ (LinearMap.range ev).comap L' := h ▸ Submodule.mem_top
      exact this
  let Φ : H' →ₗ[ℂ] 𝓗 :=
    (LinearEquiv.ofInjective ev hinj).symm.toLinearMap.comp (L'.codRestrict _ hrange)
  have hΦ : ∀ v', ev (Φ v') = L' v' := fun v' =>
    congrArg Subtype.val ((LinearEquiv.ofInjective ev hinj).apply_symm_apply (L'.codRestrict _ hrange v'))
  refine ⟨𝓗.subtype.comp Φ, fun h => hne ?_, fun h hh g hg v' v => ?_⟩
  · rw [h0, ← hΦ, hev]
    exact congrArg (fun f : H' →ₗ[ℂ] H →ₗ[ℂ] P => f v₀' v₀) h
  · have key : Φ (τ' h v') = ⟨(b h).comp (Φ v'), hstab h _ (Φ v').2⟩ := by
      apply hinj
      rw [hΦ, hL' h hh, ← hΦ v']
      rfl
    show (Φ (τ' h v') : H →ₗ[ℂ] P) (τ g v) = b h (a g ((Φ v' : H →ₗ[ℂ] P) v))
    rw [key]
    show b h ((Φ v' : H →ₗ[ℂ] P) (τ g v)) = _
    rw [(Φ v').2 g hg v]

theorem mem_K_iff {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) :
    g ∈ Formalism.REAL.Kset (allPos k) ↔ g ∈ UJset (allPos k) := by
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by simp [Formalism.REAL.Jm, allPos]
  show (g ∈ Matrix.unitaryGroup (Fin k) ℂ ∧ g * Formalism.REAL.Jm (allPos k) = Formalism.REAL.Jm (allPos k) * g) ↔
    gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k)
  rw [hJ, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul, Matrix.mem_unitaryGroup_iff']
  simp [Matrix.star_eq_conjTranspose]

open MvPolynomial in
theorem subst2_one_right {N n : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (P : MvPolynomial (Fin N × Fin n) ℂ) :
    subst2 h 1 P = ReciprocityTheory.PGsh.rowSubst h P := by
  have key : subst2 h (1 : Matrix (Fin n) (Fin n) ℂ) = ReciprocityTheory.PGsh.rowSubst h := by
    refine algHom_ext fun p => ?_
    rw [subst2_X, ReciprocityTheory.PGsh.rowSubst, aeval_X]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single p.2]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
  rw [key]

open MvPolynomial in
theorem subst2_one_left {N n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (Fin n × Fin N) ℂ) :
    subst2 1 g (rename Prod.swap P) = rename Prod.swap (ReciprocityTheory.PGsh.rowSubst g P) := by
  have key : (subst2 (1 : Matrix (Fin N) (Fin N) ℂ) g).comp (rename Prod.swap) =
      (rename Prod.swap).comp (ReciprocityTheory.PGsh.rowSubst (ι := Fin N) g) := by
    refine algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, subst2_X, ReciprocityTheory.PGsh.rowSubst, aeval_X,
      Finset.sum_eq_single p.2]
    · have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) p.2 p.swap.1 = 1 := Matrix.one_apply_eq _

      simp [map_sum, h1]
    · intro l _ hl
      have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) l p.swap.1 = 0 := Matrix.one_apply_ne hl
      simp [h1]
    · simp
  exact congrArg (fun f => f P) key

theorem isUpperUnitri_one (k : ℕ) : ReciprocityTheory.PGsh.IsUpperUnitri (1 : Matrix (Fin k) (Fin k) ℂ) :=
  ⟨fun _ => Matrix.one_apply_eq _, fun _ _ h => Matrix.one_apply_ne h.ne'⟩


open MvPolynomial in
theorem exists_joint_intertwiner : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (τ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → IsURepOn (UJset (allPos n)) τ → IsKTypeOf (allPos n) τ (fun a => (ν (Fin.castLE hn a) : ℝ)) ⊤ → IsURepOn (UJset (allPos N)) τ' → IsKTypeOf (allPos N) τ' (fun b => (ν b : ℝ)) ⊤ → ∃ Ψ : H' →ₗ[ℂ] H →ₗ[ℂ] MvPolynomial (Fin N × Fin n) ℂ, Ψ ≠ 0 ∧ ∀ h ∈ UJset (allPos N), ∀ g ∈ UJset (allPos n), ∀ v' v, Ψ (τ' h v') (τ g v) = subst2 h g (Ψ v' v) := by
  intro N n hn ν H _ _ _ τ H' _ _ _ τ' hν hz hτ hK hτ' hK'
  obtain ⟨Δ, hΔ, hU, hD⟩ := GlobalTheory.T.exists_jointHighestWeight_leadingMinorProduct N n hn ν hν hz
  have hsw : ∀ Q : MvPolynomial (Fin N × Fin n) ℂ,
      rename (Prod.swap : Fin n × Fin N → _) (rename Prod.swap Q) = Q := fun Q => by
    rw [rename_rename]; simp
  have hinj : Function.Injective
      (rename (Prod.swap : Fin n × Fin N → Fin N × Fin n) : MvPolynomial _ ℂ → MvPolynomial _ ℂ) :=
    rename_injective _ Prod.swap_injective
  obtain ⟨L', hL', v₀', hv'⟩ := GlobalTheory.T.exists_unitaryGroup_intertwiner_of_highest_weight_polynomial N (Fin n) ν H' τ' Δ hτ' hK' hΔ
    (fun g hg => by rw [← subst2_one_right, hU g 1 hg (isUpperUnitri_one n)])
    (fun d => by
      have := hD d (fun _ => 1)
      rw [Matrix.diagonal_one, subst2_one_right] at this
      simpa using this)
  obtain ⟨L, hL, v₀, hv⟩ := GlobalTheory.T.exists_unitaryGroup_intertwiner_of_highest_weight_polynomial n (Fin N) (fun a => ν (Fin.castLE hn a)) H τ
    (rename Prod.swap Δ) hτ hK
    (fun h => hΔ (by rw [← hsw Δ, h, map_zero]))
    (fun g hg => hinj (by rw [← subst2_one_left, hsw, hU 1 g (isUpperUnitri_one N) hg]))
    (fun e => hinj (by
      have := hD (fun _ => 1) e
      rw [Matrix.diagonal_one] at this
      rw [← subst2_one_left, map_smul, hsw, this]
      simp))
  have hLv : ((rename (Prod.swap : Fin n × Fin N → Fin N × Fin n)).toLinearMap.comp L) v₀ = Δ := by
    show rename Prod.swap (L v₀) = Δ
    rw [hv, hsw]
  obtain ⟨Ψ, hΨ, hΨe⟩ := exists_bilinear (UJset (allPos n)) (UJset (allPos N))
    (fun g => (τ g).toLinearMap) (fun h => (τ' h).toLinearMap)
    (fun g => (subst2 (1 : Matrix (Fin N) (Fin N) ℂ) g).toLinearMap)
    (fun h => (subst2 h (1 : Matrix (Fin n) (Fin n) ℂ)).toLinearMap)
    (fun g h x => by simp [subst2_mul])
    (fun U hS => hK.2.2.1 U le_top fun g hg => hS g ((mem_K_iff g).1 hg))
    (fun U hS => hK'.2.2.1 U le_top fun g hg => hS g ((mem_K_iff g).1 hg))
    ((rename (Prod.swap : Fin n × Fin N → Fin N × Fin n)).toLinearMap.comp L) L'
    (fun g hg u => by
      show rename Prod.swap (L (τ g u)) = subst2 1 g (rename Prod.swap (L u))
      rw [hL g hg u, subst2_one_left])
    (fun h hh u => by
      show L' (τ' h u) = subst2 h 1 (L' u)
      rw [hL' h hh u, subst2_one_right])
    v₀ v₀' (hLv.trans hv'.symm) (by rw [hLv]; exact hΔ)
  refine ⟨Ψ, hΨ, fun h hh g hg v' v => ?_⟩
  have := hΨe h hh g hg v' v
  simpa [subst2_mul] using this

end GlobalTheory.CompactHoweJoint

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTensorTypesIntertwinerMatrixPolynomialsStatement

section

@[expose] public section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_tensor_types_intertwiner_matrix_polynomials : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (τ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → IsURepOn (UJset (allPos n)) τ → IsKTypeOf (allPos n) τ (fun a => (ν (Fin.castLE hn a) : ℝ)) ⊤ → IsURepOn (UJset (allPos N)) τ' → IsKTypeOf (allPos N) τ' (fun b => (ν b : ℝ)) ⊤ → ∃ Ψ : H' →ₗ[ℂ] H →ₗ[ℂ] MvPolynomial (Fin N × Fin n) ℂ, Ψ ≠ 0 ∧ ∀ h ∈ UJset (allPos N), ∀ g ∈ UJset (allPos n), ∀ v' v, Ψ (τ' h v') (τ g v) = subst2 h g (Ψ v' v) := by
  first | exact @GlobalTheory.CompactHoweJoint.exists_joint_intertwiner | exact GlobalTheory.CompactHoweJoint.exists_joint_intertwiner | (intros; apply GlobalTheory.CompactHoweJoint.exists_joint_intertwiner <;> assumption)
end
end
