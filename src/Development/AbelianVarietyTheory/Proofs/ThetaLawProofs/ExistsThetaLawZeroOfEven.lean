module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Mathlib.LinearAlgebra.Matrix.Symmetric
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SubConjTransposeOfSymm
public import ReciprocityTheory.ThetaQuasiPeriods.Transl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.Blocks
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SpGenStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SpGenStatement
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OfRealVecHalfVec
import ReciprocityTheory.ThetaQuasiPeriods.Change
import ReciprocityTheory.ThetaQuasiPeriods.Transl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.GenBase

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsSymmMulVecAddDiagModTwo

section

@[expose] public section

namespace GlobalTheory

theorem exists_isSymm_mulVec_add_diag_mod_two :
    ∀ (g : ℕ) (n n' : Fin g → ℤ), Even (n ⬝ᵥ n') →
      ∃ S : Matrix (Fin g) (Fin g) ℤ, S.IsSymm ∧
        ∀ i, (2 : ℤ) ∣ (S.mulVec n) i + S i i - n' i := by
  intro g n n' h
  by_cases hall : ∀ i, Even (n i)
  · refine ⟨Matrix.diagonal n', Matrix.isSymm_diagonal _, fun i => ?_⟩
    obtain ⟨k, hk⟩ := hall i
    rw [Matrix.mulVec_diagonal, Matrix.diagonal_apply_eq, hk]
    exact ⟨n' i * k, by ring⟩
  · obtain ⟨p, hp⟩ := not_forall.mp hall
    obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hp
    obtain ⟨m, hm⟩ := h
    refine ⟨Matrix.of fun i j => (if i = p then n' j else 0) + (if j = p then n' i else 0),
      ?_, fun i => ?_⟩
    · ext i j
      simp only [Matrix.transpose_apply, Matrix.of_apply]
      ring
    · have hm' : ∑ j, n' j * n j = m + m := by
        rw [← hm]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      have h2 : ∑ j, (if j = p then n' i else 0) * n j = n' i * n p := by
        simp
      by_cases hi : i = p
      · subst hi
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
          if_true, hm', h2, hk]
        exact ⟨m + n' i * k + n' i, by ring⟩
      · simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
          if_neg hi, h2, hk, zero_mul, Finset.sum_const_zero]
        exact ⟨n' i * k, by ring⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaLawMul

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyPow


open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi in
theorem thetaLaw_mul : ∀ (g : ℕ) (sp sq : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (n n' m m' k k' : Fin g → ℤ), sp ∈ Matrix.symplecticGroup (Fin g) ℤ → sq ∈ Matrix.symplecticGroup (Fin g) ℤ → GlobalTheory.KeyPow.ThetaLaw g sq n n' m m' → GlobalTheory.KeyPow.ThetaLaw g sp m m' k k' → GlobalTheory.KeyPow.ThetaLaw g (sp * sq) n n' k k' := by
  intro g x y n n' m m' k k' hx hy Hy Hx
  obtain ⟨c₁, hc₁, h₁⟩ := Hy
  obtain ⟨c₂, hc₂, h₂⟩ := Hx
  refine ⟨c₂ * c₁, by rw [mul_pow, hc₁, hc₂, _root_.one_mul], fun τ hτ z => ?_⟩
  have hjy := jAut_isUnit hy hτ
  have hτ₂ := spAct_mem hy hτ
  have hjx := jAut_isUnit hx hτ₂
  rw [spAct_mul x y τ hjy, zAct_mul x y τ hjy z, h₂ _ hτ₂, h₁ τ hτ z, det_jAut_mul x y τ hjy,
    expArg_mul x y τ hjy hjx (sp_A hy hτ.1 hjy) z, eC_add]
  ring

end GlobalTheory.KeyPow
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaSqCongrModTwo

section

@[expose] public section

noncomputable section

open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.KeyPow

theorem theta_sq_congr_mod_two {g : ℕ} {k k' m m' : Fin g → ℤ} (h : ∀ i, k i % 2 = m i % 2)
    (h' : ∀ i, k' i % 2 = m' i % 2) (z : Fin g → ℂ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    theta (halfVec k) (halfVec k') z τ ^ 2 = theta (halfVec m) (halfVec m') z τ ^ 2 := by
  rw [theta_sq_red k k', theta_sq_red m m', funext h, funext h']

theorem ThetaLaw.congr_target {g : ℕ} {sp : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    {n n' k k' m m' : Fin g → ℤ} (hl : ThetaLaw g sp n n' k k') (h : ∀ i, m i % 2 = k i % 2)
    (h' : ∀ i, m' i % 2 = k' i % 2) : ThetaLaw g sp n n' m m' := by
  obtain ⟨c, hc, hlaw⟩ := hl
  exact ⟨c, hc, fun τ hτ z => by rw [theta_sq_congr_mod_two h h']; exact hlaw τ hτ z⟩

theorem thetaLaw_spTransl {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) (hS : S.IsSymm) (n n' : Fin g → ℤ) :
    ThetaLaw g (spTransl S) n n' n (n' - S *ᵥ n - fun i => S i i) := by
  set X : ℂ := -(ofRealVec (halfVec n) ⬝ᵥ (S.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec (halfVec n))) / 2 -
      ofRealVec (halfVec n) ⬝ᵥ (fun i => ((S i i : ℤ) : ℂ) / 2) with hX
  refine ⟨eC X ^ 2, ?_, fun τ _ z => ?_⟩
  · rw [← pow_mul, eC_pow]
    have h8 : ((2 * 4 : ℕ) : ℂ) * X = ((-(n ⬝ᵥ (S *ᵥ n)) - 2 * (n ⬝ᵥ fun i => S i i) : ℤ) : ℂ) := by
      have hd : ofIntVec n ⬝ᵥ (fun i => ((S i i : ℤ) : ℂ)) = ((n ⬝ᵥ fun i => S i i : ℤ) : ℂ) := by
        simp [dotProduct, ofIntVec]
      have hd2 : (fun i => ((S i i : ℤ) : ℂ) / 2) = (1 / 2 : ℂ) • fun i => ((S i i : ℤ) : ℂ) := by
        ext i; simp; ring
      rw [hX, ofRealVec_halfVec, Matrix.mulVec_smul, ← ofIntVec_mulVec, smul_dotProduct,
        dotProduct_smul, ofIntVec_dot, hd2, smul_dotProduct, dotProduct_smul, hd]
      simp only [smul_eq_mul]
      push_cast; ring
    rw [h8, eC_int]
  · have hb : halfVec (n' - S *ᵥ n - fun i => S i i) + S.map (fun x : ℤ => (x : ℝ)) *ᵥ halfVec n +
        (fun i => ((S i i : ℤ) : ℝ) / 2) = halfVec n' := by
      rw [mulVec_halfVec]
      ext i; simp only [halfVec, Pi.add_apply, Pi.sub_apply]; push_cast; ring
    have hz : zAct (spTransl S) τ z = z := by simp [zAct, jAut_spTransl]
    have he : expArg (spTransl S) τ z = 0 := by simp [expArg, jAut_spTransl, cMat_spTransl]
    rw [hz, he, spAct_spTransl, jAut_spTransl, thetaTranslTau_holds (Fin g) _ _ _ _ S hS, hb,
      mul_pow, det_one, eC_zero]
    ring

theorem thetaLaw_J {g : ℕ} (hInv : InversionStatement) (n n' : Fin g → ℤ) :
    ThetaLaw g (Matrix.J (Fin g) ℤ) n n' (-n') n := by
  set F : ℂ := 2 * (ofRealVec (halfVec (-n')) ⬝ᵥ ofRealVec (halfVec n))
  refine ⟨(-I) ^ g * eC F, ?_, fun τ hτ z => ?_⟩
  · rw [mul_pow, ← pow_mul, mul_comm g 4, pow_mul, eC_pow]
    have hI : (-I : ℂ) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]; simp
    have hF : ((4 : ℕ) : ℂ) * F = ((-(2 * (n' ⬝ᵥ n)) : ℤ) : ℂ) := by
      simp only [F, ofRealVec_halfVec, smul_dotProduct, dotProduct_smul, ofIntVec_dot, smul_eq_mul]
      simp [dotProduct]; ring
    rw [hI, one_pow, one_mul, hF, eC_int]
  · have hsym : τ.IsSymm := hτ.1
    have hs : spAct (Matrix.J (Fin g) ℤ) τ = -τ⁻¹ := by
      rw [spAct_eq, jAut_J, nAut_eq, cMat_J]; simp [Matrix.J]
    have htinv : (τ⁻¹)ᵀ = τ⁻¹ := by rw [Matrix.transpose_nonsing_inv, hsym.eq]
    have hz : zAct (Matrix.J (Fin g) ℤ) τ z = τ⁻¹ *ᵥ z := by rw [zAct, jAut_J, htinv]
    have he : expArg (Matrix.J (Fin g) ℤ) τ z = z ⬝ᵥ (τ⁻¹ *ᵥ z) := by
      rw [expArg, jAut_J, cMat_J]; simp [Matrix.J]
    have hneg : -halfVec (-n') = halfVec n' := by ext i; simp [halfVec]; ring
    rw [hs, hz, he, jAut_J, hInv g _ _ τ hτ z, hneg]
    ring

theorem thetaLaw_generators (hInv : InversionStatement) (g : ℕ) (k k' : Fin g → ℤ) :
    (∀ (S : Matrix (Fin g) (Fin g) ℤ) (n' : Fin g → ℤ), S.IsSymm →
      (∀ i, (2 : ℤ) ∣ (S.mulVec k) i + S i i + k' i - n' i) → ThetaLaw g (spTransl S) k n' k k') ∧
    ThetaLaw g (Matrix.J (Fin g) ℤ) k' k k k' := by
  refine ⟨fun S n' hS hd => (thetaLaw_spTransl S hS k n').congr_target (fun _ => rfl) fun i => ?_,
    (thetaLaw_J hInv k' k).congr_target (fun i => ?_) fun _ => rfl⟩
  · have := hd i
    simp only [Pi.sub_apply]
    omega
  · simp only [Pi.neg_apply]
    omega

end GlobalTheory.KeyPow
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsThetaLawZeroOfEven

section

@[expose] public section

namespace GlobalTheory.KeyPow


open Matrix ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi in
theorem exists_thetaLaw_zero_of_even (hInv : ReciprocityTheory.ChartRestriction.G.Key.Chi.InversionStatement) (g : ℕ)
    (n n' : Fin g → ℤ) (h : Even (n ⬝ᵥ n')) :
    ∃ sp ∈ Matrix.symplecticGroup (Fin g) ℤ, GlobalTheory.KeyPow.ThetaLaw g sp n n' 0 0 := by
  obtain ⟨S, hS, hd⟩ := GlobalTheory.exists_isSymm_mulVec_add_diag_mod_two g n n' h
  have h1 : ThetaLaw g (spTransl S) n n' n 0 :=
    (thetaLaw_generators hInv g n 0).1 S n' hS fun i => by simpa using hd i
  have h2 : ThetaLaw g (Matrix.J (Fin g) ℤ) n 0 0 n := (thetaLaw_generators hInv g 0 n).2
  have hD : (Matrix.diagonal n).IsSymm := Matrix.isSymm_diagonal _
  have h3 : ThetaLaw g (spTransl (Matrix.diagonal n)) 0 n 0 0 :=
    (thetaLaw_generators hInv g 0 0).1 _ n hD fun i => by simp
  have m1 : spTransl S ∈ Matrix.symplecticGroup (Fin g) ℤ := spTransl_mem_sp hS
  have m2 : Matrix.J (Fin g) ℤ ∈ Matrix.symplecticGroup (Fin g) ℤ := SymplecticGroup.J_mem _ _
  have m3 : spTransl (Matrix.diagonal n) ∈ Matrix.symplecticGroup (Fin g) ℤ := spTransl_mem_sp hD
  exact ⟨_, mul_mem m3 (mul_mem m2 m1), thetaLaw_mul g _ _ _ _ _ _ _ _ m3 (mul_mem m2 m1)
    (thetaLaw_mul g _ _ _ _ _ _ _ _ m2 m1 h1 h2) h3⟩

end GlobalTheory.KeyPow
end
end
