module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorPower
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorProduct
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepDualInverse

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem ev_unit_inv_mul {m : ℕ} {n : Fin (m + 1) → ℕ} {U : (MP ℤ m n).Opens} (v : Γ(MP ℤ m n, U)ˣ)
    (y : CxPts (mpStr ℤ m n) σ₀) (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ U) :
    CxPts.ev (mpStr ℤ m n) σ₀ U (↑v⁻¹ : Γ(MP ℤ m n, U)) y *
      CxPts.ev (mpStr ℤ m n) σ₀ U (v : Γ(MP ℤ m n, U)) y = 1 := by
  unfold CxPts.ev ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR
  split_ifs with h
  · rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  · exact (h hy).elim

theorem isHermRep_dual : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)),
    IsHermRep M A → IsHermRep M.dual A.inv := by
  intro m n M A hA
  obtain ⟨u, h1, h2, h3⟩ := hA
  refine ⟨fun i c => (u i c)⁻¹, ?_, ?_, ?_⟩
  · rintro (i : M.B.ι) (j : M.B.ι) c
    change Semi.res _ (u j c)⁻¹ = Semi.res _ (M.B.g i j)⁻¹ * Semi.res _ (u i c)⁻¹
    rw [map_inv, map_inv, map_inv, ← mul_inv]
    exact congrArg (·⁻¹) (h1 i j c)
  · rintro (i : M.B.ι) c c'
    change Semi.res _ (u i c)⁻¹ = Semi.res _ (u i c')⁻¹ * ∏ k, blockUnit (c k) (c' k) _ ^ (-A.a k)
    rw [map_inv, map_inv]
    have h := congrArg (·⁻¹) (h2 i c c')
    simp only [mul_inv, ← Finset.prod_inv_distrib, ← zpow_neg] at h
    exact h
  · rintro (i : M.B.ι) c y z hz (hyin : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c))
    change (A.h z)⁻¹ = (∏ k, ‖z ⟨k, c k⟩‖ ^ (-A.a k)) *
      ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)⁻¹) y‖ * Real.exp (-(M.φ σ₀).φ i y / 2)
    have e : CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)⁻¹) y =
        (CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)) y)⁻¹ :=
      eq_inv_of_mul_eq_one_left (ev_unit_inv_mul (u i c) y hyin)
    rw [h3 i c y z hz hyin]
    simp only [zpow_neg, Finset.prod_inv_distrib, neg_div, Real.exp_neg, mul_inv]
    congr 2
    rw [e, norm_inv]

end GlobalTheory.CompanionTheory.MPDict
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTrivialLineBundle

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem isHermRep_triv : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ), IsHermRep (HermLB.triv (mpStr ℤ m n)) (GlobalTheory.CompanionTheory.Ar.Top.trivLine (Bk n)) := by
  intro m n
  refine ⟨fun _ _ => 1, ?_, ?_, ?_⟩
  · intro i j c
    simp only [map_one, mul_one]
    exact (map_one (Semi.res _)).symm
  · intro i c c'
    simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine]
  · intro i c y z _ hy
    have e : CxPts.ev (mpStr ℤ m n) σ₀ ((HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)
        (((1 : Γ(MP ℤ m n, (HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)ˣ)) :
          Γ(MP ℤ m n, (HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)) y = 1 := by
      rw [CxPts.ev_eq hy, Units.val_one, map_one]
    rw [e]
    simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine, HermLB.triv, Weight.ofFun]

end GlobalTheory.CompanionTheory.MPDict
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleReadCombination

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MixZ

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet (powLine powLine_a)
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine)

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem multicone_of_isUnder {U : (MP ℤ m n).Opens} {c : ∀ k, Bk n k} {y : CxPts (mpStr ℤ m n) σ₀}
    {z : (Σ k, Bk n k) → ℂ} (hz : IsUnder y z) (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (U ⊓ mchart c)) :
    ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := fun k =>
  ⟨c k, ((hz k (c k)).1).1 (CxPts.ptsIn_mono (inf_le_right.trans (mchart_le c k)) hy)⟩

theorem isHermRep_congr {M : HermLB (mpStr ℤ m n)} {A B : HermLine (Bk n)} (ha : A.a = B.a)
    (hh : ∀ z : (Σ k, Bk n k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A.h z = B.h z)
    (hM : IsHermRep M A) : IsHermRep M B := by
  obtain ⟨u, h₁, h₂, h₃⟩ := hM
  refine ⟨u, h₁, ?_, ?_⟩
  · rw [← ha]
    exact h₂
  · intro i c y z hz hy
    rw [← hh z (multicone_of_isUnder hz hy), ← ha]
    exact h₃ i c y z hz hy

theorem isHermRep_zp {M : HermLB (mpStr ℤ m n)} {A : HermLine (Bk n)} (hM : IsHermRep M A) (e : ℤ) :
    ∃ B : HermLine (Bk n), IsHermRep (zp M e) B ∧ B.a = e • A.a ∧
      ∀ z : (Σ k, Bk n k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → B.h z = A.h z ^ e := by
  refine ⟨(powLine A e.toNat).tensor (powLine A (-e).toNat).inv,
    isHermRep_tens _ _ _ _ _ _ (PowRep.isHermRep_pow _ _ _ _ _ hM)
      (isHermRep_dual _ _ _ _ (PowRep.isHermRep_pow _ _ _ _ _ hM)), ?_, ?_⟩
  · funext k
    have e₁ : ((e.toNat : ℤ) - ((-e).toNat : ℤ)) = e := by omega
    simp only [HermLine.tensor, HermLine.inv, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, powLine_a, smul_eq_mul]
    linear_combination (A.a k) * e₁
  · intro z hz
    have hp := (A.pos z hz).ne'
    simp only [HermLine.tensor, HermLine.inv, PowRep.h_powLine]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hp]
    congr 1
    omega

theorem isHermRep_foldr {κ : Type} (M : κ → HermLB (mpStr ℤ m n)) (A : κ → HermLine (Bk n))
    (hM : ∀ o, IsHermRep (M o) (A o)) (a : κ → ℤ) (l : List κ) :
    ∃ B : HermLine (Bk n), IsHermRep (l.foldr (fun i N => (zp (M i) (a i)).tens N) (HermLB.triv (mpStr ℤ m n))) B ∧
      B.a = (l.map fun o => a o • (A o).a).sum ∧
      ∀ z : (Σ k, Bk n k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → B.h z = (l.map fun o => (A o).h z ^ a o).prod := by
  induction l with
  | nil =>
    exact ⟨_, isHermRep_triv m n, by simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine], fun z _ => by simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine]⟩
  | cons o l ih =>
    obtain ⟨B, hB, ha, hh⟩ := ih
    obtain ⟨C, hC, ca, ch⟩ := isHermRep_zp (hM o) (a o)
    refine ⟨C.tensor B, isHermRep_tens _ _ _ _ _ _ hC hB, ?_, fun z hz => ?_⟩
    · simp only [HermLine.tensor, List.map_cons, List.sum_cons, ca, ha]
    · simp only [HermLine.tensor, List.map_cons, List.prod_cons, ch z hz, hh z hz]

theorem readComb : ReadComb := by
  intro m n κ _ M A hM a
  obtain ⟨B, hB, ha, hh⟩ := isHermRep_foldr M A hM a (Finset.univ : Finset κ).toList
  refine isHermRep_congr ?_ (fun z hz => ?_) hB
  · rw [ha, Finset.sum_map_toList]
    rfl
  · rw [hh z hz, Finset.prod_map_toList]
    exact (if_pos hz).symm

end GlobalTheory.CompanionTheory.MixZ
end
end
end
