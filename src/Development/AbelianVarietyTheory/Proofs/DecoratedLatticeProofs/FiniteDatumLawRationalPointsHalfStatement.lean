module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTwistRationalLevelElementsSameCharacters
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumBasePointsLawRationalTwistPrimesStatement
import Mathlib.RingTheory.PiTensorProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentHalfEqRationalAddNsmulStandardHomStatement
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTwistRationalLevelElementsSameCharactersStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.exists_twistRational_levelElements_same_characters : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E), ∃ (κ₁ : A.U i α) (κ₁' : A.U (i + 1) γ) (x₁ y₁ : (AE (I.rec7 l Z))ˣ) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ₁.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ₁'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ IsDetRoot _ κ₁.1 x₁ ∧ IsDetRoot _ κ₁'.1 y₁ ∧ A.chr (i + 1) x₁ = A.chr (i + 1) x ∧ A.chr (i + 1) y₁ = A.chr (i + 1) y ∧ A.chi i α κ₁ = A.chi i α κ ∧ A.chi (i + 1) γ κ₁' = A.chi (i + 1) γ κ' ∧ t ∈ stdHom _ _ ∧ IsHalf A.e t ∧ actO _ _ κ₁.1⁻¹ κ₁'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) + k • t := by
  first | exact @GlobalTheory.AdForm.RatApprox.approx | exact GlobalTheory.AdForm.RatApprox.approx | (intros; apply GlobalTheory.AdForm.RatApprox.approx <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawUnderTwoLevelsModHalfLattice

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.XiLaw

theorem isHalf_add {D : D7} {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) : IsHalf e (u + v) := by
  intro r s
  simp only [Matrix.add_apply, mul_add, hu r s, hv r s]

theorem xi_law : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → (∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t → z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t → A.xi i hi α γ z₁ = A.xi i hi α γ z₂) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z z' : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • v → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * A.xi i hi α γ z' = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * A.xi i hi α γ z := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ k hk hxi κ κ' x y hx hy z z' v hv hvh hrel
  obtain ⟨κ₁, κ₁', x₁, y₁, t, r1, r1', hx1, hy1, ex, ey, ec, ec', ht, hth, hact⟩ :=
    GlobalTheory.T.exists_twistRational_levelElements_same_characters I hI hP l Z u a Ch A hA i hi α γ k hk κ κ' x y hx hy z
  have key := GlobalTheory.T.finiteDatum_basePoints_law_rational_twistPrimes I hI hP l Z u a Ch A hA i hi α γ k hk hxi κ₁ κ₁' r1 r1' x₁ y₁ hx1 hy1 z z' (v + t)
    (add_mem hv ht) (isHalf_add hvh hth) (by rw [hact, hrel, nsmul_add, add_assoc])
  rw [ex, ey, ec, ec'] at key
  exact key

end GlobalTheory.AdForm.XiLaw
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawUnderTwoLevelsModHalfLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.finiteDatum_law_under_two_levels_mod_half_lattice : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → (∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t → z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t → A.xi i hi α γ z₁ = A.xi i hi α γ z₂) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z z' : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • v → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * A.xi i hi α γ z' = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * A.xi i hi α γ z := by
  first | exact @GlobalTheory.AdForm.XiLaw.xi_law | exact GlobalTheory.AdForm.XiLaw.xi_law | (intros; apply GlobalTheory.AdForm.XiLaw.xi_law <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawRationalPointsHalf

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.RatLaw

theorem isHalf_actO {D : D7} {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (actO S T g h u) := by
  intro i j
  simp only [actO, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hu l k]
  ring

theorem law_rat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ p : ℂ, (∀ z, Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) = p * A.xi i hi α γ z) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E, (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ Φ hΦ p hp κ κ' x y hx hy z
  obtain ⟨hsupp, k, hk, hper, -⟩ := hΦ
  set ez := z.map fun r => A.e * incA (I.rec7 l Z) r with hez
  by_cases hw : IsHalf A.e (actO _ _ κ.1⁻¹ κ'.1⁻¹ ez)
  · obtain ⟨z', v, hv, hvh, hwe⟩ := GlobalTheory.T.idempotentHalf_eq_rational_add_nsmul_standardHom _ _ A.e _ hA.idem k hk _ hw
    have hΦw : Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ ez) = p * A.xi i hi α γ z' := by
      rw [hwe, hper v hv hvh, hp z']
    rw [hΦw, hp z]
    by_cases hp0 : p = 0
    · simp [hp0]
    · have hxi : ∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E)
          (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t →
          z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t →
          A.xi i hi α γ z₁ = A.xi i hi α γ z₂ := by
        intro z₁ z₂ t ht hth he
        have h1 := hp z₁
        rw [he, hper t ht hth, hp z₂] at h1
        exact (mul_left_cancel₀ hp0 h1).symm
      have hL := GlobalTheory.T.finiteDatum_law_under_two_levels_mod_half_lattice I hI hP l Z u a Ch A hA i hi α γ k hk hxi κ κ' x y hx hy z z' v hv hvh hwe
      linear_combination p * hL
  · have h1 : Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ ez) = 0 := by
      by_contra h
      exact hw (hsupp _ h)
    have h2 : Φ ez = 0 := by
      by_contra h
      exact hw (GlobalTheory.AdForm.RatLaw.isHalf_actO _ _ (hsupp _ h))
    rw [h1, h2]
    simp

end GlobalTheory.AdForm.RatLaw
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawRationalPointsHalfStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.finiteDatumLaw_rationalPoints_half : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ p : ℂ, (∀ z, Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) = p * A.xi i hi α γ z) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E, (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) := by
  first | exact @GlobalTheory.AdForm.RatLaw.law_rat | exact GlobalTheory.AdForm.RatLaw.law_rat | (intros; apply GlobalTheory.AdForm.RatLaw.law_rat <;> assumption)
end
end
