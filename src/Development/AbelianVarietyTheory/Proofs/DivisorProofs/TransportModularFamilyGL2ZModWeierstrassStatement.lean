module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QAllQConjOfDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QConjTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportOfSeparating
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VactVmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembershipStatement
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfWeierstrassPDerivWeierstrassPTorsionEq

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem wp_wpd_separate : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (x y : Fin 2 → ZMod N), x ≠ 0 → y ≠ 0 →
    wp N x τ = wp N y τ → wpd N x τ = wpd N y τ → x = y := by
  intro N _ τ x y hx hy h1 h2
  obtain ⟨hsub, -, hmem, -, -⟩ := GlobalTheory.T.torsionPointOfLatticeTau_lattice_membership N τ
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hz : tors N τ x ∉ (tauPair τ).lattice := fun h => hx ((hmem x).1 h)
  have hw : tors N τ y ∉ (tauPair τ).lattice := fun h => hy ((hmem y).1 h)
  rw [wp, wp, div_left_inj' (pow_ne_zero _ hc)] at h1
  rw [wpd, wpd, div_left_inj' (pow_ne_zero _ hc)] at h2
  rcases (Formalism.L2.Th1.F.pInjective (tauPair τ) _ _ hz hw).1 h1 with h | h
  · exact (hsub x y).1 h
  · apply (hsub x y).1
    have e : tors N τ x = -tors N τ y + ((⟨_, h⟩ : (tauPair τ).lattice) : ℂ) := by
      simp
    have h3 : (tauPair τ).derivWeierstrassP (tors N τ x) =
        -(tauPair τ).derivWeierstrassP (tors N τ y) := by
      conv_lhs => rw [e]
      rw [PeriodPair.derivWeierstrassP_add_coe, PeriodPair.derivWeierstrassP_neg]
    have h0 : (tauPair τ).derivWeierstrassP (tors N τ y) = 0 := by
      rw [h2] at h3
      linear_combination h3 / 2
    have h4 := (Formalism.L2.Th1.F.pDerivZero (tauPair τ) _ hw).1 h0
    have h5 := (tauPair τ).lattice.sub_mem h h4
    convert h5 using 1
    ring

end GlobalTheory.WpFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfWeierstrassPDerivWeierstrassPTorsionEqStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.eq_of_weierstrassP_derivWeierstrassP_torsion_eq : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (x y : Fin 2 → ZMod N), x ≠ 0 → y ≠ 0 → wp N x τ = wp N y τ → wpd N x τ = wpd N y τ → x = y := by
  first | exact @GlobalTheory.WpFam.wp_wpd_separate | exact GlobalTheory.WpFam.wp_wpd_separate | (intros; apply GlobalTheory.WpFam.wp_wpd_separate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.VmulNeZero

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.SepGL

theorem vmul_ne_zero {N : ℕ} (x : Fin 2 → ZMod N) (hx : x ≠ 0) (α : GL (Fin 2) (ZMod N)) :
    vmul x α ≠ 0 := by
  intro h
  apply hx
  have h2 : (x ᵥ* (α : Matrix (Fin 2) (Fin 2) (ZMod N))) ᵥ*
      ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = x := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  unfold vmul at h
  rw [← h2, h, Matrix.zero_vecMul]

theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (α β : GL (Fin 2) (ZMod N)), (∀ i : Fin 2, wp N (vmul (Pi.single i 1) α) τ = wp N (vmul (Pi.single i 1) β) τ ∧ wpd N (vmul (Pi.single i 1) α) τ = wpd N (vmul (Pi.single i 1) β) τ) → α = β := by
  intro N _ τ α β h
  rcases subsingleton_or_nontrivial (ZMod N) with hs | hs
  · exact Matrix.GeneralLinearGroup.ext fun i j => Subsingleton.elim _ _
  · have key : ∀ i : Fin 2, vmul (Pi.single i 1) α = vmul (Pi.single i 1) β := by
      intro i
      have h0 : (Pi.single i (1 : ZMod N) : Fin 2 → ZMod N) ≠ 0 := by
        intro h1
        have := congrFun h1 i
        simp at this
      exact GlobalTheory.T.eq_of_weierstrassP_derivWeierstrassP_torsion_eq N τ _ _ (vmul_ne_zero _ h0 α) (vmul_ne_zero _ h0 β) (h i).1 (h i).2
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    have := congrFun (key i) j
    simpa [vmul, Matrix.single_vecMul] using this

end GlobalTheory.WpFam.SepGL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportModularFamilyGL2ZModWeierstrass

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.WpFam

namespace GlobalTheory.WpFamGL

theorem transport_GL : ∀ (g : ℂ ≃+* ℂ) (N N' w : ℕ) [NeZero N] (a : (ZMod N)ˣ) (A : GL (Fin 2) (ZMod N)) (F F' : GL (Fin 2) (ZMod N) → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N' → N ∣ N' → ZetaAct g N a → IsFam (gact N 1) w F → (∀ α, QConj g N' (F α) (F' (α * dg a))) → ω₀ ≠ 0 → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → (∀ x, g (wp N x τ₀ / ω₀ ^ 2) = wp N (vmul x A) τ₁ / ω₁ ^ 2 ∧ g (wpd N x τ₀ / ω₀ ^ 3) = wpd N (vmul x A) τ₁ / ω₁ ^ 3) → ∀ α, g (F α τ₀ / ω₀ ^ w) = F' (α * A) τ₁ / ω₁ ^ w := by
  classical
  intro g N N' w _ a A F F' τ₀ τ₁ ω₀ ω₁ hN' hdiv hζ hF hFF' hω₀ h4 h6 hwp α
  let e : Fin 2 → Fin 2 → ZMod N := fun i => Pi.single i 1
  let m : Fin 2 × Bool → ℕ := fun s => if s.2 then 3 else 2
  let u : Fin 2 × Bool → GL (Fin 2) (ZMod N) → ℍ → ℂ := fun s β =>
    if s.2 then wpd N (vmul (e s.1) (β * 1)) else wp N (vmul (e s.1) (β * 1))
  let u' : Fin 2 × Bool → GL (Fin 2) (ZMod N) → ℍ → ℂ := fun s β => u s (β * dg a)
  have hact : ActBij (gact N 1) := (GlobalTheory.WpFam.Act.isRAct_gact N 1).actBij
  have hu : ∀ s, IsFam (gact N 1) (m s) (u s) := by
    rintro ⟨i, _ | _⟩
    · simpa [m, u] using (GlobalTheory.WpFamGL.main N 1 (e i)).1
    · simpa [m, u] using (GlobalTheory.WpFamGL.main N 1 (e i)).2
  have huu' : ∀ s β, QConj g N' (u s β) (u' s β) := by
    rintro ⟨i, _ | _⟩ β
    · have h := (GlobalTheory.WpFam.ConjExp.qConj_torsion N g a hζ (vmul (e i) β)).1
      rw [GlobalTheory.WpFam.Act.vmul_vmul] at h
      simpa [u, u'] using h.of_dvd hN' hdiv
    · have h := (GlobalTheory.WpFam.ConjExp.qConj_torsion N g a hζ (vmul (e i) β)).2.1
      rw [GlobalTheory.WpFam.Act.vmul_vmul] at h
      simpa [u, u'] using h.of_dvd hN' hdiv
  have hsep : ∀ β, (∀ s, u s β τ₀ = u s α τ₀) → F β τ₀ = F α τ₀ := by
    intro β hβ
    have : β = α := GlobalTheory.WpFam.SepGL.main N τ₀ β α fun i =>
      ⟨by simpa [u] using hβ (i, false), by simpa [u] using hβ (i, true)⟩
    rw [this]
  have hα : α * A * (dg a)⁻¹ * dg a = α * A := by group
  have hval : ∀ s, g (u s α τ₀ / ω₀ ^ m s) = u' s (α * A * (dg a)⁻¹) τ₁ / ω₁ ^ m s := by
    rintro ⟨i, _ | _⟩
    · simpa [u, u', m, hα, GlobalTheory.WpFam.Act.vmul_vmul] using (hwp (vmul (e i) α)).1
    · simpa [u, u', m, hα, GlobalTheory.WpFam.Act.vmul_vmul] using (hwp (vmul (e i) α)).2
  have key := GlobalTheory.QFam.transport_of_separating g (GL (Fin 2) (ZMod N)) (Fin 2 × Bool) (gact N 1) N' w
    m F (fun β => F' (β * dg a)) u u' τ₀ τ₁ ω₀ ω₁ hN' hact hF hu hFF' huu' hω₀ h4 h6 α
    (α * A * (dg a)⁻¹) hsep hval
  simpa [hα] using key

end GlobalTheory.WpFamGL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportModularFamilyGL2ZModWeierstrassStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.transport_modularFamily_GL2ZMod_weierstrass : ∀ (g : ℂ ≃+* ℂ) (N N' w : ℕ) [NeZero N] (a : (ZMod N)ˣ) (A : GL (Fin 2) (ZMod N)) (F F' : GL (Fin 2) (ZMod N) → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N' → N ∣ N' → ZetaAct g N a → IsFam (gact N 1) w F → (∀ α, QConj g N' (F α) (F' (α * dg a))) → ω₀ ≠ 0 → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → (∀ x, g (wp N x τ₀ / ω₀ ^ 2) = wp N (vmul x A) τ₁ / ω₁ ^ 2 ∧ g (wpd N x τ₀ / ω₀ ^ 3) = wpd N (vmul x A) τ₁ / ω₁ ^ 3) → ∀ α, g (F α τ₀ / ω₀ ^ w) = F' (α * A) τ₁ / ω₁ ^ w := by
  first | exact @GlobalTheory.WpFamGL.transport_GL | exact GlobalTheory.WpFamGL.transport_GL | (intros; apply GlobalTheory.WpFamGL.transport_GL <;> assumption)
end
end
