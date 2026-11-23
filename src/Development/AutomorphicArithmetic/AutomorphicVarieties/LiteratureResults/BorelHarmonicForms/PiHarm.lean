module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ActOpApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.InfAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.QdetIntertw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.TensDer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AbsHarm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CasTens
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DelCochain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.KugaSucc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.KugaZero
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneEig
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AdmEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CuspSq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.InclFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.PetEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SmForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.TformPos
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CasZero

section

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.casZero :
    UpperTheory.V.Lit.Bor.CasZero := by
  intro E _ _ _ a n e he M _ _ _ _ κ A B hA hB hAB hκ hinf c hc hcoh
  by_contra hne
  have hdel : ∀ (q : ℕ) (X : Fin q → Herm E a),
      del (B - A) e (0 : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M) X = 0 := fun q X => by
    rw [del_apply]
    simp
  rcases hcoh with ⟨ω, hco, hcl, hnz⟩ | ⟨q, ω, hco, hcl, hne'⟩
  · apply hnz
    ext X
    have h := kugaZero E a n e M A B hAB ω (hinf 0 ω hco) X
    rw [hcl, hdel, hc] at h
    exact (smul_eq_zero.1 h.symm).resolve_left hne
  · have hδ := delCochain E a n e he M κ (B - A) hκ q ω hco
    let s : M →ₗ[ℝ] M := (c⁻¹ • LinearMap.id : M →ₗ[ℂ] M).restrictScalars ℝ
    have hs : ∀ X, s.compAlternatingMap (del (B - A) e ω) X = c⁻¹ • del (B - A) e ω X := fun X => rfl
    refine hne' (s.compAlternatingMap (del (B - A) e ω)) (fun k X => ?_) (AlternatingMap.ext fun X => ?_)
    · rw [hs, hs, map_smul, hδ k X]
    · have h := kugaSucc E a n e he M A B hA hB hAB q ω (hinf _ ω hco) X
      rw [hcl, hdel, add_zero, hc, dCo_apply] at h
      have h2 : ω X = c⁻¹ • (c • ω X) := (inv_smul_smul₀ hne _).symm
      rw [dCo_apply, h2, ← h, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hs, map_smul, smul_comm c⁻¹]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.PiForm

section

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.piForm :
    UpperTheory.V.Lit.Bor.PiForm := by
  intro E _ _ _ a ha π Ξ r hone
  obtain ⟨G, hG⟩ := admEx E a Ξ
  obtain ⟨H, hH⟩ := petEx E a ha r
  obtain ⟨hinj, hcmp, -, hlie, hadj⟩ := inclFacts E a π Ξ r
  have hpos := tformPos _ Ξ.d H _ G hH.pos hG.pos
  have hmem : ∀ m, incl π Ξ m ∈ tens Ξ.d (sqSub E a r) := fun m =>
    mem_tens.2 fun i => by
      rw [hcmp]
      exact Submodule.subset_span (cuspSq E a ha π r hone _ (UpperTheory.V.Lit.Bor.cmp i m).2)
  refine ⟨((tform H G) ∘ₛₗ (incl π Ξ)).compl₂ (incl π Ξ), ⟨fun x y => ?_, fun x _ => ?_, fun x _ hx => ?_⟩,
    fun X x y => ?_⟩
  · exact hpos.herm _ _
  · exact hpos.nonneg _ (hmem x)
  · exact hinj ((hpos.definite _ (hmem x) hx).trans (map_zero _).symm)
  · show tform H G (incl π Ξ x) (incl π Ξ _) = tform H G (incl π Ξ _) (incl π Ξ y)
    rw [hlie, hadj]
    exact smForm E a Ξ r H G hH hG X _ (hmem x) _ (hmem y)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.PiHarm

section

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem piHarm_abs (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a n : ℕ) (e : Fin n → Herm E a)
    (he : IsFrame e) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
    (κ : Kinf E a → Module.End ℂ M) (A B : Lie E a →ₗ[ℝ] Module.End ℂ M) (r : ℝ)
    (a1 : IsLieHom A) (b1 : IsLieHom B) (hab : ∀ X Y, Commute (A X) (B Y))
    (a2 : ∀ (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)), κ k * A (toL X) = A (toL (k.1 * X * star k.1)) * κ k)
    (b2 : ∀ (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)), κ k * B (toL X) = B (toL (k.1 * X * star k.1)) * κ k)
    (hder : SepDer κ (A + B)) (c : ℂ) (hc : ∀ m, (cas (shift B (-r)) e - cas (shift A r) e) m = c • m)
    (hC : HasCohomology κ (A + B)) (H : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (hH : IsPos H ⊤)
    (hadj : ∀ (X : Herm E a) x y, H x ((A + B) (toL X.1) y) = H (adj A B r (toL X.1) x) y)
    (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) (hω : IsCochain κ ω) :
    dCo (A + B) ω = 0 ∧ Coclosed (adj A B r) e ω := by
  obtain ⟨-, -, l3, l4⟩ := ellFacts E a
  have hA := l4 _ A r a1
  have hB := l4 _ B (-r) b1
  have hsum := shift_add_shift A B r
  have hcom : ∀ X Y, Commute (shift A r X) (shift B (-r) Y) := fun X Y => by
    rw [shift_apply, shift_apply]
    exact ((hab X Y).add_right ((Commute.one_right _).smul_right _)).add_left ((Commute.one_left _).smul_left _)
  have hinf : ∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), IsCochain κ ω → InfEq (shift A r + shift B (-r)) ω := by
    rw [hsum]
    exact infAbs E a M κ (A + B) hder
  have hK : ∀ (k : Kinf E a) (X : Herm E a), κ k * (shift B (-r) - shift A r) (toL X.1) =
      (shift B (-r) - shift A r) (toL (adHerm k X).1) * κ k := fun k X => by
    have e1 : (adHerm k X).1 = k.1 * X.1 * star k.1 := rfl
    rw [e1, LinearMap.sub_apply, LinearMap.sub_apply, shift_apply, shift_apply, shift_apply, shift_apply, l3 k X.1,
      mul_sub, sub_mul, mul_add, mul_add, add_mul, add_mul, a2, b2, mul_smul_comm, mul_smul_comm, smul_mul_assoc,
      smul_mul_assoc, mul_one, one_mul]
  have hc0 : c = 0 := casZero E a n e he M κ _ _ hA hB hcom hK hinf c hc (by rw [hsum]; exact hC)
  have hcas : cas (shift B (-r)) e = cas (shift A r) e :=
    sub_eq_zero.1 (LinearMap.ext fun m => by rw [hc m, hc0, zero_smul]; rfl)
  have := absHarm E a n e he M _ _ hA hB hcom hcas H hH (by rw [hsum]; exact hadj) q ω (hinf q ω hω)
  rw [hsum] at this
  exact this

theorem UpperTheory.V.Lit.Bor.piHarm :
    UpperTheory.V.Lit.Bor.PiHarm := by
  intro E _ _ _ a ha n e he π Ξ r hr hC q ω hω
  obtain ⟨a1, a2, -⟩ := tensA E a π Ξ
  obtain ⟨b1, b2, -⟩ := tensB E a π Ξ
  obtain ⟨c, hc⟩ := casTens E a n e he π Ξ r
  obtain ⟨H, hH, hadj⟩ := piForm E a ha π Ξ r (oneEig E a π Ξ r hr hC)
  exact piHarm_abs E a n e he _ (tensorK π Ξ) (lieA π Ξ) (lieB π Ξ) r a1 b1 (lieA_commute π Ξ) a2 b2
    (tensDer E a π Ξ) c hc hC H hH hadj q ω hω
end
end
