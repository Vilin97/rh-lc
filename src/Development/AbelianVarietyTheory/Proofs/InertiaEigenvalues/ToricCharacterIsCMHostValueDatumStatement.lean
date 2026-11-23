module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateEmbeddingIsCMTypeSqrtMinusD
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseCondOfSplitPrimesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorExponentAtPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlacesBelowSplitCoprimeConductorOfAdmissible
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlacesBelowSplitCoprimeConductorOfAdmissible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitsInCMFieldPlaceBelowOfCompletelySplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0HasInfinityTypeConjRatioStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0UnitaryTrivOnMaxRealSubfield
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateEmbeddingIsCMTypeSqrtMinusDStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

theorem _root_.GlobalTheory.T.conjugateEmbedding_isCMType_sqrtMinusD : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsCMType (phi H) ∧ ∀ g g', phi H g H.sqrtMinusD = phi H g' H.sqrtMinusD := by
  first | exact @GlobalTheory.LamTie.CMType.phi_cmType | exact GlobalTheory.LamTie.CMType.phi_cmType | (intros; apply GlobalTheory.LamTie.CMType.phi_cmType <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLeOfLe

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem levelLe_of_le {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {m m' : ℕ}
    (h : χ.LevelLe w m) (hm : m ≤ m') : χ.LevelLe w m' := by
  intro x hx hv

  refine h x hx (le_trans hv ?_)
  rw [WithZero.exp_le_exp]
  omega

theorem expAt_mul_inv : ∀ (E : Type) [Field E] [NumberField E] (χ χ' : Formalism.L2.Host.HChar E) (w : HeightOneSpectrum (𝓞 E)) (n : ℕ),
    1 ≤ n → ExpAt χ w n → χ'.LevelLe w (n - 1) → ExpAt (χ' * χ⁻¹) w n := by
  intro E _ _ χ χ' w n hn hχ hχ' m
  constructor
  · intro hm

    by_contra hlt
    have h1 : (χ' * χ⁻¹).LevelLe w (n - 1) := levelLe_of_le hm (by omega)
    have h2 : χ.LevelLe w (n - 1) := by
      have h3 := Formalism.L2.Host.HChar.LevelLe.mul (Formalism.L2.Host.HChar.LevelLe.inv h1) hχ'
      have h4 : (χ' * χ⁻¹)⁻¹ * χ' = χ := by group
      rwa [h4] at h3
    have := (hχ (n - 1)).mp h2
    omega
  · intro hm

    have hc : χ.LevelLe w m := (hχ m).mpr hm
    have hc' : χ'.LevelLe w m := levelLe_of_le hχ' (by omega)
    exact Formalism.L2.Host.HChar.LevelLe.mul hc' (Formalism.L2.Host.HChar.LevelLe.inv hc)

end GlobalTheory.LamTie
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LamConductorExponent

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem mu0_del_tame {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (C.mu0 j * C.delAt l).LevelLe w 1 := by
  have hd : (C.delAt l).TameAt w := by
    unfold CharFrame.delAt; split_ifs
    · exact C.isDel'.tame w
    · exact C.isDel.tame w
  exact HChar.LevelLe.mul ((C.isMu0 j).tame w) hd

theorem mu0_del_unr {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : ¬ Over4 D.host w) : (C.mu0 j * C.delAt l).UnrAt w := by
  have h1 : ∀ k, ¬ OverP D.host (D.host.g k) w := fun k hk => hw (Or.inl ⟨k, hk⟩)
  have hd : (C.delAt l).UnrAt w := by
    unfold CharFrame.delAt; split_ifs
    · exact C.isDel'.unr w (fun h => hw (Or.inr (Or.inr h)))
    · exact C.isDel.unr w (fun h => hw (Or.inr (Or.inl h)))
  exact HChar.UnrAt.mul ((C.isMu0 j).unr w h1) hd

theorem lam0_expAt : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)),
    ExpAt (Z.lam0 l j a) w (expIn (cond0 D.host Z.w0) (below w)) := by
  intro D Z hZ l j a w
  obtain ⟨h4, h0, hO⟩ := expIn_cond0 D.R D.host Z.q0 Z.w0 hZ.places w
  have hA := hZ.aux a
  unfold LamDat.lam0
  by_cases hw : Over4 D.host w
  · rw [h4 hw]
    exact expAt_mul_inv _ (Z.chi a) _ w 2 (by norm_num) (hA.two w hw) (mu0_del_tame Z.C l j w)
  · by_cases hb : below w = below Z.w0
    · rw [(h0 hb).2]
      have hu := mu0_del_unr Z.C l j w hw
      exact expAt_mul_inv _ (Z.chi a) _ w 1 le_rfl (hA.one w hb) ((HChar.unrAt_iff _ _).1 hu)
    · rw [hO hw hb]
      have hu := HChar.UnrAt.mul (mu0_del_unr Z.C l j w hw) (HChar.UnrAt.inv (hA.unr w hw hb))
      intro m
      exact ⟨fun _ => Nat.zero_le m, fun _ => HChar.UnrAt.levelLe hu m⟩

end GlobalTheory.LamTie
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LamConductorExponentStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

theorem _root_.GlobalTheory.T.lam_conductor_exponent : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), ExpAt (Z.lam0 l j a) w (expIn (cond0 D.host Z.w0) (below w)) := by
  first | exact @GlobalTheory.LamTie.lam0_expAt | exact GlobalTheory.LamTie.lam0_expAt | (intros; apply GlobalTheory.LamTie.lam0_expAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitsInCMFieldPlaceBelowOfCompletelySplitStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

theorem _root_.GlobalTheory.T.splitsInCMField_placeBelow_of_completelySplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ discr E → (∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = p) → ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → Splits (below P) := by
  first | exact @GlobalTheory.LamTie.SplitBelow.splits_below_of_absNorm | exact GlobalTheory.LamTie.SplitBelow.splits_below_of_absNorm | (intros; apply GlobalTheory.LamTie.SplitBelow.splits_below_of_absNorm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0UnitaryTrivOnMaxRealSubfieldStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

theorem _root_.GlobalTheory.T.lam0_isUnitary_and_trivOnF : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m), (Z.lam0 l j a).IsUnitary ∧ TrivOnF (Z.lam0 l j a) := by
  first | exact @GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield | exact GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield | (intros; apply GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricCharacterIsCMHostValueDatum

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem toricCharacter_isCMHostValueDatum : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (s : ℕ), 1 ≤ s → (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 → IsHostDatum D.host (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 l j a) := by
  intro D Z hZ l j a s hs hN
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨hcm, hind⟩ := GlobalTheory.T.conjugateEmbedding_isCMType_sqrtMinusD D.R D.host
  obtain ⟨hκ, hinf⟩ := GlobalTheory.T.one_le_kap_and_lam0_hasInf D Z hZ l j a s hN
  obtain ⟨hu, ht⟩ := GlobalTheory.T.lam0_isUnitary_and_trivOnF D Z hZ l j a
  have hb : IsBaseCond (cond0 D.host Z.w0) :=
    GlobalTheory.T.isBaseCond_of_split_primes D.R D.host Z.q0 Z.w0 (fun p hp P hP => by
      obtain ⟨h1, -, h3, h4⟩ := hZ.places.splits p hp
      exact GlobalTheory.T.splitsInCMField_placeBelow_of_completelySplit D.host.E p h1 h3 h4 P hP) hZ.places
  refine ⟨hcm, hind, hs, hκ, hb, hu, ht, hinf, fun v P hP => ⟨fun h => absurd h (Finset.notMem_empty v), fun _ => ?_⟩⟩
  have hv : v = below P := HeightOneSpectrum.ext (hP.symm.trans (over_below P))
  subst hv
  exact GlobalTheory.T.lam_conductor_exponent D Z hZ l j a P

end GlobalTheory.LamTie
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricCharacterIsCMHostValueDatumStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

theorem _root_.GlobalTheory.T.isHostDatum_kap_lam0_of_ok : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (s : ℕ), 1 ≤ s → (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 → IsHostDatum D.host (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 l j a) := by
  first | exact @GlobalTheory.LamTie.toricCharacter_isCMHostValueDatum | exact GlobalTheory.LamTie.toricCharacter_isCMHostValueDatum | (intros; apply GlobalTheory.LamTie.toricCharacter_isCMHostValueDatum <;> assumption)
end
end
