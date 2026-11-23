module

public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsHyp
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDualInjectiveEquiv
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Formalism.ConjugateSelfDual.Statement
import Mathlib.RepresentationTheory.Basic
import ReciprocityTheory.GaloisValuations.GlobalA
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDualInjectiveEquivStatement

section

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.finite_dual_injective_equiv : ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y], (∃ f : Y →ₗ[ZMod n] Module.Dual (ZMod n) X, Function.Injective f) → (∃ g : X →ₗ[ZMod n] Module.Dual (ZMod n) Y, Function.Injective g) → Nonempty (Y ≃ₗ[ZMod n] Module.Dual (ZMod n) X) ∧ Nat.card X = Nat.card Y := by
  first | exact @GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair | exact GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair | (intros; apply GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsShaHalf

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

theorem shaHalf_of_perfectPair {n : ℕ} [NeZero n] {X Y : Type} [AddCommGroup X]
    [Module (ZMod n) X] [AddCommGroup Y] [Module (ZMod n) Y] (h : PerfectPair (R := ZMod n) X Y) :
    Finite Y ∧ Finite X ∧ Nonempty (X ≃ₗ[ZMod n] Module.Dual (ZMod n) Y) ∧
      Nat.card Y = Nat.card X := by
  obtain ⟨hX, hY, P, hP, hP'⟩ := h
  have key := GlobalTheory.T.finite_dual_injective_equiv n Y X ⟨P, hP.1⟩ ⟨P.flip, hP'.1⟩
  exact ⟨hY, hX, key.1, key.2⟩

section Published

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)

theorem shaDual_of_perfectPair
    (h1 : PerfectPair (R := ZMod (l ^ r)) (Sha2 ρ (locFam S Av) (continuous_locFam S Av))
      (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)))
    (h2 : PerfectPair (R := ZMod (l ^ r)) (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av))
      (Sha1 ρ (locFam S Av) (continuous_locFam S Av))) : ShaDual S Av μ ρ := by
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  exact ⟨shaHalf_of_perfectPair h1, shaHalf_of_perfectPair h2⟩

end Published

end PositivityTheory.Lit1.PTN
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsTransfer

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

section Abstract

variable {R : Type} [CommRing R]

theorem exact_of_transfer {A B C A' B' C' : Type} [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup A'] [Module R A'] [AddCommGroup B']
    [Module R B'] [AddCommGroup C'] [Module R C'] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (f' : A' →ₗ[R] B') (g' : B' →ₗ[R] C') (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B') (eC : C ≃ₗ[R] C')
    (u v : Rˣ) (hf : ∀ a, f' (eA a) = u • eB (f a)) (hg : ∀ b, g' (eB b) = v • eC (g b))
    (h : Function.Exact f' g') : Function.Exact f g := by
  unfold Function.Exact at h ⊢
  intro b
  constructor
  · intro hb
    have h1 : g' (eB b) = 0 := by rw [hg, hb, map_zero, smul_zero]
    obtain ⟨a', ha'⟩ := (h (eB b)).1 h1
    refine ⟨(u : R) • eA.symm a', eB.injective ?_⟩
    have := hf (eA.symm a')
    rw [LinearEquiv.apply_symm_apply, ha'] at this
    rw [map_smul, map_smul, this, Units.smul_def]
  · rintro ⟨a, rfl⟩
    have h2 : g' (f' (eA a)) = 0 := (h _).2 ⟨_, rfl⟩
    rw [hf, Units.smul_def, map_smul, hg, ← Units.smul_def, smul_eq_zero_iff_eq,
      smul_eq_zero_iff_eq, LinearEquiv.map_eq_zero_iff] at h2
    exact h2

end Abstract

section Published

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
  (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
  (hρ : ContAction ρ)

theorem nineTermExact_of_nineCmp
    (h : NineCmp (loc0 S Av ρ) (tr0 S Av μ j ρ) (loc1 S Av ρ) (tr1 S Av μ j ρ hρ)
      (loc2 S Av ρ) (tr2 S Av μ j ρ)) : NineTermExact S Av μ j ρ hρ := by
  obtain ⟨B0, B1, B2, B3, B4, B5, B6, B7, BetaSesquilinearity, g0, g1, g2, g3, g4, g5, g6, g7,
    e0, e1, e2, e3, e4, e5, e6, e7, e8, u, h0, h1, h3, h4, h6, h7,
    i0, x01, x12, x23, x34, x45, x56, x67, s7⟩ := h
  have k2 : ∀ a, g2 (e2 a) = (1 : (ZMod (l ^ r))ˣ) • e3 ((e3.symm.toLinearMap ∘ₗ g2 ∘ₗ e2.toLinearMap) a) := by
    intro a; rw [one_smul]; exact (e3.apply_symm_apply _).symm
  have k5 : ∀ a, g5 (e5 a) = (1 : (ZMod (l ^ r))ˣ) • e6 ((e6.symm.toLinearMap ∘ₗ g5 ∘ₗ e5.toLinearMap) a) := by
    intro a; rw [one_smul]; exact (e6.apply_symm_apply _).symm
  refine ⟨e3.symm.toLinearMap ∘ₗ g2 ∘ₗ e2.toLinearMap, e6.symm.toLinearMap ∘ₗ g5 ∘ₗ e5.toLinearMap,
    ?_, exact_of_transfer _ _ _ _ e0 e1 e2 _ _ h0 h1 x01,
    exact_of_transfer _ _ _ _ e1 e2 e3 _ _ h1 k2 x12,
    exact_of_transfer _ _ _ _ e2 e3 e4 _ _ k2 h3 x23,
    exact_of_transfer _ _ _ _ e3 e4 e5 _ _ h3 h4 x34,
    exact_of_transfer _ _ _ _ e4 e5 e6 _ _ h4 k5 x45,
    exact_of_transfer _ _ _ _ e5 e6 e7 _ _ k5 h6 x56,
    exact_of_transfer _ _ _ _ e6 e7 e8 _ _ h6 h7 x67, ?_⟩
  · intro a b hab
    apply e0.injective
    apply i0
    rw [h0, h0, hab]
  · intro y
    obtain ⟨b, hb⟩ := s7 (e8 y)
    refine ⟨((u 5 : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) • e7.symm b, e8.injective ?_⟩
    have := h7 (e7.symm b)
    rw [LinearEquiv.apply_symm_apply, hb] at this
    rw [map_smul, map_smul, this, Units.smul_def]

end Published

end PositivityTheory.Lit1.PTN
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsHypOfCmp

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

theorem ptfsHyp_of_cmp (hN : NineCmpFS) (hS : ShaCmpFS) : PositivityTheory.PTN.PtfsHyp := by
  intro K _ _ l _ r hl hr ζ hζ inv hinv S hS' Av hAv μ hμ M _ _ _ _ _ ρ hρ
  exact ⟨nineTermExact_of_nineCmp S Av μ _ ρ hρ
      (hN K l r hl hr ζ hζ inv hinv S hS' Av hAv μ hμ M ρ hρ),
    shaDual_of_perfectPair S Av μ ρ (hS K l r hl hr ζ hζ inv hinv S hS' Av hAv μ hμ M ρ hρ).1
      (hS K l r hl hr ζ hζ inv hinv S hS' Av hAv μ hμ M ρ hρ).2⟩

end PositivityTheory.Lit1.PTN
end
end
end
