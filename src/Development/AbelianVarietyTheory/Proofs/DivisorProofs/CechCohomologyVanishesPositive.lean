module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcycFOfPiSh
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSepClosedResidueFieldOfModuleFinite
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelSpecTensorPowerStatement
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStrictlyHenselianTateTwistAcyclic

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem finite_sh_acyclic_twists : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ s i : ℤ, 0 < s → Subsingleton (Ht q (sp T) s i) := by
  intro q _ A _ hA _ T _ _ hfin s i hs
  obtain ⟨hH, hsep⟩ := hA
  obtain ⟨ι, hι, F, hF, hAF, e, hHF, hF'⟩ :=
    GlobalTheory.finite_algebra_strictly_henselian_pi A T
  exact acycF_of_pi_sh (ZMod q) (tw q i) ι F T ⟨e.toRingEquiv⟩
    (fun j => ⟨hHF j, (hF' j).1⟩) s hs

end GlobalTheory.EtC.GmStep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStrictlyHenselianTateTwistAcyclicStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.finite_strictlyHenselian_tateTwist_acyclic : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ s i : ℤ, 0 < s → Subsingleton (Ht q (sp T) s i) := by
  first | (exact @GlobalTheory.EtC.GmStep.finite_sh_acyclic_twists) | (exact GlobalTheory.EtC.GmStep.finite_sh_acyclic_twists) | (intros; apply GlobalTheory.EtC.GmStep.finite_sh_acyclic_twists  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProIsometryOfLocalIsometries

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem cech_level_acyc : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 0 < s → Subsingleton (Ht q (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) s i) := by
  intro q _ A _ hA hq A' _ _ hfin k s i hs
  obtain ⟨e0, -, -, -⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  haveI : Subsingleton (Ht q (sp (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) s i) :=
    GlobalTheory.T.finite_strictlyHenselian_tateTwist_acyclic q A hA hq _ inferInstance s i hs
  let f : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌)) :=
    disc.map e0.hom
  let g : disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌)) ⟶ sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) :=
    disc.map e0.inv
  have hgf : g ≫ f = 𝟙 _ := by
    exact (disc.mapIso e0).inv_hom_id
  have hinj : Function.Injective (pull (ZMod q) f (tw q i) s) := by
    intro x y hxy
    have := congrArg (pull (ZMod q) g (tw q i) s) hxy
    rwa [← pull_comp, ← pull_comp, hgf, pull_id, pull_id] at this
  exact hinj.subsingleton

end GlobalTheory.EtC.GmStep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyVanishesPositive

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.cech_cohomology_vanishes_positive : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 0 < s → Subsingleton (Ht q (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) s i) := by
  first | (exact @GlobalTheory.EtC.GmStep.cech_level_acyc) | (exact GlobalTheory.EtC.GmStep.cech_level_acyc) | (intros; apply GlobalTheory.EtC.GmStep.cech_level_acyc  <;> assumption)
end
end
