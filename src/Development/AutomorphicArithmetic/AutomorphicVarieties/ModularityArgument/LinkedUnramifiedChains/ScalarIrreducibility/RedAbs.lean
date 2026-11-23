module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.ChevPrime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.CompDim
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.HeightLeOfDim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.HtOfSum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.IntOfNorm
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.RegDom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.TanBound

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DomMin

section

@[expose] public section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.domMin :
    ∀ (A : Type) [CommRing A] (q : Ideal A) [q.IsPrime], IsDomain (Localization.AtPrime q) → ∀ P ∈ minimalPrimes A, P ≤ q → ∀ a ∈ P, ∃ s ∉ P, s * a = 0 := by
  intro A _ q _ hD P hP hPq a ha
  letI : Nontrivial (Localization.AtPrime q) := hD.toNontrivial
  letI : NoZeroDivisors (Localization.AtPrime q) :=
    isCancelMulZero_iff_noZeroDivisors.mp hD.toIsCancelMulZero
  have hK : (RingHom.ker (algebraMap A (Localization.AtPrime q))).IsPrime := RingHom.ker_isPrime _
  have hle : RingHom.ker (algebraMap A (Localization.AtPrime q)) ≤ P := by
    intro x hx
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) x).1 hx
    have h0 : (m : A) * x ∈ P := by rw [hm]; exact P.zero_mem
    exact (hP.1.1.mem_or_mem h0).resolve_left (fun h => m.2 (hPq h))
  have hge : P ≤ RingHom.ker (algebraMap A (Localization.AtPrime q)) := hP.2 ⟨hK, bot_le⟩ hle
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) a).1 (hge ha)
  exact ⟨m, fun h => m.2 (hPq h), hm⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.RedCrit

section

@[expose] public section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.redCrit :
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (q : Ideal A), q.IsPrime → (∀ P ∈ associatedPrimes A A, P ≤ q → P ∈ minimalPrimes A) →
        (∀ P ∈ minimalPrimes A, P ≤ q → ∀ a ∈ P, ∃ s ∉ P, s * a = 0) → ∀ a : A, (∀ P : Ideal A, P.IsPrime → P ≤ q → a ∈ P) → ∃ s ∉ q, s * a = 0 := by
  intro A _ _ q hq h1 h2 a ha
  by_contra hcon
  push_neg at hcon
  let N : Submodule A A := Submodule.span A {a}
  have hann : ∀ x, x ∈ Module.annihilator A N ↔ x * a = 0 := by
    intro x
    rw [Module.mem_annihilator]
    constructor
    · intro h
      exact congrArg Subtype.val (h ⟨a, Submodule.mem_span_singleton_self a⟩)
    · intro h m
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp m.2
      apply Subtype.ext
      change x * (m : A) = 0
      rw [← hc, smul_eq_mul, mul_left_comm, h, mul_zero]
  have hle : Module.annihilator A N ≤ q := by
    intro x hx
    by_contra hxq
    exact hcon x hxq ((hann x).mp hx)
  obtain ⟨P, hP, hPq⟩ := Ideal.exists_minimalPrimes_le hle
  have hPass : P ∈ associatedPrimes A N :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A N hP
  have hPA : P ∈ associatedPrimes A A :=
    associatedPrimes.subset_of_injective N.injective_subtype hPass
  have hPmin := h1 P hPA hPq
  obtain ⟨s, hsP, hs⟩ := h2 P hPmin hPq a (ha P hPmin.1.1 hPq)
  exact hsP (hP.1.2 ((hann s).mpr hs))
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.RedAbs

section

@[expose] public section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.redAbs : UpperTheory.V.J.RedAbs := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro l _ c _ F C₀ n hF hn S M Gd hAG hDB hTan ξ hξ hTI b hb
  haveI hA : IsNoetherianRing S.A := (Fr.gr_A hF hn S).2.2.2.2.2.1
  haveI hq : (RingHom.ker ξ).IsPrime := RingHom.ker_isPrime _
  obtain ⟨x, L, Q, hO⟩ := UpperTheory.V.J.locAt l c F C₀ n hF hn S ξ hξ
  have hN : Q.height ≤ ((n * F.d + 1 : ℕ) : ℕ∞) :=
    UpperTheory.V.J.htUp l c F C₀ n hF hn S M hAG (fun Z hZ hMZ => (hDB Z hZ hMZ).1) _ x L Q hO hTI
  have hass := (UpperTheory.V.J.htLow l c F C₀ n hF hn S _ x L Q hO).2 hN
  have hTIle : ∀ P : Ideal S.A, P ≤ RingHom.ker ξ → S.u.TI P := fun P hle =>
    ⟨⟨fun h => hTI.1.1 (h.trans hle), fun h => hTI.1.2 (h.trans hle)⟩, fun h3 h => hTI.2 h3 (h.trans hle)⟩
  have hmin : ∀ P ∈ minimalPrimes S.A, P ≤ RingHom.ker ξ → ∀ a ∈ P, ∃ s ∉ P, s * a = 0 := by
    intro P hP hPq
    have hPp : P.IsPrime := hP.1.1
    have hPT := hTIle P hPq
    have hZp : (S.π P).IsPrime := Ideal.IsPrime.comap _
    have hMZ : M ≤ S.π P := hAG P hPp hPT
    obtain ⟨hle, hdn⟩ := hDB (S.π P) hZp hMZ
    have hdim : ringKrullDim (S.B ⧸ S.π P) = ((1 + n * F.d : ℕ) : WithBot ℕ∞) :=
      le_antisymm hle (UpperTheory.V.J.compDim l c F C₀ n hF hn S _ x L Q hO hTI P hP hPq)
    obtain ⟨ξ', hV, hT', hPk, hG⟩ := UpperTheory.V.J.genPt l c F C₀ n hF hn S P Gd hP hPT (hdn hdim)
    haveI hq' : (RingHom.ker ξ').IsPrime := RingHom.ker_isPrime _
    have hMk : M ≤ RingHom.ker (ξ'.comp S.inc) := fun m hm => hPk (hMZ hm)
    have hF1 := hTan ξ' hV hT' hMk hG
    have hrk : Module.rank (Qbar l) (PtDer ξ' (Qbar l)) ≤ ((n * F.d + 1 : ℕ) : Cardinal) := by
      refine (UpperTheory.V.J.tanBound l c F C₀ n hF hn S ξ' hV.1).trans ?_
      rw [Nat.cast_add, Nat.cast_one]
      gcongr
    obtain ⟨x', L', Q', hO'⟩ := UpperTheory.V.J.locAt l c F C₀ n hF hn S ξ' hV.1
    have hht := (UpperTheory.V.J.htLow l c F C₀ n hF hn S _ x' L' Q' hO').1
    have hdom := UpperTheory.V.J.regDom l c S.A ξ' (n * F.d + 1) hrk hht
    exact UpperTheory.V.J.domMin S.A (RingHom.ker ξ') hdom P hP hPk
  obtain ⟨s, hs, hsb⟩ := UpperTheory.V.J.redCrit S.A (RingHom.ker ξ) hq hass hmin (S.inc b)
    (fun P hPp hPq => hAG P hPp (hTIle P hPq) hb)
  exact ⟨s, fun h => hs (RingHom.mem_ker.2 h), hsb⟩
end
end
