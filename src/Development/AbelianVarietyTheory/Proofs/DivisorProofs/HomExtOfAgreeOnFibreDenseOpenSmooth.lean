module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Spectrum.Prime.Topology
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonZeroDivisorLocalizationGeneralOfNoetherianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeTheoreticallyDominantOfGermInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinimStatement
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorAvoidsFibreMinimalPrimes

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem annihilator_avoids_fibre_minimalPrimes
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B] (b : B)
    (hd : ∀ q : PrimeSpectrum B, q ∈ closure ({P : PrimeSpectrum B | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' {PrimeSpectrum.comap (algebraMap A B) q}))
    (u : PrimeSpectrum B) : ∃ g : B, g * b = 0 ∧ ∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes,
      Q ≤ u.asIdeal → g ∉ Q := by
  classical
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) u
  let I₀ : Ideal B := p.asIdeal.map (algebraMap A B)
  let T : Set (Ideal B) := {Q | Q ∈ I₀.minimalPrimes ∧ Q.comap (algebraMap A B) = p.asIdeal}
  have hTfin : T.Finite := by
    let e := PrimeSpectrum.preimageOrderIsoFiber A B p
    haveI : IsNoetherianRing (p.asIdeal.Fiber B) :=
      Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField _
    have hM : {j : PrimeSpectrum (p.asIdeal.Fiber B) | j.asIdeal ∈ minimalPrimes (p.asIdeal.Fiber B)}.Finite :=
      (minimalPrimes.finite_of_isNoetherianRing _).preimage (fun x _ y _ h => PrimeSpectrum.ext h)
    refine (hM.image fun j => (e.symm j).1.asIdeal).subset ?_
    rintro Q ⟨hQmin, hQp⟩
    have hQprime : Q.IsPrime := hQmin.1.1
    let Q' : PrimeSpectrum B := ⟨Q, hQprime⟩
    have hQ'mem : Q' ∈ PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p} := by
      show PrimeSpectrum.comap (algebraMap A B) Q' = p
      ext1; exact hQp
    obtain ⟨J, hJmin, hJle⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ (e ⟨Q', hQ'mem⟩).asIdeal)
    have hJprime : J.IsPrime := hJmin.1.1
    let j : PrimeSpectrum (p.asIdeal.Fiber B) := ⟨J, hJprime⟩
    refine ⟨j, hJmin, ?_⟩
    have hle : e.symm j ≤ ⟨Q', hQ'mem⟩ := by
      rw [← e.le_iff_le, e.apply_symm_apply]; exact hJle
    have hle' : (e.symm j).1.asIdeal ≤ Q := hle
    have hover : (e.symm j).1.asIdeal.comap (algebraMap A B) = p.asIdeal :=
      congrArg PrimeSpectrum.asIdeal (e.symm j).2
    have hge : I₀ ≤ (e.symm j).1.asIdeal := by
      rw [Ideal.map_le_iff_le_comap, hover]
    exact le_antisymm hle' (hQmin.2 ⟨(e.symm j).1.isPrime, hge⟩ hle')
  obtain ⟨s, hs⟩ := hTfin.exists_finset_coe
  have hsT : ∀ i, i ∈ s ↔ i ∈ T := fun i => by rw [← hs]; rfl
  let K : Ideal B := LinearMap.ker (LinearMap.toSpanSingleton B B b)
  have hK : ∀ x, x ∈ K ↔ x * b = 0 := fun x => by
    simp [K, LinearMap.toSpanSingleton_apply, smul_eq_mul]
  have key : ∀ Q ∈ T, ¬ K ≤ Q := by
    intro Q hQ hKQ
    have hQprime : Q.IsPrime := hQ.1.1.1
    have hnot : ¬ (∏ Q'' ∈ s.erase Q, Q'') ≤ Q := by
      rw [hQprime.prod_le]
      rintro ⟨i, hi, hiQ⟩
      have hiT : i ∈ T := (hsT i).1 (Finset.mem_of_mem_erase hi)
      exact Finset.ne_of_mem_erase hi (le_antisymm hiQ (hQ.1.2 hiT.1.1 hiQ))
    obtain ⟨f, hfprod, hfQ⟩ := SetLike.not_le_iff_exists.1 hnot
    have hfo : ∀ Q'' ∈ T, Q'' ≠ Q → f ∈ Q'' := fun Q'' hQ'' hne =>
      (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_erase.2 ⟨hne, (hsT Q'').2 hQ''⟩))) hfprod
    let Qp : PrimeSpectrum B := ⟨Q, hQprime⟩
    have hcl := hd Qp
    rw [mem_closure_iff] at hcl
    obtain ⟨P, hPf, ⟨t, htP, htb⟩, hPfib⟩ :=
      hcl (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) (PrimeSpectrum.basicOpen f).isOpen hfQ
    have hPf' : f ∉ P.asIdeal := hPf
    have hPover : P.asIdeal.comap (algebraMap A B) = p.asIdeal :=
      (congrArg PrimeSpectrum.asIdeal hPfib).trans hQ.2
    have hI₀P : I₀ ≤ P.asIdeal := by rw [Ideal.map_le_iff_le_comap, hPover]
    obtain ⟨Q', hQ'min, hQ'P⟩ := Ideal.exists_minimalPrimes_le hI₀P
    have hQ'T : Q' ∈ T := ⟨hQ'min, le_antisymm ((Ideal.comap_mono hQ'P).trans hPover.le)
      (Ideal.map_le_iff_le_comap.1 hQ'min.1.2)⟩
    by_cases hQQ : Q' = Q
    · subst hQQ
      exact htP (hQ'P (hKQ ((hK t).2 htb)))
    · exact hPf' (hQ'P (hfo Q' hQ'T hQQ))
  have hprime : ∀ i ∈ s, i ≠ ⊥ → i ≠ ⊥ → (id i : Ideal B).IsPrime := fun i hi _ _ =>
    ((hsT i).1 hi).1.1.1
  have hnot := mt (Ideal.subset_union_prime (f := id) (I := K) ⊥ ⊥ hprime).1 (by
    rintro ⟨i, hi, hKi⟩; exact key i ((hsT i).1 hi) hKi)
  rw [Set.not_subset] at hnot
  obtain ⟨g, hgK, hgU⟩ := hnot
  refine ⟨g, (hK g).1 hgK, fun Q hQ hQu hgQ => hgU ?_⟩
  have hQT : Q ∈ T := ⟨hQ, le_antisymm (Ideal.comap_mono hQu) (Ideal.map_le_iff_le_comap.1 hQ.1.2)⟩
  exact Set.mem_biUnion (show Q ∈ (↑s : Set (Ideal B)) from (hsT Q).2 hQT) hgQ

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorAvoidsFibreMinimalPrimesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.exists_annihilator_not_mem_minimalPrimes_le : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B] (b : B),
    (∀ q : PrimeSpectrum B, q ∈ closure ({P : PrimeSpectrum B | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' {PrimeSpectrum.comap (algebraMap A B) q})) →
    ∀ u : PrimeSpectrum B, ∃ g : B, g * b = 0 ∧ ∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes,
      Q ≤ u.asIdeal → g ∉ Q := by
  first | exact @GlobalTheory.annihilator_avoids_fibre_minimalPrimes | exact GlobalTheory.annihilator_avoids_fibre_minimalPrimes | (intros; apply GlobalTheory.annihilator_avoids_fibre_minimalPrimes <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDenseAffineChartPrimes

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Topology

namespace GlobalTheory

theorem fibre_dense_affine_chart_primes : ∀ (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens) (U : X.Opens) (V : T.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : U ≤ p ⁻¹ᵁ V),
    (∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) →
    ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) →
    ∀ q : PrimeSpectrum Γ(X, U), q ∈ closure ({P : PrimeSpectrum Γ(X, U) | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (p.appLE V U e).hom ⁻¹' {PrimeSpectrum.comap (p.appLE V U e).hom q}) := by
  intro X T p W U V hU hV e hW b hb q
  set f := hU.fromSpec with hf
  have hemb : IsOpenEmbedding f := f.isOpenEmbedding

  have hmemU : ∀ P : PrimeSpectrum Γ(X, U), f P ∈ U := fun P => hU.range_fromSpec.le ⟨P, rfl⟩
  have hprime : ∀ P : PrimeSpectrum Γ(X, U), hU.primeIdealOf ⟨f P, hmemU P⟩ = P := fun P =>
    hemb.injective (hU.fromSpec_primeIdealOf _)
  have hcomap : ∀ P : PrimeSpectrum Γ(X, U),
      PrimeSpectrum.comap (p.appLE V U e).hom P = hV.primeIdealOf ⟨p (f P), e (hmemU P)⟩ := by
    intro P
    have := IsAffineOpen.comap_primeIdealOf_appLE (f := p) V hV U hU e (hmemU P)
    rw [hprime P] at this
    exact this
  set A : Set X := (W : Set X) ∩ p ⁻¹' {p (f q)} with hA
  have hq : q ∈ closure (f ⁻¹' A) := by
    rw [← hemb.isOpenMap.preimage_closure_eq_closure_preimage hemb.continuous]
    exact hW (f q)
  refine closure_mono ?_ hq
  intro P hP
  obtain ⟨hPW, hPp⟩ := hP
  refine ⟨?_, ?_⟩
  · let _ : Algebra Γ(X, U) (X.presheaf.stalk (f P)) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨f P, hmemU P⟩
    haveI hloc : IsLocalization P.asIdeal.primeCompl (X.presheaf.stalk (f P)) := hU.isLocalization_stalk' P (hmemU P)
    have h0 : algebraMap Γ(X, U) (X.presheaf.stalk (f P)) b = 0 := hb (f P) (hmemU P) hPW
    obtain ⟨⟨s, hs⟩, hsb⟩ := (IsLocalization.map_eq_zero_iff P.asIdeal.primeCompl _ b).mp h0
    exact ⟨s, hs, hsb⟩
  · show PrimeSpectrum.comap (p.appLE V U e).hom P = PrimeSpectrum.comap (p.appLE V U e).hom q
    rw [hcomap P, hcomap q]
    have : p (f P) = p (f q) := hPp
    congr 2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDenseAffineChartPrimesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.mem_closure_annihilator_primes_inter_fibre : ∀ (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens) (U : X.Opens) (V : T.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : U ≤ p ⁻¹ᵁ V),
    (∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) →
    ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) →
    ∀ q : PrimeSpectrum Γ(X, U), q ∈ closure ({P : PrimeSpectrum Γ(X, U) | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (p.appLE V U e).hom ⁻¹' {PrimeSpectrum.comap (p.appLE V U e).hom q}) := by
  first | exact @GlobalTheory.fibre_dense_affine_chart_primes | exact GlobalTheory.fibre_dense_affine_chart_primes | (intros; apply GlobalTheory.fibre_dense_affine_chart_primes <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeTheoreticallyDominantOfGermInjectiveStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.schemeTheoreticallyDominant_of_germ_injective : ∀ (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens),
    (∀ (U : X.Opens) (V : T.Opens), IsAffineOpen U → IsAffineOpen V → U ≤ p ⁻¹ᵁ V →
      ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) → b = 0) →
    IsSchemeTheoreticallyDominant W.ι := by
  first | exact @GlobalTheory.isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine | exact GlobalTheory.isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine | (intros; apply GlobalTheory.isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtOfAgreeOnFibreDenseOpenSmooth

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.FibreDense

theorem alg (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B] (b : B)
    (h : ∀ q : PrimeSpectrum B, q ∈ closure ({P : PrimeSpectrum B | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' {PrimeSpectrum.comap (algebraMap A B) q})) : b = 0 := by
  by_contra hb
  let I : Ideal B := LinearMap.ker (LinearMap.toSpanSingleton B B b)
  have hI : I ≠ ⊤ := by
    intro h1
    have : (1 : B) ∈ I := h1 ▸ Submodule.mem_top
    simp [I] at this
    exact hb this
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hI
  let u : PrimeSpectrum B := ⟨m, hm.isPrime⟩
  obtain ⟨g, hg, hgQ⟩ := GlobalTheory.T.exists_annihilator_not_mem_minimalPrimes_le A B b h u
  have h0 := GlobalTheory.T.nonZeroDivisor_localization_general_of_noetherian GlobalTheory.T.smooth_algebra_localization_eq_zero_of_avoid_fibre_minimal A B b g u hg hgQ
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff u.asIdeal.primeCompl _ b).1 h0
  exact s.2 (hle (by simpa [I] using hs))

theorem dense (X T : Scheme.{0}) (p : X ⟶ T) [Smooth p] (W : X.Opens)
    (hW : ∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) : IsSchemeTheoreticallyDominant W.ι := by
  refine GlobalTheory.T.schemeTheoreticallyDominant_of_germ_injective X T p W fun U V hU hV e b hb => ?_
  letI := (p.appLE V U e).hom.toAlgebra
  haveI : Algebra.Smooth Γ(T, V) Γ(X, U) := HasRingHomProperty.appLE @Smooth p ‹_› ⟨V, hV⟩ ⟨U, hU⟩ e
  exact alg Γ(T, V) Γ(X, U) b (GlobalTheory.T.mem_closure_annihilator_primes_inter_fibre X T p W U V hU hV e hW b hb)

theorem ext_of_dominant {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (d : W ⟶ X) [IsSchemeTheoreticallyDominant d] (hU : d ≫ f = d ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  haveI : IsSeparated Y'.hom := ‹IsSeparated s›
  let U' : Over Z := Over.mk (d ≫ f ≫ s)
  let d' : U' ⟶ X' := Over.homMk d
  have e : d' ≫ f' = d' ≫ g' := by
    ext1
    exact hU
  let l := equalizer.lift d' e
  have hd : d = l.left ≫ (equalizer.ι f' g').left := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_bot_iff.1
    calc _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := Scheme.Hom.le_ker_comp _ _
      _ = ⊥ := by rw [← hd]; exact d.ker_eq_bot
  haveI : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hker
  have h0 : IsIso ((Over.forget Z).map (equalizer.ι f' g')) := (inferInstance : IsIso (equalizer.ι f' g').left)
  have : IsIso (equalizer.ι f' g') := isIso_of_reflects_iso _ (Over.forget Z)
  have hfg : f' = g' := (cancel_epi (equalizer.ι f' g')).1 (equalizer.condition f' g')
  exact congrArg CommaMorphism.left hfg

theorem main : ∀ (X T Y : Scheme.{0}) (p : X ⟶ T) [Smooth p] (q : Y ⟶ T) [IsSeparated q] (W : X.Opens),
    (∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) →
    ∀ f g : X ⟶ Y, f ≫ q = g ≫ q → W.ι ≫ f = W.ι ≫ g → f = g := by
  intro X T Y p _ q _ W hW f g hfg hfgW
  haveI := dense X T p W hW
  exact ext_of_dominant q hfg W.ι hfgW

end GlobalTheory.FibreDense
end
end
