module

public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.LemmaX
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.RatioOneKilled
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkAssemble
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.Reduce
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.DefsForms
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.MainCoind
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
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.GlobalEulerFormulaInf
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Scalars
public import GroundTheory.ProfiniteCohomology.EulerChar
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.RealHerbrand
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Coprime
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Finite
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.TypeStar
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.SumEqCardMulSub
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GlobalEulerCharAtOfRatioOne

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkDevis

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_devis

theorem ratioOne_of_killed_l (ℓ : ℕ) [Fact ℓ.Prime] (P : FiniteSubfield → Prop) (h : RatioOneKilled ℓ P) :
    RatioOne ℓ P := by
  intro K S hS hSl hP ιr M _ _ hM
  obtain ⟨r, hr⟩ := hM
  have : Finite S := hS
  induction r generalizing M with
  | zero =>
    have : Subsingleton M := ⟨fun a b => by
      have ha := hr a
      have hb := hr b
      simp only [pow_zero, one_smul] at ha hb
      rw [ha, hb]⟩
    exact gsEulerRatio_eq_one_of_subsingleton S M ιr
  | succ r ih =>
    letI : Module (ULift.{0} ℤ) M := M.hV2
    let T : Module.End (ULift.{0} ℤ) M := (ℓ : Module.End (ULift.{0} ℤ) M)
    have hTx : ∀ x : M, T x = ℓ • x := fun x => Module.End.natCast_apply ℓ x
    have hT : ∀ g, Commute T (M.ρ g) := fun g => Nat.cast_commute ℓ _
    have hD : ∀ g, (⊤ : Submodule _ _) ≤ Submodule.comap (M.ρ g) ⊤ := fun _ => le_top
    have hSE := rangeStepComplex_shortExact T hT ⊤ hD
    have : Finite (Rep.subrepresentation M ⊤ hD) :=
      Finite.of_injective (fun x : Rep.subrepresentation M ⊤ hD => (x.1 : M)) fun _ _ h => Subtype.ext h
    have : Finite (Rep.subrepresentation M _ (inf_ker_le_comap T hT ⊤ hD)) :=
      Finite.of_injective (fun x : Rep.subrepresentation M _ (inf_ker_le_comap T hT ⊤ hD) => (x.1 : M))
        fun _ _ h => Subtype.ext h
    have : Finite (Rep.subrepresentation M _ (map_le_comap T hT ⊤ hD)) :=
      Finite.of_injective (fun x : Rep.subrepresentation M _ (map_le_comap T hT ⊤ hD) => (x.1 : M))
        fun _ _ h => Subtype.ext h
    have hl : ∃ r : ℕ, ∀ m : (rangeStepComplex T hT ⊤ hD).X₂, (ℓ ^ r) • m = 0 :=
      ⟨r + 1, fun m => Subtype.ext (hr m.1)⟩
    have hmul := ratio_shortExact_l ℓ K S hS hSl ιr _ hSE hl
    have h1 : gsEulerRatio S (rangeStepComplex T hT ⊤ hD).X₁ ιr = 1 := by
      refine h K S hS hSl hP ιr _ fun m => Subtype.ext ?_
      have h' : T m.1 = 0 := m.2.2
      rw [hTx] at h'
      exact h'
    have h3 : gsEulerRatio S (rangeStepComplex T hT ⊤ hD).X₃ ιr = 1 := by
      refine ih _ fun m => Subtype.ext ?_
      obtain ⟨x, -, hx⟩ := m.2
      change (ℓ ^ r) • m.1 = 0
      rw [← hx, hTx, smul_smul, ← pow_succ]
      exact hr x
    have htop : gsEulerRatio S M ιr = gsEulerRatio S (rangeStepComplex T hT ⊤ hD).X₂ ιr :=
      (gsEulerRatio_eq_of_iso S (M.subrepresentation ⊤ hD) ιr (subrepresentationTopIso M hD)).symm
    rw [htop, hmul, h1, h3, mul_one]

end PositivityTheory.Lit1.GEN.W_devis
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.Assemble

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN

theorem ratioOne_of_killed_l (ℓ : ℕ) [Fact ℓ.Prime] (P : FiniteSubfield → Prop) (h : RatioOneKilled ℓ P) :
    RatioOne ℓ P :=
  W_devis.ratioOne_of_killed_l ℓ P h

theorem ratioOne_of_lemmaX (ℓ : ℕ) [Fact ℓ.Prime] (hX : GlobalEulerCharCoprime) : RatioOne ℓ (fun _ => True) :=
  ratioOne_of_killed_l ℓ _ (W_assemble.ratioOneKilled_of_lemmaX ℓ hX)

end PositivityTheory.Lit1.GEN
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.RatioEqOneOfAltSum

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]

theorem pow_ratio_eq_one {ι : Type*} [Fintype ι] (ℓ : ℕ) (hl0 : (ℓ : ℚ) ≠ 0) (a0 a1 a2 m c : ℕ) (b : ι → ℕ)
    (h : (a0 : ℤ) - a1 + a2 = ∑ v, (b v : ℤ) - c * m) :
    ((ℓ ^ a0 : ℕ) : ℚ) * ((ℓ ^ a2 : ℕ) : ℚ) / ((ℓ ^ a1 : ℕ) : ℚ) * ((ℓ ^ m : ℕ) : ℚ) ^ c /
      ∏ v, ((ℓ ^ b v : ℕ) : ℚ) = 1 := by
  push_cast
  rw [Finset.prod_pow_eq_pow_sum, ← pow_mul, div_eq_one_iff_eq (pow_ne_zero _ hl0),
    div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ hl0), ← pow_add, ← pow_add, ← pow_add]
  congr 1
  have h' : ((a0 + a2 + m * c : ℕ) : ℤ) = ((∑ v, b v + a1 : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast h'


open scoped Classical in
theorem ratio_eq_one_of_altSum [Finite S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hMl : ∀ m : M, ℓ • m = 0)
    (h : (Module.finrank (ZMod ℓ) (cohomology (zmodRepOfTorsion ℓ M hMl) 0) : ℤ) - Module.finrank (ZMod ℓ) (cohomology (zmodRepOfTorsion ℓ M hMl) 1) +
        Module.finrank (ZMod ℓ) (cohomology (zmodRepOfTorsion ℓ M hMl) 2) =
      ∑ v : {v : InfinitePlace K.1 // v.IsReal},
          (Module.finrank (ZMod ℓ) (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom (zmodRepOfTorsion ℓ M hMl)) 0) : ℤ) -
        Fintype.card (InfinitePlace K.1) * Module.finrank (ZMod ℓ) (zmodRepOfTorsion ℓ M hMl)) :
    gsEulerRatio S M ιr = 1 := by
  have hlp : ℓ.Prime := Fact.out
  have : Finite (zmodRepOfTorsion ℓ M hMl) := ‹Finite M›
  have : Module.Finite (ZMod ℓ) (zmodRepOfTorsion ℓ M hMl) := Module.Finite.of_finite
  have hcardM : Nat.card M = ℓ ^ Module.finrank (ZMod ℓ) (zmodRepOfTorsion ℓ M hMl) :=
    natCard_eq_pow_finrank_zmod ℓ (zmodRepOfTorsion ℓ M hMl)
  have hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card M : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := by
    intro v hv
    by_contra hvS
    apply hℓS v hvS
    rw [hcardM, Nat.cast_pow] at hv
    exact v.isPrime.mem_of_pow_mem _ hv
  have hcard : ∀ i ≤ 2, Nat.card (cohomology M i) =
      ℓ ^ Module.finrank (ZMod ℓ) (cohomology (zmodRepOfTorsion ℓ M hMl) i) := fun i hi => by
    have := finite_cohomology_gs K S M hS i hi
    have : Finite (cohomology (zmodRepOfTorsion ℓ M hMl) i) :=
      Finite.of_equiv _ (cohomologyZModEquiv ℓ M hMl i).toEquiv
    rw [Nat.card_congr (cohomologyZModEquiv ℓ M hMl i).toEquiv, natCard_eq_pow_finrank_zmod ℓ]
  have hreal : ∀ v, gsRealH0Card S M ιr v = ℓ ^ Module.finrank (ZMod ℓ)
      (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom (zmodRepOfTorsion ℓ M hMl)) 0) := fun v => by
    have := gsReal_finite_cohomology S ιr M v 0 (by norm_num)
    let e := cohomologyAddEquivOfEquiv (A := Rep.res (gsRealFamily S ιr v).toMonoidHom M)
      (A' := Rep.res (gsRealFamily S ιr v).toMonoidHom (zmodRepOfTorsion ℓ M hMl))
      (zmodRepOfTorsionEquiv ℓ M hMl) (fun _ _ => rfl) 0
    have : Finite (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom (zmodRepOfTorsion ℓ M hMl)) 0) :=
      Finite.of_equiv _ e.toEquiv
    exact (Nat.card_congr e.toEquiv).trans (natCard_eq_pow_finrank_zmod ℓ _)
  have hl0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hlp.ne_zero
  unfold gsEulerRatio
  rw [eulerChar_eq, hcard 0 (by norm_num), hcard 1 (by norm_num), hcard 2 (by norm_num), hcardM,
    Finset.prod_congr rfl (fun v _ => by rw [hreal v])]
  exact pow_ratio_eq_one ℓ hl0 _ _ _ _ _ _ h

end PositivityTheory.Lit1.GEN.X
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.LemmaX

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

theorem lemmaX : PositivityTheory.Lit1.GEN.GlobalEulerCharCoprime := by
  intro K S hS ℓ _ hℓS L _ hL hPn hcop hζ hK ιr M _ _ hMl hMP
  have : Finite S := hS
  refine ratio_eq_one_of_altSum hℓS ιr M hMl ?_
  have : Finite (zmodRepOfTorsion ℓ M hMl) := ‹Finite M›
  have : Module.Finite (ZMod ℓ) (zmodRepOfTorsion ℓ M hMl) := Module.Finite.of_finite
  exact altSum hL hℓS hPn hcop hζ hK ιr (zmodRepOfTorsion ℓ M hMl) (fun g m => by
    have := congrArg (fun f => f m) (hMP g g.2)
    exact this)

end PositivityTheory.Lit1.GEN.X
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GlobalEulerCharOfLemmaX

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace PositivityTheory.Lit1.GEN

theorem globalEulerChar_of_lemmaX (hX : GlobalEulerCharCoprime) : ReciprocityTheory.Gal.GlobalEulerChar := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S rhoS
  exact globalEulerCharAt_of_ratioOne S rhoS (ratioOne_of_lemmaX l hX)

theorem globalEulerChar_full : ReciprocityTheory.Gal.GlobalEulerChar :=
  globalEulerChar_of_lemmaX X.lemmaX

end PositivityTheory.Lit1.GEN
end
end
