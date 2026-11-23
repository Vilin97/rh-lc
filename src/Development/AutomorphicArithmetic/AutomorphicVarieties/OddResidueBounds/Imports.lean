module

public import Formalism.GaloisCohomology.Statement
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LenOfCard
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.FnOne
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CondDisc
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.CoefMapSingle
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.BridgeDefs
import Formalism.ConjugateSelfDual.Statement
import Formalism.GaloisCohomology.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealCounting.ClassC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.SelCard
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.UnrInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DvdOfIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadExists
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LogDisc

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.logDisc :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → (discr E).natAbs ≤ N ^ Module.finrank ℚ E ∧ Module.finrank ℚ E ≤ N := by
  intro E _ _ N hN ⟨φ⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  let F := φ.fieldRange
  have e : E ≃ₐ[ℚ] F := AlgEquiv.ofInjectiveField φ
  have hrank : Module.finrank ℚ E = Module.finrank ℚ F := e.toLinearEquiv.finrank_eq
  have hdisc : discr E = discr F := NumberField.discr_eq_discr_of_algEquiv E e
  obtain ⟨hprod, -, -⟩ := KStar.Ram.natAbs_discr_eq_finprod_conductor (N := N) (K := CyclotomicField N ℚ) F
  obtain ⟨hcard, -⟩ := KStar.Ram.card_fieldChars (N := N) (K := CyclotomicField N ℚ) F
  constructor
  · rw [hdisc, hprod, hrank, ← hcard]
    haveI : Fintype (KStar.Ram.fieldChars N F) := Fintype.ofFinite _
    rw [finprod_eq_prod_of_fintype, Nat.card_eq_fintype_card, ← Finset.card_univ]
    exact Finset.prod_le_pow_card _ _ _
      (fun ψ _ => Nat.le_of_dvd hN (DirichletCharacter.conductor_dvd_level _))
  · have hinj : Function.Injective φ.toLinearMap := (φ : E →+* CyclotomicField N ℚ).injective
    have h := LinearMap.finrank_le_finrank_of_injective hinj
    rw [IsCyclotomicExtension.finrank (CyclotomicField N ℚ)
      (Polynomial.cyclotomic.irreducible_rat hN)] at h
    exact h.trans (Nat.totient_le N)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LogH

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.logH :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 2 ≤ N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → Real.log (classNumber E) ≤ 3 * Module.finrank ℚ E * Real.log N := by
  intro E _ _ N hN hE
  obtain ⟨hd, hn⟩ := UpperTheory.V.Odd.logDisc E N (by omega) hE
  have hc := KStar.IdealCounting.log_classNumber_le E
  have hd1 : (1 : ℝ) ≤ |(discr E : ℝ)| := by
    exact_mod_cast Int.one_le_abs (discr_ne_zero E)
  have hd2 : |(discr E : ℝ)| ≤ (N : ℝ) ^ Module.finrank ℚ E := by
    have h : (((discr E).natAbs : ℕ) : ℝ) ≤ (N : ℝ) ^ Module.finrank ℚ E := by exact_mod_cast hd
    rwa [Nat.cast_natAbs, Int.cast_abs] at h
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn' : (Module.finrank ℚ E : ℝ) ≤ N := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ (Module.finrank ℚ E : ℝ) := Nat.cast_nonneg _
  generalize Module.finrank ℚ E = n at *
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hL1 : Real.log N ≤ N - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hD0 : 0 ≤ Real.log |(discr E : ℝ)| := Real.log_nonneg hd1
  have hD : Real.log |(discr E : ℝ)| ≤ n * Real.log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by linarith) hd2
  have hnL : (n : ℝ) * Real.log N ≤ N * (N - 1) := mul_le_mul hn' hL1 hL0 (by linarith)
  have h2 : Real.log (1 + Real.log |(discr E : ℝ)| / 2) ≤ 2 * Real.log N := by
    have e : 2 * Real.log N = Real.log ((N : ℝ) ^ 2) := by rw [Real.log_pow]; norm_num
    rw [e]
    apply Real.log_le_log (by linarith)
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 hn0
  have h4 := mul_nonneg hn0 hL0
  nlinarith
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.UnrSel

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.unrSel :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], (∃ ζ : E, IsPrimitiveRoot ζ l) → ∃ f : UnrHom E Ω l → SelK (Above E l) l ⧸ (powK E l).subgroupOf (SelK (Above E l) l), Function.Injective f := by
  intro E Ω _ _ _ _ _ l _ hζE
  obtain ⟨ζ₀, hζ₀⟩ := hζE
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI : Fact (1 < l) := ⟨(Fact.out : l.Prime).one_lt⟩
  have hζ : IsPrimitiveRoot (algebraMap E Ω ζ₀) l := hζ₀.map_of_injective (algebraMap E Ω).injective
  have hgζ : ∀ g : G E Ω, g (algebraMap E Ω ζ₀) = algebraMap E Ω ζ₀ := fun g => g.commutes ζ₀
  have hdata : ∀ φ : UnrHom E Ω l, ∃ β : Ω, ∃ a : Eˣ, β ^ l = algebraMap E Ω a ∧
      ∀ g : G E Ω, g β = algebraMap E Ω ζ₀ ^ (φ.1 g).val * β := by
    intro φ
    obtain ⟨hlc, hadd, -⟩ := φ.2
    exact radExists E Ω l (algebraMap E Ω ζ₀) (fun _ => 1) φ.1 hζ
      (fun g => by rw [hgζ, ZMod.val_one, pow_one]) hlc (fun g h => by rw [hadd, one_mul])
  choose β a hβa hgβ using hdata
  have hsel : ∀ φ, a φ ∈ SelK (Above E l) l := by
    intro φ
    show ∀ v ∉ Above E l, _
    intro v hv
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    refine dvdOfIne E Ω l A v (β φ) (a φ) hA (hβa φ) ?_
    intro g hg
    have hnot : ¬ A.valuation (l : Ω) < 1 := by
      intro h
      apply hv
      have hp := hA (l : 𝓞 E)
      have he : algebraMap E Ω (((l : 𝓞 E) : E)) = (l : Ω) := by simp
      exact hp.mp (he ▸ h)
    have h0 : φ.1 g = 0 := φ.2.2.2 A hnot g hg
    rw [hgβ, h0, ZMod.val_zero, pow_zero, one_mul]
  refine ⟨fun φ => QuotientGroup.mk ⟨a φ, hsel φ⟩, fun φ ψ hfe => ?_⟩
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hfe
  obtain ⟨c, hc⟩ := hfe
  have hc' : a ψ = a φ * c ^ l := by
    have h : c ^ l = (a φ)⁻¹ * a ψ := by simpa using hc
    rw [h, mul_inv_cancel_left]
  have hβne : ∀ φ, β φ ≠ 0 := by
    intro φ h
    have h' := hβa φ
    rw [h, zero_pow (NeZero.ne l)] at h'
    exact (a φ).ne_zero ((map_eq_zero_iff _ (algebraMap E Ω).injective).mp h'.symm)
  have hcΩ : algebraMap E Ω (c : E) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap E Ω).injective).mpr c.ne_zero
  apply Subtype.ext
  funext g
  have hγl : (β ψ / (β φ * algebraMap E Ω c)) ^ l = 1 := by
    rw [div_pow, mul_pow, hβa ψ, hβa φ, ← map_pow, ← map_mul, hc', Units.val_mul, Units.val_pow_eq_pow_val]
    exact div_self ((map_ne_zero_iff _ (algebraMap E Ω).injective).mpr
      (mul_ne_zero (a φ).ne_zero (pow_ne_zero _ c.ne_zero)))
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hγl
  have hgγ : g (β ψ / (β φ * algebraMap E Ω c)) = β ψ / (β φ * algebraMap E Ω c) := by
    rw [← hi, map_pow, hgζ]
  have hγ0 : β ψ / (β φ * algebraMap E Ω c) ≠ 0 := div_ne_zero (hβne ψ) (mul_ne_zero (hβne φ) hcΩ)
  have hgγ' : g (β ψ / (β φ * algebraMap E Ω c)) =
      algebraMap E Ω ζ₀ ^ (ψ.1 g).val / algebraMap E Ω ζ₀ ^ (φ.1 g).val *
        (β ψ / (β φ * algebraMap E Ω c)) := by
    rw [map_div₀, map_mul, hgβ, hgβ, AlgEquiv.commutes, mul_assoc, mul_div_mul_comm]
  have hζb : algebraMap E Ω ζ₀ ^ (φ.1 g).val ≠ 0 := pow_ne_zero _ (hζ.ne_zero (NeZero.ne l))
  have hq : algebraMap E Ω ζ₀ ^ (ψ.1 g).val / algebraMap E Ω ζ₀ ^ (φ.1 g).val = 1 := by
    apply mul_right_cancel₀ hγ0
    rw [one_mul, ← hgγ', hgγ]
  have hpow := ((div_eq_one_iff_eq hζb).mp hq).symm
  exact ZMod.val_injective l (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hpow)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.Imports

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.gen :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ), 0 < N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∀ (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ), ∃ g : ℕ, Module.length ℤ_[l] (Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l])) ≤ g ∧ (g : ℝ) ≤ 8 * l * Module.finrank ℚ E * Real.log ((l : ℝ) * N) := by
  intro E Ω _ _ _ _ _ N hN hE l hl D e
  have hl2 : 2 ≤ l := hl.out.two_le
  obtain ⟨hdeg, hζ, hemb⟩ := fnOne E Ω l
  obtain ⟨f, hf⟩ := unrInj E Ω l D e
  obtain ⟨f', hf'⟩ := unrSel (Fn E Ω l 1) Ω l hζ
  obtain ⟨hfin, hcard⟩ := selCard (Fn E Ω l 1) l
  have hH := logH (Fn E Ω l 1) (l * N) (by nlinarith) (hemb N hN hE)
  haveI := Finite.of_injective _ (hf'.comp hf)
  obtain ⟨k, hk, hc⟩ := lenOfCard l (Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l]))
  have h1 := (Nat.card_le_card_of_injective _ (hf'.comp hf)).trans hcard
  rw [hc] at h1
  have hn : Module.finrank ℚ (Fn E Ω l 1) ≤ l * Module.finrank ℚ E := by
    rw [← Module.finrank_mul_finrank ℚ E (Fn E Ω l 1), mul_comm]
    exact Nat.mul_le_mul_right _ ((Nat.le_of_dvd (by omega) hdeg).trans (by omega))
  refine ⟨k, hk.le, ?_⟩
  have hh : (0 : ℝ) < classNumber (Fn E Ω l 1) := by exact_mod_cast classNumber_pos _
  generalize Module.finrank ℚ (Fn E Ω l 1) = m at *
  generalize classNumber (Fn E Ω l 1) = h at *
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl2
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h2 : (l : ℝ) ^ k ≤ (l : ℝ) ^ (2 * m) * h := by exact_mod_cast h1
  have h3 := Real.log_le_log (by positivity) h2
  rw [Real.log_mul (by positivity) hh.ne', Real.log_pow, Real.log_pow] at h3
  push_cast at h3 hH
  have ha : Real.log 2 ≤ Real.log l := Real.log_le_log (by norm_num) hl'
  have hb : Real.log l ≤ Real.log ((l : ℝ) * N) := Real.log_le_log (by positivity) (by nlinarith)
  have h2' := Real.log_two_gt_d9
  have hn' : (m : ℝ) ≤ l * Module.finrank ℚ E := by exact_mod_cast hn
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have h4 := mul_le_mul_of_nonneg_left hb hm
  have h5 : (k : ℝ) * (5 / 8) ≤ k * Real.log l := mul_le_mul_of_nonneg_left (by linarith) hk0
  have h6 := mul_le_mul_of_nonneg_right hn' (show 0 ≤ Real.log ((l : ℝ) * N) by linarith)
  nlinarith
end
end
