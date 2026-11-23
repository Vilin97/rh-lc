module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ExistsPlaceRat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HthPlace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Algebra.Field.Defs
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StSel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StTame
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Ufacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StConj

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V
open scoped Pointwise

theorem UpperTheory.V.Fr.st_conj :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (k : Type) [Field k] (κ : G ℚ Ω →* kˣ) (y : G ℚ Ω → k), (∀ s t, y (s * t) = y s + κ s * y t) → ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (A A' : ValuationSubring Ω), IsPlaceOver A v → IsPlaceOver A' v → (∃ b, ∀ s ∈ Dec (F := ℚ) A, y s = κ s * b - b) → ∃ b, ∀ s ∈ Dec (F := ℚ) A', y s = κ s * b - b := by
  intro Ω _ _ _ k _ κ y hy v A A' hA hA' ⟨b, hb⟩
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (F := ℚ) hA hA'
  refine ⟨(κ σ : k) * b - y σ, fun s hs => ?_⟩
  have hs' : s • A' = A' := mem_Dec.mp hs
  have ht : σ⁻¹ * s * σ ∈ Dec (F := ℚ) A := by
    rw [mem_Dec, mul_smul, mul_smul, hσ, hs', ← hσ, ← mul_smul, inv_mul_cancel, one_smul]
  have hbt := hb _ ht
  have hκ : κ (σ⁻¹ * s * σ) = κ s := by
    rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  have hκ' : ((κ (σ⁻¹ * s * σ) : kˣ) : k) = κ s := congrArg Units.val hκ
  have h1 := hy s σ
  have h2 := hy σ (σ⁻¹ * s * σ)
  have h3 : σ * (σ⁻¹ * s * σ) = s * σ := by group
  rw [h3] at h2
  linear_combination -h1 + h2 + (κ σ : k) * hbt + (κ σ : k) * b * hκ'
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StEta

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.st_eta :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (η : G ℚ Ω →* ℤˣ) (D : ℕ) (δ : Ω), 0 < D → δ ^ 2 = -(D : Ω) → (∀ s : G ℚ Ω, s δ = (η s : ℤ) • δ) → ∀ σ : G ℚ Ω, IsCC σ → η σ = -1 := by
  intro Ω _ _ _ η D δ hD hδ hs σ hσ
  obtain ⟨j, hj⟩ := hσ
  rcases Int.units_eq_one_or (η σ) with h | h
  · exfalso
    have h1 : σ δ = δ := by rw [hs σ, h]; simp
    have h2 : j δ = starRingEnd ℂ (j δ) := by
      have := hj δ
      rw [← this]
      exact congrArg j h1.symm
    have h3 : (j δ) ^ 2 = -(D : ℂ) := by
      rw [← map_pow, hδ]; simp
    have him : (j δ).im = 0 := Complex.conj_eq_iff_im.mp h2.symm
    have h4 := congrArg Complex.re h3
    simp [sq, him] at h4
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    nlinarith [mul_self_nonneg (j δ).re]
  · exact h
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StMu

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.st_mu :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (M a : ℕ), M ≠ 0 → ∀ (C : Type) [Group C] (χ : G ℚ Ω →* C), Af.KillsMu (M ^ a) χ → IsOpen (χ.ker : Set (G ℚ Ω)) ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → Ine (F := ℚ) A ≤ χ.ker := by
  intro Ω _ _ _ M a hM C _ χ hk
  haveI : NeZero (M ^ a) := ⟨pow_ne_zero _ hM⟩
  obtain ⟨hopen, -, -, -, hine⟩ := UpperTheory.V.Chr.clsFacts ℚ Ω (M ^ a)
  have hle : (UpperTheory.V.Chr.cls ℚ Ω (M ^ a)).ker ≤ χ.ker := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    apply hk s
    intro ζ hζ
    rw [UpperTheory.V.Chr.cls_spec (M ^ a) s ζ hζ, hs, Units.val_one, ZMod.val_one_eq_one_mod,
      ← pow_eq_pow_mod 1 hζ, pow_one]
  refine ⟨Subgroup.isOpen_mono hle hopen, ?_⟩
  intro A hA
  refine le_trans (hine A ?_) hle
  rw [Nat.cast_pow, map_pow, not_lt]
  exact one_le_pow₀ (not_lt.mp hA)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StRes

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.st_res :
    ∀ (Γ k : Type) [Group Γ] [Field k] (κ : Γ →* kˣ) (U : Subgroup Γ), commutator Γ ≤ U → (∃ u ∈ U, κ u ≠ 1) → ∀ y : Γ → k, (∀ s t, y (s * t) = y s + κ s * y t) → (∃ b, ∀ s ∈ U, y s = κ s * b - b) → ∃ b, ∀ s, y s = κ s * b - b := by
  intro Γ k _ _ κ U hU hu y hy hb
  obtain ⟨u, huU, hu1⟩ := hu
  obtain ⟨b, hb⟩ := hb
  refine ⟨b, fun s => ?_⟩
  have hc : s * u * s⁻¹ * u⁻¹ ∈ U := by
    apply hU
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top s) (Subgroup.mem_top u)
    rw [commutatorElement_def] at this
    exact this
  have hv : s * u * s⁻¹ ∈ U := by
    have := U.mul_mem hc huU
    simpa using this
  have hκ : κ (s * u * s⁻¹) = κ u := by
    rw [map_mul, map_mul, map_inv, mul_comm (κ s) (κ u), mul_inv_cancel_right]
  have h1 := hy s u
  have h2 := hy (s * u * s⁻¹) s
  rw [inv_mul_cancel_right, hb _ hv, hκ] at h2
  rw [hb u huU] at h1
  have hne : ((κ u : k) - 1) ≠ 0 := by
    intro h
    apply hu1
    ext
    simpa using sub_eq_zero.mp h
  apply mul_left_cancel₀ hne
  linear_combination h1 - h2
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Strict

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem st_char : GC.Hypotheses₂ → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (κ : G ℚ Ω →* kˣ), IsOpen (κ.ker : Set (G ℚ Ω)) → (∃ σ : G ℚ Ω, IsCC σ ∧ κ σ ≠ 1) → (∃ s, κ s ≠ GC.cycF ℚ Ω l k s) → ∀ N w : ℕ, N ≠ 0 → w.Prime → w ≠ l → (∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → Ine (F := ℚ) A ≤ κ.ker) → (∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → Dec (F := ℚ) A ≤ κ.ker ⊓ (GC.cycF ℚ Ω l k).ker) → (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ s ∈ Dec (F := ℚ) A, κ s ≠ 1) →
    ∃ y : G ℚ Ω → k, IsLocallyConstant y ∧ (∀ s t, y (s * t) = y s + κ s * y t) ∧ (¬ ∃ b, ∀ s, y s = κ s * b - b) ∧ (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ b, ∀ s ∈ Dec (F := ℚ) A, y s = κ s * b - b) ∧
      ∀ A : ValuationSubring Ω, ¬ A.valuation (w : Ω) < 1 → ∀ s ∈ Ine (F := ℚ) A, κ s = 1 → y s = 0 := by
  intro hP Ω _ _ _ l _ hl2 k _ _ _ κ hκo hcc hcyc N w hN hw hwl hram hdecw hdecl
  have hlp : l.Prime := Fact.out
  obtain ⟨hIt, hex, hne, hdict⟩ := Kum.placeDict ℚ Ω
  obtain ⟨S, v₀, hv₀, hS⟩ := st_set Ω l w N hlp hw hN _ κ hram
  have hmem : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ), IsPlaceOver A v →
      (A.valuation (n : Ω) < 1 ↔ (n : 𝓞 ℚ) ∈ v.asIdeal) :=
    fun A v n h => hdict A v n h
  have hw0 : (w : 𝓞 ℚ) ∈ v₀.asIdeal := (hv₀ v₀).2 rfl
  have hl_notin : (l : 𝓞 ℚ) ∉ v₀.asIdeal := by
    intro hl
    have hcop : IsCoprime (l : ℤ) (w : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hlp hw).2 (Ne.symm hwl))
    have hcop' : IsCoprime (l : 𝓞 ℚ) (w : 𝓞 ℚ) := by
      simpa using hcop.map (Int.castRingHom (𝓞 ℚ))
    obtain ⟨u, u', hu⟩ := hcop'
    apply v₀.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hu]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hw0)
  have hv₀S : v₀ ∈ S := (hS v₀ (placeOf Ω v₀) (isPlaceOver_placeOf Ω v₀)).2 (Or.inr (Or.inl rfl))
  have hCA : ContainsAbove S l := fun v hv => (hS v (placeOf Ω v) (isPlaceOver_placeOf Ω v)).2 (Or.inl hv)
  have hout : ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v → Ine (F := ℚ) A ≤ κ.ker := by
    intro v hv A hA
    by_contra h
    exact hv ((hS v A hA).2 (Or.inr (Or.inr h)))
  have hdec0 : ∀ A : ValuationSubring Ω, IsPlaceOver A v₀ → Dec (F := ℚ) A ≤ κ.ker ⊓ (GC.cycF ℚ Ω l k).ker :=
    fun A hA => hdecw A ((hmem A v₀ w hA).2 hw0)
  have hother : ∀ v ∈ S, v ≠ v₀ → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∃ s ∈ Dec (F := ℚ) A, κ s ≠ 1 := by
    intro v hv hne' A hA
    rcases (hS v A hA).1 hv with h | h | h
    · exact hdecl A ((hmem A v l hA).2 h)
    · exact absurd h hne'
    · obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.1 h
      exact ⟨s, Ine_le_Dec A hs, by rwa [MonoidHom.mem_ker] at hs'⟩
  obtain ⟨y, hyc, hyco, hynot, hyout, hyS⟩ :=
    st_sel hP Ω l hl2 k κ hκo hcc hcyc S hCA hout v₀ hv₀S hl_notin hdec0 hother
  have hcob : ∀ v ∈ S, v ≠ v₀ → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
      ∃ b, ∀ s ∈ Dec (F := ℚ) A, y s = (κ s : k) * b - b := by
    intro v hv hne' A hA
    obtain ⟨A0, hA0, hb⟩ := hyS v hv hne'
    exact st_conj Ω k κ y hyco v A0 A hA0 hA hb
  refine ⟨y, hyc, hyco, hynot, ?_, ?_⟩
  · intro A hA
    obtain ⟨v, hv⟩ := hex A (hne A l hlp.ne_zero hA)
    have hlv := (hmem A v l hv).1 hA
    refine hcob v (hCA v hlv) ?_ A hv
    rintro rfl
    exact hl_notin hlv
  · intro A hA s hs hκs
    by_cases htop : A = ⊤
    · subst htop
      rw [hIt] at hs
      rw [Subgroup.mem_bot.1 hs]
      have h := hyco 1 1
      rw [mul_one, map_one, Units.val_one, one_mul] at h
      simpa using h
    obtain ⟨v, hv⟩ := hex A htop
    by_cases hvS : v ∈ S
    · have hvne : v ≠ v₀ := by
        intro h
        exact hA ((hmem A v w hv).2 (h ▸ hw0))
      obtain ⟨b, hb⟩ := hcob v hvS hvne A hv
      rw [hb s (Ine_le_Dec A hs), hκs, Units.val_one, one_mul, sub_self]
    · exact hyout v hvS A hv s hs

theorem UpperTheory.V.Fr.strict :
    GC.Hypotheses₂ → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (H₀ : Subgroup (G ℚ Ω)) (w : ℕ), FrobeniusSplitPrimeDatum η M H₀ → FrobeniusWitnessPrime l η Ψ M w → ∀ (m : ℕ) (a : ℕ), a = 1 ∨ a = 2 → StrictCl l η Ψ ((barChar O Ψ)⁻¹ ^ a * etaO O η) (Upl l Hb H₀ w m) := by
  intro hP Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG H₀ w h0 hw m a ha
  have hlp : l.Prime := Fact.out
  haveI : Finite (ResidueField O) := hG.fin
  have hF := ufacts l η Ψ σ B M Hb hG H₀ w h0 hw m
  set U := Upl l Hb H₀ w m with hU
  set κ : G ℚ Ω →* (ResidueField O)ˣ := (barChar O Ψ)⁻¹ ^ a * etaO O η with hκdef
  have hκ : ∀ s, κ s = ((barChar O Ψ s)⁻¹) ^ a * etaO O η s := fun s => rfl
  have hκη : ∀ s, η s = 1 → κ s = ((barChar O Ψ s)⁻¹) ^ a := by
    intro s h1
    rw [hκ]
    show _ * Units.map _ (η s) = _
    rw [h1, map_one, mul_one]
  have hκ1 : ∀ s, η s = 1 → barChar O Ψ s = 1 → κ s = 1 := by
    intro s h1 h2
    rw [hκη s h1, h2, inv_one, one_pow]
  obtain ⟨b, hηb, hΨb⟩ := hG.cyc
  have hκK : Af.KillsMu (M ^ b) κ := fun s hs => hκ1 s (hηb s hs) (hΨb s hs)
  obtain ⟨hKo, hram⟩ := st_mu Ω M b hG.M_ne _ κ hκK
  have hM_l : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → A.valuation (M : Ω) < 1 := by
    intro A hA
    obtain ⟨t, ht⟩ := hG.l_dvd
    rw [ht, Nat.cast_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (valuation_natCast_le_one A t)) hA
  have hdecl : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ s ∈ Dec (F := ℚ) A ⊓ U, κ s ≠ 1 := by
    intro A hA
    obtain ⟨s, hs, hs2⟩ := hF.f3 A hA
    have hη : η s = 1 := hF.split A (hM_l A hA) hs
    refine ⟨s, hs, ?_⟩
    rw [hκη s hη]
    rcases ha with rfl | rfl
    · intro h
      apply hs2
      rw [pow_one, inv_eq_one] at h
      rw [h, one_pow]
    · intro h
      apply hs2
      rwa [inv_pow, inv_eq_one] at h
  have hne1 : (-1 : ResidueField O) ≠ 1 := by
    rw [Ne, neg_one_eq_one_iff, ringChar.eq (ResidueField O) l]
    exact hG.odd
  obtain ⟨D, δ, hD, -, hδ, hηδ⟩ := hG.quad
  have hησ : η σ = -1 := st_eta Ω η D δ hD hδ hηδ σ hG.cc
  have hκσ : κ σ ≠ 1 := by
    rw [hκ, hG.even, inv_one, one_pow, one_mul]
    intro h
    apply hne1
    have h' := congrArg (fun u : (ResidueField O)ˣ => (u : ResidueField O)) h
    simpa [etaO, hησ] using h'
  have hcyc : ∃ s, κ s ≠ GC.cycF ℚ Ω l (ResidueField O) s := by
    have hex : ∃ s ∈ U ⊓ η.ker, (omO Ω l O) s * (barChar O Ψ) s ^ (a : ℤ) ≠ 1 := by
      rcases ha with rfl | rfl
      · exact hF.f2b 1 (Or.inl rfl)
      · exact hF.f2c 2 (Or.inl rfl)
    obtain ⟨s, hs, hne⟩ := hex
    have hη : η s = 1 := (Subgroup.mem_inf.1 hs).2
    refine ⟨s, fun h => hne ?_⟩
    have h' : omO Ω l O s = κ s := h.symm
    rw [h', hκη s hη, zpow_natCast, inv_pow, inv_mul_cancel]
  have hwl : w ≠ l := by
    intro h
    have h1 : w % l = 1 % l := hw.one
    rw [h, Nat.mod_self, Nat.mod_eq_of_lt hlp.one_lt] at h1
    exact zero_ne_one h1
  have hdecw : ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 →
      Dec (F := ℚ) A ≤ κ.ker ⊓ (GC.cycF ℚ Ω l (ResidueField O)).ker := by
    intro A hA s hs
    obtain ⟨h12, h3⟩ := Subgroup.mem_inf.1 (hw.split A hA hs)
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 h12
    exact Subgroup.mem_inf.2 ⟨hκ1 s h1 h2, h3⟩
  obtain ⟨y, hyc, hyco, hynot, hydec, hyw⟩ :=
    st_char hP Ω l hG.odd (ResidueField O) κ hKo ⟨σ, hG.cc, hκσ⟩ hcyc M w hG.M_ne hw.prime hwl hram hdecw
      (fun A hA => by
        obtain ⟨s, hs, h⟩ := hdecl A hA
        exact ⟨s, (Subgroup.mem_inf.1 hs).1, h⟩)
  refine ⟨y, hyc, hyco, ?_, hydec, ?_⟩
  · rintro ⟨b0, hb0⟩
    obtain ⟨s, hs, hκs⟩ := hdecl B hG.over_l
    exact hynot (st_res (G ℚ Ω) _ κ U hF.ab ⟨s, (Subgroup.mem_inf.1 hs).2, hκs⟩ y hyco ⟨b0, hb0⟩)
  · intro B' hB' s hs hη hΨ
    have hs' := Subgroup.mem_inf.1 hs
    by_cases hBw : B'.valuation (w : Ω) < 1
    · have hth' := hth Ω l w hw.prime hw.one
      have hsH : s ∈ Hth Ω l w := by
        have h2 := hs'.2
        simp only [hU, Upl, Subgroup.mem_inf] at h2
        exact h2.1.1.2
      refine st_tame Ω l (ResidueField O) B' hB' _ hth'.1 hth'.2.1 hth'.2.2.1 (hth'.2.2.2.2 B' hBw) y hyc ?_ s
        (Subgroup.mem_inf.2 ⟨hs'.1, hsH⟩)
      intro s1 hs1 t1 _
      have hk : κ s1 = 1 := (Subgroup.mem_inf.1 (hdecw B' hBw (Ine_le_Dec B' hs1))).1
      rw [hyco, hk, Units.val_one, one_mul]
    · exact hyw B' hBw s hs'.1 (hκ1 s hη hΨ)
end
end
