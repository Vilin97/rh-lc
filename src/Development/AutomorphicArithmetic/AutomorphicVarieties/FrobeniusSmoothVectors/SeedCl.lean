module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.SlopeTestRemainingChoices
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.UnramIff
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScStrip
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScTeich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HthPlace
import Mathlib.Tactic.Polynomial.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SoCls

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScCong

section

@[expose] public section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.sc_cong :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (u : c.Oˣ) (a : (Qbar l)ˣ), ‖a.val - u.val.1‖ < 1 → Sd.Cong (a ^ 2) 1 → Units.map (residue c.O).toMonoidHom u ^ 2 = 1 := by
  intro l _ c u a ha hcong
  have hu := (sc_norm l c u.val).1
  unfold Sd.Cong at hcong
  rw [Units.val_pow_eq_pow_val, Units.val_one] at hcong
  set x : PadicAlgCl l := ((u.val : c.O) : PadicAlgCl l) with hx
  set y : PadicAlgCl l := a.val with hy
  have hy1 : ‖y‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (y - x) x
    rw [sub_add_cancel] at h
    exact h.trans (max_le ha.le hu)
  have hxy : ‖x + y‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max x y).trans (max_le hu hy1)
  have hmem : (u.val ^ 2 - 1 : c.O) ∈ maximalIdeal c.O := by
    rw [(sc_norm l c _).2]
    have e : ((u.val ^ 2 - 1 : c.O) : PadicAlgCl l) = (x - y) * (x + y) + (y ^ 2 - 1) := by
      rw [hx]
      push_cast
      ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hcong)
    rw [norm_mul]
    have : ‖x - y‖ < 1 := by rw [← norm_neg, neg_sub]; exact ha
    nlinarith [norm_nonneg (x - y), norm_nonneg (x + y)]
  ext
  simp only [Units.val_pow_eq_pow_val, Units.coe_map, Units.val_one]
  rw [← sub_eq_zero]
  have h0 := (residue_eq_zero_iff _).2 hmem
  rw [map_sub, map_pow, map_one] at h0
  exact h0
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScDisc

section

@[expose] public section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.sc_disc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [NumberField K] [Algebra K Ω], Module.finrank ℚ K = 2 → (∀ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 → Ine (F := ℚ) B ≤ galOf ℚ K Ω) → ¬ (l : ℤ) ∣ discr K := by
  intro Ω _ _ _ l _ K _ _ _ h2 hB
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩
  haveI : IsGalois ℚ K := {}
  have hl : l.Prime := Fact.out
  rw [← (UpperTheory.V.CF.unramIff).2.1 K l hl, (UpperTheory.V.CF.unramIff).1 K l hl]
  intro w hw
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver (F := K) Ω w
  have hv : A.valuation (l : Ω) < 1 := by
    have h := (hA (l : 𝓞 K)).2 hw
    simpa only [map_natCast] using h
  have hI := hB A hv
  rw [← UpperTheory.V.CF.ineAbs ℚ K Ω A w hA, Subgroup.eq_bot_iff_forall]
  rintro _ ⟨σ, hσ, rfl⟩
  have hσ' : ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x := hI hσ
  ext x
  apply (algebraMap K Ω).injective
  show algebraMap K Ω (σ.restrictNormal K x) = algebraMap K Ω x
  rw [AlgEquiv.restrictNormal_commutes]
  exact hσ' x
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScQuad

section

@[expose] public section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.sc_quad :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (η : G ℚ Ω →* ℤˣ) (D : ℕ) (δ : Ω), 0 < D → δ ^ 2 = -(D : Ω) → (∀ s : G ℚ Ω, s δ = (η s : ℤ) • δ) → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra K Ω), Module.finrank ℚ K = 2 ∧ IsTotallyComplex K ∧ galOf ℚ K Ω = η.ker := by
  intro Ω _ _ _ η D δ hD hδ hη
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have h0 : ((D : ℕ) : Ω) = 0 := by
      have := hδ.symm
      simpa using this
    exact hD.ne' (by exact_mod_cast h0)
  set p : Polynomial ℚ := Polynomial.X ^ 2 + Polynomial.C (D : ℚ) with hp
  have hmon : p.Monic := Polynomial.monic_X_pow_add_C _ two_ne_zero
  have hdeg : p.natDegree = 2 := Polynomial.natDegree_X_pow_add_C
  have hroot : Polynomial.aeval δ p = 0 := by
    simp [hp, hδ]
  have hirr : Irreducible p := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) ?_
    intro x hx
    simp only [hp, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hx
    nlinarith [sq_nonneg x]
  have hmin : p = minpoly ℚ δ := minpoly.eq_of_irreducible_of_monic hirr hroot hmon
  have hint : IsIntegral ℚ δ := ⟨p, hmon, by rw [← Polynomial.aeval_def]; exact hroot⟩
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({δ} : Set Ω)) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : NumberField (IntermediateField.adjoin ℚ ({δ} : Set Ω)) := by constructor
  refine ⟨IntermediateField.adjoin ℚ ({δ} : Set Ω), inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · rw [IntermediateField.adjoin.finrank hint, ← hmin, hdeg]
  · refine ⟨fun v => ?_⟩
    rw [NumberField.InfinitePlace.isComplex_iff]
    intro hr
    rw [NumberField.ComplexEmbedding.isReal_iff] at hr
    set φ := v.embedding
    let d : IntermediateField.adjoin ℚ ({δ} : Set Ω) := ⟨δ, IntermediateField.mem_adjoin_simple_self ℚ δ⟩
    have hd : d ^ 2 = -(D : IntermediateField.adjoin ℚ ({δ} : Set Ω)) := Subtype.ext (by simpa [d] using hδ)
    have hz : (φ d) ^ 2 = -(D : ℂ) := by
      have := congrArg φ hd
      simpa using this
    have hc : (starRingEnd ℂ) (φ d) = φ d := by
      have := RingHom.congr_fun hr d
      simpa using this
    have him : (φ d).im = 0 := Complex.conj_eq_iff_im.mp hc
    have hre := congrArg Complex.re hz
    simp [pow_two, him] at hre
    nlinarith [mul_self_nonneg (φ d).re]
  · ext σ
    rw [mem_galOf, MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : σ δ = δ := h ⟨δ, IntermediateField.mem_adjoin_simple_self ℚ δ⟩
      rw [hη σ] at h1
      rcases Int.units_eq_one_or (η σ) with h2 | h2
      · exact h2
      · exfalso
        rw [h2] at h1
        simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] at h1
        have : (2 : Ω) * δ = 0 := by linear_combination -h1
        rcases mul_eq_zero.mp this with h3 | h3
        · exact two_ne_zero h3
        · exact hδ0 h3
    · intro h x
      have hσδ : σ δ = δ := by rw [hη σ, h]; simp
      have hext : ((σ : Ω →ₐ[ℚ] Ω).comp (IntermediateField.val _) :
          IntermediateField.adjoin ℚ ({δ} : Set Ω) →ₐ[ℚ] Ω) = IntermediateField.val _ :=
        IntermediateField.algHom_ext_of_eq_adjoin ℚ rfl (by
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact hσδ)
      exact AlgHom.congr_fun hext x
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScTheta

section

@[expose] public section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.sc_theta :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (w : ℕ), w.Prime → w ≡ 1 [MOD l] → ∃ θ : G ℚ Ω →* (Qbar l)ˣ, θ.ker = Hth Ω l w ∧ θ ≠ 1 ∧ θ ^ l = 1 ∧ Af.KillsMu w θ := by
  intro Ω _ _ _ l _ w hw hwl
  obtain ⟨-, hc, hidx, -, -⟩ := hth Ω l w hw hwl
  haveI hN : (Hth Ω l w).Normal := ⟨fun n hn g => by
    have h0 := Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n)
    rw [commutatorElement_def] at h0
    have h1 := hc h0
    have h2 : g * n * g⁻¹ = g * n * g⁻¹ * n⁻¹ * n := by group
    rw [h2]
    exact (Hth Ω l w).mul_mem h1 hn⟩
  have hcardQ : Nat.card (G ℚ Ω ⧸ Hth Ω l w) = l := hidx
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Qbar l) l
  have hcardR : Nat.card (rootsOfUnity l (Qbar l)) = l := hζ.card_rootsOfUnity
  let e := mulEquivOfPrimeCardEq hcardQ hcardR
  let θ : G ℚ Ω →* (Qbar l)ˣ :=
    (rootsOfUnity l (Qbar l)).subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (Hth Ω l w)))
  have hθ : ∀ s, θ s = ((e (QuotientGroup.mk' (Hth Ω l w) s) : rootsOfUnity l (Qbar l)) : (Qbar l)ˣ) :=
    fun s => rfl
  have hker : θ.ker = Hth Ω l w := by
    ext s
    rw [MonoidHom.mem_ker, hθ]
    constructor
    · intro h
      have h' : e (QuotientGroup.mk' (Hth Ω l w) s) = 1 := Subtype.ext h
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h'
      exact h'
    · intro h
      have h' : QuotientGroup.mk' (Hth Ω l w) s = 1 := (QuotientGroup.eq_one_iff s).mpr h
      rw [h', map_one]
      rfl
  refine ⟨θ, hker, ?_, ?_, ?_⟩
  · intro h1
    have htop : Hth Ω l w = ⊤ := by rw [← hker, h1, MonoidHom.ker_one]
    rw [htop, Subgroup.index_top] at hidx
    exact (Fact.out : l.Prime).one_lt.ne hidx
  · ext s
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, hθ]
    exact congrArg Units.val ((mem_rootsOfUnity _ _).mp (e (QuotientGroup.mk' (Hth Ω l w) s)).2)
  · unfold Af.KillsMu
    intro s hs
    rw [← MonoidHom.mem_ker, hker]
    unfold Hth
    refine ⟨⟨1, fun z hz => ?_⟩, ⟨1, fun z hz => ?_⟩⟩
    · rw [one_pow, pow_one]
      exact hs z hz
    · rw [one_pow, pow_one]
      have e1 := congrArg (s⁻¹ : G ℚ Ω) (hs z hz)
      rw [← e1]
      simp
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SeedCl

section

@[expose] public section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem km_mono {Ω C : Type} [Field Ω] [CharZero Ω] [Monoid C] {m n : ℕ} (h : m ∣ n) {χ : G ℚ Ω →* C}
    (hχ : Af.KillsMu m χ) : Af.KillsMu n χ := fun s hs => hχ s fun ζ hζ => hs ζ (by
  obtain ⟨k, rfl⟩ := h
  rw [pow_mul, hζ, one_pow])

private theorem split_of {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [Fact l.Prime] {N w : ℕ} (hw : w ≡ 1 [MOD N])
    {χ : G ℚ Ω →* (Qbar l)ˣ} (hχ : Af.KillsMu N χ) : Sd.SplitAt N w χ :=
  ⟨hχ, fun s hs => hχ s fun ζ hζ => by
    rw [hs ζ hζ, pow_eq_pow_mod w hζ, hw, ← pow_eq_pow_mod 1 hζ, pow_one]⟩

theorem UpperTheory.V.Fr.seed_cl :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* c.Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∃ Q : ℕ, Q ≠ 0 ∧ ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (w : ℕ), IsAbelianGalois ℚ L → galOf ℚ L Ω = upl Ω L ⊓ η.ker → FrobeniusWitnessPrime l η Ψ M w → w ≡ 1 [MOD Q] → upl Ω L ≤ Hth Ω l w → (∃ s ∈ galOf ℚ L Ω, barChar c.O Ψ s ^ 2 ≠ 1) → SeedClause c η Ψ σ L := by
  intro Ω _ _ _ l _ c _ η Ψ σ B M Hb hG
  have hlp : l.Prime := Fact.out
  obtain ⟨a, hηa, hΨa⟩ := hG.cyc
  obtain ⟨j, hj⟩ := hG.Ψ_l
  obtain ⟨D, δ, hD, -, hδ, hηδ⟩ := hG.quad
  obtain ⟨K, iK, nK, aK, hK2, hKc, hKη⟩ := sc_quad Ω η D δ hD hδ hηδ
  obtain ⟨T, hT, hTa⟩ := sc_teich Ω l c hG.fin
  have hM : M ^ a * l ≠ 0 := mul_ne_zero (pow_ne_zero _ hG.M_ne) hlp.ne_zero
  obtain ⟨r, N, hlN, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM l hlp.one_lt.ne'
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hM (by rw [hN, mul_zero])
  let φ : G ℚ Ω →* (ResidueField c.O)ˣ := barChar c.O Ψ * (omO Ω l c.O ^ j)⁻¹
  let χ' : G ℚ Ω →* (Qbar l)ˣ := T.comp φ
  let η' : G ℚ Ω →* (Qbar l)ˣ := (Units.map (Int.castRingHom (Qbar l)).toMonoidHom).comp η
  have hφ : ∀ s, φ s = barChar c.O Ψ s * ((omO Ω l c.O) s ^ j)⁻¹ := fun s => rfl
  have hχ : ∀ s, χ' s = T (φ s) := fun s => rfl
  have hη'ker : η'.ker = η.ker := by
    ext s
    simp only [MonoidHom.mem_ker]
    exact map_eq_one_iff _ (Units.map_injective (f := (Int.castRingHom (Qbar l)).toMonoidHom) Int.cast_injective)
  have hφK : Af.KillsMu (M ^ a * l) φ := by
    intro s hs
    have h1 : barChar c.O Ψ s = 1 := km_mono (dvd_mul_right _ _) hΨa s hs
    have h2 : omO Ω l c.O s = 1 := km_mono (dvd_mul_left _ _) (sc_om Ω l c.O).1 s hs
    rw [hφ, h1, h2, one_pow, inv_one, mul_one]
  have hχK : Af.KillsMu (M ^ a * l) χ' := by
    intro s hs
    rw [hχ, hφK s hs, map_one]
  have hη'K : Af.KillsMu (M ^ a * l) η' := by
    intro s hs
    have h1 : η s = 1 := km_mono (dvd_mul_right _ _) hηa s hs
    show Units.map _ (η s) = 1
    rw [h1, map_one]
  have hχN : Af.KillsMu N χ' := by
    refine sc_strip Ω l _ χ' r N hN0 hlN (hN ▸ hχK) B hG.over_l ?_
    intro s hs
    rw [MonoidHom.mem_ker, hχ, hφ, hj B hG.over_l s hs, mul_inv_cancel, map_one]
  have hη'N : Af.KillsMu N η' := by
    refine sc_strip Ω l _ η' r N hN0 hlN (hN ▸ hη'K) B hG.over_l ?_
    rw [hη'ker]
    exact hG.η_l B hG.over_l
  have hT1 : T (-1) = -1 := by
    have hne : (-1 : (ResidueField c.O)ˣ) ≠ 1 := by
      intro h
      have h' : (-1 : ResidueField c.O) = 1 := by
        simpa using congrArg (fun u : (ResidueField c.O)ˣ => (u : ResidueField c.O)) h
      rw [neg_one_eq_one_iff, ringChar.eq (ResidueField c.O) l] at h'
      exact hG.odd h'
    have hsq : ((T (-1) : (Qbar l)ˣ) : Qbar l) * (T (-1) : Qbar l) = 1 := by
      rw [← Units.val_mul, ← map_mul, neg_one_mul, neg_neg, map_one, Units.val_one]
    rcases mul_self_eq_one_iff.1 hsq with h | h
    · exact absurd (hT (by rw [map_one]; exact Units.ext h)) hne
    · exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
  have happ : ∀ s, (GlobalTheory.GalOfCusp.cycBar ℚ Ω l ^ j * χ') s =
      (GlobalTheory.GalOfCusp.cycBar ℚ Ω l) s ^ j * T ((Units.map ↑(residue c.O)) (Ψ s) * ((omO Ω l c.O) s ^ j)⁻¹) :=
    fun s => rfl
  have hord : ¬ l ∣ orderOf χ' := by
    classical
    haveI := Fintype.ofFinite (ResidueField c.O)
    have hpow : χ' ^ Fintype.card (ResidueField c.O)ˣ = 1 := MonoidHom.ext fun s => by
      show (T (φ s)) ^ Fintype.card (ResidueField c.O)ˣ = 1
      rw [← map_pow, pow_card_eq_one, map_one]
    intro hd
    have hd2 := hd.trans (orderOf_dvd_of_pow_eq_one hpow)
    obtain ⟨n, -, hcard⟩ := FiniteField.card (ResidueField c.O) l
    rw [Fintype.card_units, hcard] at hd2
    have hl1 : l ∣ l ^ (n : ℕ) := dvd_pow_self l n.ne_zero
    have hpos : 1 ≤ l ^ (n : ℕ) := Nat.one_le_pow _ _ hlp.pos
    have h3 : l ∣ (l ^ (n : ℕ) - 1) + 1 := by
      rw [Nat.sub_add_cancel hpos]
      exact hl1
    exact hlp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right hd2).1 h3))
  refine ⟨N, hN0, ?_⟩
  intro L _ _ _ _ w hLab hLgal hw hwQ hLth hs0
  obtain ⟨s0, hs0L, hs0⟩ := hs0
  obtain ⟨θ, hθker, hθ1, hθl, hθw⟩ := sc_theta Ω l w hw.prime hw.one
  have hwN : ¬ w ∣ N := by
    intro hd
    have hd' : w ∣ M ^ a * l := hN ▸ dvd_mul_of_dvd_right hd _
    rcases (Nat.Prime.dvd_mul hw.prime).1 hd' with h | h
    · exact hw.cop (hw.prime.dvd_of_dvd_pow h)
    · have hwl := (Nat.prime_dvd_prime_iff_eq hw.prime hlp).1 h
      have h1 : w % l = 1 % l := hw.one
      rw [hwl, Nat.mod_self, Nat.mod_eq_of_lt hlp.one_lt] at h1
      exact zero_ne_one h1
  have hLK : galOf ℚ L Ω ≤ galOf ℚ K Ω := by
    rw [hKη, hLgal]
    exact inf_le_right
  refine ⟨K, iK, nK, aK, N, w, χ', η', θ, j, ?_, ?_, hord, fun s => rfl, fun s => happ s ▸ hTa (Ψ s) j s, ?_⟩
  · refine ⟨hG.cc, ⟨hG.odd, Nat.pos_of_ne_zero hN0, hlN, hw.prime, hwN, hθ1, hθl, hθw⟩, hK2, hKc, hLab, hLK,
      by rw [hη'ker, hKη], split_of hwQ hη'N, split_of hwQ hχN, ?_, ?_, ?_⟩
    · rw [hθker, hLgal]
      exact inf_le_left.trans hLth
    · rw [hχ, hφ, hG.even, (sc_om Ω l c.O).2 σ hG.cc, one_mul, ← inv_pow, inv_neg_one, map_pow, hT1]
    · refine ⟨s0, hs0L, fun hc => hs0 ?_⟩
      exact sc_cong l c (Ψ s0) _ (happ s0 ▸ hTa (Ψ s0) j s0) hc
  · intro heq
    apply hG.g4
    intro s hs
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hs
    have h1 : χ' s = 1 := by
      rw [hχ, hφ, hs.1, hs.2, one_pow, inv_one, mul_one, map_one]
    rw [heq] at h1
    rw [← hη'ker]
    exact h1
  · exact sc_disc Ω l K hK2 (fun B' hB' => hKη ▸ hG.η_l B' hB')
end
end
