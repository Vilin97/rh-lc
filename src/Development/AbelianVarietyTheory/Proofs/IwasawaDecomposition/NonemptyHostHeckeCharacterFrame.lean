module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveCharacterOfIsCyclic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
public import Development.AutomorphicArithmetic.WeightCongruences.ProdResidueCharNormOneUnitEqOne
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostDeltaCharacterInertialOrderFifteenExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExists

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlacePropertiesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.completelySplitPrime_host_place_properties : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime → SplitsC H.E p → ∀ v : HeightOneSpectrum (𝓞 H.E), OverP H p v → Ideal.absNorm v.asIdeal = p ∧ ((p : ℕ) : 𝓞 H.E) ∉ v.asIdeal ^ 2 ∧ IsSplitPl H v ∧ ∀ (Q : HeightOneSpectrum (𝓞 H.K)), ((p : ℕ) : 𝓞 H.K) ∈ Q.asIdeal → ∀ v', ConjPl H.conj.toRingEquiv v v' → OverP H p v' ∧ (v.under (𝓞 H.K) = Q ↔ v'.under (𝓞 H.K) ≠ Q) := by
  first | exact @GlobalTheory.Mem.Chr.splitsC_main | exact GlobalTheory.Mem.Chr.splitsC_main | (intros; apply GlobalTheory.Mem.Chr.splitsC_main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityTypeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.exists_heckeChar_trivOn_realSubfield_infinityType : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), CMData F c φ → ∀ (e : I → ℤ) (S : Finset (HeightOneSpectrum (𝓞 L))) (θ0 : ∀ v : HeightOneSpectrum (𝓞 L), (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ), (∀ w ∈ S, ∀ w', ConjPl c.toRingEquiv w w' → w' ∉ S) → (∀ ζ : (𝓞 L)ˣ, (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 L) : L) ^ m = 1) → (∏ i, φ i ((ζ : 𝓞 L) : L) ^ (-e i)) * ∏ w ∈ S, ((θ0 w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) : ℂˣ) : ℂ) = 1) → ∃ χ : HChar L, χ.IsUnitary ∧ χ.TrivOn F ∧ χ.HasInf φ (fun i => -2 * e i) ∧ (∀ v, χ.TameAt v) ∧ (∀ v, v ∉ S → (∀ w ∈ S, ¬ ConjPl c.toRingEquiv w v) → χ.UnrAt v) ∧ (∀ w ∈ S, ∀ (k : Lˣ) (y : 𝓞 L) (b : (𝓞 L ⧸ w.asIdeal)ˣ), (k : L) = (y : L) → (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal y → χ.locK w k = θ0 w b) ∧ (∀ w ∈ S, ∀ n : ℕ, ((∀ x, IsUnitAt w x → χ.loc w x ^ n = 1) ↔ θ0 w ^ n = 1) ∧ ∀ w', ConjPl c.toRingEquiv w w' → ((∀ x, IsUnitAt w' x → χ.loc w' x ^ n = 1) ↔ θ0 w ^ n = 1)) := by
  first | exact @GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn | exact GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn | (intros; apply GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryMuZeroCharactersOfSplitTypePrimesAl

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.MuZero

theorem exists_residue_char {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {p : ℕ} (hp : p.Prime)
    (hw : Ideal.absNorm w.asIdeal = p) (ω : (ZMod p)ˣ →* ℂˣ) :
    ∃ θ : (𝓞 L ⧸ w.asIdeal)ˣ →* ℂˣ, θ (-1) = ω (-1) ∧ ∀ (a : ℕ) (ha : a.Coprime p),
      ∃ b : (𝓞 L ⧸ w.asIdeal)ˣ, (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 L) ∧
        θ b = ω (ZMod.unitOfCoprime a ha) := by
  have hc : Nat.card (𝓞 L ⧸ w.asIdeal) = p := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 L ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  let _ : Fintype (𝓞 L ⧸ w.asIdeal) := Fintype.ofFinite _
  let ρ : ZMod p ≃+* (𝓞 L ⧸ w.asIdeal) := ZMod.ringEquivOfPrime _ hp (by rw [← Nat.card_eq_fintype_card, hc])
  refine ⟨ω.comp (Units.map (ρ.symm : (𝓞 L ⧸ w.asIdeal) →* ZMod p)), ?_, fun a ha => ?_⟩
  · rw [MonoidHom.comp_apply]
    congr 1
    ext
    simp
  · refine ⟨Units.map (ρ : ZMod p →* (𝓞 L ⧸ w.asIdeal)) (ZMod.unitOfCoprime a ha), ?_, ?_⟩
    · simp
    · rw [MonoidHom.comp_apply]
      congr 1
      ext
      simp

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

theorem eq_of_overP {k k' : Fin 2} {w : HeightOneSpectrum (𝓞 H.E)} (h : OverP H (H.g k) w)
    (h' : OverP H (H.g k') w) : k = k' := by
  by_contra hne
  have hg : H.g k ≠ H.g k' := by
    fin_cases k <;> fin_cases k'
    · exact absurd rfl hne
    · exact H.g_ne
    · exact H.g_ne.symm
    · exact absurd rfl hne
  have hc : IsCoprime ((H.g k : ℕ) : 𝓞 H.E) ((H.g k' : ℕ) : 𝓞 H.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (H.g_prime k) (H.g_prime k')).2 hg)
  obtain ⟨s, t, hst⟩ := hc
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hst]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h) (w.asIdeal.mul_mem_left _ h')


open Classical in
theorem exists_unitary_mu_zero_characters_of_split_type_primes : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (P : PiBar H) (W : Omg H) (e : R.Psi → ℚ) (j : ℕ), (∀ k, SplitsC H.E (H.g k)) → (∀ τ, ∃ z : ℤ, e τ = z) → UpperTheory.MUQ (embPsi H) e → Mu0Exists P W e j := by
  intro R H P W e j hs hint hev
  choose z hz using hint
  have hmu : UpperTheory.MU (embPsi H) z := hev.mu hz
  haveI := H.galois
  haveI : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ H.K H.E
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hce : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
  have hsp := fun k => GlobalTheory.T.completelySplitPrime_host_place_properties R H (H.g k) (H.g_prime k) (hs k)
  have hθ : ∀ w : HeightOneSpectrum (𝓞 H.E), ∃ θ : (𝓞 H.E ⧸ w.asIdeal)ˣ →* ℂˣ, θ (-1) = 1 ∧
      ∀ k, P.Div k w → ∀ (a : ℕ) (ha : a.Coprime (H.g k)),
        ∃ b : (𝓞 H.E ⧸ w.asIdeal)ˣ, (b : 𝓞 H.E ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 H.E) ∧
          θ b = (W.om k (ZMod.unitOfCoprime a ha) ^ (2 * (j + 1)))⁻¹ := by
    intro w
    by_cases h : ∃ k, P.Div k w
    · obtain ⟨k, hk⟩ := h
      obtain ⟨θ, h1, h2⟩ := exists_residue_char w (H.g_prime k) (hsp k w (P.overP hk)).1
        ((W.om k ^ (2 * (j + 1)))⁻¹)
      refine ⟨θ, ?_, fun k' hk' => ?_⟩
      · rw [h1, MonoidHom.inv_apply, MonoidHom.pow_apply, pow_mul, ← map_pow, neg_one_sq, map_one, one_pow, inv_one]
      · obtain rfl := eq_of_overP (P.overP hk) (P.overP hk')
        exact h2
    · exact ⟨1, rfl, fun k hk => absurd ⟨k, hk⟩ h⟩
  choose θ hθ1 hθ2 using hθ
  let S : Finset (HeightOneSpectrum (𝓞 H.E)) := Finset.univ.biUnion fun k => aboveF (L := H.E) H.K (P.pb k)
  have hS : ∀ w, w ∈ S ↔ ∃ k, P.Div k w := fun w => by
    simp only [S, Finset.mem_biUnion, Finset.mem_univ, true_and, aboveF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rfl
  have hmem : ∀ k w, w ∈ aboveF (L := H.E) H.K (P.pb k) ↔ P.Div k w := fun k w => by
    simp only [aboveF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rfl
  have hres : ∀ (k : Fin 2) (ζ : (𝓞 H.E)ˣ), (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 H.E) : H.E) ^ m = 1) →
      ∏ w ∈ aboveF (L := H.E) H.K (P.pb k), θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) = 1 :=
    fun k ζ hζ => UpperTheory.prod_residue_char_norm_one_unit_eq_one H.K H.E (H.g k) (H.g_prime k) (P.pb k) _ (fun w => hmem k w)
      (fun w hw => ⟨(hsp k w (P.overP ((hmem k w).1 hw))).1, (hsp k w (P.overP ((hmem k w).1 hw))).2.1⟩)
      ((W.om k ^ (2 * (j + 1)))⁻¹) θ (fun w hw a ha => hθ2 w k ((hmem k w).1 hw) a ha) ζ (H.der.norm_mu _ hζ)
  have hdisj : (↑(Finset.univ : Finset (Fin 2)) : Set (Fin 2)).PairwiseDisjoint
      (fun k => aboveF (L := H.E) H.K (P.pb k)) := by
    intro k _ k' _ hkk'
    refine Finset.disjoint_left.2 fun w hw hw' => hkk' ?_
    exact eq_of_overP (P.overP ((hmem k w).1 hw)) (P.overP ((hmem k' w).1 hw'))
  obtain ⟨χ, hu, ht, hi, htame, hunr, hloc, -⟩ := GlobalTheory.T.exists_heckeChar_trivOn_realSubfield_infinityType H.F H.E c (R.Psi) (embPsi H) hcm z S θ
    (by
      intro w hw w' hcj hw'
      obtain ⟨k, hk⟩ := (hS w).1 hw
      obtain ⟨k', hk'⟩ := (hS w').1 hw'
      rw [hce] at hcj
      obtain ⟨ho, hiff⟩ := (hsp k w (P.overP hk)).2.2.2 (P.pb k) (P.pb_over k) w' hcj
      obtain rfl := eq_of_overP ho (P.overP hk')
      exact hiff.1 hk hk')
    (by
      intro ζ hζ
      have hinf : ∏ i, embPsi H i ((ζ : 𝓞 H.E) : H.E) ^ (-z i) = 1 := hmu.neg _ hζ
      have hfin : ∏ w ∈ S, θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) = 1 := by
        rw [Finset.prod_biUnion hdisj]
        exact Finset.prod_eq_one fun k _ => hres k ζ hζ
      rw [hinf, one_mul, ← Units.coe_prod]
      exact (congrArg Units.val hfin).trans Units.val_one)
  refine ⟨χ, hu, ht, ⟨_, fun τ => ?_, hi⟩, fun v hv => hunr v ?_ ?_, htame, fun k w hw a ha x hx => ?_⟩
  · show _ = 2 * -e τ
    rw [hz τ]
    push_cast
    ring
  · intro h
    obtain ⟨k, hk⟩ := (hS v).1 h
    exact hv k (P.overP hk)
  · intro w hw hcj
    obtain ⟨k, hk⟩ := (hS w).1 hw
    rw [hce] at hcj
    exact hv k ((hsp k w (P.overP hk)).2.2.2 (P.pb k) (P.pb_over k) v hcj).1
  · obtain ⟨b, hb, hb'⟩ := hθ2 w k hw a ha
    rw [← hb']
    exact hloc w ((hS w).2 ⟨k, hw⟩) x (a : 𝓞 H.E) b (by rw [hx]; simp) hb

end GlobalTheory.Mem.MuZero
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryMuZeroCharactersOfSplitTypePrimesAlStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.mu0Exists_of_splits_of_integral_of_MUQ : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (P : PiBar H) (W : Omg H) (e : R.Psi → ℚ) (j : ℕ), (∀ k, SplitsC H.E (H.g k)) → (∀ τ, ∃ z : ℤ, e τ = z) → UpperTheory.MUQ (embPsi H) e → Mu0Exists P W e j := by
  first | exact @GlobalTheory.Mem.MuZero.exists_unitary_mu_zero_characters_of_split_type_primes | exact GlobalTheory.Mem.MuZero.exists_unitary_mu_zero_characters_of_split_type_primes | (intros; apply GlobalTheory.Mem.MuZero.exists_unitary_mu_zero_characters_of_split_type_primes <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedCmTypeHeckeCharOnHost

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.ChiPsiExist


open Classical in
theorem exists_chiPsi : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ χ : HChar H.E, IsChiPsi H χ := by
  intro R H
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  obtain ⟨χ, hu, ht, hi, -, hunr, -⟩ :=
    GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn H.F H.E c (R.Psi) (embPsi H) hcm (fun _ => -1) ∅ (fun _ => 1)
      (fun w hw => absurd hw (Finset.notMem_empty w))
      (by
        intro ζ hζ
        rw [Finset.prod_empty, mul_one]
        exact UpperTheory.Mu.prod_emb_zpow H (Equiv.refl _) hζ _)
  exact ⟨χ, hu, fun v => hunr v (Finset.notMem_empty v) (fun w hw => absurd hw (Finset.notMem_empty w)), ht, hi⟩

end GlobalTheory.Mem.ChiPsiExist
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedCmTypeHeckeCharOnHostStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.exists_unramified_cmType_heckeChar_on_host : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ χ : HChar H.E, IsChiPsi H χ := by
  first | exact @GlobalTheory.Mem.ChiPsiExist.exists_chiPsi | exact GlobalTheory.Mem.ChiPsiExist.exists_chiPsi | (intros; apply GlobalTheory.Mem.ChiPsiExist.exists_chiPsi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostDeltaCharacterInertialOrderFifteenExistsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.host_delta_character_inertial_order_fifteen_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime → p % 15 = 1 → SplitsC H.E p → DeltaExists (H := H) p := by
  first | exact @GlobalTheory.Mem.DeltaZero.delta_exists | exact GlobalTheory.Mem.DeltaZero.delta_exists | (intros; apply GlobalTheory.Mem.DeltaZero.delta_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExistsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.host_etaTilde_character_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), EtaTExists H := by
  first | exact @GlobalTheory.Mem.EtaT.etaT_exists | exact GlobalTheory.Mem.EtaT.etaT_exists | (intros; apply GlobalTheory.Mem.EtaT.etaT_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyHostHeckeCharacterFrame

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

namespace GlobalTheory

theorem nonempty_hFrame : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (e : Fin R.m → R.Psi → ℚ), (∀ k, SplitsC H.E (H.g k)) → SplitsC H.E H.pde → SplitsC H.E H.pde' → (∀ j τ, ∃ z : ℤ, e j τ = z) → (∀ j, UpperTheory.MUQ (embPsi H) (e j)) → Nonempty (HFrame H e) := by
  intro R H e hg hp hp' he hs
  obtain ⟨⟨P⟩, ⟨W⟩⟩ := GlobalTheory.nonempty_piBar_and_omg R H
  have hmu : ∀ j : Fin R.m, ∃ χ : HChar H.E, IsMu0 P W (e j) j.1 χ := fun j =>
    GlobalTheory.T.mu0Exists_of_splits_of_integral_of_MUQ R H P W (e j) j.1 hg (he j) (hs j)
  choose mu hmu using hmu
  obtain ⟨eta, heta⟩ := GlobalTheory.T.host_etaTilde_character_exists R H
  obtain ⟨chi, hchi⟩ := GlobalTheory.T.exists_unramified_cmType_heckeChar_on_host R H
  obtain ⟨d, hd⟩ := GlobalTheory.T.host_delta_character_inertial_order_fifteen_exists R H H.pde H.pde_prime H.pde_mod.1 hp
  obtain ⟨d', hd'⟩ := GlobalTheory.T.host_delta_character_inertial_order_fifteen_exists R H H.pde' H.pde'_prime H.pde_mod.2 hp'
  exact ⟨⟨P, W, mu, eta, chi, d, d', hmu, heta, hchi, hd, hd'⟩⟩

end GlobalTheory
end
end
