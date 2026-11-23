module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.DescGS
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.Hypotheses.GalCohDefs
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.ExistsZmodPrimeRepresentationOfTorsion
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.CocycleCardEulerFormula
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.LocalH1FiniteModL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.PerpTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.Strict
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.SumDeg
import Mathlib.GroupTheory.Nilpotent
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.ZMod.LocalRing
public import Mathlib.Algebra.Azumaya.Basic

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.ExistsComplexConjugationAtRealPlace

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.exists_complexConjugation_at_realPlace :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : InfinitePlace F), w.IsReal → ∃ c : G F Ω, IsCCAt w c := by
  intro F Ω _ _ _ _ _ w hw
  let φ : F →+* ℂ := w.embedding
  have hreal : ∀ x : F, starRingEnd ℂ (φ x) = φ x := by
    intro x
    have h := congrArg (fun ψ : F →+* ℂ => ψ x)
      (NumberField.ComplexEmbedding.isReal_iff.mp (NumberField.InfinitePlace.isReal_iff.mp hw))
    simpa using h
  letI : Algebra F ℂ := φ.toAlgebra
  have halg : ∀ x : F, algebraMap F ℂ x = φ x := fun x => rfl
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Normal F Ω := IsAlgClosure.normal F Ω
  let j : Ω →ₐ[F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let E : IntermediateField F ℂ := j.fieldRange
  let e : Ω ≃ₐ[F] E := AlgEquiv.ofInjectiveField j
  haveI : Normal F E := Normal.of_algEquiv e
  let cj : ℂ →ₐ[F] ℂ :=
    { (starRingEnd ℂ : ℂ →+* ℂ) with
      commutes' := fun x => by
        show starRingEnd ℂ (algebraMap F ℂ x) = algebraMap F ℂ x
        rw [halg]; exact hreal x }
  have hrange : (cj.comp E.val).fieldRange = E := AlgHom.fieldRange_of_normal _
  have hmem : ∀ y : Ω, starRingEnd ℂ (j y) ∈ E := by
    intro y
    have h1 : (cj.comp E.val) (e y) ∈ (cj.comp E.val).fieldRange := AlgHom.mem_fieldRange.mpr ⟨e y, rfl⟩
    rw [hrange] at h1
    have h2 : ((e y : E) : ℂ) = j y := rfl
    simpa [cj, h2] using h1
  let f' : Ω →ₐ[F] E := (cj.comp j).codRestrict E.toSubalgebra (fun y => hmem y)
  let σ0 : Ω →ₐ[F] Ω := e.symm.toAlgHom.comp f'
  have hbij : Function.Bijective σ0 := Algebra.IsAlgebraic.algHom_bijective σ0
  let c : Ω ≃ₐ[F] Ω := AlgEquiv.ofBijective σ0 hbij
  refine ⟨c, (j : Ω →+* ℂ), ?_, ?_⟩
  · intro x
    have h3 : ((e (e.symm (f' x)) : E) : ℂ) = j (e.symm (f' x)) := rfl
    rw [AlgEquiv.apply_symm_apply] at h3
    show j (e.symm (f' x)) = starRingEnd ℂ (j x)
    rw [← h3]
    rfl
  · have h4 : (j : Ω →+* ℂ).comp (algebraMap F Ω) = φ := by
      ext x
      simp [halg]
    rw [h4]
    exact NumberField.InfinitePlace.mk_embedding w
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.ShaCard

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical
open scoped Pointwise

theorem UpperTheory.V.Ws.tate_shafarevich_card_mod_l :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (Av : S → ValuationSubring Ω) (K : Subgroup (G F Ω)) (r : ℕ), (∀ v, IsPlaceOver (Av v) v.1) → K.Normal → ¬ l ∣ K.index → (∀ g ∈ K, ∀ m, ρ (toGS Ω _ g) m = m) → XRk l 1 K r → CardLe (Sha1 ρ (locFam S Av) (continuous_locFam S Av)) (Nat.card M ^ (r + 1)) := by
  intro F Ω _ _ _ _ _ l hl M _ _ _ _ _ S ρ Av K r hA hN hK hρ hX
  have hM : ∀ m : M, l • m = 0 := by
    intro m
    rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ 1)) l m]
    have h0 : ((l : ℕ) : ZMod (l ^ 1)) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 (by rw [pow_one])
    rw [h0, zero_smul]
  have hB := UpperTheory.V.Ws.card_cocycles_vanishing_on_inertia_le_pow F Ω l (ZMod (l ^ 1)) M hM (ρ.comp (toGS Ω _)) K r hK hρ hX
  obtain ⟨p1, p2, -, -⟩ := UpperTheory.V.Kum.placeDict F Ω
  have hmem : ∀ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) ∈ Sha1 ρ (locFam S Av) (continuous_locFam S Av) →
      (fun g => z.1 (toGS Ω _ g)) ∈ cocOff (ρ.comp (toGS Ω _)) (ineOff F Ω 1 ∩ K) := by
    intro z hz
    have hz1 : z.1 1 = 0 := by
      have := z.2.2 1 1
      rw [one_mul, map_one, Module.End.one_apply] at this
      exact left_eq_add.1 this
    have hc : ∀ a b : G F Ω, z.1 (toGS Ω _ (a * b)) = z.1 (toGS Ω _ a) + ρ (toGS Ω _ a) (z.1 (toGS Ω _ b)) :=
      fun a b => by rw [map_mul, z.2.2]
    refine ⟨(IsLocallyConstant.iff_continuous _).2 (z.2.1.comp (continuous_toGS Ω _)), hc, ?_⟩
    rintro u ⟨⟨A, -, hu⟩, huK⟩
    show z.1 (toGS Ω _ u) = 0
    by_cases hT : A = ⊤
    · subst hT
      rw [p1, Subgroup.mem_bot] at hu
      rw [hu, map_one, hz1]
    obtain ⟨v, hv⟩ := p2 A hT
    by_cases hvS : v ∈ S
    · obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (hA ⟨v, hvS⟩) hv
      have hd : g⁻¹ * u * g ∈ Dec (F := F) (Av ⟨v, hvS⟩) := by
        have h : u • g • Av ⟨v, hvS⟩ = g • Av ⟨v, hvS⟩ := Ine_le_Dec _ hu
        show (g⁻¹ * u * g) • Av ⟨v, hvS⟩ = Av ⟨v, hvS⟩
        rw [mul_smul, mul_smul, h, inv_smul_smul]
      have hk : g⁻¹ * u * g ∈ K := by simpa using hN.conj_mem u huK g⁻¹
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 ((Submodule.mem_iInf _).1 hz ⟨v, hvS⟩))
      have h0 : z.1 (toGS Ω _ (g⁻¹ * u * g)) = 0 := (hm ⟨_, hd⟩).trans (sub_eq_zero.2 (hρ _ hk m))
      have h1 := hc g (g⁻¹ * u * g)
      rw [h0, map_zero, add_zero, mul_assoc, mul_inv_cancel_left, hc, hρ u huK] at h1
      exact add_eq_right.1 h1
    · have hn : u ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) := by
        apply Subgroup.le_topologicalClosure
        apply Subgroup.subset_normalClosure
        simp only [Set.mem_iUnion]
        exact ⟨v, hvS, A, hv, hu⟩
      have : toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) u = 1 := (QuotientGroup.eq_one_iff _).2 hn
      rw [this, hz1]
  choose s hs using Submodule.Quotient.mk_surjective ((B1 ρ).comap (Z1 ρ).subtype)
  refine hB.of_injective (fun x => ⟨_, hmem (s x.1) ((hs x.1).symm ▸ x.2)⟩) fun x y h => ?_
  apply Subtype.ext
  rw [← hs x.1, ← hs y.1]
  congr 1
  apply Subtype.ext
  funext a
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  exact congrFun (congrArg Subtype.val h) g
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.GwCount

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.greenberg_wiles_count_mod_l :
    CohomologyHyp → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (K : Subgroup (G F Ω)) (r : ℕ) (c : InfinitePlace F → G F Ω), l ≠ 2 → ContainsAbove S l → ContAction ρ → K.Normal → ¬ l ∣ K.index → (∀ g ∈ K, ∀ m, ρ (toGS Ω _ g) m = m) → K ≤ (cycMod F Ω l 1).ker → XRk l 1 K r → (∀ w, w.IsReal → IsCCAt w (c w)) → Finite (Z1 ρ) ∧ Nat.card (Z1 ρ) * archH0Card S ρ c ≤ Nat.card M ^ (r + 2 + S.card + Module.finrank ℚ F) := by
  intro P F Ω _ _ _ _ _ l hp M _ _ _ _ _ S ρ K r c hl hS hρ hN hK hρK hKc hX hc
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := F) (Ω := Ω) (l := l) (r := 1) (S := S) hS
  choose Av hA using fun v : S => (exists_isPlaceOver Ω v.1 : ∃ A : ValuationSubring Ω, IsPlaceOver A v.1)
  have e := P.gw F Ω l 1 M S ρ one_pos hl hS hρ μ hμ Av hA c hc (fun _ => ⊤)
  haveI : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact hp.out⟩
  haveI hfd : Finite (TDual (ZMod (l ^ 1)) M) := DFunLike.finite _
  have hf1 : Finite (H1 ρ) := (P.gf F Ω l 1 M S ρ one_pos hS hρ).2.1
  obtain ⟨hZ, eZ⟩ := cocycle_card_euler_formula _ _ M ρ hρ hf1
  refine ⟨hZ, ?_⟩
  have hM : 0 < Nat.card M := Nat.card_pos
  have hD : Nat.card (TDual (ZMod (l ^ 1)) M) = Nat.card M := by
    show Nat.card (Module.Dual (ZMod (l ^ 1)) M) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod (l ^ 1)) (V := Module.Dual (ZMod (l ^ 1)) M),
      Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank]
  have hsha := (tate_shafarevich_card_mod_l F Ω l (TDual (ZMod (l ^ 1)) M) S (twDual μ ρ) Av K r hA hN hK (fun g hg y => by
    refine DFunLike.ext _ _ fun m => ?_
    have h1 : μ (toGS Ω _ g) = 1 := by
      have := hKc hg
      rw [← hμ] at this
      exact this
    rw [twDual_apply, h1, ← map_inv, hρK _ (K.inv_mem hg), Units.val_one, one_mul]) hX).2
  rw [hD, ← dualSelmer_orthogonalComplement_conditions P.loc.lt F Ω l M S ρ hρ μ Av hμ hA] at hsha
  have hsel : Sel ρ (locFam S Av) (continuous_locFam S Av) (fun _ => ⊤) = ⊤ :=
    eq_top_iff.2 fun x _ => (mem_Sel _ _ _ _ _).2 fun _ => trivial
  have htop : ∀ (N : Type) [AddCommGroup N] [Module (ZMod (l ^ 1)) N],
      Nat.card (⊤ : Submodule (ZMod (l ^ 1)) N) = Nat.card N :=
    fun N _ _ => Nat.card_congr Submodule.topEquiv.toEquiv
  rw [hsel, htop] at e
  simp only [htop] at e
  have hloc : (∏ v : S, Nat.card (H1 (ρ.comp (locFam S Av v)))) ≤
      (∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v)))) * Nat.card M ^ (S.card + Module.finrank ℚ F) := by
    refine (Finset.prod_le_prod' fun v _ => (local_h1_finite_mod_l P.loc.lf P.loc.lt P.loc.le F Ω l M (Av v) v.1
      (ρ.comp (locFam S Av v)) (hA v) (hρ.comp' (continuous_locFam S Av v))).2).trans ?_
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hM ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_coe,
      Finset.sum_coe_sort S (fun v => if ((l : ℕ) : 𝓞 F) ∈ v.asIdeal then locDeg v else 0)]
    exact Nat.add_le_add_left (sum_local_degree_above_l_le_finrank F l S) _
  have p1 : 0 < Nat.card (H0 ρ) := Nat.card_pos
  have p2 : 0 < Nat.card (H0 (twDual μ ρ)) := Nat.card_pos
  have p3 : 0 < ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) :=
    Finset.prod_pos fun v _ => Nat.card_pos
  have key := e.le.trans (Nat.mul_le_mul (Nat.mul_le_mul_right _ hsha) hloc)
  generalize (∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v)))) = q at p3 key
  generalize Nat.card (H0 (twDual μ ρ)) = b at p2 key
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos p1 p3)
  calc _ = (Nat.card (Z1 ρ) * Nat.card (H0 ρ)) * 1 * q * archH0Card S ρ c := by ring
    _ ≤ (Nat.card (Z1 ρ) * Nat.card (H0 ρ)) * b * q * archH0Card S ρ c := by gcongr; exact p2
    _ = Nat.card M * (Nat.card (H1 ρ) * b * q * archH0Card S ρ c) := by rw [eZ]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ key
    _ = _ := by ring
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.CardGlobalCocyclesLeOfIwasawaRank

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem plDvd_fin (F : Type) [Field F] [NumberField F] (N : ℕ) (hN : N ≠ 0) : (plDvd F N).Finite := by
  have h : Ideal.span {((N : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hN
  refine (Ideal.finite_factors h).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

theorem UpperTheory.V.Ws.card_globalCocycles_le_of_iwasawaRank :
    CohomologyHyp → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M], (∀ m : M, l • m = 0) → ∀ (ρ : Representation R (G F Ω) M) (K : Subgroup (G F Ω)) (N r g : ℕ), l ≠ 2 → N ≠ 0 → l ∣ N → (plDvd F N).ncard ≤ g → (∀ σ ∈ ineOff F Ω N, ∀ m, ρ σ m = m) → K.Normal → IsOpen (K : Set (G F Ω)) → ¬ l ∣ K.index → (∀ σ ∈ K, ∀ m, ρ σ m = m) → K ≤ (cycMod F Ω l 1).ker → XRk l 1 K r → CardLe (cocOff ρ (ineOff F Ω N)) (Nat.card M ^ (r + 2 + g + Module.finrank ℚ F)) ∧ (IsTotallyReal F → (∀ σ : G F Ω, IsCC σ → ∀ m, ρ σ m = m) → CardLe (cocOff ρ (ineOff F Ω N)) (Nat.card M ^ (r + 2 + g))) := by
  intro P F Ω _ _ _ _ _ l _ R M _ _ _ _ hlM ρ K N r g hl hN hlN hg hI hKn hKo hKi hKρ hKc hX
  obtain ⟨inst, ρ', hρ'⟩ := exists_zmod_prime_representation_of_torsion l (G F Ω) R M hlM ρ
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  have hfin := plDvd_fin F N hN
  have hcard : hfin.toFinset.card ≤ g := by rwa [← Set.ncard_eq_toFinset_card _ hfin]
  have hmem : ∀ v, v ∈ plDvd F N → v ∈ hfin.toFinset := fun v hv => hfin.mem_toFinset.2 hv
  generalize hfin.toFinset = S at hcard hmem
  have hS : ContainsAbove S l := fun v hv => hmem v (by
    obtain ⟨k, rfl⟩ := hlN
    show ((l * k : ℕ) : 𝓞 F) ∈ v.asIdeal
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hv)
  obtain ⟨ρS, h1, h2, h3⟩ := exists_descent_to_galoisGroupUnramifiedOutside F Ω (ZMod (l ^ 1)) M S ρ' K N hmem
    (fun σ h m => by rw [hρ', hI σ h]) hKo (fun σ h m => by rw [hρ', hKρ σ h])
  have hc : ∀ w : InfinitePlace F, ∃ c : G F Ω, w.IsReal → IsCCAt w c := fun w => by
    by_cases hw : w.IsReal
    · obtain ⟨c, hc⟩ := exists_complexConjugation_at_realPlace F Ω w hw
      exact ⟨c, fun _ => hc⟩
    · exact ⟨1, fun h => absurd h hw⟩
  choose c hc using hc
  obtain ⟨hZ, hb⟩ := greenberg_wiles_count_mod_l P F Ω l M S ρS K r c hl hS h2 hKn hKi
    (fun σ h m => by rw [h1, hρ', hKρ σ h]) hKc hX hc
  have hM : 0 < Nat.card M := Nat.card_pos
  have hex : ∀ z : cocOff ρ (ineOff F Ω N), ∃ y : Z1 ρS, ∀ g, y.1 (toGS Ω _ g) = z.1 g := fun z => by
    obtain ⟨y, hy, e⟩ := h3 z.1 ⟨z.2.1, fun a b => by rw [hρ']; exact z.2.2.1 a b, z.2.2.2⟩
    exact ⟨⟨y, hy⟩, e⟩
  choose f hf using hex
  have hinj : Function.Injective f := fun a b h => Subtype.ext (funext fun x => by rw [← hf, ← hf, h])
  have hb' : Nat.card (Z1 ρS) * archH0Card S ρS c ≤ Nat.card M ^ (r + 2 + g + Module.finrank ℚ F) :=
    hb.trans (Nat.pow_le_pow_right hM (by omega))
  refine ⟨CardLe.of_injective ⟨hZ, le_trans (Nat.le_mul_of_pos_right _ ?_) hb'⟩ f hinj, fun hF hcc => ?_⟩
  · unfold archH0Card
    refine Nat.mul_pos (Finset.prod_pos fun w _ => ?_) (pow_pos hM _)
    haveI : Nonempty {m : M // ρS (toGS Ω _ (c w)) m = m} := ⟨⟨0, map_zero _⟩⟩
    exact Nat.card_pos
  · have ha : archH0Card S ρS c = Nat.card M ^ Module.finrank ℚ F := by
      rw [archH0Card, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, mul_one,
        Finset.filter_true_of_mem fun w _ => IsTotallyReal.isReal w]
      have hw : ∀ w, Nat.card {m : M // ρS (toGS Ω _ (c w)) m = m} = Nat.card M := fun w => by
        obtain ⟨j, hj, -⟩ := hc w (IsTotallyReal.isReal w)
        exact Nat.card_congr (Equiv.subtypeUnivEquiv fun m => by rw [h1, hρ', hcc _ ⟨j, hj⟩])
      rw [Finset.prod_congr rfl fun w _ => hw w, Finset.prod_const, Finset.card_univ,
        IsTotallyReal.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
    rw [ha, pow_add _ (r + 2 + g)] at hb'
    exact CardLe.of_injective ⟨hZ, Nat.le_of_mul_le_mul_right hb' (pow_pos hM _)⟩ f hinj
end
end
