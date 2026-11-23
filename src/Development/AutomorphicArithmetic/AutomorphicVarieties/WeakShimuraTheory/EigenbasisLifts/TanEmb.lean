module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Derivation.ToSquareZero
public import Mathlib.RingTheory.Ideal.Cotangent
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.Etale.Field
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import ReciprocityTheory.GaloisValuations.GlobalA

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.CotDer

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.cotDer :
    ∀ (O R : Type) [CommRing O] [IsDomain O] [CharZero O] [CommRing R] [IsLocalRing R] [Algebra O R], Function.Injective (algebraMap O (ResidueField R)) → Algebra.IsAlgebraic O (ResidueField R) →
        ∃ d : Derivation O R (CotangentSpace R), ∀ a : maximalIdeal R, d a = (maximalIdeal R).toCotangent a := by
  intro O R _ _ _ _ _ _ hinj halg
  haveI : FaithfulSMul O (ResidueField R) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  letI : Algebra (FractionRing O) (ResidueField R) := FractionRing.liftAlgebra O _
  haveI := FractionRing.isScalarTower_liftAlgebra O (ResidueField R)
  haveI := halg
  haveI : Algebra.IsAlgebraic (FractionRing O) (ResidueField R) :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective O (FractionRing O))
  haveI : Algebra.FormallyEtale (FractionRing O) (ResidueField R) := Algebra.FormallyEtale.of_isSeparable _ _
  haveI : Algebra.FormallyEtale O (FractionRing O) := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors O)
  haveI : Algebra.FormallyEtale O (ResidueField R) := Algebra.FormallyEtale.comp O (FractionRing O) _
  have hle : maximalIdeal R ^ 2 ≤ maximalIdeal R := Ideal.pow_le_self two_ne_zero
  let g : R ⧸ maximalIdeal R ^ 2 →ₐ[O] ResidueField R := Ideal.Quotient.factorₐ O hle
  have hgmk : ∀ a : R, g (Ideal.Quotient.mk _ a) = residue R a := fun a => rfl
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨a, rfl⟩ := residue_surjective x
    exact ⟨_, hgmk a⟩
  have hker : ∀ x, g x = 0 → x ∈ (maximalIdeal R).cotangentIdeal := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hgmk, residue_eq_zero_iff] at hx
    exact Ideal.mk_mem_cotangentIdeal.mpr hx
  have hnil : IsNilpotent (RingHom.ker (g : R ⧸ maximalIdeal R ^ 2 →+* ResidueField R)) := by
    refine ⟨2, le_bot_iff.mp ?_⟩
    refine (Ideal.pow_right_mono (fun x hx => hker x hx) 2).trans ?_
    rw [Ideal.cotangentIdeal_square]
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id O (ResidueField R)) g hg hnil
  have hs : ∀ x, g (s x) = x := fun x => Algebra.FormallySmooth.liftOfSurjective_apply _ g hg hnil x
  let φ := s.comp (IsScalarTower.toAlgHom O R (ResidueField R))
  have e : (Ideal.Quotient.mkₐ O (maximalIdeal R).cotangentIdeal).comp φ
      = IsScalarTower.toAlgHom O R ((R ⧸ maximalIdeal R ^ 2) ⧸ (maximalIdeal R).cotangentIdeal) := by
    ext r
    show Ideal.Quotient.mk _ (s (algebraMap R (ResidueField R) r))
      = Ideal.Quotient.mk _ (Ideal.Quotient.mk (maximalIdeal R ^ 2) r)
    rw [Ideal.Quotient.eq]
    apply hker
    rw [map_sub, hs, hgmk, ResidueField.algebraMap_eq, sub_self]
  let D := derivationToSquareZeroOfLift (maximalIdeal R).cotangentIdeal
    (Ideal.cotangentIdeal_square _) φ e
  refine ⟨-(((maximalIdeal R).cotangentEquivIdeal.symm :
      (maximalIdeal R).cotangentIdeal →ₗ[R] (maximalIdeal R).Cotangent).compDer D), fun a => ?_⟩
  have hφ : φ a = 0 := by
    show s (algebraMap R (ResidueField R) a) = 0
    rw [ResidueField.algebraMap_eq, (residue_eq_zero_iff _).mpr a.2, map_zero]
  show -((maximalIdeal R).cotangentEquivIdeal.symm (D a)) = _
  rw [neg_eq_iff_eq_neg, ← map_neg, LinearEquiv.symm_apply_eq]
  ext
  simp only [D, derivationToSquareZeroOfLift_apply, hφ, zero_sub, Ideal.cotangentEquivIdeal_apply, map_neg,
    Submodule.coe_neg, Ideal.toCotangent_to_quotient_square]
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.TanEmb

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem dual_der (O R K : Type) [CommRing O] [IsDomain O] [CharZero O] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra O R] [Field K] [Algebra O K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K]
    (y : R →ₐ[O] K) (hy : ∀ a ∈ maximalIdeal R, y a = 0) :
    ∃ (D : Fin (maximalIdeal R).spanFinrank → R →ₗ[O] K) (r : Fin (maximalIdeal R).spanFinrank → R),
      (∀ i, D i ∈ PtDer y K) ∧ ∀ i j, D i (r j) = if j = i then 1 else 0 := by
  classical
  let yb : ResidueField R →+* K :=
    Ideal.Quotient.lift (maximalIdeal R) y.toRingHom (fun a ha => hy a ha)
  have hyb : ∀ f : R, yb (algebraMap R (ResidueField R) f) = y f := fun f => rfl
  have h1 : ∀ c : O, yb (algebraMap O (ResidueField R) c) = algebraMap O K c := by
    intro c
    rw [← y.commutes c]
    rfl
  let ya : ResidueField R →ₐ[O] K := { yb with commutes' := h1 }
  have hyinj : Function.Injective yb := yb.injective
  have hinj : Function.Injective (algebraMap O (ResidueField R)) := by
    intro a b hab
    apply FaithfulSMul.algebraMap_injective O K
    rw [← h1, ← h1, hab]
  have halg : Algebra.IsAlgebraic O (ResidueField R) :=
    Algebra.IsAlgebraic.of_injective ya hyinj
  obtain ⟨d, hd⟩ := UpperTheory.V.Ws.Eb.cotDer O R hinj halg
  have hn : Module.finrank (ResidueField R) (CotangentSpace R) = (maximalIdeal R).spanFinrank :=
    (IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R).symm
  let b := Module.finBasisOfFinrankEq (ResidueField R) (CotangentSpace R) hn
  have hsurj : ∀ j, ∃ a : maximalIdeal R, (maximalIdeal R).toCotangent a = b j :=
    fun j => (maximalIdeal R).toCotangent_surjective (b j)
  choose a ha using hsurj
  have hsm : ∀ (r : R) (v : CotangentSpace R) i,
      yb (b.coord i (r • v)) = y r * yb (b.coord i v) := by
    intro r v i
    rw [← algebraMap_smul (ResidueField R) r v, map_smul, smul_eq_mul, map_mul, hyb]
  let D : Fin (maximalIdeal R).spanFinrank → R →ₗ[O] K := fun i =>
    { toFun := fun f => yb (b.coord i (d f))
      map_add' := by
        intro f g
        simp only [map_add (f := _)]
      map_smul' := by
        intro c f
        rw [RingHom.id_apply, Algebra.smul_def, Derivation.leibniz, Derivation.map_algebraMap,
          smul_zero, add_zero, hsm, y.commutes, Algebra.smul_def] }
  refine ⟨D, fun j => (a j : R), ?_, ?_⟩
  · intro i
    intro f g
    show yb (b.coord i (d (f * g))) = y f • yb (b.coord i (d g)) + y g • yb (b.coord i (d f))
    rw [Derivation.leibniz, map_add (f := _), map_add (f := _), hsm, hsm, smul_eq_mul, smul_eq_mul]
  · intro i j
    show yb (b.coord i (d (a j : R))) = _
    rw [hd, ha, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

theorem UpperTheory.V.Ws.Eb.tanEmb :
    ∀ (O B K : Type) [CommRing O] [IsDomain O] [CharZero O] [CommRing B] [IsNoetherianRing B] [Algebra O B] [Field K] [Algebra O K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (x : B →ₐ[O] K) (p : Ideal B) [p.IsPrime], p = RingHom.ker x →
        ∀ N : ℕ, Module.rank K (PtDer x K) ≤ N → (maximalIdeal (Localization.AtPrime p)).spanFinrank ≤ N := by
  intro O B K _ _ _ _ _ _ _ _ _ _ x p _ hp N hN
  classical
  let R := Localization.AtPrime p
  have hker : ∀ b : B, b ∈ p ↔ x b = 0 := by
    intro b
    rw [hp]
    exact Iff.rfl
  have hunit : ∀ s : p.primeCompl, IsUnit (x s) := by
    intro s
    apply IsUnit.mk0
    intro h0
    exact s.2 ((hker s).2 h0)
  let y : R →ₐ[O] K := IsLocalization.liftAlgHom (M := p.primeCompl) (f := x) hunit
  have hyx : ∀ b : B, y (algebraMap B R b) = x b := fun b => IsLocalization.lift_eq _ _
  have hy : ∀ a ∈ maximalIdeal R, y a = 0 := by
    intro a ha
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a
    have hb : b ∈ p := by
      rwa [IsLocalization.AtPrime.mk'_mem_maximal_iff R p] at ha
    have h1 := congrArg y (IsLocalization.mk'_spec R b s)
    rw [map_mul, hyx, hyx, (hker b).1 hb] at h1
    exact (mul_eq_zero.mp h1).resolve_right (hunit s).ne_zero
  obtain ⟨D, r, hD, hDr⟩ := dual_der O R K y hy
  have hDl : ∀ i (u w : R), D i (u * w) = y u * D i w + y w * D i u := by
    intro i u w
    have := hD i u w
    rwa [smul_eq_mul, smul_eq_mul] at this
  let L : B →ₗ[O] R := (IsScalarTower.toAlgHom O B R).toLinearMap
  have hL : ∀ b, L b = algebraMap B R b := fun b => rfl
  have hmem : ∀ i, (D i).comp L ∈ PtDer x K := by
    intro i f g
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, hL, hL, hL, map_mul,
      hDl, hyx, hyx, smul_eq_mul, smul_eq_mul]
  let v : Fin (maximalIdeal R).spanFinrank → PtDer x K := fun i => ⟨(D i).comp L, hmem i⟩
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    let E : R → K := fun a => ∑ i, g i * D i a
    have hE : ∀ u w : R, E (u * w) = y u * E w + y w * E u := by
      intro u w
      simp only [E, hDl, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl (fun i _ => ?_) <;> ring
    have hB : ∀ b : B, E (algebraMap B R b) = 0 := by
      intro b
      have := congrArg (fun w : PtDer x K => (w : B →ₗ[O] K) b) hg
      simpa [v, E, hL] using this
    have hR : ∀ a : R, E a = 0 := by
      intro a
      obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a
      have h1 := hB b
      rw [← IsLocalization.mk'_spec R b s, hE, hB, mul_zero, zero_add, hyx] at h1
      exact (mul_eq_zero.mp h1).resolve_left (hunit s).ne_zero
    intro j
    have := hR (r j)
    simpa [E, hDr] using this
  have hc := hli.cardinal_le_rank
  rw [Cardinal.mk_fintype, Fintype.card_fin] at hc
  exact_mod_cast hc.trans hN
end
end
