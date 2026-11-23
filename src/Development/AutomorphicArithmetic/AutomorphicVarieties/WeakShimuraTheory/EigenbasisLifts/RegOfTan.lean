module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.RingKrullDimQuotientSpanSingletonAddOne
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DerLam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DimLeOfInt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Lean.Meta.ExprDefEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.TanEmb
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.RegOfDim

section

@[expose] public section

open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.regOfDim :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (J : Ideal R), J ≠ ⊤ →
      ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ J) → J = ⊥ := by
  intro R _ _ _ J hJ hdim
  have hR := ringKrullDim_le_spanFinrank_maximalIdeal R
  have hq := ringKrullDim_quotient_le J
  have heq : ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    le_antisymm (hdim.trans hq) hR
  have hJeq : ringKrullDim (R ⧸ J) = ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
    le_antisymm (hq.trans hR) hdim
  haveI : IsRegularLocalRing R := ⟨heq⟩
  haveI := PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.isDomain R
  by_contra hne
  obtain ⟨r, hrJ, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hnz : r ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hr0
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnz
  have hsub : Ideal.span {r} ≤ J := (Ideal.span_singleton_le_iff_mem J).2 hrJ
  have h2 : ringKrullDim (R ⧸ J) ≤ ringKrullDim (R ⧸ Ideal.span {r}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hsub) (Ideal.Quotient.factor_surjective hsub)
  have h3 : ringKrullDim (R ⧸ J) + 1 ≤ ringKrullDim (R ⧸ J) := by
    calc ringKrullDim (R ⧸ J) + 1 ≤ ringKrullDim (R ⧸ Ideal.span {r}) + 1 := by gcongr
      _ ≤ ringKrullDim R := h1
      _ = ringKrullDim (R ⧸ J) := by rw [hJeq, heq]
  rw [hJeq] at h3
  norm_cast at h3
  omega
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DimLow

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.dimLow :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (N : ℕ) (B : Type) [CommRing B] [Algebra c.O B] [IsCO c.O B] (f : MvPowerSeries (Fin N) c.O →ₐ[c.O] B) (J : Ideal B), ((Ideal.Quotient.mk J).comp (f : MvPowerSeries (Fin N) c.O →+* B)).Finite → (∀ a, a ≠ 0 → ∀ b, f a * b ∈ J → b ∈ J) →
        ∀ (x : B →ₐ[c.O] PadicAlgCl l) (p : Ideal B) [p.IsPrime], p = RingHom.ker x → J ≤ p → (N : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime p ⧸ J.map (algebraMap B (Localization.AtPrime p))) := by
  intro l _ c N B _ _ _ f J hfin hreg x p _ hpx hJp
  obtain ⟨P, hP, hPp⟩ := Ideal.exists_minimalPrimes_le hJp
  haveI hPprime : P.IsPrime := hP.1.1
  have hJP : J ≤ P := hP.1.2
  haveI : IsCO c.O (B ⧸ P) :=
    co_quot c.O B (B ⧸ P) (Ideal.Quotient.mkₐ c.O P) Ideal.Quotient.mk_surjective
  set g : MvPowerSeries (Fin N) c.O →ₐ[c.O] B ⧸ P := (Ideal.Quotient.mkₐ c.O P).comp f with hg
  have hinj : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra hne
    have hmem : f a ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact ha
    obtain ⟨y, hyJ, hy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hP hmem
    exact hyJ (hreg a hne y hy)
  have hfinP : (g : MvPowerSeries (Fin N) c.O →+* B ⧸ P).Finite := by
    have h2 := (RingHom.Finite.of_surjective _ (Ideal.Quotient.factor_surjective hJP)).comp hfin
    convert h2 using 1
    exact RingHom.ext fun a => rfl
  have hxP : ∀ a ∈ P, x a = 0 := fun a ha => by
    have h3 : a ∈ RingHom.ker x := hpx ▸ hPp ha
    exact h3
  set xb : B ⧸ P →ₐ[c.O] PadicAlgCl l := Ideal.Quotient.liftₐ P x hxP with hxb
  have hxbmk : ∀ b, xb (Ideal.Quotient.mk P b) = x b := fun b => rfl
  have hht := htLow c N (B ⧸ P) g hinj hfinP xb
  set q : Ideal (B ⧸ P) := RingHom.ker xb with hq
  haveI : q.IsPrime := RingHom.ker_isPrime _
  have hpq : p = Ideal.comap (Ideal.Quotient.mk P) q := by
    ext b
    rw [hpx, Ideal.mem_comap, hq, RingHom.mem_ker, RingHom.mem_ker, hxbmk]
  let φ := Localization.localRingHom p q (Ideal.Quotient.mk P) hpq
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective (s : B ⧸ P)
    have hs'p : s' ∈ p.primeCompl := by
      intro h
      apply s.2
      rw [hpq] at h
      rw [← hs']
      exact h
    refine ⟨IsLocalization.mk' (Localization.AtPrime p) r' ⟨s', hs'p⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hs'
  have hker : ∀ a ∈ J.map (algebraMap B (Localization.AtPrime p)), φ a = 0 := by
    intro a ha
    have hle : J.map (algebraMap B (Localization.AtPrime p)) ≤ RingHom.ker φ := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [Localization.localRingHom_to_map]
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hJP hb), map_zero]
    exact hle ha
  have hψ := Ideal.Quotient.lift_surjective_of_surjective _ hker hφ
  have hdim := ringKrullDim_le_of_surjective _ hψ
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)] at hdim
  calc (N : WithBot ℕ∞) ≤ (q.height : WithBot ℕ∞) := by exact_mod_cast hht
    _ ≤ _ := hdim
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RegOfTan

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem rank_le_res {O A B K : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing B] [Algebra O B]
    [Field K] [Algebra O K] (f : A →ₐ[O] B) (x : B →ₐ[O] K)
    (h : ∀ x' : B →ₐ[O] DualNumber K, (∀ b, (x' b).fst = x b) → (∀ a, (x' (f a)).snd = 0) → ∀ b, (x' b).snd = 0) :
    Module.rank K (PtDer x K) ≤ Module.rank K (PtDer (x.comp f) K) := by
  classical
  let F : PtDer x K →ₗ[K] PtDer (x.comp f) K :=
    { toFun := fun D => ⟨(D : B →ₗ[O] K).comp f.toLinearMap, by
        intro a a'
        have hD := D.2 (f a) (f a')
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, AlgHom.comp_apply]
        simpa using hD⟩
      map_add' := fun D E => by
        ext a
        simp
      map_smul' := fun c D => by
        ext a
        simp }
  refine LinearMap.rank_le_of_injective F ?_
  have key : ∀ G : PtDer x K, F G = 0 → G = 0 := by
    intro G hG
    have hmul : ∀ b b' : B, (G : B →ₗ[O] K) (b * b') = x b • (G : B →ₗ[O] K) b' + x b' • (G : B →ₗ[O] K) b :=
      G.2
    have h1 : (G : B →ₗ[O] K) 1 = 0 := by
      have := hmul 1 1
      simp only [map_one, one_smul, mul_one] at this
      have h2 : (G : B →ₗ[O] K) 1 + (G : B →ₗ[O] K) 1 = (G : B →ₗ[O] K) 1 + 0 := by
        rw [add_zero]; exact this.symm
      exact add_left_cancel h2
    have hc : ∀ r : O, (G : B →ₗ[O] K) (algebraMap O B r) = 0 := by
      intro r
      rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]
    have halg : ∀ r : O, algebraMap O (DualNumber K) r = TrivSqZeroExt.inl (algebraMap O K r) := fun r => rfl
    let y : B →ₐ[O] DualNumber K :=
      { toFun := fun b => TrivSqZeroExt.inl (x b) + TrivSqZeroExt.inr ((G : B →ₗ[O] K) b)
        map_one' := by
          ext <;> simp [h1]
        map_mul' := fun b b' => by
          ext
          · simp
          · simp [hmul b b', smul_eq_mul, mul_comm, add_comm]
        map_zero' := by
          ext <;> simp
        map_add' := fun b b' => by
          ext <;> simp [add_comm, add_left_comm, add_assoc]
        commutes' := fun r => by
          rw [halg]
          ext
          · simp
          · simp [hc] }
    have hz := h y (fun b => by simp [y]) (fun a => by
      have := congrArg (fun H : PtDer (x.comp f) K => (H : A →ₗ[O] K) a) hG
      simpa [F, y] using this)
    ext b
    simpa [y] using hz b
  intro D E hDE
  have := key (D - E) (by rw [map_sub, hDE, sub_self])
  exact sub_eq_zero.1 this

theorem UpperTheory.V.Ws.Eb.regOfTan :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (N : ℕ) (B : Type) [CommRing B] [Algebra c.O B] [IsCO c.O B] (f : MvPowerSeries (Fin N) c.O →ₐ[c.O] B) (J : Ideal B), ((Ideal.Quotient.mk J).comp (f : MvPowerSeries (Fin N) c.O →+* B)).Finite → (∀ a, a ≠ 0 → ∀ b, f a * b ∈ J → b ∈ J) →
        ∀ x : B →ₐ[c.O] PadicAlgCl l, J ≤ RingHom.ker x → (∀ x' : B →ₐ[c.O] DualNumber (PadicAlgCl l), (∀ b, (x' b).fst = x b) → (∀ a, (x' (f a)).snd = 0) → ∀ b, (x' b).snd = 0) → ∀ q : Ideal B, q.IsPrime → q ≤ RingHom.ker x → J ≤ q := by
  intro l _ c N B _ _ _ f J hfin hreg x hJ htan q hq hqx
  haveI : Algebra.IsAlgebraic ℤ_[l] (PadicAlgCl l) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ_[l]) (K := ℚ_[l])).2 inferInstance
  haveI : Algebra.IsAlgebraic c.O (PadicAlgCl l) :=
    Algebra.IsAlgebraic.extendScalars (R := ℤ_[l]) (UpperTheory.V.Base.dvrFacts l c.O).1
  haveI : FaithfulSMul c.O (PadicAlgCl l) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI hp : (RingHom.ker x).IsPrime := RingHom.ker_isPrime _
  have h1 := tanEmb c.O B (PadicAlgCl l) x (RingHom.ker x) rfl N
    ((rank_le_res f x htan).trans (derLam c N (x.comp f)))
  have h2 := dimLow c N B f J hfin hreg x (RingHom.ker x) rfl hJ
  have hne : J.map (algebraMap B (Localization.AtPrime (RingHom.ker x))) ≠ ⊤ := by
    intro ht
    have := Ideal.map_mono (f := algebraMap B (Localization.AtPrime (RingHom.ker x))) hJ
    rw [ht, Localization.AtPrime.map_eq_maximalIdeal] at this
    exact (maximalIdeal.isMaximal _).ne_top (top_le_iff.1 this)
  have h3 := UpperTheory.V.AlgebraTools.regOfDim _ _ hne (le_trans (by exact_mod_cast h1) h2)
  intro a ha
  have h4 : algebraMap B (Localization.AtPrime (RingHom.ker x)) a = 0 := by
    have := Ideal.mem_map_of_mem (algebraMap B (Localization.AtPrime (RingHom.ker x))) ha
    rw [h3] at this
    exact this
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff (RingHom.ker x).primeCompl _ a).1 h4
  have h5 : (s : B) * a ∈ q := by rw [hs]; exact q.zero_mem
  exact (hq.mem_or_mem h5).resolve_left fun h => s.2 (hqx h)
end
end
