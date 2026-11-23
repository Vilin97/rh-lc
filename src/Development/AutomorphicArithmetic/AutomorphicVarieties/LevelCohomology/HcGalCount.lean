module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.FiniteCompactlySupportedH1
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.IneFixRoots
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.LocallyConstant.Basic
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
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.DecZhat
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Connected.Separation
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcFrameOb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGalIdx
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.PtTail
import Mathlib.GroupTheory.Nilpotent
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.ZMod.LocalRing
public import Mathlib.Data.FunLike.Fintype
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GlobalEulerCharacteristicRationalsOddPrime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcLocEuler
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcUrAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcUrIndex
import Mathlib.Tactic.Basify

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DerivativeLocallyConstant

section

@[expose] public section

theorem UpperTheory.Reformulated.B.DerivativeLocallyConstant.dz_locConst :
    ∀ {Γ A : Type} [inst : Group Γ] [inst_1 : TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [inst_3 : Group A] (ψ : Γ →* A), IsOpen (↑ψ.ker : Set Γ) → IsLocallyConstant (⇑ψ : Γ → A) := by
  intro Γ A _ _ _ _ ψ h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (ψ.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change x⁻¹ * x ∈ ψ.ker
    simp
  · intro y hy
    have hy' : ψ (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
    rw [map_mul, map_inv, inv_mul_eq_one] at hy'
    exact hy'.symm
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DzExistsPrime

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Qk11.dz_exists_prime :
    ∀
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
    n ≠ (0 : ℕ) →
      (↑n : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal →
        ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal := by
  intro v n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    exact absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) v.isPrime.ne_top
  | prime p hp => intro _ h; exact ⟨p, hp, dvd_rfl, h⟩
  | mul a b iha ihb =>
    intro hab h
    rw [Nat.cast_mul] at h
    rcases v.isPrime.mem_or_mem h with h | h
    · obtain ⟨p, hp, hd, hm⟩ := iha (left_ne_zero_of_mul hab) h
      exact ⟨p, hp, hd.mul_right _, hm⟩
    · obtain ⟨p, hp, hd, hm⟩ := ihb (right_ne_zero_of_mul hab) h
      exact ⟨p, hp, hd.mul_left _, hm⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDecZhat

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.decZhat :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ), p.Prime → ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∃ φ : Dec (F := ℚ) A, ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ ∧ ∀ n : ℕ, 0 < n → ∃ d : Dec (F := ℚ) A →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ (Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A), d s = 1) ∧ d φ = Multiplicative.ofAdd 1 := by
  intro Ω _ _ _ p hp A hA
  have : Fact p.Prime := ⟨hp⟩
  have hP := UpperTheory.V.Base.places ℚ Ω p A
  obtain ⟨v, hv⟩ := hP.1 fun h => (hP.2.1 h).2 hA
  obtain ⟨φ, -, hClosure, hFiniteQuotients⟩ := UpperTheory.V.GC.decZhat ℚ Ω v A hv
  exact ⟨φ, hClosure, hFiniteQuotients⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcPtTail

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X
open UpperTheory.V.Loc GlobalTheory.Published GlobalTheory.Published.PoitouTate

theorem UpperTheory.V.X.ptTail :
    LocalFiniteness → GlobalFiniteness → GlobalTheory.Published.PoitouTateNormalised → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (S : Finset (HeightOneSpectrum (𝓞 ℚ))), (∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ S) → ∀ (A : S → ValuationSubring Ω), (∀ v, IsPlaceOver (A v) v.1) → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), ContAction ρ → finrank k (Sha2 ρ (fun v => locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (A v)) fun v => continuous_locHom _ (A v)) + ∑ v, finrank k (H2 (ρ.comp (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (A v)))) = finrank k (H2 ρ) + finrank k (Loc.H0dual (cycK Ω l k) (ρ.comp (toGS Ω _))) := by
  intro hL hG hP Ω _ _ _ l _ h2 S hS A hA k _ _ _ M _ _ _ _ _ ρ hρ
  exact UpperTheory.V.GC.ptTail hL hG hP ℚ Ω l h2 S hS A hA k M ρ hρ
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGalTail

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.galTail :
    LocalFiniteness → GlobalFiniteness → GlobalTheory.Published.PoitouTateNormalised → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}, GalData l SP T Q pl K → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (GS Ω SP) M), ContAction ρ → finrank k (shaF (galFrame SP T Q v0 pl K) ρ) + ∑ v : T, finrank k (H2 (ρ.comp (locHom SP (pl v)))) + ∑ q : Q, finrank k (H2 (ρ.comp (locHom SP (pl q)))) = finrank k (H2 ρ) + finrank k (Loc.H0dual (cycK Ω l k) (ρ.comp (toGS Ω SP))) := by
  intro lf gf pt Ω _ _ _ l _ SP T Q v0 pl K hD k _ _ _ M _ _ _ _ _ ρ hρ
  obtain ⟨S, e, rfl, hl, hT, hQ⟩ := galIdx Ω l v0 hD
  let B : T ⊕ Q → ValuationSubring Ω := Sum.elim (fun v => pl v) (fun q => pl q)
  have hB : ∀ x, IsPlaceOver (B x) (e x).1 := by
    rintro (v | q)
    · exact hT v
    · exact hQ q
  have hA : ∀ v : S, IsPlaceOver (B (e.symm v)) v.1 := fun v => by
    have := hB (e.symm v)
    rwa [e.apply_symm_apply] at this
  have h := ptTail lf gf pt Ω l hD.l_odd S hl (fun v => B (e.symm v)) hA k M ρ hρ
  have hsum : ∑ v : S, finrank k (H2 (ρ.comp (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (B (e.symm v))))) =
      ∑ v : T, finrank k (H2 (ρ.comp (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (pl v)))) +
        ∑ q : Q, finrank k (H2 (ρ.comp (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (pl q)))) := by
    rw [e.symm.sum_comp (fun x => finrank k (H2 (ρ.comp (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (B x))))),
      Fintype.sum_sum_type]
    rfl
  have hsha : Sha2 ρ (fun v => locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (B (e.symm v)))
      (fun v => continuous_locHom _ (B (e.symm v))) = shaF (galFrame (S : Set (HeightOneSpectrum (𝓞 ℚ))) T Q v0 pl K) ρ := by
    have h1 := e.symm.iInf_comp (g := fun x => LinearMap.ker (resH2 ρ (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (B x)) (continuous_locHom _ (B x))))
    rw [iInf_sum] at h1
    exact h1
  rw [hsum, hsha, ← add_assoc] at h
  exact h
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGlobEuler

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.globEuler :
    GlobalFiniteness → GlobalEulerChar → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (S : Finset (HeightOneSpectrum (𝓞 ℚ))), (∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ S) → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), ContAction ρ → ∀ σ : G ℚ Ω, IsCC σ → Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧ finrank k (H1 ρ) + finrank k (LinearMap.ker (ρ (toGS Ω _ σ) - 1)) = finrank k (H0 ρ) + finrank k (H2 ρ) + finrank k M := by
  intro hF hE Ω _ inst _ l _ hl S hS k _ _ _ M _ _ _ _ _ ρ hρ σ hσ
  have hc : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hM : Finite M := Module.finite_of_finite k
  exact UpperTheory.global_euler_characteristic_rationals_odd_prime hF hE Ω l hl k M S ρ hS hρ σ hσ
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGalCount

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.galCount :
    HcPublished → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}, GalData l SP T Q pl K → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] (ρ : Representation k (GS Ω SP) M), (∀ m, IsLocallyConstant fun g => ρ g m) → (∀ q ∈ Q, ∀ g ∈ Ine (F := ℚ) (pl q), g ∈ K → ρ (toGS Ω SP g) = 1) → ∀ σ : G ℚ Ω, IsCC σ → Module.Finite k ((galFrame SP T Q v0 pl K).Ob ρ) ∧ Module.Finite k ((galFrame SP T Q v0 pl K).H1c ρ) ∧ finrank k ((galFrame SP T Q v0 pl K).Ob ρ) = finrank k ((galFrame SP T Q v0 pl K).H1c ρ) + finrank k (LinearMap.ker (ρ (toGS Ω SP σ) - 1)) + finrank k (Loc.H0dual (cycK Ω l k) (ρ.comp (toGS Ω SP))) := by
  intro P Ω _ _ _ l _ SP T Q v0 pl K hD k _ _ _ M _ _ _ ρ hlc hN σ hσ
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  haveI : Finite M := Module.finite_of_finite k
  have hρ : ContAction ρ := by
    unfold ReciprocityTheory.Gal.ContAction
    rw [continuous_prod_of_discrete_right]
    exact fun m => (hlc m).continuous
  have hN' : ∀ q, ∀ n ∈ (galFrame SP T Q v0 pl K).N q, ρ ((galFrame SP T Q v0 pl K).ψ q n) = 1 :=
    fun q n hn => hN q.1 q.2 n.1 hn.1 hn.2
  have tail := galTail P.lf P.gf P.pt Ω l v0 hD k M ρ hρ
  have hG : Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧ finrank k (H1 ρ) + finrank k (LinearMap.ker (ρ (toGS Ω _ σ) - 1)) = finrank k (H0 ρ) + finrank k (H2 ρ) + finrank k M := by
    obtain ⟨S, e, rfl, hS, -⟩ := galIdx Ω l v0 hD
    exact globEuler P.gf P.ge Ω l hD.l_odd S hS k M ρ hρ σ hσ
  obtain ⟨g1, g2, g3⟩ := hG
  have hc : ∀ p, ContAction (ρ.comp (locHom SP (pl p))) := fun p =>
    hρ.comp ((continuous_locHom SP (pl p)).prodMap continuous_id)
  have loc := fun p (hp : p ∈ T ∨ p ∈ Q) => locEuler P.lf P.lt P.le Ω l p (hD.prime p hp) (pl p) (hD.isOver p hp) k M _ (hc p)
  obtain ⟨a1, a2⟩ := framed_h1_euler_formula (galFrame SP T Q v0 pl K) ρ hρ hN' g1
  obtain ⟨b1, b2⟩ := frameOb (galFrame SP T Q v0 pl K) ρ hρ hN' g1 g2 (fun v => (loc v.1 (.inl v.2)).1)
    (fun q => (loc q.1 (.inr q.2)).1)
  refine ⟨b1, a1, ?_⟩
  have hT : ∑ v : T, finrank k (H1 (ρ.comp (locHom SP (pl v)))) = ∑ v : T, finrank k (H0 (ρ.comp (locHom SP (pl v)))) +
      ∑ v : T, finrank k (H2 (ρ.comp (locHom SP (pl v)))) + finrank k M := by
    rw [Finset.sum_congr rfl fun (v : T) _ => (loc v.1 (.inl v.2)).2.2.1, Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single ⟨l, hD.l_mem⟩]
    · simp
    · intro b _ hb
      exact if_neg fun h => hb (Subtype.ext h)
    · simp
  have hQ : ∑ q : Q, finrank k (H1 (ρ.comp (locHom SP (pl q)))) =
      ∑ q : Q, finrank k (H1ur (ρ.comp (locHom SP (pl q))) ((Ine (F := ℚ) (pl q) ⊓ K).subgroupOf (Dec (F := ℚ) (pl q)))) +
      ∑ q : Q, finrank k (H2 (ρ.comp (locHom SP (pl q)))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hql : (q : ℕ) ≠ l := fun h => Finset.disjoint_left.1 hD.disj hD.l_mem (h ▸ q.2)
    obtain ⟨φ, h1, h2⟩ := decZhat Ω q (hD.prime _ (.inr q.2)) (pl q) (hD.isOver _ (.inr q.2))
    rw [(loc q.1 (.inr q.2)).2.2.1, if_neg hql, add_zero,
      urIndex l _ (hc q) ((Ine (F := ℚ) (pl q)).subgroupOf (Dec (F := ℚ) (pl q))) ((Ine (F := ℚ) (pl q) ⊓ K).subgroupOf (Dec (F := ℚ) (pl q)))
        (Subgroup.comap_mono inf_le_left) ?_,
      urAbs _ (hc q) _ φ h1 h2]
    rw [Subgroup.relIndex_subgroupOf (Ine_le_Dec _), Subgroup.inf_relIndex_left]
    exact hD.idx q q.2
  change _ + _ = _ + ∑ v : T, finrank k (H0 (ρ.comp (locHom SP (pl v)))) at a2
  change _ + _ + ∑ q : Q, finrank k (H1ur (ρ.comp (locHom SP (pl q))) ((Ine (F := ℚ) (pl q) ⊓ K).subgroupOf (Dec (F := ℚ) (pl q)))) =
    _ + ∑ v : T, finrank k (H1 (ρ.comp (locHom SP (pl v)))) + ∑ q : Q, finrank k (H1 (ρ.comp (locHom SP (pl q)))) + _ at b2
  omega
end
end
