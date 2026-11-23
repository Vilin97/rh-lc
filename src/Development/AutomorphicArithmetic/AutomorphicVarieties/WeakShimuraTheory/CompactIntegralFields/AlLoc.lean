module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Mathlib.FieldTheory.IsAlgClosed.Basic
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsValuationExtensionIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ResidueIsIntegralOfAlgebraicOverDvr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIntegralClosurePreimageOfIsIntegral

section

@[expose] public section

open Polynomial in
theorem UpperTheory.exists_integralClosure_preimage_of_isIntegral :
    ∀ (R E k : Type) [CommRing R] [Field E] [IsAlgClosed E] [Algebra R E] [CommRing k] [IsDomain k] (ψ : integralClosure R E →+* k) (x : k), IsIntegral ℤ x → ∃ y, ψ y = x := by
  intro R E k _ _ _ _ _ _ ψ x hx
  classical
  obtain ⟨p, hpm, hpx⟩ := hx
  set q : E[X] := p.map (algebraMap ℤ E) with hq
  have hqm : q.Monic := hpm.map _
  have hqs : q.Splits := IsAlgClosed.splits q
  let lift : E → integralClosure R E := fun a => if h : IsIntegral R a then ⟨a, h⟩ else 0
  have hlift : ∀ a ∈ q.roots, ((lift a : integralClosure R E) : E) = a := by
    intro a ha
    have hr : q.IsRoot a := (mem_roots hqm.ne_zero).1 ha
    have hi : IsIntegral ℤ a := ⟨p, hpm, by
      rw [eval₂_eq_eval_map]
      exact hr⟩
    have hiR : IsIntegral R a := hi.tower_top
    simp [lift, hiR]
  have hfac : p.map (algebraMap ℤ (integralClosure R E)) = (q.roots.map fun a => X - C (lift a)).prod := by
    apply Polynomial.map_injective (algebraMap (integralClosure R E) E) Subtype.val_injective
    rw [Polynomial.map_map, Polynomial.map_multiset_prod, Multiset.map_map]
    have e : (algebraMap (integralClosure R E) E).comp (algebraMap ℤ (integralClosure R E)) = algebraMap ℤ E :=
      RingHom.ext_int _ _
    rw [e, ← hq]
    conv_lhs => rw [hqs.eq_prod_roots_of_monic hqm]
    congr 1
    apply Multiset.map_congr rfl
    intro a ha
    simp only [Function.comp_apply, Polynomial.map_sub, map_X, map_C]
    congr 2
    exact (hlift a ha).symm
  have hk : p.map (algebraMap ℤ k) = (q.roots.map fun a => X - C (ψ (lift a))).prod := by
    have e : ψ.comp (algebraMap ℤ (integralClosure R E)) = algebraMap ℤ k := RingHom.ext_int _ _
    rw [← e, ← Polynomial.map_map, hfac, Polynomial.map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp
  have h0 : (p.map (algebraMap ℤ k)).eval x = 0 := by
    rw [eval_map]
    exact hpx
  rw [hk, eval_multiset_prod, Multiset.map_map, Multiset.prod_eq_zero_iff] at h0
  obtain ⟨a, _, ha⟩ := Multiset.mem_map.1 h0
  refine ⟨lift a, ?_⟩
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C] at ha
  exact (sub_eq_zero.1 ha).symm
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.AlLoc

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem al_loc {l : ℕ} [Fact l.Prime] (c : Coef l) {B : Type} [CommRing B] [IsDomain B] [CharP B l] (g : c.O →+* B) :
    IsLocalHom g := by
  have hl : (l : c.O) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hk : RingHom.ker g ≠ ⊥ := fun h => hl (by
    have : (l : c.O) ∈ RingHom.ker g := by rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    rwa [h, Ideal.mem_bot] at this)
  have hm : RingHom.ker g = maximalIdeal c.O := eq_maximalIdeal ((RingHom.ker_isPrime g).isMaximal hk)
  refine ⟨fun x hx => by_contra fun h => hx.ne_zero ?_⟩
  have : x ∈ RingHom.ker g := hm ▸ (mem_maximalIdeal x).2 h
  exact this

private theorem al_le {l : ℕ} [Fact l.Prime] (c : Coef l) : c.O ≤ integralClosure ℤ_[l] (PadicAlgCl l) := fun x hx =>
  (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val

theorem UpperTheory.V.Ws.ambL :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
      [Finite (ResidueField A)] [CharP A l] (a : c.O →+* A), ∃ (𝔞 : Amb l) (f : A →+* 𝔞.V), CharP 𝔞.K l ∧ 𝔞.IsDvr f ∧ f.comp a = 𝔞.a c := by
  intro l _ c A _ _ _ _ _ _ a
  haveI := c.dvr
  haveI := c.fin
  let K := AlgebraicClosure (FractionRing A)
  let g0 : A →+* K := (algebraMap (FractionRing A) K).comp (algebraMap A (FractionRing A))
  have hg0 : Function.Injective g0 :=
    (algebraMap (FractionRing A) K).injective.comp (IsFractionRing.injective A (FractionRing A))
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing g0
  let f : A →+* V := g0.codRestrict V hV
  have hfinj : Function.Injective f := fun x y h => hg0 (congrArg Subtype.val h)
  have hfloc : IsLocalHom f := hloc
  haveI hK : CharP K l := charP_of_injective_ringHom hg0 l
  haveI : CharP V l := charP_of_injective_ringHom hfinj l
  have heq : V.subtype.comp f = g0 := RingHom.ext fun _ => rfl
  have halg : ∀ z : K, ∃ p : A[X], p ≠ 0 ∧ eval₂ (V.subtype.comp f) z p = 0 := by
    intro z
    obtain ⟨q, hq0, hq⟩ := Algebra.IsAlgebraic.isAlgebraic (R := FractionRing A) z
    refine ⟨IsLocalization.integerNormalization (nonZeroDivisors A) q, ?_, ?_⟩
    · rwa [Ne, IsFractionRing.integerNormalization_eq_zero_iff]
    · rw [Polynomial.aeval_def] at hq
      rw [heq]
      exact IsLocalization.integerNormalization_eval₂_eq_zero (nonZeroDivisors A)
        (algebraMap (FractionRing A) K) q hq
  let S := integralClosure c.O (PadicAlgCl l)
  have hinj : Function.Injective (algebraMap c.O S) := by
    intro x y h
    apply Subtype.ext
    have h2 := congrArg Subtype.val h
    exact h2
  obtain ⟨Φ, hΦ⟩ := UpperTheory.exists_valuation_extension_integral c.O S K V hinj (f.comp a)
  have hS : ∀ c' : Coef l, ∀ x : c'.O, (x : PadicAlgCl l) ∈ S := fun c' x =>
    IsIntegral.tower_top (A := c.O) (al_le c' x.2)
  let ι : ∀ c' : Coef l, c'.O →+* S := fun c' => c'.O.val.toRingHom.codRestrict S (hS c')
  refine ⟨Amb.mk K V (fun c' => Φ.comp (ι c')) ?_ ?_ ?_, f, hK, ⟨hfinj, hfloc, inferInstance, inferInstance, halg⟩, ?_⟩
  · intro c1 c2 h x
    exact congrArg Φ (Subtype.ext rfl)
  · intro c'
    exact al_loc c' _
  · intro x
    obtain ⟨p, hp0, hp⟩ := halg x
    have hint := UpperTheory.residue_isIntegral_of_algebraic_over_dvr A K V f hfinj hfloc x ⟨p, hp0, hp⟩
    obtain ⟨y, hy⟩ := UpperTheory.exists_integralClosure_preimage_of_isIntegral c.O (PadicAlgCl l) (ResidueField V)
      ((IsLocalRing.residue V).comp Φ) (IsLocalRing.residue V x) hint
    have hyl : IsIntegral ℤ_[l] (y : PadicAlgCl l) := isIntegral_trans (A := c.O) _ y.2
    obtain ⟨c', -, hc'⟩ := (coefSup l).2.2.1 c y.1 hyl
    refine ⟨c', ⟨y.1, hc'⟩, ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hy]
    rfl
  · exact hΦ.symm.trans (congrArg Φ.comp (RingHom.ext fun x => Subtype.ext rfl))
end
end
