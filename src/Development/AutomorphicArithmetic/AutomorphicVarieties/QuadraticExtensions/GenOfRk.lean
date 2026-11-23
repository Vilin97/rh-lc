module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ZmodToQZ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.QzInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.EmbedQZ
public import Formalism.GaloisCohomology.Statement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.QzBasic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Algebra.Order.Star.Real
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.QzEnd

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.qzEnd :
    ∀ (l : ℕ) [Fact l.Prime] (f : QZ l →ₗ[ℤ_[l]] QZ l), ∃ c : ℤ_[l], ∀ x, f x = c • x := by
  intro l _ f
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hz : ∀ q : ℚ_[l], QZ.mk l q = 0 ↔ ‖q‖ ≤ 1 := by
    intro q
    show (Submodule.Quotient.mk q : ℚ_[l] ⧸ ZlSub l) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro h
      exact ⟨⟨q, h⟩, rfl⟩
  set x : ℕ → QZ l := fun k => QZ.mk l (((l : ℚ_[l]) ^ k)⁻¹) with hx
  have hA : ∀ (c : ℤ_[l]) (k : ℕ), c • x k = 0 ↔ ‖c‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro c k
    show QZ.mk l ((c : ℚ_[l]) * ((l : ℚ_[l]) ^ k)⁻¹) = 0 ↔ _
    have hpos : (0 : ℝ) < (l : ℝ) ^ (-(k : ℤ)) := by positivity
    rw [hz, norm_mul, norm_inv, Padic.norm_p_pow, mul_inv_le_iff₀ hpos, one_mul]
    exact Iff.rfl
  have hC : ∀ (k : ℕ) (y : QZ l), (l ^ k) • y = 0 → ∃ a : ℤ_[l], y = a • x k := by
    intro k y hy
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) y
    have h1 : QZ.mk l ((l : ℚ_[l]) ^ k * q) = 0 := by
      rw [← hy]
      show _ = (Submodule.Quotient.mk ((l ^ k) • q) : ℚ_[l] ⧸ ZlSub l)
      rw [nsmul_eq_mul]
      push_cast
      rfl
    rw [hz] at h1
    refine ⟨⟨(l : ℚ_[l]) ^ k * q, h1⟩, ?_⟩
    show QZ.mk l q = QZ.mk l (((l : ℚ_[l]) ^ k * q) * ((l : ℚ_[l]) ^ k)⁻¹)
    congr 1
    field_simp
  have hstep : ∀ k, x k = (l : ℤ_[l]) • x (k + 1) := by
    intro k
    show QZ.mk l (((l : ℚ_[l]) ^ k)⁻¹) = QZ.mk l ((l : ℚ_[l]) * ((l : ℚ_[l]) ^ (k + 1))⁻¹)
    congr 1
    rw [pow_succ]
    field_simp
  have hkill : ∀ k, (l ^ k) • x k = 0 := by
    intro k
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], hA]
    push_cast
    rw [PadicInt.norm_p_pow]
  have hex : ∀ k, ∃ a : ℤ_[l], f (x k) = a • x k := by
    intro k
    apply hC
    rw [← map_nsmul, hkill, map_zero]
  choose a ha using hex
  have hdiff : ∀ k, ‖a (k + 1) - a k‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro k
    rw [← hA, sub_smul, sub_eq_zero, ← ha k, hstep k, map_smul, ha (k + 1)]
    exact smul_comm _ _ _
  have hr : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  have hcs : CauchySeq a := by
    refine cauchySeq_of_le_geometric ((l : ℝ)⁻¹) 1 hr (fun n => ?_)
    rw [dist_comm, dist_eq_norm, one_mul, inv_pow, ← zpow_natCast, ← zpow_neg]
    exact hdiff n
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcs
  have hmono : ∀ k m, k ≤ m → ‖a m - a k‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base =>
      rw [sub_self, norm_zero]
      positivity
    | succ m hkm ih =>
      have := PadicInt.nonarchimedean (a (m + 1) - a m) (a m - a k)
      rw [sub_add_sub_cancel] at this
      refine this.trans (max_le ((hdiff m).trans ?_) ih)
      exact zpow_le_zpow_right₀ hl.le (by omega)
  have hck : ∀ k, ‖c - a k‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro k
    have ht : Filter.Tendsto (fun m => ‖a m - a k‖) Filter.atTop (nhds ‖c - a k‖) :=
      (hc.sub_const (a k)).norm
    exact le_of_tendsto ht (Filter.eventually_atTop.2 ⟨k, fun m hm => hmono k m hm⟩)
  have hfx : ∀ k, f (x k) = c • x k := by
    intro k
    have := (hA (c - a k) k).2 (hck k)
    rw [sub_smul, sub_eq_zero] at this
    rw [this, ha k]
  refine ⟨c, fun y => ?_⟩
  obtain ⟨k, hk⟩ := (qzBasic l).2.1 y
  obtain ⟨b, rfl⟩ := hC k y hk
  rw [map_smul, hfx, smul_comm]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.DualGen

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.dualGen :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [AddCommGroup D] [Module ℤ_[l] D] (r : ℕ), (∀ x : D, ∃ k : ℕ, (l : ℤ_[l]) ^ k • x = 0) → CardLe (Submodule.torsionBy ℤ_[l] D (l : ℤ_[l])) (l ^ r) →
      Tower.GenLE ℤ_[l] (D →ₗ[ℤ_[l]] QZ l) r := by
  intro l _ D _ _ r htors hcard
  classical
  obtain ⟨f, hf⟩ := embedQZ l D r htors hcard
  haveI := PropA.qzInj l
  refine ⟨Fintype.linearCombination ℤ_[l] (fun i => (LinearMap.proj i).comp f), ?_⟩
  intro φ
  obtain ⟨ψ, hψ⟩ := Module.Injective.out (R := ℤ_[l]) (Q := QZ l) f hf φ
  choose c hc using fun i => qzEnd l (ψ.comp (LinearMap.single ℤ_[l] (fun _ : Fin r => QZ l) i))
  refine ⟨c, ?_⟩
  ext d
  rw [Fintype.linearCombination_apply, ← hψ d]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  conv_rhs => rw [← Finset.univ_sum_single (f d)]

  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 := hc i (f d i)
  simp only [LinearMap.comp_apply, LinearMap.single_apply] at h1
  exact h1.symm
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.GenOfRk

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.genOfRk :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (N r : ℕ) (U : Subgroup (G F Ω)), IsClosed (U : Set (G F Ω)) → XRk l N (cycU l U) r → Tower.GenLE ℤ_[l] (Xinf l N U) r := by
  intro F Ω _ _ _ _ _ l _ N rk U hU hrk
  classical
  have hQ : ∀ q : QZ l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • q = 0 := by
    intro q
    revert q
    show ∀ q : ℚ_[l] ⧸ ZlSub l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • q = 0
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt ‖x‖ hl
      refine ⟨r, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      have hn : ‖(l : ℚ_[l]) ^ r * x‖ ≤ 1 := by
        rw [norm_mul, norm_pow, Padic.norm_p]
        have hp : (0 : ℝ) < (l : ℝ) ^ r := by positivity
        rw [inv_pow, inv_mul_le_iff₀ hp, mul_one]
        exact hr.le
      refine ⟨⟨(l : ℚ_[l]) ^ r * x, hn⟩, ?_⟩
      simp [Algebra.smul_def]
      rfl
  have hC : IsClosed ((cycU l U : Subgroup (G F Ω)) : Set (G F Ω)) :=
    hU.inter (isClosed_singleton.preimage (continuous_cycZ F Ω l))
  haveI : CompactSpace (cycU l U) := isCompact_iff_compactSpace.mp hC.isCompact
  have htors : ∀ φ : Dinf l N U, ∃ k : ℕ, (l : ℤ_[l]) ^ k • φ = 0 := by
    intro φ
    have hfin := IsLocallyConstant.range_finite φ.2.1
    choose r hr using hQ
    refine ⟨∑ q ∈ hfin.toFinset, r q, ?_⟩
    apply Subtype.ext
    funext u
    have hq : (φ : cycU l U → QZ l) u ∈ hfin.toFinset := by simp
    change (l : ℤ_[l]) ^ (∑ q ∈ hfin.toFinset, r q) • (φ : cycU l U → QZ l) u = 0
    rw [← Finset.add_sum_erase _ _ hq, pow_add, mul_comm, mul_smul, hr, smul_zero]
  obtain ⟨ι, hι, hιr, -⟩ := zmodToQZ l 1
  let κ : ZMod l →+ QZ l := ι.comp (ZMod.ringEquivCongr (pow_one l).symm).toAddMonoidHom
  have hκ : Function.Injective κ := hι.comp (ZMod.ringEquivCongr (pow_one l).symm).injective
  have hκr : ∀ q : QZ l, (l : ℤ_[l]) • q = 0 → κ (Function.invFun κ q) = q := by
    intro q hq
    apply Function.invFun_eq
    obtain ⟨a, ha⟩ := (hιr q).2 (by rw [pow_one]; exact hq)
    exact ⟨(ZMod.ringEquivCongr (pow_one l).symm).symm a, by simp [κ, ha]⟩
  have hval : ∀ φ : Submodule.torsionBy ℤ_[l] (Dinf l N U) (l : ℤ_[l]), ∀ u : cycU l U,
      (l : ℤ_[l]) • ((φ : Dinf l N U) : cycU l U → QZ l) u = 0 := by
    intro φ u
    have h := (Submodule.mem_torsionBy_iff _ _).1 φ.2
    have h2 := congrArg (fun ψ : Dinf l N U => (ψ : cycU l U → QZ l) u) h
    exact h2
  let f : Submodule.torsionBy ℤ_[l] (Dinf l N U) (l : ℤ_[l]) → XDual N (cycU l U) (ZMod l) (ZMod l) :=
    fun φ => ⟨fun u => Function.invFun κ (((φ : Dinf l N U) : cycU l U → QZ l) u), by
      have hφ := (φ : Dinf l N U).2
      refine ⟨by exact hφ.1.comp (Function.invFun κ), ?_, ?_, ?_⟩
      · intro a b
        apply hκ
        rw [map_add (f := _), hκr _ (hval φ _), hκr _ (hval φ _), hκr _ (hval φ _), hφ.2.1]
      · intro A u hu
        apply hκ
        rw [hκr _ (hval φ _), hφ.2.2.1 A u hu, map_zero]
      · intro A hA u hu
        apply hκ
        rw [hκr _ (hval φ _), hφ.2.2.2 A hA u hu, map_zero]⟩
  have hf : Function.Injective f := by
    intro φ ψ h
    apply Subtype.ext
    apply Subtype.ext
    funext u
    have h1 := congrArg (fun χ : XDual N (cycU l U) (ZMod l) (ZMod l) => κ ((χ : cycU l U → ZMod l) u)) h
    simp only [f] at h1
    rwa [hκr _ (hval φ u), hκr _ (hval ψ u)] at h1
  exact dualGen l (Dinf l N U) rk htors (hrk.of_injective f hf)
end
end
