module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.WpBridge
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SigmaLogDeriv2
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.AddLaw
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.AddLaw
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.StAddRight
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Tactic.TypeStar
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.AddDbl

section

@[expose] public section

noncomputable section

namespace PI.GalTorsConj.W

open Formalism.L2.Th1.F
open Filter Topology

namespace ZetaDoubling

open OriginCoordinatesAdd

def mu (L : PeriodPair) (z : ℂ) : ℂ :=
  (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) / L.derivWeierstrassP z

lemma hasDerivAt_two_mul (z : ℂ) : HasDerivAt (fun y : ℂ => 2 * y) 2 z := by
  simpa using (hasDerivAt_id z).const_mul (2 : ℂ)

lemma ev_two (L : PeriodPair) {z : ℂ} (h2 : 2 * z ∉ L.lattice) :
    ∀ᶠ z' in 𝓝 z, 2 * z' ∉ L.lattice := by
  have ho : IsOpen ((fun y : ℂ => 2 * y) ⁻¹' (L.lattice : Set ℂ)ᶜ) :=
    L.isClosed_lattice.isOpen_compl.preimage (continuous_const.mul continuous_id)
  exact ho.mem_nhds h2

lemma ev_self (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) : ∀ᶠ z' in 𝓝 z, z' ∉ L.lattice :=
  L.isClosed_lattice.isOpen_compl.mem_nhds hz

lemma derivWeierstrassP_ne_zero (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) (h2 : 2 * z ∉ L.lattice) :
    L.derivWeierstrassP z ≠ 0 := by
  intro h
  exact h2 ((pDerivZero L z hz).1 h)

lemma hasDerivAt_mu (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) (hy : L.derivWeierstrassP z ≠ 0) :
    HasDerivAt (mu L)
      ((12 * L.weierstrassP z * L.derivWeierstrassP z * L.derivWeierstrassP z
        - (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) * (6 * L.weierstrassP z ^ 2 - L.g₂ / 2))
        / L.derivWeierstrassP z ^ 2) z := by
  have hN := (((hasDerivAt_wp L hz).pow 2).const_mul (6 : ℂ)).sub_const (L.g₂ / 2)
  have hQ := hN.div (pSecond L z hz) hy
  refine (hQ.congr_of_eventuallyEq (f₁ := mu L)
    (Filter.Eventually.of_forall (fun y => rfl))).congr_deriv ?_
  simp only [Pi.pow_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  ring

lemma zetaDbl (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) (h2 : 2 * z ∉ L.lattice) :
    wZeta L (2 * z) = 2 * wZeta L z + mu L z / 2 := by
  have hy := derivWeierstrassP_ne_zero L hz h2
  have hs : wSigma L z ≠ 0 := fun h => hz ((sigmaZero L z).1 h)
  have hF := (sigmaLogDeriv L (2 * z) h2).comp z (hasDerivAt_two_mul z)
  have hG := (pSecond L z hz).neg.mul ((sigmaLogDeriv L z hz).pow 4)
  have heq : (fun y => -L.derivWeierstrassP y * wSigma L y ^ 4) =ᶠ[𝓝 z]
      (wSigma L ∘ fun y : ℂ => 2 * y) := by
    filter_upwards [ev_self L hz] with y hy'
    exact (sigmaDouble L y hy').symm
  have e := (hF.congr_of_eventuallyEq heq).unique hG
  rw [sigmaDouble L z hz] at e
  simp only [Pi.pow_apply, Pi.neg_apply, Nat.cast_ofNat, show (4 : ℕ) - 1 = 3 from rfl] at e
  have e2 : wZeta L (2 * z) * (-L.derivWeierstrassP z) * 2 =
      -(6 * L.weierstrassP z ^ 2 - L.g₂ / 2) + -L.derivWeierstrassP z * (4 * wZeta L z) := by
    apply mul_right_cancel₀ (pow_ne_zero 4 hs)
    linear_combination e
  have hy2 : (2 : ℂ) * L.derivWeierstrassP z ≠ 0 := mul_ne_zero two_ne_zero hy
  have e3 : wZeta L (2 * z) = (6 * L.weierstrassP z ^ 2 - L.g₂ / 2 +
      4 * L.derivWeierstrassP z * wZeta L z) / (2 * L.derivWeierstrassP z) := by
    rw [eq_div_iff hy2]
    linear_combination -e2
  rw [e3]
  unfold mu
  field_simp
  ring

lemma dblA (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) (h2 : 2 * z ∉ L.lattice) :
    L.weierstrassP (2 * z) = L.weierstrassP z -
      (12 * L.weierstrassP z * L.derivWeierstrassP z * L.derivWeierstrassP z
        - (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) * (6 * L.weierstrassP z ^ 2 - L.g₂ / 2))
        / L.derivWeierstrassP z ^ 2 / 4 := by
  have hy := derivWeierstrassP_ne_zero L hz h2
  have hL := (zetaHasDeriv L (2 * z) h2).comp z (hasDerivAt_two_mul z)
  have hR := ((zetaHasDeriv L z hz).const_mul (2 : ℂ)).add ((hasDerivAt_mu L hz hy).div_const 2)
  have heq : (fun y => 2 * wZeta L y + mu L y / 2) =ᶠ[𝓝 z] (wZeta L ∘ fun y : ℂ => 2 * y) := by
    filter_upwards [ev_self L hz, ev_two L h2] with y h1 h3
    exact (zetaDbl L h1 h3).symm
  have e := (hL.congr_of_eventuallyEq heq).unique hR
  linear_combination (-1 / 2 : ℂ) * e

lemma dbl_alg (x y g : ℂ) (hy : y ≠ 0) :
    x - (12 * x * y * y - (6 * x ^ 2 - g / 2) * (6 * x ^ 2 - g / 2)) / y ^ 2 / 4 = dblX x y g := by
  unfold dblX
  field_simp
  ring

lemma dblB (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) (h2 : 2 * z ∉ L.lattice) :
    L.weierstrassP (2 * z) = dblX (L.weierstrassP z) (L.derivWeierstrassP z) L.g₂ := by
  rw [dblA L hz h2]
  exact dbl_alg _ _ _ (derivWeierstrassP_ne_zero L hz h2)

end ZetaDoubling


open OriginCoordinatesAdd ZetaDoubling in
theorem dblLaw : DblLaw := by
  intro L z hz h2
  refine ⟨dblB L hz h2, ?_⟩
  have hy := derivWeierstrassP_ne_zero L hz h2
  have hL := (hasDerivAt_wp L h2).comp z (hasDerivAt_two_mul z)
  have hR := (((hasDerivAt_mu L hz hy).pow 2).div_const (4 : ℂ)).sub
    ((hasDerivAt_wp L hz).const_mul (2 : ℂ))
  have heq : (fun y => mu L y ^ 2 / 4 - 2 * L.weierstrassP y) =ᶠ[𝓝 z]
      (L.weierstrassP ∘ fun y : ℂ => 2 * y) := by
    filter_upwards [ev_self L hz, ev_two L h2] with y h1 h3
    show mu L y ^ 2 / 4 - 2 * L.weierstrassP y = L.weierstrassP (2 * y)
    rw [dblB L h1 h3]
    rfl
  have e := (hL.congr_of_eventuallyEq heq).unique hR
  simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at e
  unfold mu at e
  unfold dblY
  rw [← dbl_alg _ _ _ hy]
  linear_combination (1 / 2 : ℂ) * e

end PI.GalTorsConj.W

end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.MulDefs

section

@[expose] public section

noncomputable section

namespace PI.GalTorsConj.W

open Formalism.L2.Th1.F

def ExtRho : Prop :=
  ∀ (M M₁ : IntermediateField ℚ ℂ) (h : M ≤ M₁), (∀ x ∈ M₁, IsAlgebraic M x) →
    ∀ ρ : M →ₐ[ℚ] ℂ, ∃ ρ₁ : M₁ →ₐ[ℚ] ℂ, ∀ x : M, ρ₁ (IntermediateField.inclusion h x) = ρ x

end PI.GalTorsConj.W

end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.IncAdjInclusion

section

@[expose] public section

noncomputable section

namespace PI.GalTorsConj.W

open Polynomial

theorem extRho : ExtRho := by
  intro M M₁ h halg ρ
  letI iA : Algebra M M₁ := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI hA : Algebra.IsAlgebraic M M₁ := by
    refine ⟨fun x => ?_⟩
    let f : M₁ →ₐ[M] ℂ :=
      { toRingHom := (M₁.val : M₁ →+* ℂ)
        commutes' := fun _ => rfl }
    exact (isAlgebraic_algHom_iff f M₁.val.injective).mp (halg x x.2)
  letI iC : Algebra M ℂ := ρ.toRingHom.toAlgebra
  let φ : M₁ →ₐ[M] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨{ toRingHom := φ.toRingHom, commutes' := φ.toRingHom.map_rat_algebraMap }, fun x => ?_⟩
  exact φ.commutes x

end PI.GalTorsConj.W

end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.WpOnto

section

@[expose] public section

noncomputable section

namespace PI.GalTorsConj.W

open PI.GalTorsConj Filter Topology

theorem wp_onto (L : PeriodPair) (x : ℂ) : ∃ z, z ∉ L.lattice ∧ L.weierstrassP z = x := by
  apply GlobalTheory.exists_weierstrassP_eq <;> assumption

theorem pOnto : POnto := by
  intro L x y hxy
  obtain ⟨z, hz, hzx⟩ := wp_onto L x
  have hsq := L.derivWeierstrassP_sq z hz
  rw [hzx, ← hxy] at hsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exact ⟨z, hz, hzx, h⟩
  · refine ⟨-z, ?_, by rw [L.weierstrassP_neg, hzx], by rw [L.derivWeierstrassP_neg, h, neg_neg]⟩
    intro hm
    exact hz (by simpa using L.lattice.neg_mem hm)

end PI.GalTorsConj.W

end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.TorsValsFinite

section

@[expose] public section

noncomputable section

namespace PI.GalTorsConj.W

open Polynomial Formalism.L2.Th1.F

theorem mulStable_nat (L : PeriodPair) (n : ℕ) : MulStable L (n : ℂ) := by
  intro ω hω
  rw [← nsmul_eq_mul]
  exact nsmul_mem hω n

theorem tors_vals_finite (L : PeriodPair) (n : ℕ) (hn : 0 < n) :
    {v : ℂ | ∃ s, (n : ℂ) * s ∈ L.lattice ∧ s ∉ L.lattice ∧ L.weierstrassP s = v}.Finite := by
  have hα : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨S, hS⟩ := kerRepsExist L (n : ℂ) hα (mulStable_nat L n)
  refine (S.finite_toSet.image L.weierstrassP).subset ?_
  rintro v ⟨s, h1, h2, rfl⟩
  obtain ⟨P, hP, hsP⟩ := hS.2.2 s h1 h2
  refine ⟨P, hP, ?_⟩
  have e : s = P + (s - P) := by ring
  rw [e, wp_add_mem L P hsP]

theorem shift_emb (M : IntermediateField ℚ ℂ) (x : ℂ) (hx : Transcendental M x) (k : ℕ) :
    ∃ σ : IntermediateField.adjoin M {x} →ₐ[M] ℂ,
      σ (IntermediateField.AdjoinSimple.gen M x) = x + k := by
  have hk : Transcendental M (x + k) := by
    intro halg
    apply hx
    have h2 : IsIntegral M (k : ℂ) := by
      simpa using (isIntegral_algebraMap (R := M) (A := ℂ) (x := (k : M)))
    simpa using (halg.isIntegral.sub h2).isAlgebraic
  have hφ : nonZeroDivisors M[X] ≤ (nonZeroDivisors ℂ).comap (aeval (x + k) : M[X] →ₐ[M] ℂ) := by
    intro p hp
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero] at hp ⊢
    intro h0
    exact hk ⟨p, hp, h0⟩
  refine ⟨(RatFunc.liftAlgHom (aeval (x + k) : M[X] →ₐ[M] ℂ) hφ).comp
    (RatFunc.algEquivOfTranscendental x hx).symm.toAlgHom, ?_⟩
  rw [AlgHom.comp_apply]
  change RatFunc.liftAlgHom _ hφ ((RatFunc.algEquivOfTranscendental x hx).symm _) = _
  rw [RatFunc.algEquivOfTranscendental_symm_gen]
  have := RatFunc.liftAlgHom_apply_div (aeval (x + k) : M[X] →ₐ[M] ℂ) hφ X 1
  simpa using this

def rsHom (M : IntermediateField ℚ ℂ) (E : IntermediateField M ℂ) (σ : E →ₐ[M] ℂ) :
    E.restrictScalars ℚ →ₐ[ℚ] ℂ :=
  RingHom.toRatAlgHom
    { toFun := fun z => σ ⟨z, z.2⟩
      map_one' := σ.map_one
      map_mul' := fun a b => σ.map_mul ⟨a, a.2⟩ ⟨b, b.2⟩
      map_zero' := σ.map_zero
      map_add' := fun a b => σ.map_add ⟨a, a.2⟩ ⟨b, b.2⟩ }

theorem alg_of_sq {F : Type*} [Field F] [Algebra F ℂ] {x y a b : ℂ}
    (hsq : y ^ 2 = 4 * x ^ 3 - a * x - b)
    (hx : IsAlgebraic F x) (ha : IsAlgebraic F a) (hb : IsAlgebraic F b) : IsAlgebraic F y := by
  have hx' := mem_algebraicClosure_iff.mpr hx
  have ha' := mem_algebraicClosure_iff.mpr ha
  have hb' := mem_algebraicClosure_iff.mpr hb
  have h4 : (4 : ℂ) ∈ algebraicClosure F ℂ := by
    have := natCast_mem (algebraicClosure F ℂ) 4
    exact_mod_cast this
  have hw : 4 * x ^ 3 - a * x - b ∈ algebraicClosure F ℂ :=
    sub_mem (sub_mem (mul_mem h4 (pow_mem hx' 3)) (mul_mem ha' hx')) hb'
  rw [← hsq] at hw
  exact IsAlgebraic.of_pow two_pos (mem_algebraicClosure_iff.mp hw)

theorem wp_isAlgebraic (L : PeriodPair) (M : IntermediateField ℚ ℂ) (hg2 : L.g₂ ∈ M)
    (hg3 : L.g₃ ∈ M) (n : ℕ) (t : ℂ) (hn : 0 < n) (hnt : (n : ℂ) * t ∈ L.lattice)
    (ht : t ∉ L.lattice) : IsAlgebraic M (L.weierstrassP t) := by
  by_contra htr
  apply (tors_vals_finite L n hn).not_infinite
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => L.weierstrassP t + k) ?_ ?_
  · intro a b hab
    simp only at hab
    exact_mod_cast add_left_cancel hab
  intro k
  obtain ⟨σ, hσ⟩ := shift_emb M (L.weierstrassP t) htr k
  let Mx : IntermediateField ℚ ℂ := (IntermediateField.adjoin M {L.weierstrassP t}).restrictScalars ℚ
  have hMx : ∀ z ∈ M, z ∈ Mx := fun z hz =>
    (IntermediateField.adjoin M {L.weierstrassP t}).algebraMap_mem ⟨z, hz⟩
  have hxMx : L.weierstrassP t ∈ Mx := IntermediateField.mem_adjoin_simple_self M _
  let M₂ : IntermediateField ℚ ℂ := (algebraicClosure Mx ℂ).restrictScalars ℚ
  have hle : Mx ≤ M₂ := fun z hz => by
    show z ∈ algebraicClosure Mx ℂ
    exact mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (⟨z, hz⟩ : Mx))
  have halg₂ : ∀ z ∈ M₂, IsAlgebraic Mx z := fun z hz => mem_algebraicClosure_iff.mp hz
  obtain ⟨ρ₂, hρ₂⟩ := extRho Mx M₂ hle halg₂ (rsHom M _ σ)
  have hg2₂ : L.g₂ ∈ M₂ := hle (hMx _ hg2)
  have hg3₂ : L.g₃ ∈ M₂ := hle (hMx _ hg3)
  have hx₂ : L.weierstrassP t ∈ M₂ := hle hxMx
  have hy₂ : L.derivWeierstrassP t ∈ M₂ := by
    have hsq : L.derivWeierstrassP t ^ 2
        = 4 * L.weierstrassP t ^ 3 - L.g₂ * L.weierstrassP t - L.g₃ := by
      have e := L.derivWeierstrassP_sq t ht
      linear_combination e
    show L.derivWeierstrassP t ∈ algebraicClosure Mx ℂ
    exact mem_algebraicClosure_iff.mpr (alg_of_sq hsq
      (isAlgebraic_algebraMap (⟨_, hxMx⟩ : Mx))
      (isAlgebraic_algebraMap (⟨_, hMx _ hg2⟩ : Mx))
      (isAlgebraic_algebraMap (⟨_, hMx _ hg3⟩ : Mx)))
  have hfix : ∀ z (hz : z ∈ M) (hz₂ : z ∈ M₂), ρ₂ ⟨z, hz₂⟩ = z := by
    intro z hz hz₂
    have e1 : (⟨z, hz₂⟩ : M₂) = IntermediateField.inclusion hle ⟨z, hMx z hz⟩ := rfl
    rw [e1, hρ₂]
    exact σ.commutes ⟨z, hz⟩
  have hρx : ρ₂ ⟨_, hx₂⟩ = L.weierstrassP t + k := by
    have e1 : (⟨_, hx₂⟩ : M₂) = IntermediateField.inclusion hle ⟨_, hxMx⟩ := rfl
    rw [e1, hρ₂]
    exact hσ
  have hg2' : L.g₂ = ρ₂ ⟨_, hg2₂⟩ := (hfix _ hg2 hg2₂).symm
  have hg3' : L.g₃ = ρ₂ ⟨_, hg3₂⟩ := (hfix _ hg3 hg3₂).symm
  obtain ⟨t₂, hst⟩ := st_exists (L := L) (L' := L) (M := M₂) (ρ := ρ₂) pOnto hg2₂ hg3₂ hg2' hg3' t
    (Or.inr ⟨hx₂, hy₂⟩)
  have hn₂ := (st_mem_iff (st_nsmul addLaw dblLaw hg2₂ hg2' hst n)).mp hnt
  rcases hst with ⟨h1, -⟩ | ⟨-, h2, hx', hy', e1, -⟩
  · exact absurd h1 ht
  · refine ⟨t₂, hn₂, h2, ?_⟩
    rw [e1]
    exact hρx

end PI.GalTorsConj.W

end
end
end
