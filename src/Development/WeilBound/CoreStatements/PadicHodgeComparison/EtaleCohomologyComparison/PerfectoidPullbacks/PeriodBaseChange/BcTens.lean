module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.BWMorL
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrisZeroSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilpotentIdentityMorphismCompat
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.OB

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAcrisTruncatedWitt

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.CrisFlat

theorem flat_quotient_of_flat {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    (I : Ideal R) (J : Ideal A) (hJ : J = I.map (algebraMap R A)) (f : R ⧸ I →+* A ⧸ J)
    (hf : ∀ a, f (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (algebraMap R A a)) :
    letI := f.toAlgebra; Module.Flat (R ⧸ I) (A ⧸ J) := by
  subst hJ
  letI := f.toAlgebra
  haveI : IsScalarTower R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) :=
    IsScalarTower.of_algebraMap_eq fun a => (hf a).symm
  let e₀ : (R ⧸ I) ⊗[R] A ≃ₗ[R] A ⧸ I.map (algebraMap R A) :=
    (TensorProduct.comm R (R ⧸ I) A).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).symm.toLinearEquiv.restrictScalars R)
  let e : (R ⧸ I) ⊗[R] A ≃ₗ[R ⧸ I] A ⧸ I.map (algebraMap R A) :=
    e₀.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  exact Module.Flat.of_linearEquiv e.symm

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def wToAcr0 (r : Res l K) : WittVector l r.k →+* (base l).Acr0 :=
  (algebraMap (base l).W (base l).Acr0).comp ((base l).sW.comp (WittVector.map r.s))

theorem isTorsionFree_acris_zero (r : Res l K) :
    letI := (wToAcr0 r).toAlgebra; Module.IsTorsionFree (WittVector l r.k) (base l).Acr0 := by
  letI := (wToAcr0 r).toAlgebra
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro a x h
  by_cases ha : a = 0
  · exact Or.inl ha
  refine Or.inr ?_
  obtain ⟨m, b, e⟩ := WittVector.exists_eq_pow_p_mul' a ha
  rw [Algebra.smul_def] at h
  have h1 : (wToAcr0 r a : Localization.Away (l : (base l).W)) * (x : Localization.Away (l : (base l).W)) = 0 :=
    congrArg Subtype.val h
  have hl : IsUnit (l : Localization.Away (l : (base l).W)) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (l : (base l).W)) (l : (base l).W)
    rwa [map_natCast] at this
  have hu : IsUnit (wToAcr0 r a : Localization.Away (l : (base l).W)) := by
    have e2 : (wToAcr0 r a : Localization.Away (l : (base l).W)) =
        (l : Localization.Away (l : (base l).W)) ^ m * ((base l).Acr0.val.toRingHom.comp (wToAcr0 r)) b := by
      change ((base l).Acr0.val.toRingHom.comp (wToAcr0 r)) a = _
      rw [e, map_mul, map_pow, map_natCast]
    rw [e2]
    exact (hl.pow m).mul (b.isUnit.map _)
  exact Subtype.ext ((hu.mul_right_eq_zero).1 h1)

theorem flat_acris_zero (r : Res l K) :
    letI := (wToAcr0 r).toAlgebra; Module.Flat (WittVector l r.k) (base l).Acr0 := by
  letI := (wToAcr0 r).toAlgebra
  haveI := isTorsionFree_acris_zero r
  infer_instance

theorem flat_acr (r : Res l K) (n : ℕ) :
    letI := (Mid.wn r n).toAlgebra; Module.Flat (Wc.Wm l r.k n) ((base l).Acr n) := by
  letI := (wToAcr0 r).toAlgebra
  haveI := flat_acris_zero r
  refine flat_quotient_of_flat (R := WittVector l r.k) (A := (base l).Acr0)
    (Ideal.span {(l : WittVector l r.k) ^ n}) (Ideal.span {(l : (base l).Acr0) ^ n}) ?_ (Mid.wn r n) ?_
  · rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]
  · intro a
    exact (Mid.wn_mk r n a).trans ((base l).cris_algebraMap n (WittVector.map r.s a))

end GlobalTheory.CompanionTheory.CrisFlat
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAcrisTruncatedWittStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.flat_acris_truncated_witt : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (n : ℕ), letI := (Mid.wn r n).toAlgebra; Module.Flat (Wc.Wm l r.k n) ((base l).Acr n) := by
  first | exact @GlobalTheory.CompanionTheory.CrisFlat.flat_acr | exact GlobalTheory.CompanionTheory.CrisFlat.flat_acr | (intros; apply GlobalTheory.CompanionTheory.CrisFlat.flat_acr <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilpotentIdentityMorphismCompatStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.nilpotent_identity_morphism_compat : ∀ {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] {I : Ideal R}
    {I' : Ideal R'} {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} (hp : p ≠ 0) (hn : IsNilpotent (p : R))
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'}
    (m : NMor γ q κ γ' q κ' (algebraMap R R')) (hu : m.u = 𝟙 X) (hg : m.g = RingHom.id O) (U : Cov q)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q' : ObjectProperty (Thick (nlFun γ' p X q κ')))
    (hQ : Q = St ⊤ {⊤}) (hQ' : Q' = St ⊤ {⊤}) (h : ∀ T, Q' T → Q ((m.mor p).functor.obj T))
    (ha : ∀ a : R', (m.smor Q Q' h).LeC a (oT Q) (oT Q')) (hb : ∀ a : R', (m.smor Q Q' h).LeC a (oB Q) (oB Q')) (j : ℕ),
    Tens R (N := fun _ : Unit => R') (M := fun _ => CH.H (sq (oT Q) (oB Q)) j) (M' := CH.H (sq (oT Q') (oB Q')) j)
      fun _ a x => ((m.smor Q Q' h).sqC a (ha a) (hb a)).pull j x := by
  first | exact @GlobalTheory.CompanionTheory.BcCov.bc_cover | exact GlobalTheory.CompanionTheory.BcCov.bc_cover | (intros; apply GlobalTheory.CompanionTheory.BcCov.bc_cover <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothModelTensorWittComparison

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.BcAcris

theorem pull_comm {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K) (j n : ℕ)
    (Q' : ObjectProperty (Thick (nlFun (B.DD true (base l) n) l M.X M.p (Mid.κm r n)))) (a : AW r)
    (y : (Wc.HS l (B.schFn M.p) r.ρ j).M n) :
    (toQ Q' ((base l).cris n)).pull j (idA r a • bWL r M n j y) =
      (base l).cris n a • (toQ Q' ((base l).cris n)).pull j
        ((B.omMor ((nm r M n).mor l) r.w (Mid.wn_mk r n)).pull j y) := by
  have e : bWL r M n j y = (B.omMor ((nm r M n).mor l) r.w (Mid.wn_mk r n)).pull j y :=
    congrArg (fun t => CH.Mor.pull t j y) (bWMorL_eq r M n)
  exact (congrArg (fun v => (toQ Q' ((base l).cris n)).pull j (idA r a • v)) e).trans
    (LinearMap.map_smulₛₗ ((toQ Q' ((base l).cris n)).pull j) (idA r a) _)



theorem bc_tens : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K), M.Sm → ∀ j n,
    Tens (WittVector l r.k) (N := fun _ : Unit => AW r) (M := fun _ => (Wc.HS l (B.schFn M.p) r.ρ j).M n)
      (M' := Mid.HM r M n j) fun _ a y => idA r a • bWL r M n j y := by
  intro l _ K r M hM j n
  letI := (Mid.wn r n).toAlgebra
  haveI : Module.Flat (Wc.Wm l r.k n) ((base l).Acr n) := GlobalTheory.T.flat_acris_truncated_witt r n
  obtain ⟨U⟩ := cov_of_sm M hM
  let m := nm r M n
  let Q : ObjectProperty (Thick (nlFun (Wc.pd l r.k n) l M.X M.p ((Wc.res l r.k n).comp r.ρ))) := St ⊤ {⊤}
  let Q' : ObjectProperty (Thick (nlFun (B.DD true (base l) n) l M.X M.p (Mid.κm r n))) := St ⊤ {⊤}
  have hQ : ∀ T, Q T := st_all
  have hQ' : ∀ T, Q' T := st_all
  have h : ∀ T, Q' T → Q ((m.mor l).functor.obj T) := fun T _ => hQ _
  have ha : ∀ a, (m.smor Q Q' h).LeC a (oT Q) (oT Q') := fun a => GlobalTheory.CompanionTheory.BcCov.leC_top _ a _ _ (oT_top Q')
  have hb : ∀ a, (m.smor Q Q' h).LeC a (oB Q) (oB Q') := fun a => GlobalTheory.CompanionTheory.BcCov.leC_bot _ a _ _ fun T => oB_bot Q _
  have T := GlobalTheory.T.nilpotent_identity_morphism_compat (Fact.out : l.Prime).ne_zero (l_nil r n) m rfl rfl U Q Q' rfl rfl h ha hb j
  refine tens_change (A := AW r) (Ideal.Quotient.mk _) ((base l).cris n) (cris_surjective n) (fun w => rfl)
    Ideal.Quotient.mk_surjective ((l : WittVector l r.k) ^ n)
    (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)) ?_
    ((toQ Q (Ideal.Quotient.mk _)).pull j) (toQ_pull_bijective Q _ hQ j)
    ((toQ Q' ((base l).cris n)).pull j).toAddMonoidHom (toQ_pull_bijective Q' _ hQ' j)
    _ _ ?_ T
  · intro a h0
    obtain ⟨b, hb'⟩ := cris_ker n a h0
    refine ⟨b, hb'.trans ?_⟩
    change _ = r.w _ * b
    rw [map_pow, map_natCast]
  · intro a y
    have key := sqC_toQ m Q Q' h (Ideal.Quotient.mk _) ((base l).cris n) r.w (Mid.wn_mk r n) ((base l).cris n a)
      (ha _) (hb _) j y
    exact (pull_comm r M j n Q' a y).trans key.symm

end GlobalTheory.CompanionTheory.BcAcris
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothModelTensorWittComparisonStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.smooth_model_tensor_witt_comparison : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K), M.Sm → ∀ j n, Tens (WittVector l r.k) (N := fun _ : Unit => AW r) (M := fun _ => (Wc.HS l (B.schFn M.p) r.ρ j).M n) (M' := Mid.HM r M n j) fun _ a y => idA r a • bWL r M n j y := by
  first | exact @GlobalTheory.CompanionTheory.BcAcris.bc_tens | exact GlobalTheory.CompanionTheory.BcAcris.bc_tens | (intros; apply GlobalTheory.CompanionTheory.BcAcris.bc_tens <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.BcTens

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg

namespace CrystallineSemistableComparison.Pb

theorem bc_tens : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K), M.Sm →
    ∀ j n, Tens (WittVector l r.k) (N := fun _ : Unit => AW r) (M := fun _ => (HSW r M j).M n) (M' := Mid.HM r M n j)
      fun _ a y => idA r a • bW r M n j y := fun r M hM j n => GlobalTheory.T.smooth_model_tensor_witt_comparison r M hM j n

end CrystallineSemistableComparison.Pb
end
end
end
