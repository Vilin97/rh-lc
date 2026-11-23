module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.JoinType
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothColRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalFixedTensorStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfFiniteLengthSubquotients
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfProductsStatement
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import GroundTheory.LocalFields.PadicLogSeries

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LinearIndependentEigenvectors

section

@[expose] public section

theorem UpperTheory.Reformulated.B.LinearIndependentEigenvectors.li_eig :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] {Ξ P : Type}
    (T : P → V →ₗ[ℂ] V) (ev : Ξ → P → ℂ),
    Function.Injective ev →
      ∀ (v : Ξ → V),
        (∀ (ξ : Ξ), v ξ ≠ (0 : V)) → (∀ (ξ : Ξ) (p : P), (T p : V → V) (v ξ) = ev ξ p • v ξ) → LinearIndependent ℂ v := by
  intro V _ _ Ξ P T ev hinj v hv hT
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => intro g _ i hi; simp at hi
  | insert a s ha ih =>
    intro g hg
    rw [Finset.sum_insert ha] at hg
    have hs : ∀ i ∈ s, g i = 0 := by
      intro i hi
      have hne : ev i ≠ ev a := fun h => ha (hinj h ▸ hi)
      obtain ⟨p, hp⟩ := Function.ne_iff.mp hne
      have h1 : (g a * ev a p) • v a + ∑ j ∈ s, (g j * ev j p) • v j = 0 := by
        have h := congrArg (T p) hg

        simpa only [map_add (f := _), map_sum, map_smul, map_zero, hT, smul_smul] using h
      have h2 : (g a * ev a p) • v a + ∑ j ∈ s, (g j * ev a p) • v j = 0 := by
        have h := congrArg (fun x => ev a p • x) hg
        simpa only [smul_add, Finset.smul_sum, smul_zero, smul_smul, mul_comm] using h
      have h3 : ∑ j ∈ s, (g j * (ev j p - ev a p)) • v j = 0 := by
        simp only [mul_sub, sub_smul, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        exact add_left_cancel (h1.trans h2.symm)
      have h4 := ih (fun j => g j * (ev j p - ev a p)) h3 i hi
      exact (mul_eq_zero.mp h4).resolve_right (sub_ne_zero.mpr hp)
    have h0 : ∑ j ∈ s, g j • v j = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [hs j hj, zero_smul]
    rw [h0, add_zero] at hg
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact (smul_eq_zero.mp hg).resolve_right (hv _)
    · exact hs i hi
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.JeigRFinite

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


namespace UpperTheory.HeckeLevelFrameExistence.Ev

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Tail

section Gen

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem fix_map {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (K : Subgroup G) {v : V}
    (hv : v ∈ fixed ρ K) : φ.toLinearEquiv v ∈ fixed σ K := by
  intro h
  have h1 : ρ (h : G) v = (((1 : K →* ℂˣ) h : ℂˣ) : ℂ) • v := hv h
  rw [Representation.Equiv.toLinearEquiv_apply, ← φ.toIntertwiningMap.isIntertwining,
    ← Representation.Equiv.toLinearEquiv_apply, h1, map_smul]
  rfl

theorem hk_map {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (K : Subgroup G) (f : G → ℂ) (v : V) :
    φ.toLinearEquiv (hkG ρ K f v) = hkG σ K f (φ.toLinearEquiv v) := by
  unfold hkG
  refine (φ.toLinearEquiv.toAddEquiv.map_finsum (fun q : G ⧸ K => f q.out • ρ q.out v)).trans (finsum_congr fun q => ?_)
  change φ.toLinearEquiv (f q.out • ρ q.out v) = f q.out • σ q.out (φ.toLinearEquiv v)
  rw [map_smul, Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply,
    φ.toIntertwiningMap.isIntertwining]

theorem hk_lin (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ) : ∃ T : V →ₗ[ℂ] V, ∀ v, hkG ρ K f v = T v := by
  by_cases h : (Function.support fun q : G ⧸ K => f q.out).Finite
  · refine ⟨∑ q ∈ h.toFinset, f q.out • ρ q.out, fun v => ?_⟩
    unfold hkG
    rw [finsum_eq_sum_of_support_subset (s := h.toFinset), LinearMap.sum_apply]
    · rfl
    · intro q hq
      rw [Set.Finite.coe_toFinset]
      intro h0
      apply hq
      simp only [h0, zero_smul]
  · refine ⟨0, fun v => ?_⟩
    unfold hkG
    by_cases hv : v = 0
    · simp [hv]
    · refine finsum_of_infinite_support fun hfin => h (hfin.subset fun q hq h0 => ?_)
      rcases smul_eq_zero.1 h0 with h1 | h1
      · exact hq h1
      · apply hv
        have := congrArg (ρ q.out⁻¹) h1
        rwa [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this

theorem li_eig {Ξ P : Type} (T : P → V →ₗ[ℂ] V) (ev : Ξ → P → ℂ) (hinj : Function.Injective ev) (v : Ξ → V)
    (h0 : ∀ ξ, v ξ ≠ 0) (hv : ∀ ξ p, T p (v ξ) = ev ξ p • v ξ) : LinearIndependent ℂ v :=
  _root_.UpperTheory.Reformulated.B.LinearIndependentEigenvectors.li_eig T ev hinj v h0 hv

theorem fin_eig {Ξ P : Type} (U : Submodule ℂ V) [FiniteDimensional ℂ U] (T : P → V →ₗ[ℂ] V) (ev : Ξ → P → ℂ)
    (hinj : Function.Injective ev) : {ξ | ∃ v ∈ U, v ≠ 0 ∧ ∀ p, T p v = ev ξ p • v}.Finite := by
  choose v hU h0 hv using fun ξ : {ξ | ∃ v ∈ U, v ≠ 0 ∧ ∀ p, T p v = ev ξ p • v} => ξ.2
  have h := li_eig T (fun ξ : {ξ | ∃ v ∈ U, v ≠ 0 ∧ ∀ p, T p v = ev ξ p • v} => ev ξ.1)
    (hinj.comp Subtype.val_injective) v h0 hv
  have h' : LinearIndependent ℂ fun ξ => (⟨v ξ, hU ξ⟩ : U) := LinearIndependent.of_comp U.subtype h
  haveI := h'.finite_of_isNoetherian
  exact Set.toFinite _

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def JEigR {V : Type} [AddCommGroup V] [Module ℂ V] (w : Pl E) (ρ : Representation ℂ (GLw a w × GLw b w) V)
    (ϖ : (w.adicCompletion E)ˣ) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ) : Prop :=
  ∃ v ∈ fixed ρ (I2 a b w), v ≠ 0 ∧
    ∀ x y, Gap x → Gap y → hkG ρ (I2 a b w) (dc2 w ϖ x y) v = ev2 w ξa ξb x y • v

theorem jeigR_equiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {w : Pl E}
    {ρ : Representation ℂ (GLw a w × GLw b w) V} {σ : Representation ℂ (GLw a w × GLw b w) W} (φ : ρ.Equiv σ)
    {ϖ : (w.adicCompletion E)ˣ} {ξa : Fin a → ℂˣ} {ξb : Fin b → ℂˣ} (h : JEigR w ρ ϖ ξa ξb) :
    JEigR w σ ϖ ξa ξb := by
  obtain ⟨v, hv, hv0, he⟩ := h
  refine ⟨φ.toLinearEquiv v, fix_map φ _ hv, fun h0 => hv0 (φ.toLinearEquiv.injective (by rw [h0, map_zero])),
    fun x y hx hy => ?_⟩
  rw [← hk_map, he x y hx hy, map_smul]

theorem qh_ne_zero (w : Pl E) : qh w ≠ 0 := by
  unfold qh
  rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
  have hq : qV E w ≠ 0 := by
    exact Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero hq

theorem pw_ne_zero {m : ℕ} (y : Fin m → ℂˣ) (x : Fin m → ℤ) : pw y x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => Units.ne_zero _

theorem pw_shift {m : ℕ} (y : Fin m → ℂˣ) (x : Fin m → ℤ) (i : Fin m) :
    pw y (fun j => x j + if j = i then 1 else 0) = pw y x * (y i : ℂ) := by
  have key : ∀ j, (((y j ^ (x j + if j = i then 1 else 0) : ℂˣ)) : ℂ) =
      ((y j ^ x j : ℂˣ) : ℂ) * (if j = i then (y i : ℂ) else 1) := by
    intro j
    by_cases h : j = i
    · subst h
      simp [_root_.zpow_add]
    · simp [h]
  simp only [pw, key, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]

def g0 (m : ℕ) : Fin m → ℤ := fun i => 2 * ((m : ℤ) - (i : ℕ))

theorem gap0 (m : ℕ) : Gap (g0 m) := by
  intro i j hij
  have := Fin.lt_def.1 hij
  simp only [g0]
  omega

theorem gap1 (m : ℕ) (i : Fin m) : Gap (fun j => g0 m j + if j = i then 1 else 0) := by
  intro j l hjl
  have := Fin.lt_def.1 hjl
  simp only [g0]
  split_ifs <;> omega

theorem ev2_inj (w : Pl E) : Function.Injective (fun (ξ : (Fin a → ℂˣ) × (Fin b → ℂˣ))
    (p : {p : (Fin a → ℤ) × (Fin b → ℤ) // Gap p.1 ∧ Gap p.2}) => ev2 w ξ.1 ξ.2 p.1.1 p.1.2) := by
  rintro ⟨ξa, ξb⟩ ⟨ξa', ξb'⟩ h
  have hx : ∀ (x : Fin a → ℤ) (y : Fin b → ℤ), Gap x → Gap y → ev2 w ξa ξb x y = ev2 w ξa' ξb' x y :=
    fun x y hx hy => congrFun h ⟨(x, y), hx, hy⟩
  have hd : ∀ {N : ℕ} (x : Fin N → ℤ), dl w x ≠ 0 := fun _ => zpow_ne_zero _ (qh_ne_zero w)
  have h0 := hx (g0 a) (g0 b) (gap0 a) (gap0 b)
  simp only [ev2] at h0
  have hM : pw ξa (g0 a) * pw ξb (g0 b) = pw ξa' (g0 a) * pw ξb' (g0 b) := by
    refine mul_left_cancel₀ (mul_ne_zero (hd (g0 a)) (hd (g0 b))) ?_
    linear_combination h0
  have hM0 : pw ξa' (g0 a) * pw ξb' (g0 b) ≠ 0 := mul_ne_zero (pw_ne_zero _ _) (pw_ne_zero _ _)
  refine Prod.ext (funext fun i => Units.ext ?_) (funext fun i => Units.ext ?_)
  · have h1 := hx _ (g0 b) (gap1 a i) (gap0 b)
    simp only [ev2, pw_shift] at h1
    refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (hd (fun j => g0 a j + if j = i then 1 else 0))
      (hd (g0 b))) hM0) ?_
    linear_combination h1 - (dl w (fun j => g0 a j + if j = i then 1 else 0) * dl w (g0 b) * (ξa i : ℂ)) * hM
  · have h1 := hx (g0 a) _ (gap0 a) (gap1 b i)
    simp only [ev2, pw_shift] at h1
    refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (hd (g0 a))
      (hd (fun j => g0 b j + if j = i then 1 else 0))) hM0) ?_
    linear_combination h1 - (dl w (g0 a) * dl w (fun j => g0 b j + if j = i then 1 else 0) * (ξb i : ℂ)) * hM

theorem jeigR_finite {V : Type} [AddCommGroup V] [Module ℂ V] (w : Pl E)
    (ρ : Representation ℂ (GLw a w × GLw b w) V) (ϖ : (w.adicCompletion E)ˣ)
    [FiniteDimensional ℂ (fixed ρ (I2 a b w))] :
    {ξ : (Fin a → ℂˣ) × (Fin b → ℂˣ) | JEigR w ρ ϖ ξ.1 ξ.2}.Finite := by
  choose T hT using fun (p : {p : (Fin a → ℤ) × (Fin b → ℤ) // Gap p.1 ∧ Gap p.2}) =>
    hk_lin ρ (I2 a b w) (dc2 w ϖ p.1.1 p.1.2)
  refine (fin_eig (fixed ρ (I2 a b w)) T _ (ev2_inj w)).subset ?_
  rintro ⟨ξa, ξb⟩ ⟨v, hv, hv0, he⟩
  exact ⟨v, hv, hv0, fun p => by rw [← hT]; exact he _ _ p.2.1 p.2.2⟩

end UpperTheory.HeckeLevelFrameExistence.Ev

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.FrameExOf

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FX

open PositivityTheory.Rg.BcB.F

def FixFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Pre E n) (w : Pl E)
  (K : Subgroup (GLw n w)), IsOpen (K : Set (GLw n w)) → IsCompact (K : Set (GLw n w)) →
  FiniteDimensional ℂ ↥(fixed (Tail.prodAt D w) K)

end PositivityTheory.Rg.BcB.F.FX

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfFiniteLengthSubquotientsStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology

theorem _root_.GlobalTheory.T.admissible_of_finite_length_subquotients : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ → HasFiniteLength ρ → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), IsSubquotient σ ρ → σ.IsIrreducible → IsAdmissible σ) → IsAdmissible ρ := by
  first | exact @GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength | exact GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength | (intros; apply GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.FixFin

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX

open PositivityTheory.Rg.BcB.F

theorem fixFin : FixFin := by
  intro E _ _ _ n D w K hKo hKc
  have hs : IsSmooth (Tail.prodAt D w) := GlobalTheory.SmGL.isSmooth_parInd _ _
  have hfl : HasFiniteLength (Tail.prodAt D w) :=
    GlobalTheory.T.finite_length_of_products (w.adicCompletion E) (Fin n) (Fin D.c) (fun i => Fin (D.N i)) (GlobalTheory.SmGL.stdBlocks D.N D.h)
      (fun i => (D.σ i w).V) (fun i => (D.σ i w).ρ) (fun i => (D.σ i w).smooth) (fun i => (D.σ i w).irred)
  have hadm : IsAdmissible (Tail.prodAt D w) :=
    GlobalTheory.T.admissible_of_finite_length_subquotients (Tail.prodAt D w) hs hfl fun W _ _ σ hsub hirr =>
      PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top (w.adicCompletion E) n W σ (hsub.isSmooth hs) hirr
  exact hadm.2 K hKo hKc

end PositivityTheory.Rg.BcB.F.FX

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.EigFin

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical TensorProduct




attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem eig_abs (hII : IsoInv) {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (w : Pl E)
    (ϖ : (w.adicCompletion E)ˣ) {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (τ₁ : Representation ℂ (GLw a w) X) (τ₂ : Representation ℂ (GLw b w) Y) (h₁ : IsAdmissible τ₁) (h₂ : IsAdmissible τ₂) :
    ∃ (Z : Set ((Fin a → ℂˣ) × (Fin b → ℂˣ))) (m : ℕ), Z.Finite ∧
      ∀ (X' Y' : Type) [AddCommGroup X'] [Module ℂ X'] [AddCommGroup Y'] [Module ℂ Y']
        (ρ₁ : Representation ℂ (GLw a w) X') (ρ₂ : Representation ℂ (GLw b w) Y'), Nonempty (ρ₁.Equiv τ₁) → Nonempty (ρ₂.Equiv τ₂) →
        Module.finrank ℂ (fixed (GlobalTheory.SmGL.extTensor ρ₁ ρ₂) (I2 a b w)) ≤ m ∧
          ∀ ξa ξb, Ev.JEigR w (GlobalTheory.SmGL.extTensor ρ₁ ρ₂) ϖ ξa ξb → (ξa, ξb) ∈ Z := by
  haveI : FiniteDimensional ℂ (fixed (GlobalTheory.SmGL.extTensor τ₁ τ₂) (I2 a b w)) :=
    GlobalTheory.T.finiteDimensional_fixed_tensor _ _ _ _ τ₁ τ₂ _ _
      (h₁.2 _ (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori _ _) (GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori _ _))
      (h₂.2 _ (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori _ _) (GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori _ _))
  refine ⟨_, Module.finrank ℂ (fixed (GlobalTheory.SmGL.extTensor τ₁ τ₂) (I2 a b w)), Ev.jeigR_finite w (GlobalTheory.SmGL.extTensor τ₁ τ₂) ϖ, ?_⟩
  rintro X' Y' _ _ _ _ ρ₁ ρ₂ ⟨Φa⟩ ⟨Φb⟩
  have Φ : (GlobalTheory.SmGL.extTensor ρ₁ ρ₂).Equiv (GlobalTheory.SmGL.extTensor τ₁ τ₂) := GlobalTheory.SmGL.RowOneCell.extTensorEquiv Φa Φb
  exact ⟨(hII _ _ _ _ _ ⟨Φ⟩ (I2 a b w)).2.1.le, fun ξa ξb h => Ev.jeigR_equiv Φ h⟩

theorem admissible_hecke_word_product {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (P : Pre E n) (w : Pl E) :
    IsAdmissible (prodAt P w) :=
  ⟨GlobalTheory.SmGL.isSmooth_parInd _ _, fun K ho hc => fixFin E n P w K ho hc⟩

theorem eig_one (hII : IsoInv) (hSPr : StrictProd) {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
    (PA : Pre E a) (PB : Pre E b) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) :
    ∃ (Z : Set ((Fin a → ℂˣ) × (Fin b → ℂˣ))) (m : ℕ), Z.Finite ∧ ∀ (Pa : Pre E a) (Pb : Pre E b), Strict Pa PA → Strict Pb PB →
      Module.finrank ℂ (fixed (pairAt Pa Pb w) (I2 a b w)) ≤ m ∧ ∀ ξa ξb, JEig Pa Pb w ϖ ξa ξb → (ξa, ξb) ∈ Z := by
  obtain ⟨Z, m, hZ, h⟩ := eig_abs hII w ϖ (prodAt PA w) (prodAt PB w) (admissible_hecke_word_product PA w) (admissible_hecke_word_product PB w)
  refine ⟨Z, m, hZ, fun Pa Pb ha hb => ?_⟩
  have h' := h _ _ (prodAt Pa w) (prodAt Pb w) (hSPr E a Pa PA ha w) (hSPr E b Pb PB hb w)
  exact ⟨h'.1, fun ξa ξb hj => h'.2 ξa ξb hj⟩

end UpperTheory.HeckeLevelFrameExistence.CF

end
end
end
