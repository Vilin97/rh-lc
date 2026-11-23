module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMuSemidirectCyclicCoverOfMemGKinfCoeffs
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Mathlib.Algebra.CharP.Subring
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.RingTheory.LittleWedderburn
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.ZMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisQlEqGaloisKPrimeMulGaloisKinftyStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoversTameOfFrobeniusTeichmuller

section

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CoverGen

open GlobalTheory.KinfCover

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]

theorem covers_of_sigma_teich {k : GQ l} (s : ZMod a) (z : Fq l a) (hze : z ^ e = 1)
    (hs : ∀ w : Wq l a, Per.σA k (wA l a w) = wA l a ((sigma l a ^ s.val) w))
    (hz : ϖ.kummer k = Fq.val l a z) : ∃ γ : TameGal K l e a, Covers K t ϖ k γ := by
  let ζ : rootsOfUnity e K := rootsOfUnity.mkOfPowEq (algebraMap O K (t (WittVector.teichmuller l z))) (by
    rw [← map_pow, ← map_pow, ← map_pow, hze, map_one, map_one, map_one])
  refine ⟨⟨ζ, Multiplicative.ofAdd s⟩, fun f f' hf' => ?_⟩
  set m : ℕ := s.val with hmdef
  have hms : ((m : ℕ) : ZMod a) = s := ZMod.natCast_zmod_val s
  set c : ZMod a → O := fun τ => emb t τ (WittVector.teichmuller l z) with hc
  have hroot : ∀ τ, TameGal.root (⟨ζ, Multiplicative.ofAdd s⟩ : TameGal K l e a) τ =
      algebraMap O K (c τ) := fun τ => by
    have h1 : c τ = t (WittVector.teichmuller l z) ^ l ^ (-τ).val := by
      change t ((sigma l a ^ (-τ).val) (WittVector.teichmuller l z)) = _
      rw [sigma_pow_teich, map_pow]
    rw [h1, map_pow]
    change (((ζ ^ l ^ (-τ).val : rootsOfUnity e K) : Kˣ) : K) = _
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, rootsOfUnity.coe_mkOfPowEq]
  have hf'' : ∀ τ, f' τ = equivA O K (rescale (c τ) ((equivA O K).symm (f (τ - m)))) := fun τ => by
    refine Subtype.ext ?_
    rw [hf' τ, ringAct_apply, hroot, coe_equivA, ← rescale_map, ← coe_equivA, AlgEquiv.apply_symm_apply, hms]
    rfl
  have hRHS : ϖ.iTot t K f' =
      ∑ τ, idem (constA t) τ * ϖ.evO O (rescale (c τ) ((equivA O K).symm (f (τ - m)))) := by
    rw [PiSys.iTot, glue_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hf'' τ, PiSys.iA_equivA]

  rw [hRHS, PiSys.iTot, glue_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.addRight (m : ZMod a)) _ _ fun σ => ?_
  rw [map_mul, galOA_idem t hs, Equiv.coe_addRight, add_sub_cancel_right]
  change _ * galOA O k (ϖ.evO O ((equivA O K).symm (f σ))) = _
  rw [galOA_evO t ϖ z hz.symm, idem_mul_glue]

end GlobalTheory.CoverGen

theorem GlobalTheory.CoverGen.exists_covers_of_sigma_teich : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (k : GQ l) (s : ZMod a) (z : Fq l a), z ^ e = 1 → (∀ w : Wq l a, Per.σA k (wA l a w) = wA l a ((sigma l a ^ s.val) w)) → ϖ.kummer k = Fq.val l a z → ∃ γ : TameGal K l e a, Covers K t ϖ k γ :=
  fun _ _ _ _ _ _ _ K _ _ _ _ _ _ _ _ _ _ t ϖ _ s z hze hs hz => GlobalTheory.CoverGen.covers_of_sigma_teich t ϖ K s z hze hs hz
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoversTameOfFrobeniusTeichmullerStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_coversTame_of_frobenius_teichmuller : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (k : GQ l) (s : ZMod a) (z : Fq l a), z ^ e = 1 → (∀ w : Wq l a, Per.σA k (wA l a w) = wA l a ((sigma l a ^ s.val) w)) → ϖ.kummer k = Fq.val l a z → ∃ γ : TameGal K l e a, Covers K t ϖ k γ := by
  first | exact @GlobalTheory.CoverGen.exists_covers_of_sigma_teich | exact GlobalTheory.CoverGen.exists_covers_of_sigma_teich | (intros; apply GlobalTheory.CoverGen.exists_covers_of_sigma_teich <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomEqPowFrob

section

@[expose] public section

noncomputable section

namespace GlobalTheory.FrobeniusPower

open Polynomial

theorem ringHom_eq_pow_frob (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Finite F] [CharP F p]
    (φ : F →+* F) : ∃ m : ℕ, ∀ x : F, φ x = x ^ p ^ m := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let ψ : F →ₐ[ZMod p] F :=
    { φ with
      commutes' := fun r =>
        RingHom.congr_fun (RingHom.ext_zmod (φ.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) F)) r }
  have hinj : Function.Injective ψ := ψ.toRingHom.injective
  let σ : F ≃ₐ[ZMod p] F := AlgEquiv.ofBijective ψ ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F).2 σ
  refine ⟨n, fun x => ?_⟩
  have h1 : σ x = φ x := rfl
  rw [← h1, ← hn, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]

theorem finite_Fq (l : ℕ) [hl : Fact (Nat.Prime l)] (a : ℕ) [NeZero a] : Finite (GlobalTheory.BKReal.Fq l a) := by
  have hq : 1 < l ^ a := Nat.one_lt_pow (NeZero.ne a) hl.out.one_lt
  have hp : (X ^ (l ^ a) - X : (Formalism.BasicNotions.Loc.OCb l)[X]) ≠ 0 := by
    intro h
    have h2 := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f (l ^ a)) h
    simp only [coeff_sub, coeff_X_pow, coeff_X, if_true, coeff_zero, if_neg hq.ne] at h2
    simp at h2
  have hsub : ((GlobalTheory.BKReal.resSub l a : Subring (Formalism.BasicNotions.Loc.OCb l)) : Set (Formalism.BasicNotions.Loc.OCb l)) ⊆
      {x | (X ^ (l ^ a) - X : (Formalism.BasicNotions.Loc.OCb l)[X]).IsRoot x} := by
    intro x hx
    have hx' : iterateFrobenius (Formalism.BasicNotions.Loc.OCb l) l a x = x := hx
    rw [iterateFrobenius_def] at hx'
    show Polynomial.eval x (X ^ (l ^ a) - X) = 0
    rw [eval_sub, eval_pow, eval_X, hx', sub_self]
  have h : Finite ↥(GlobalTheory.BKReal.resSub l a) := ((Polynomial.finite_setOf_isRoot hp).subset hsub).to_subtype
  exact h

theorem main : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (a : ℕ) [inst : NeZero a]
    (φ : GlobalTheory.BKReal.Fq l a →+* GlobalTheory.BKReal.Fq l a), ∃ (m : ℕ), ∀ (x : GlobalTheory.BKReal.Fq l a),
      (φ : GlobalTheory.BKReal.Fq l a → GlobalTheory.BKReal.Fq l a) x = x ^ l ^ m := by
  intro l hl a _ φ
  haveI := finite_Fq l a
  haveI : IsDomain (GlobalTheory.BKReal.Fq l a) := inferInstanceAs (IsDomain ↥(GlobalTheory.BKReal.resSub l a))
  haveI : CharP (GlobalTheory.BKReal.Fq l a) l :=
    inferInstanceAs (CharP ↥(GlobalTheory.BKReal.resSub l a) l)
  letI : Field (GlobalTheory.BKReal.Fq l a) := (Finite.isDomain_to_isField _).toField
  exact ringHom_eq_pow_frob l (GlobalTheory.BKReal.Fq l a) φ

end GlobalTheory.FrobeniusPower
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionCyclotomicPower

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal

variable (l : ℕ) [hl : Fact l.Prime] (a : ℕ) [NeZero a]

def galFq (g : GQ l) : Fq l a →+* Fq l a :=
  ((Per.σF g).comp (Fq.val l a)).codRestrict (resSub l a) fun x => by
    rw [mem_resSub, RingHom.comp_apply, ← map_pow]
    exact congrArg (Per.σF g) (mem_resSub.1 x.2)

theorem val_galFq (g : GQ l) (x : Fq l a) : Fq.val l a (galFq l a g x) = Per.σF g (Fq.val l a x) := rfl

theorem exists_pow_eq (φ : Fq l a →+* Fq l a) : ∃ m : ℕ, ∀ x, φ x = x ^ l ^ m := by
  first
  | exact @_root_.GlobalTheory.FrobeniusPower.main
  | exact _root_.GlobalTheory.FrobeniusPower.main
  | (apply _root_.GlobalTheory.FrobeniusPower.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FrobeniusPower.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FrobeniusPower.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FrobeniusPower.main ..)
  | (intro h; exact _root_.GlobalTheory.FrobeniusPower.main h _ (fun _ => Iff.rfl))
  | exact _root_.GlobalTheory.FrobeniusPower.main ‹_› _ (fun _ => Iff.rfl)
  | (apply _root_.GlobalTheory.FrobeniusPower.main <;> first | assumption | exact fun _ => Iff.rfl)

theorem gal_wA_pow (g : GQ l) :
    ∃ s : ZMod a, ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ s.val) w) := by
  obtain ⟨m, hm⟩ := exists_pow_eq l a (galFq l a g)
  refine ⟨(m : ZMod a), fun w => ?_⟩
  rw [ZMod.val_natCast, ← pow_eq_pow_mod m (sigma_pow_eq_one l a)]
  refine WittVector.ext fun n => ?_
  rw [GlobalTheory.RingIface.sigA_coeff]
  change Per.σF g (Fq.val l a (w.coeff n)) = Fq.val l a (((sigma l a ^ m) w).coeff n)
  rw [coeff_sigma_pow, ← hm, val_galFq]

end GlobalTheory.BKReal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionCyclotomicPowerStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galois_action_cyclotomic_power : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : GQ l), ∃ s : ZMod a, ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ s.val) w) := by
  first | exact @GlobalTheory.BKReal.gal_wA_pow | exact GlobalTheory.BKReal.gal_wA_pow | (intros; apply GlobalTheory.BKReal.gal_wA_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerMemFqOfMemGKinf

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal

theorem kummer_mem_Fq_of_mem_GKinf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (ϖ : PiSys l e), e + 1 = l ^ a → ∀ k ∈ ϖ.GKinf, ∃ z : Fq l a, z ^ e = 1 ∧ ϖ.kummer k = Fq.val l a z := by
  intro l _ a e _ _ ϖ he k hk
  have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk
  have hr : ∀ n, ϖ.ratio k n ^ e = 1 := fun n => by
    have hmem : ϖ.seq n ^ e ∈ ϖ.Kinf := IntermediateField.subset_adjoin _ _ ⟨n, rfl⟩
    refine Subtype.ext ?_
    rw [SubmonoidClass.coe_pow, PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow, hfix _ hmem,
      div_self (pow_ne_zero _ (ϖ.seq_ne_zero n)), map_one]
    rfl
  have hK : ϖ.kummer k ^ e = 1 := Perfection.ext fun n => by
    erw [map_pow, map_one]
    change Ideal.Quotient.mk _ (ϖ.ratio k n) ^ e = 1
    rw [← map_pow, hr, map_one]
  have hmem : ϖ.kummer k ∈ resSub l a := by
    rw [mem_resSub, ← he, pow_succ, hK, one_mul]
  obtain ⟨z, hz⟩ : ∃ z : Fq l a, Fq.val l a z = ϖ.kummer k := ⟨(⟨ϖ.kummer k, hmem⟩ : ↥(resSub l a)), rfl⟩
  refine ⟨z, Fq.val_injective l a ?_, hz.symm⟩
  rw [map_pow, map_one, hz, hK]

end GlobalTheory.BKReal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerMemFqOfMemGKinfStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_root_of_unity_kummer_eq : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), e + 1 = l ^ a → ∀ k ∈ ϖ.GKinf, ∃ z : Fq l a, z ^ e = 1 ∧ ϖ.kummer k = Fq.val l a z := by
  first | exact @GlobalTheory.BKReal.kummer_mem_Fq_of_mem_GKinf | exact GlobalTheory.BKReal.kummer_mem_Fq_of_mem_GKinf | (intros; apply GlobalTheory.BKReal.kummer_mem_Fq_of_mem_GKinf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisDecompTameCoverAction

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TameCoverGen

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : BKGal.Gl l),
    ∃ h k : BKGal.Gl l, g = h * k ∧ BKGal.sQ l h ∈ GK (ϖ.field a) ∧
      ∃ γ : BK.TameGal K l e a, BKGal.Covers K t ϖ (BKGal.sQ l k) γ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ g
  have he : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := K)
  obtain ⟨h, hh, k, hk, hg⟩ :=
    GlobalTheory.T.galoisQl_eq_galoisKPrime_mul_galoisKinfty l a e ϖ he (BKGal.sQ l g)
  let h' : BKGal.Gl l :=
    ⟨h, GK_le (K := Formalism.MainNotions.ElementDenominator.qlExt l) (K' := ϖ.field a) bot_le hh⟩
  refine ⟨h', h'⁻¹ * g, by rw [mul_inv_cancel_left], hh, ?_⟩
  have hk' : BKGal.sQ l (h'⁻¹ * g) = k := by
    rw [map_mul, map_inv, show BKGal.sQ l g = h * k from hg]
    change h⁻¹ * (h * k) = k
    rw [inv_mul_cancel_left]
  rw [hk']
  obtain ⟨s, hs⟩ := GlobalTheory.T.galois_action_cyclotomic_power l a k
  obtain ⟨z, hz, hkz⟩ := GlobalTheory.T.exists_root_of_unity_kummer_eq l a e ϖ he k hk
  exact GlobalTheory.T.exists_coversTame_of_frobenius_teichmuller l a e O K t ϖ k s z hz hs hkz

end GlobalTheory.TameCoverGen
end
end
