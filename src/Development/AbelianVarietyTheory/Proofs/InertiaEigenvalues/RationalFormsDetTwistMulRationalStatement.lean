module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicCompletionIntegersLeIntAE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CurveOverOfRayIn
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicCharacterEqProdUnramifiedValueZpow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterPowEqOneFiniteIdelesOfOrderDvd
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldElementRelativeApproxCompletions
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsDetRootFinPartOne
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ExistsBaseRingOfConjugationFixedTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverFormsMulComponentFunction

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldElementRelativeApproxCompletionsStatement

section

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_field_element_relative_approx_completions : ∀ (L : Type) [Field L] [NumberField L] (R : Finset (HeightOneSpectrum (𝓞 L))) (z : ∀ P : HeightOneSpectrum (𝓞 L), P.adicCompletion L), (∀ P ∈ R, z P ≠ 0) → ∃ k : Lˣ, ∀ P ∈ R, Valued.v (z P - algebraMap L (P.adicCompletion L) (k : L)) ≤ WithZero.exp (-1 : ℤ) * Valued.v (z P) := by
  first | exact @GlobalTheory.WeakApprox.exists_units_approx | exact GlobalTheory.WeakApprox.exists_units_approx | (intros; apply GlobalTheory.WeakApprox.exists_units_approx <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalApprox

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistValues
variable {D : D7}

theorem pow_eq_one (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle) (hc : ChrEq δc δ) (n : ℕ)
    (hn : δ.OrderDvd n) (x : (AE D)ˣ) : δc x ^ n = 1 := by
  have hH : IsHeckeChar D (δc ^ n) := by
    refine ⟨?_, fun k => ?_⟩
    · exact (continuous_pow n).comp hc.1.1
    · rw [MonoidHom.pow_apply, hc.1.2 k, one_pow]
  have := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (δc ^ n) hH (fun y hy => by
    rw [MonoidHom.pow_apply]
    exact GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D δc δ hc n hn y hy) x
  rwa [MonoidHom.pow_apply] at this

theorem exists_pow_of_snd {R A B I : Type} [CommRing R] [CommRing A] [CommRing B] (e : R ≃+* A × B)
    (s : A ≃+* (I → ℂ)) (n : ℕ) (hn : 0 < n) (x : Rˣ) (hx : (e x).2 = 1) : ∃ V : Rˣ, x = V ^ n := by
  have hz : ∀ τ, s (e x).1 τ ≠ 0 := by
    intro τ h0
    have h1 : s (e x).1 * s (e ((x⁻¹ : Rˣ) : R)).1 = 1 := by
      rw [← map_mul, ← Prod.fst_mul, ← map_mul, Units.mul_inv, map_one, Prod.fst_one, map_one]
    have := congrFun h1 τ
    rw [Pi.mul_apply, h0, zero_mul, Pi.one_apply] at this
    exact zero_ne_one this
  choose w hw using fun τ => IsAlgClosed.exists_pow_nat_eq (s (e x).1 τ) hn
  have hw0 : ∀ τ, w τ ≠ 0 := fun τ h0 => hz τ (by rw [← hw τ, h0, zero_pow hn.ne'])
  let wi : I → ℂ := fun τ => (w τ)⁻¹
  have hwi : w * wi = 1 := funext fun τ => mul_inv_cancel₀ (hw0 τ)
  have hiw : wi * w = 1 := funext fun τ => inv_mul_cancel₀ (hw0 τ)
  let U : (A × B)ˣ := ⟨(s.symm w, 1), (s.symm wi, 1), by
      rw [Prod.mk_mul_mk, ← map_mul, hwi, map_one, mul_one]; rfl, by
      rw [Prod.mk_mul_mk, ← map_mul, hiw, map_one, mul_one]; rfl⟩
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom U, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.coe_map]
  change (x : R) = (e.symm (s.symm w, 1)) ^ n
  rw [← map_pow, Prod.pow_mk, one_pow, ← map_pow,
    show w ^ n = s (e x).1 from funext fun τ => by rw [Pi.pow_apply, hw τ], RingEquiv.symm_apply_apply, ← hx,
    Prod.mk.eta, RingEquiv.symm_apply_apply]

theorem eq_one_of_finPart (c : (AE D)ˣ →* Circle) (n : ℕ) (hn : 0 < n) (hpow : ∀ x, c x ^ n = 1) (x : (AE D)ˣ)
    (hx : finPart D (x : AE D) = 1) : c x = 1 := by
  obtain ⟨e, he, -, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  obtain ⟨V, hV⟩ := exists_pow_of_snd e (Formalism.IndefR.Eqv.splitEquiv D) n hn x ((he _).2.trans hx)
  rw [hV, map_pow, hpow]

theorem exists_global_approx : ∀ (L : Type) [Field L] [NumberField L] (R : Finset (HeightOneSpectrum (𝓞 L))) (z : ∀ P : HeightOneSpectrum (𝓞 L), P.adicCompletion L), (∀ P ∈ R, z P ≠ 0) → ∃ k : Lˣ, ∀ P ∈ R, Valued.v (z P - algebraMap L (P.adicCompletion L) (k : L)) ≤ WithZero.exp (-1 : ℤ) * Valued.v (z P) :=
  GlobalTheory.T.exists_field_element_relative_approx_completions



open Formalism.L2.Host in
theorem mem_of_infPart {k : Type} [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle)
    (hc : ChrEq δc δ) (n : ℕ) (hn : 0 < n) (hord : δ.OrderDvd n) (htame : ∀ v, δ.TameAt v) (hval : δ.ValuesIn 0 σ)
    (x : (AE D)ˣ) (hx : infPart D (x : AE D) = 1) : ((δc x : Circle) : ℂ) ∈ σ.fieldRange := by
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h4 δc δ hc
  have hev := GlobalTheory.HeckeSplit.eventually_unrAt δ.1 δ.2.1
  set Rm := (Filter.eventually_cofinite.1 hev).toFinset with hRmdef
  have hRm : ∀ P, P ∉ Rm → δ.UnrAt P := fun P hP => by
    by_contra h
    exact hP ((Set.Finite.mem_toFinset _).2 h)
  let zz : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ := Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x
  have hz0 : ∀ P, (zz : FiniteAdeleRing (𝓞 D.host.E) D.host.E) P ≠ 0 := (FiniteAdeleRing.isUnit_iff.1 zz.isUnit).1
  obtain ⟨k, hk⟩ := exists_global_approx D.host.E Rm (fun P => (zz : FiniteAdeleRing (𝓞 D.host.E) D.host.E) P)
    (fun P _ => hz0 P)
  let K : (AE D)ˣ := Units.map (incA D).toMonoidHom k
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  have e1 : δc x = δc (b (x * K⁻¹)) := by
    have : δc (x * K⁻¹) = δc x := by rw [map_mul, map_inv, hc.1.2 k, inv_one, mul_one]
    rw [← this]
    conv_lhs => rw [hab (x * K⁻¹)]
    rw [map_mul, eq_one_of_finPart δc n hn (pow_eq_one δ δc hc n hord) _ (ha _).2, one_mul]
  set y := b (x * K⁻¹) with hydef
  have hy : infPart D (y : AE D) = 1 := (hb _).1
  have hyP : ∀ P, ι (finPart D (y : AE D)) P =
      (zz : FiniteAdeleRing (𝓞 D.host.E) D.host.E) P * algebraMap D.host.E _ ((k⁻¹ : D.host.Eˣ) : D.host.E) := by
    intro P
    rw [(hb _).2, Units.val_mul, map_mul, map_mul]
    have : ((K⁻¹ : (AE D)ˣ) : AE D) = incA D ((k⁻¹ : D.host.Eˣ) : D.host.E) := rfl
    rw [this]
    show _ * ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((k⁻¹ : D.host.Eˣ) : D.host.E)) P = _
    rw [h1]
    rfl

  let yy : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ := Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom y
  have hy0 : ∀ P, ι (finPart D (y : AE D)) P ≠ 0 := (FiniteAdeleRing.isUnit_iff.1 yy.isUnit).1
  obtain ⟨S0, -, -, hS0⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN yy
  choose kk hkk using fun P => GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P _ (hy0 P)
  have key := hprod y hy (S0 ∪ Rm) kk (fun P _ => ⟨(hkk P).1, (hkk P).2.1⟩)
    (fun P hP => hS0 P fun h => hP (Finset.mem_union_left _ h))
  rw [e1, key]
  refine prod_mem fun P _ => ?_
  have hva : ∀ t : D.host.E, Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) t) = P.valuation D.host.E t :=
    fun t => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P t
  by_cases hR : P ∈ Rm
  ·
    set zP := (zz : FiniteAdeleRing (𝓞 D.host.E) D.host.E) P with hzP
    have hk0 : Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) ≠ 0 := by
      rw [hva]; exact (Valuation.ne_zero_iff _).2 k.ne_zero
    have hlt : WithZero.exp (-1 : ℤ) < 1 := by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    have hzv : Valued.v zP = Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) := by
      refine (Valuation.map_eq_of_sub_lt _ ?_).symm
      rw [Valuation.map_sub_swap]
      exact (hk P hR).trans_lt (mul_lt_of_lt_one_left (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (hz0 P))) hlt)
    have hkinv : algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E) *
        algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hkv' : Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E)) *
        Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) = 1 := by
      rw [← map_mul, hkinv, map_one]
    have hyv : Valued.v (ι (finPart D (y : AE D)) P) = 1 := by
      rw [hyP, map_mul, mul_comm, hzv]; exact hkv'
    have hy1 : Valued.v (ι (finPart D (y : AE D)) P - 1) ≤ WithZero.exp (-1 : ℤ) := by
      have : ι (finPart D (y : AE D)) P - 1 = (zP - algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) *
          algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E) := by
        rw [hyP, sub_mul, mul_comm (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)), hkinv]
      rw [this, map_mul]
      calc Valued.v (zP - _) * Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E))
          ≤ WithZero.exp (-1 : ℤ) * Valued.v zP *
            Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E)) :=
            mul_le_mul' (hk P hR) le_rfl
        _ = WithZero.exp (-1 : ℤ) := by rw [mul_assoc, hzv, mul_comm (Valued.v (algebraMap _ _ (k : D.host.E))), hkv', mul_one]
    obtain ⟨q1, q2, q3⟩ := hkk P
    have hq : Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (kk P : D.host.E)) = 1 := by
      rw [hva, ← q1, hyv]
    have hq1 : Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (kk P : D.host.E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
      have e2 : algebraMap D.host.E (P.adicCompletion D.host.E) (kk P : D.host.E) - 1 =
          (ι (finPart D (y : AE D)) P - 1) - (ι (finPart D (y : AE D)) P - algebraMap D.host.E _ (kk P : D.host.E)) := by ring
      rw [e2]
      refine (Valuation.map_sub _ _ _).trans (max_le hy1 ?_)
      rw [← hva, hq, mul_one] at q3
      simpa using q3
    have ht := htame P (Formalism.L2.Host.atFin P (kk P)) hq hq1
    have : δ.locK P (kk P) = 1 := ht
    rw [this, Units.val_one]
    exact one_mem _
  ·
    have hu := hRm P hR
    have hkv0 : P.valuation D.host.E (kk P : D.host.E) ≠ 0 := (Valuation.ne_zero_iff _).2 (kk P).ne_zero
    have hm : P.valuation D.host.E (kk P : D.host.E) = WithZero.exp (-(-WithZero.log (P.valuation D.host.E (kk P : D.host.E)))) := by
      rw [neg_neg, WithZero.exp_log hkv0]
    rw [GlobalTheory.CharUnramVal.locK_eq_val_zpow δ P hu (kk P) _ hm, Units.val_zpow_eq_zpow_val]
    refine zpow_mem ?_ _
    obtain ⟨t, ht⟩ := hval P hu
    refine ⟨t, ht.trans ?_⟩
    simp [Formalism.L2.Host.HChar.valTw]

theorem mem_fieldRange : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ g, dd g ∈ σ.fieldRange := by
  intro D V pd k _ σ δ δc hT dd hdd g
  obtain ⟨hc, ⟨n, hn, hord⟩, -, htame, -, hval⟩ := hT
  have key : ∀ x : (AE D)ˣ, ((δc x : Circle) : ℂ) ∈ σ.fieldRange := by
    intro x
    obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
    rw [hab x, map_mul, eq_one_of_finPart δc n hn (pow_eq_one δ δc hc n hord) _ (ha x).2, one_mul]
    exact mem_of_infPart σ δ δc hc n hn hord htame hval _ (hb x).1
  rcases hdd with ⟨hex, hv⟩ | ⟨hex, hv⟩
  · obtain ⟨x, hx⟩ := hex g
    rw [hv g x hx]
    exact key x
  · obtain ⟨x, hx⟩ := hex g
    rw [hv g x hx, MonoidHom.inv_apply, Circle.coe_inv]
    exact inv_mem (key x)

end GlobalTheory.TwistValues
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrincipalRoot

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistLeft

theorem exists_principal_root {D : D7} (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) :
    ∃ e : D.host.Eˣ, IsDetRoot V γ (Units.map (incA D).toMonoidHom e) := by
  obtain ⟨γ₀, -, h0⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  have hdet : ((matHom V γ).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det =
      incA D γ₀.1.det := by
    rw [← GlobalTheory.DetRootRows.det_bc, h0]; rfl
  generalize γ₀.1.det = d at hdet
  have hc : ∀ e : D.host.E, cA D (incA D e) = incA D (star e) := fun e => rfl
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  have hn : star d * d = 1 := by
    have := det_conj_mul V γ
    apply GlobalTheory.DetRootRows.inclR_injective (F := D.host.F) (AF D.host.F)
    rw [map_mul, map_one, ← hc, ← hdet]
    exact this
  obtain ⟨e, he0, he⟩ : ∃ e : D.host.E, e ≠ 0 ∧ e = d * star e := by
    by_cases hd : d = -1
    · obtain ⟨a, ha⟩ := GlobalTheory.RecDict.cmData_sig_ne_id D.sp.cm
      refine ⟨a - star a, sub_ne_zero.2 (Ne.symm ha), ?_⟩
      rw [hd, star_sub, star_star]; ring
    · refine ⟨1 + d, fun h => hd (by linear_combination h), ?_⟩
      rw [star_add, star_one]; linear_combination -hn
  refine ⟨Units.mk0 e he0, ?_⟩
  unfold IsDetRoot
  rw [hdet]
  show incA D e = incA D d * cA D (incA D e)
  rw [hc, ← map_mul, ← he]

theorem muVal_left {D : D7} (V : HSp D) (χ : (AE D)ˣ →* Circle)
    (hE : ∀ x : D.host.Eˣ, χ (Units.map (incA D).toMonoidHom x) = 1) (mu : GA D V → ℂ) (hmu : MuVal V χ mu)
    (γ : GA D V) (hγ : γ ∈ GQ V) (h : GA D V) : mu (γ * h) = mu h := by
  obtain ⟨x, hx⟩ := hmu.1 h
  obtain ⟨e, he⟩ := exists_principal_root V γ hγ
  rw [hmu.2 _ _ (detRootMul_holds V γ h _ x he hx), hmu.2 h x hx, map_mul, hE e, one_mul]

theorem twist_left : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E)
    (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) →
    ∀ γ ∈ GQ V, ∀ h : GA D V, dd (γ * h) = dd h := by
  intro D V pd k _ σ δ δc ht dd hdd γ hγ h
  have hE : ∀ x : D.host.Eˣ, δc (Units.map (incA D).toMonoidHom x) = 1 := ht.1.1.2
  rcases hdd with hm | hm
  · exact muVal_left V δc hE dd hm γ hγ h
  · exact muVal_left V δc⁻¹ (fun x => by rw [MonoidHom.inv_apply, hE x, inv_one]) dd hm γ hγ h

end GlobalTheory.TwistLeft
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalFormsDetTwistMulRational

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistRat

theorem curveOver_of_rayIn : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ (N : ℕ), 3 ≤ N → ∀ (Fc : IntermediateField ℚ ℂ) (σ : Fc →+* ℂ), RayIn D N σ.fieldRange → GlobalTheory.CompRat.CurveOver Q.H Fc N := GlobalTheory.TwistRat.Field.curveOver_of_rayIn

theorem twist_mem_fieldRange : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ g, dd g ∈ σ.fieldRange := GlobalTheory.TwistValues.mem_fieldRange

theorem twist_eq_of_finHom : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ h h' : GA D V, finHom V h = finHom V h' → dd h = dd h' := GlobalTheory.TwistFinPart.twist_eq_of_finHom

theorem twist_mul_left : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ γ ∈ GQ V, ∀ h : GA D V, dd (γ * h) = dd h := GlobalTheory.TwistLeft.twist_left

theorem twist_mul_right : ∀ (D : D7) (V : HSp D) (M pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsAuxiliarySplitSquarefreeLevel D M pd → IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ u : GA D V, Formalism.L2.Pj.gLat V u = ↑(Formalism.L2.Pj.latHat V) → GlobalTheory.Member.FinCong V (M * pd) u → ∀ h : GA D V, dd (h * u) = dd h := GlobalTheory.TwistRat.Right.dd_mul_right

theorem muVal_cast {D : D7} {V W : HSp D} (h : V = W) (χ : (AE D)ˣ →* Circle) (dd : GA D W → ℂ) (hd : MuVal W χ dd) :
    MuVal V χ (castDict h.symm dd) := by
  subst h; exact hd

theorem castDict_mul {D : D7} {V W : HSp D} (h : V = W) (dd : GA D W → ℂ) (φ : GA D V → ℂ) :
    castDict h (fun g => castDict h.symm dd g * φ g) = fun g => dd g * castDict h φ g := by
  subst h; rfl

theorem isRat_twist : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D)
        (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
      ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GoodCover T R i C (κ i).n →
      ∀ (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist C.d.pd C.σ₂ δ δc →
      ∀ dd : GA D (Wc D i) → ℂ, MuVal (Wc D i) δc dd ∨ MuVal (Wc D i) δc⁻¹ dd →
      ∀ φ : GA D (Wc D i) → ℂ, IsRat T i hV C (κ i) φ → IsRat T i hV C (κ i) (fun g => dd g * φ g) := by
  intro hRF D G _ _ Pl0 T0 A T _ R F κ v₀ hL hLev hGrp hFam hMod hThP hTie i hV hFP gramR c0R c0L hFT u hu C hGC δ δc hTw dd hdd φ hφ
  obtain ⟨hU, -, hAux, -, hRay⟩ := hGC
  obtain ⟨φ', hφ', rfl⟩ := hφ
  have hlev : C.d.l₂.M = T.Q.l.M * C.d.pd := hU.1.2.1
  have hpd : 0 < C.d.pd := hAux.1.pos
  have hN3 : 3 ≤ T.Q.l.M * C.d.pd := le_trans T.Q.l.three_le (Nat.le_mul_of_pos_right _ hpd)
  have hcurve : GlobalTheory.CompRat.CurveOver T.Q.H C.d.c₂.F (T.Q.l.M * C.d.pd) :=
    curveOver_of_rayIn hRF D T.Q hL.pins.1 _ hN3 C.d.c₂.F C.σ₂ hRay
  set dd' : GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ := castDict hV.symm dd with hdd'
  have hdd2 : MuVal _ δc dd' ∨ MuVal _ δc⁻¹ dd' :=
    hdd.imp (muVal_cast hV δc dd) (muVal_cast hV δc⁻¹ dd)
  have hval := twist_mem_fieldRange D _ C.d.pd _ C.σ₂ δ δc hTw dd' hdd2
  choose w hw using fun g => RingHom.mem_fieldRange.1 (hval g)
  have hinj : ∀ g g', dd' g = dd' g' → w g = w g' := fun g g' h => C.σ₂.injective (by rw [hw, hw, h])
  have key := (GlobalTheory.CoverComp.forms_mul_comp D T hL ((i : ℕ) + 1) ⟨Nat.succ_pos _, i.2⟩ T.σ₀ rfl C hU
    (T.Q.l.M * C.d.pd) (Nat.mul_pos (by have := T.Q.l.three_le; omega) hpd) (by rw [hlev]) (Or.inr hcurve) w
    (fun h h' hh => hinj _ _ (twist_eq_of_finHom D _ C.d.pd _ C.σ₂ δ δc hTw dd' hdd2 h h' hh))
    (fun γ hγ h => hinj _ _ (twist_mul_left D _ C.d.pd _ C.σ₂ δ δc hTw dd' hdd2 γ hγ h))
    (fun u hu1 hu2 h => hinj _ _ (twist_mul_right D _ T.Q.l.M C.d.pd _ C.σ₂ δ δc hAux hTw dd' hdd2 u hu1 (hlev ▸ hu2) h))
    (wtA (κ i)) (κ i).n).1 φ' hφ'
  refine ⟨_, key, ?_⟩
  simp only [hw]
  exact castDict_mul hV dd φ'

end GlobalTheory.TwistRat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalFormsDetTwistMulRationalStatement

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.rationalForms_detTwist_mul_rational : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D)
        (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
      ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GoodCover T R i C (κ i).n →
      ∀ (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist C.d.pd C.σ₂ δ δc →
      ∀ dd : GA D (Wc D i) → ℂ, MuVal (Wc D i) δc dd ∨ MuVal (Wc D i) δc⁻¹ dd →
      ∀ φ : GA D (Wc D i) → ℂ, IsRat T i hV C (κ i) φ → IsRat T i hV C (κ i) (fun g => dd g * φ g) := by
  first | exact @GlobalTheory.TwistRat.isRat_twist | exact GlobalTheory.TwistRat.isRat_twist | (intros; apply GlobalTheory.TwistRat.isRat_twist <;> assumption)
end
end
end
