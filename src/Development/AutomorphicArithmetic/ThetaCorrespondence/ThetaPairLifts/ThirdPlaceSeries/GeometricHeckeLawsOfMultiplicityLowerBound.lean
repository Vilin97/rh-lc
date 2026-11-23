module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfSumMulEmbeddingsEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicIntegerPointOfFiniteExtensionStatement
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
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
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EvLawsGenFrNonemptyComp
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientIntegralFramedPointCompleteFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitHeckePrimeOffLevelOfHeckeIndexPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTransferEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSumLeOfLe
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeGeometricOfMultiplicityLowerBound
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLinearRelationDescendBaseField

section

@[expose] public section

namespace GlobalTheory

theorem linRelation_descend : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (ι : Type) [Fintype ι]
    (V : Set (ι → K)) (c : ι → Ω), c ≠ 0 → (∀ v ∈ V, ∑ s, c s * algebraMap K Ω (v s) = 0) →
    ∃ d : ι → K, d ≠ 0 ∧ ∀ v ∈ V, ∑ s, d s * v s = 0 := by
  intro K Ω _ _ _ ι _ V c hc hV
  obtain ⟨s0, hs0⟩ : ∃ s, c s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (funext h)
  let b := Module.Basis.ofVectorSpace K Ω
  obtain ⟨j, hj⟩ : ∃ j, b.repr (c s0) j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hs0
    have h0 : b.repr (c s0) = 0 := Finsupp.ext h
    exact b.repr.map_eq_zero_iff.mp h0
  refine ⟨fun s => b.repr (c s) j, fun h => hj (congrFun h s0), fun v hv => ?_⟩
  have h2 : ∑ s, v s • c s = 0 := by
    rw [← hV v hv]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Algebra.smul_def, mul_comm]
  have h3 := congrArg (fun x => b.repr x j) h2

  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
  map_zero, Finsupp.coe_zero, Pi.zero_apply] at h3
  rw [← h3]
  exact Finset.sum_congr rfl fun s _ => mul_comm _ _

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLinearRelationDescendBaseFieldStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_linear_relation_descend_base_field : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (ι : Type) [Fintype ι] (V : Set (ι → K)) (c : ι → Ω), c ≠ 0 → (∀ v ∈ V, ∑ s, c s * algebraMap K Ω (v s) = 0) → ∃ d : ι → K, d ≠ 0 ∧ ∀ v ∈ V, ∑ s, d s * v s = 0 := by
  first | exact @GlobalTheory.linRelation_descend | exact GlobalTheory.linRelation_descend | (intros; apply GlobalTheory.linRelation_descend <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightSectionEqZeroOfVanishingFiniteExtensions

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg


set_option synthInstance.maxHeartbeats 200000 in
theorem sec_eq_zero_of_finite_values :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : Rul Xo c), h ∈ sec Xo c a n → (∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (y : FrPt Xo c L), evR Xo c h y = 0) → h = 0 := by
  intro E _ _ _ H Dw l Xo c a n h hh hv
  obtain ⟨hL, -, -, -⟩ := evLaws_genFr_nonempty_comp E H Dw l Xo c
  funext p y
  show h p y = 0

  have key : ∀ m : Ideal p.R, m.IsMaximal → h p y ∈ m := by
    intro m hm
    letI : Field (p.R ⧸ m) := Ideal.Quotient.field m
    haveI : Algebra.FiniteType c.F (p.R ⧸ m) := inferInstance
    haveI : FiniteDimensional c.F (p.R ⧸ m) := finite_of_finite_type_of_isJacobsonRing c.F (p.R ⧸ m)
    obtain ⟨w, hw⟩ := hL.bc p.R (p.R ⧸ m) (Ideal.Quotient.mkₐ c.F m) y
    have e := evR_eq_map_of_test_point hL hh p (Ideal.Quotient.mkₐ c.F m) y w hw
    rw [hv (p.R ⧸ m) w, Ideal.Quotient.mkₐ_eq_mk] at e
    exact Ideal.Quotient.eq_zero_iff_mem.mp e.symm

  have hj : h p y ∈ (⊥ : Ideal p.R).jacobson :=
    Ideal.mem_sInf.mpr fun J hJ => key J hJ.2
  have hrad : (⊥ : Ideal p.R).IsRadical := by
    intro x hx
    obtain ⟨k, hk⟩ := hx
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hk
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact p.rad ⟨k, hk⟩
  rw [IsJacobsonRing.out (inferInstance : IsJacobsonRing p.R) hrad] at hj
  exact hj

end GlobalTheory.Reg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightSectionEqZeroOfVanishingFiniteExtensionsStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem _root_.GlobalTheory.T.weightSection_eq_zero_of_vanishing_finite_extensions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : Rul Xo c), h ∈ sec Xo c a n → (∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (y : FrPt Xo c L), evR Xo c h y = 0) → h = 0 := by
  first | exact @GlobalTheory.Reg.sec_eq_zero_of_finite_values | exact GlobalTheory.Reg.sec_eq_zero_of_finite_values | (intros; apply GlobalTheory.Reg.sec_eq_zero_of_finite_values <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Detects

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

namespace GlobalTheory.PointsDetectAlg

theorem core {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ} [Fact p.Prime] (φ : c.F →+* ℂ_[p]) (hI : IntAll Xo c)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) {ι : Type} [Fintype ι] (g : ι → Rul Xo c) (hg : ∀ s, g s ∈ sec Xo c a n)
    (hli : LinearIndependent c.F g) (w : ι → ℂ_[p])
    (hw : ∀ z : PtC Xo c φ, ∑ s, w s * valC z.1 (g s) = 0) : w = 0 := by
  by_contra hw0
  let wP : ι → PAt φ := w
  have hrel : ∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (σ : L →ₐ[c.F] PAt φ)
      (y : FrPt Xo c L), ∑ s, wP s * σ (evR Xo c (g s) y) = 0 := by
    intro L _ _ _ σ y
    obtain ⟨z, u, hu, hz⟩ := GlobalTheory.T.exists_algebraicInteger_point_of_finiteExtension E H Dw l Xo c p φ hI L ((toCp φ).comp σ.toRingHom)
      (fun a => by simp [toCp_algebraMap]) y a n
    have h1 := hw z
    simp only [hz _ (hg _)] at h1
    have h2 : u * ∑ s, w s * toCp φ (σ (evR Xo c (g s) y)) = 0 := by
      rw [Finset.mul_sum, ← h1]
      refine Finset.sum_congr rfl fun s _ => ?_
      change u * (w s * toCp φ (σ _)) = w s * (u * toCp φ (σ _))
      ring
    exact (mul_eq_zero.1 h2).resolve_left hu
  let K := algebraicClosure c.F (PAt φ)
  let V : Set (ι → K) := {v | ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L) (_ : FiniteDimensional c.F L)
    (σ : L →ₐ[c.F] PAt φ) (y : FrPt Xo c L), ∀ s, (v s : PAt φ) = σ (evR Xo c (g s) y)}
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.T.exists_linear_relation_descend_base_field K (PAt φ) ι V wP hw0 (by
    rintro v ⟨L, _, _, _, σ, y, hv⟩
    simpa only [IntermediateField.algebraMap_apply, hv] using hrel L σ y)

  have hdrel : ∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (σ : L →ₐ[c.F] PAt φ)
      (y : FrPt Xo c L), ∑ s, (d s : PAt φ) * σ (evR Xo c (g s) y) = 0 := by
    intro L _ _ _ σ y
    have hmem : (fun s => (⟨σ (evR Xo c (g s) y), mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := c.F) (evR Xo c (g s) y)).algHom σ)⟩ : K)) ∈ V :=
      ⟨L, inferInstance, inferInstance, inferInstance, σ, y, fun s => rfl⟩
    have := congrArg (fun x : K => (x : PAt φ)) (hd _ hmem)
    simpa using this

  let K0 := IntermediateField.adjoin c.F (Set.range fun s => (d s : PAt φ))
  have hfin : FiniteDimensional c.F K0 := IntermediateField.finiteDimensional_adjoin (fun x hx => by
    obtain ⟨s, rfl⟩ := hx
    exact (mem_algebraicClosure_iff.1 (d s).2).isIntegral)
  letI : Module.Free c.F K0 := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact inferInstance
  let bs := Module.finBasis c.F K0
  let m := Module.finrank c.F K0
  let e : Fin m → PAt φ := fun t => (bs t : PAt φ)
  have he : LinearIndependent c.F e :=
    bs.linearIndependent.map' K0.val.toLinearMap (LinearMap.ker_eq_bot.2 K0.val.injective)
  have hea : ∀ t, IsAlgebraic c.F (e t) := fun t =>
    (Algebra.IsAlgebraic.isAlgebraic (R := c.F) (bs t)).algHom K0.val
  have dmem : ∀ s, (d s : PAt φ) ∈ K0 := fun s => IntermediateField.subset_adjoin _ _ ⟨s, rfl⟩
  let q : ι → Fin m → c.F := fun s t => bs.repr ⟨d s, dmem s⟩ t
  have hq : ∀ s, (d s : PAt φ) = ∑ t, algebraMap c.F (PAt φ) (q s t) * e t := by
    intro s
    have h := congrArg (fun x : K0 => (x : PAt φ)) (bs.sum_repr ⟨d s, dmem s⟩)
    simp only [IntermediateField.coe_sum, Algebra.smul_def] at h
    exact h.symm
  let hh : Fin m → Rul Xo c := fun t => ∑ s, q s t • g s
  have hhsec : ∀ t, hh t ∈ sec Xo c a n := fun t => Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (hg s)
  have hev : ∀ (L : Type) [Field L] [Algebra c.F L] (y : FrPt Xo c L) (t : Fin m),
      evR Xo c (hh t) y = ∑ s, algebraMap c.F L (q s t) * evR Xo c (g s) y := by
    intro L _ _ y t
    have := map_sum (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y)
      (fun s => q s t • g s) Finset.univ
    simp only [evalL, LinearMap.coe_mk, AddHom.coe_mk, evalAt_smul] at this
    exact this
  have hzero : ∀ t, hh t = 0 := by
    intro t
    refine GlobalTheory.T.weightSection_eq_zero_of_vanishing_finite_extensions E H Dw l Xo c a n (hh t) (hhsec t) fun L _ _ _ y => ?_
    have := GlobalTheory.T.eq_zero_of_sum_mul_embeddings_eq_zero' c.F (PAt φ) L m e he hea (fun t => evR Xo c (hh t) y) (fun σ => by
      rw [← hdrel L σ y]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hev, map_sum, map_mul, AlgHom.commutes, hq, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
      ring)
    exact congrFun this t
  have hq0 : ∀ s t, q s t = 0 := fun s t =>
    Fintype.linearIndependent_iff.1 hli (fun s => q s t) (hzero t) s
  apply hd0
  funext s
  apply Subtype.ext
  rw [hq s]
  simp [hq0]

end GlobalTheory.PointsDetectAlg

namespace GlobalTheory.PointsDetectAlg

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct

theorem detects : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), Detects YS fw iC b j := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j x hx
  let bV := Module.Basis.ofVectorSpace S.Ks (NX.FmK S ((j : ℕ) + 1))
  let B := Algebra.TensorProduct.basis (NX.KB S i b) bV
  let r := B.repr x
  let g : r.support → T0.R ((j : ℕ) + 1) := fun s => (cuspOf YS fw j (bV s) : T0.R ((j : ℕ) + 1))
  have hx' : x = ∑ s : r.support, r s • B s := by
    conv_lhs => rw [← B.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact (Finset.sum_coe_sort r.support (fun s => r s • B s)).symm
  have hval : ∀ z : Pts YS iC b ((j : ℕ) + 1), ∑ s : r.support, iC (r s) * valC z.1 (g s) = 0 := by
    intro z
    have h := hx z
    rw [hx'] at h
    have e : valAt YS fw j z.1 (∑ s : r.support, r s • B s) = ∑ s : r.support, valAt YS fw j z.1 (r s • B s) :=
      map_sum (valAt YS fw j z.1) (fun s : r.support => r s • B s) Finset.univ
    rw [← h]
    refine Eq.trans ?_ e.symm
    refine Finset.sum_congr rfl fun s _ => ?_
    refine Eq.trans ?_ (valAt_smul YS fw j z.1 (r s) (B s)).symm
    congr 1
    have hb : B s = ((1 : NX.KB S i b) ⊗ₜ[S.Ks] bV s : NX.KB S i b ⊗[S.Ks] _) :=
      Algebra.TensorProduct.basis_apply _ _
    refine Eq.trans ?_ (congrArg (valAt YS fw j z.1) hb).symm
    refine Eq.trans ?_ (valAt_tmul YS fw j z.1 1 (bV s)).symm
    exact (one_mul _).symm.trans (congrArg (· * _) (map_one iC).symm)
  have hli : LinearIndependent T0.Q.c.F g := by
    rw [Fintype.linearIndependent_iff]
    intro cf hcf s
    have h1 : ((cuspOf YS fw j (∑ t : r.support, (eKs YS).symm (cf t) • bV t) : Cu T0 κ j) : T0.R ((j : ℕ) + 1)) = 0 := by

      rw [← hcf, map_sum]
      simp only [cuspOf_smul, RingEquiv.apply_symm_apply]
      push_cast
      rfl
    have h2 : ∑ t : r.support, (eKs YS).symm (cf t) • bV t = 0 :=
      (cuspOf YS fw j).injective ((Subtype.ext h1).trans (map_zero _).symm)
    have h3 := Fintype.linearIndependent_iff.1 (bV.linearIndependent.comp _ Subtype.val_injective) _ h2 s
    simpa using h3
  have hI : IntAll (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c := fw.laws.intAll _ ⟨Nat.le_add_left _ _, j.2⟩
  have hw := core (embC YS iC b) hI (wtA (κ j)) (κ j).n g (fun s => cuspOf_mem_sec YS fw j _) hli
    (fun s => iC (r s)) hval
  have hr : ∀ s : r.support, r s = 0 := fun s => (map_eq_zero iC).1 (congrFun hw s)
  rw [hx']
  exact (Finset.sum_eq_zero fun s _ => by rw [hr s]; exact zero_smul _ _).trans rfl

end GlobalTheory.PointsDetectAlg

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricHeckeLawsOfMultiplicityLowerBound

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem GlobalTheory.HeightCounting.Up.geoLaws_at_levelB1_states : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (i : (Dof x).ntw.Tw), GlobalTheory.GeoTie.GeoLaws l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) := by
  intro hP hS hL
  have hH := _root_.GlobalTheory.T.heckeGeo_at_levelB1_states hP hS hL
  refine hH.trans (StepW.of_all fun K B f T w _ _ hw P x l i => ?_)
  have hint := (Dof x).nth.iC_int i
  refine ⟨?_, ?_, ?_, hw P x l i, ?_, ?_, ?_⟩
  · intro b j
    exact GlobalTheory.PointsDetectAlg.detects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hint b j
  · intro b j
    exact GlobalTheory.GeoTie.supDescent_side _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hint b j
  · intro b j f
    exact l.b.ser.sup i _ b _ _ f
  · intro b j
    exact GlobalTheory.T.heckeQuotient_integral_framed_point_complete_field hS.hkInt _ _ _ _ _ _ _ _ _ _ _ x.m.z.geo.κ x.m.z.geo.v₀ x.m.z.geo.fw _ _ hint b j
  · intro j k Pl hk
    obtain ⟨hHP, -⟩ := GlobalTheory.T.isSplitHeckePrimeOffLevel_of_heckeIndexPlace _ _ x.m.z.geo.fw.laws i k Pl hk
    obtain ⟨n, hn⟩ := GlobalTheory.HeckeCount.card_hkKer_const _ _ _ _ (x.m.z.core.Q.Xo ((j : ℕ) + 1)) x.m.z.core.Q.c Pl.asIdeal
      (GlobalTheory.GeoTie.charAt Pl) k (GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 hHP)
    exact ⟨n, fun b z => hn _ z.1⟩
  · intro j hj b
    exact l.b.ser.off i j b (fun h => hj (Finset.mem_Icc.2 h))
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.geoLaws_iC_at_levelB1_of_serN : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (i : (Dof x).ntw.Tw), GlobalTheory.GeoTie.GeoLaws l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.geoLaws_at_levelB1_states | exact _root_.GlobalTheory.HeightCounting.Up.geoLaws_at_levelB1_states | (intros; apply _root_.GlobalTheory.HeightCounting.Up.geoLaws_at_levelB1_states <;> assumption)
end
end
end
end
