module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFIntZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFStep
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFVert
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreDim
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfArithSystemStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.EqZeroOfEventuallyEval
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreBij
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreMult
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreSum
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFHoriz
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFIntZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFSecRed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFFibreSum
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFVert
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRatioAlgDep
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PfAtZero
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Contract
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixed
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixedField
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GeoNum
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageArithClosed
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivSupport
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumRatSection
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjContract

-- Source module: GroundTheory.HeightsAndTheta.Heights.Intersections.PPFSecRed

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

theorem PFSecRed.exists_form_not_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P n) (c : K → ℕ) :
    ∃ s : MRing ι, IsMultiHomog s c ∧ s ∉ P :=
  ⟨∏ k, (X ⟨k, (hP.2.1.2.2 k).choose⟩ : MRing ι) ^ c k, AvoidRing.isMultiHomog_coordProd _ c,
    AvoidRing.coordProd_not_mem hP.2.1.1 _ (fun k => (hP.2.1.2.2 k).choose_spec) c⟩

theorem PFSecRed.proof
    (hMult : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      MultilinStatement F ι)
    (hDim : FibreDimStatement) : PFSecRed.Statement := by
  intro I hI r hsec K _ ι _ K' _ ι' _ κ v P' d G J L L' N hv hP' hP hJ hL hL' hN

  let c : K' → ℕ := fun k => (-(N (Fin.last r)).a k).toNat
  let H : HermLine ι' := HermLine.sqMetric c
  let A : HermLine ι' := (N (Fin.last r)).tensor H
  have hHs : IsSmoothHerm H := isSmoothHerm_sqMetric c
  have hAs : IsSmoothHerm A := isSmoothHerm_tensor (hN _) hHs
  let a : K' → ℕ := fun k => ((N (Fin.last r)).a k + c k).toNat
  have hAa : ∀ k, A.a k = a k := by
    intro k
    show (N (Fin.last r)).a k + ((-(N (Fin.last r)).a k).toNat : ℤ) =
      (((N (Fin.last r)).a k + ((-(N (Fin.last r)).a k).toNat : ℤ)).toNat : ℤ)
    omega
  have hHa : ∀ k, H.a k = c k := fun k => rfl
  obtain ⟨sA, hsA, hsAP⟩ := PFSecRed.exists_form_not_mem hP' a
  obtain ⟨sH, hsH, hsHP⟩ := PFSecRed.exists_form_not_mem hP' c
  have hsnoc : ∀ B : HermLine ι', IsSmoothHerm B →
      ∀ j, IsSmoothHerm ((Fin.snoc (Fin.init N) B : Fin (r + 1) → HermLine ι') j) := by
    intro B hB j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa using hB
    · rw [Fin.snoc_castSucc]; exact hN _
  have e1 := hsec K ι K' ι' κ v P' d G J L L' (Fin.snoc (Fin.init N) A) sA a hv hP' hP hJ hL hL'
    (hsnoc A hAs) (by simpa using hAa) hsA hsAP
  have e2 := hsec K ι K' ι' κ v P' d G J L L' (Fin.snoc (Fin.init N) H) sH c hv hP' hP hJ hL hL'
    (hsnoc H hHs) (by simpa using hHa) hsH hsHP

  have hM : ∀ j, IsSmoothHerm (Fin.append L' (Fin.init N) j) := by
    intro j
    induction j using Fin.addCases with
    | left i => rw [Fin.append_left]; exact IsPullHerm.isSmoothHerm hv (hL' i) (hL i)
    | right i => rw [Fin.append_right]; exact hN _
  have hadd := (hI K' ι').2.1 P' (d + r) (Fin.append L' (Fin.init N)) (N (Fin.last r)) H hP' hM (hN _) hHs
  rw [← Fin.append_snoc, ← Fin.append_snoc, ← Fin.append_snoc, Fin.snoc_init_self] at hadd

  have hV := hDim K ι K' ι' κ v P' d (r + 1) G hv hP' hP
  have hJadd := hMult G.Φ (FibreBlock κ) (fibreIdx ι' κ) J hJ (fibreIdeal κ G) (r + 1)
    (Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ (N (Fin.last r)).a)) (Fin.last r)
    (fibreDeg κ (N (Fin.last r)).a) (fibreDeg κ H.a) hV
  simp only [Fin.update_snoc_last] at hJadd
  have f0 : (fun j => fibreDeg κ (N j).a) =
      Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ (N (Fin.last r)).a) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
  have f1 : (fun j => fibreDeg κ ((Fin.snoc (Fin.init N) A : Fin (r + 1) → HermLine ι') j).a) =
      Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ (N (Fin.last r)).a + fibreDeg κ H.a) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]; rfl
    · simp [Fin.init]
  have f2 : (fun j => fibreDeg κ ((Fin.snoc (Fin.init N) H : Fin (r + 1) → HermLine ι') j).a) =
      Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ H.a) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [Fin.init]
  rw [f1] at e1
  rw [f2] at e2
  have key : I K' ι' P' (d + (r + 1)) (Fin.append L' N) =
      I K' ι' P' (d + (r + 1)) (Fin.append L' (Fin.snoc (Fin.init N) A)) -
        I K' ι' P' (d + (r + 1)) (Fin.append L' (Fin.snoc (Fin.init N) H)) := by
    rw [eq_sub_iff_add_eq]
    exact hadd.symm
  rw [f0, key, e1, e2, hJadd]
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.Inter
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.Intersections.PPFStep

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem isSmoothHerm_of_isPullHerm' {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {A : HermLine ι} {A' : HermLine ι'} (hA : IsSmoothHerm A) (h : IsPullHerm κ v A A') :
    IsSmoothHerm A' := by
  have e : A'.h = A.h ∘ fun z' p => z' (v p) := funext h.2
  unfold IsSmoothHerm
  rw [e]
  refine hA.comp (contDiff_pi.2 fun p => contDiff_apply ℝ (fun _ => ℂ) (v p)).contDiffOn ?_
  intro z' hz'
  simp only [Set.mem_ofPred_eq] at hz' ⊢
  intro k
  obtain ⟨i', hi'⟩ := hz' (κ k)
  obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨pi, by rw [hp]; exact hi'⟩

theorem arithDim_lt_of_lt {P Q : Ideal (MRing ι)} {d d₀ : ℕ} (hP : IsArithVar P d) (hQ : IsArithVar Q d₀)
    (hle : P ≤ Q) (hne : P ≠ Q) : d₀ < d := by
  obtain ⟨f, hfQ, hfP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  have := hP.2.1.1
  have hf0 : Ideal.Quotient.mk P f ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hf0)
  have h2 : ringKrullDim (MRing ι ⧸ Q) ≤
      ringKrullDim ((MRing ι ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P f}) := by
    refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor hle) ?_) ?_
    · intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [map_mul, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hfQ, mul_zero]
    · intro z
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk P z), rfl⟩
  rw [hP.2.2.2] at h1
  rw [hQ.2.2.2] at h2
  have h3 : ((d₀ + Fintype.card K : ℕ) : WithBot ℕ∞) + 1 ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    le_trans (by gcongr) h1
  have h4 : ((d₀ + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast h3
  have h5 : d₀ + Fintype.card K + 1 ≤ d + Fintype.card K := by exact_mod_cast h4
  omega

end SlopeTestRemainingChoices

theorem PFStep.proof (hSec : PFSecRed.Statement) (hVert : PFVert.Statement) (hInt : PFIntZero.Statement)
    (hHor : PFHoriz.Statement) (hSum : PFFibreSum.Statement) (hIm : ImageArithStatement) (hCM : ContractMixedStatement) : PFStep.Statement := by
  intro I hI r hr
  refine hSec I hI r ?_
  intro K _ ι _ K' _ ι' _ κ v P' d G J L L' N s a hv hP' hP hJ hL hL' hN ha hs hsP
  have hP1 : IsArithVar P' (d + r + 1) := hP'
  have hsec : IsSectionOn P' (N (Fin.last r)) s := ⟨a, ha, hs, hsP⟩
  have hM : ∀ j, IsSmoothHerm (Fin.append L' (Fin.init N) j) := by
    intro j
    induction j using Fin.addCases with
    | left i => rw [Fin.append_left]; exact isSmoothHerm_of_isPullHerm' hv (hL i) (hL' i)
    | right i => rw [Fin.append_right]; exact hN _
  have hR := (hI K' ι').2.2 P' (d + r) (Fin.append L' (Fin.init N)) (N (Fin.last r)) s a hP1 hM (hN _) ha hs hsP
  rw [← Fin.append_snoc, Fin.snoc_init_self] at hR
  refine hR.trans ?_
  rw [recR_eq, hInt K ι K' ι' κ v P' d r L L' (Fin.init N) (N (Fin.last r)) s hv hP1 hP hL hL', sub_zero, cycR,
    ← hSum K ι K' ι' κ v P' d r G J N s a hv hP1 hP hJ ha hs hsP, finsum_mem_mul]
  refine finsum_mem_congr rfl fun W hW => ?_
  by_cases hh : IsHorizontal W
  · have hWa : IsArithVar W (d + r) := (divSuppArith K' ι' P' (d + r) (N (Fin.last r)) s W hP1 hsec hW).1 hh
    by_cases hd : imageZ v W = imageZ v P'
    · rw [if_pos hh, if_pos ⟨hh, hd⟩,
        hHor I r hr K ι K' ι' κ v P' W d G J L L' (Fin.init N) hv hWa hd hP hJ hL hL' (fun j => hN _)]
      exact (mul_assoc _ _ _).symm
    · rw [if_pos hh, if_neg (fun h => hd h.2), mul_zero, zero_mul]
      obtain ⟨d₀, -, hd₀⟩ := hIm K ι K' ι' κ v W (d + r) hP.1 hv hWa
      have hle : imageZ v P' ≤ imageZ v W := Ideal.comap_mono (le_sup_left.trans hW.1.1.2)
      rw [hCM I hI K ι K' ι' κ v W d₀ d r L L' (Fin.init N) hv hWa hd₀
        (arithDim_lt_of_lt hP hd₀ hle (Ne.symm hd)) hL hL' (fun j => hN _), mul_zero]
  · rw [if_neg hh, if_neg (fun h => hh h.1),
      hVert K ι K' ι' κ v P' d r L L' (Fin.init N) s a W hv hP1 hP hL' hs hsP hW hh]
    simp

end

end GroundTheory.Heights₂.Heights.Inter
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Multilin

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem Multilin.of_found
    (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u})
    (hEx : FieldNumbers.ExistsForm.Statement.{u})
    (hDiv : FieldNumbers.DivCycleSupport.Statement.{u})
    (hAdd : FieldNumbers.IntNumAdd.Statement.{u})
    {K : Type} [Fintype K] (F : Type u) [Field F] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.MultilinStatement F ι := by
  classical
  intro I hI V n L j a b hV
  have e : ∀ L' : Fin n → K → ℤ, I V n L' = intNum F V L' := fun L' =>
    Numbers.agree_of hBase hCut hEx hDiv I hI V n L' hV
  have hP : NumbersDVR.IsMultiProjPrime V := (Objects.isMultiProjPrime_iff V).mpr hV.1
  rw [e, e, e]
  exact hAdd F K ι V hP.multiHomog hP.relevant n (relDim_eq_of_ringKrullDim V n hV.2) L j a b

theorem Multilin.full {K : Type} [Fintype K] (F : Type u) [Field F] (ι : K → Type)
    [∀ k, Fintype (ι k)] : ReciprocityTheory.ChartRestriction.G.AI.I1.MultilinStatement F ι :=
  Multilin.of_found FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
    FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full FieldNumbers.IntNumAdd.full F ι

end GroundTheory.Heights₂.Heights.Targets
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystem

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv.ProjF

open GroundTheory.Heights₂.Heights

theorem pfIntZero : Inter.PFIntZero.Statement :=
  Inter.PFIntZero.proof (Inter.pointFormRank_holds.proof Inter.RatioAlgDep.proof)

theorem pfVert : Inter.PFVert.Statement :=
  Inter.PFVert.proof (by intros; exact geoNumStatement _) (by intros; exact Targets.ExistsUnique.full _ _)
    Targets.contractMixedField

theorem contractMixed : ContractMixedStatement :=
  Targets.ContractMixed.of_found imageArith Targets.Contract.pulledBackForms_topDensity_vanish
    (Inter.ProjectivePointVertical.proof (by intros; exact geoNumStatement _) (by intros; exact Targets.ExistsUnique.full _ _)
      (by intros; exact Targets.ProjContract.full _ _ _ _ _))
    pfIntZero pfVert

theorem pfStep : Inter.PFStep.Statement :=
  Inter.PFStep.proof (Inter.PFSecRed.proof (by intros; exact Targets.Multilin.full _ _) GlobalTheory.CompanionTheory.Ar.Giv.fibreDim) pfVert pfIntZero
    Inter.PFHoriz.proof (Inter.PFFibreSum.proof GlobalTheory.CompanionTheory.Ar.Giv.fibreDim Inter.PFFibreBij.proof Inter.PFFibreMult.proof)
    imageArith contractMixed

theorem projFormula : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFStatement := fun h =>
  Inter.PushforwardProjLineFlag.proof (GlobalTheory.T.generic_degree_of_arith_system h) pfStep

end GlobalTheory.CompanionTheory.Ar.Giv.ProjF
end
end
