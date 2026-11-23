module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreIncomp
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocResidueDeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PContractRelDimLe
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForward
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Assembly
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreDivSupp
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreOverFinite
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocMaxIdeals
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocResidueFrac
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StChartScalingIndep
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocResidueAdjoin
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocRankAdjoin
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
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocResidueFibreDim
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartRankAdjoin
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreDivSupp
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreTail
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogIdealChain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPCProof
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueFrac
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFnDegRelDeg
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjDeg
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.NumericalSegre

-- Source module: GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueAdjoin

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem SemilocResidueAdjoin.isMultiHomogIdeal_map {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {R : Type} [CommRing R] (φ : ℤ →+* R) {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    IsMultiHomogIdeal (P.map (MvPolynomial.map φ : MRing ι →+* MRingOver R ι)) := by
  obtain ⟨S, hS, rfl⟩ := hP
  refine ⟨MvPolynomial.map φ '' S, ?_, Ideal.map_span _ _⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, fun m hm => ha m (MvPolynomial.support_map_subset _ _ hm)⟩

theorem SemilocResidueAdjoin.exists_int_mul {σ F : Type} [Field F]
    (hF : ∀ c : F, ∃ a b : ℤ, (b : F) ≠ 0 ∧ c = a / b) (f : MvPolynomial σ F) :
    ∃ (g : MvPolynomial σ ℤ) (d : ℤ), (d : F) ≠ 0 ∧ C (d : F) * f = MvPolynomial.map (Int.castRingHom F) g := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    obtain ⟨a, b, hb, rfl⟩ := hF c
    refine ⟨C a, b, hb, ?_⟩
    rw [map_C, ← C_mul, mul_div_cancel₀ _ hb, eq_intCast]
  | add f g hf hg =>
    obtain ⟨g₁, d₁, h₁, e₁⟩ := hf
    obtain ⟨g₂, d₂, h₂, e₂⟩ := hg
    refine ⟨C d₂ * g₁ + C d₁ * g₂, d₁ * d₂, by push_cast; exact mul_ne_zero h₁ h₂, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_C, map_C, ← e₁, ← e₂, eq_intCast, eq_intCast]
    push_cast
    rw [C_mul]
    ring
  | mul_X f q hf =>
    obtain ⟨g, d, h, e⟩ := hf
    exact ⟨g * X q, d, h, by rw [map_mul, map_X, ← e, mul_assoc]⟩

theorem SemilocResidueAdjoin.isMultiHomogIdeal_ker {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (hF : ∀ c : F, ∃ a b : ℤ, (b : F) ≠ 0 ∧ c = a / b)
    (x : (Σ k, ι k) → Ω) (hmh : IsMultiHomogIdeal (RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω))) :
    IsMultiHomogIdeal (RingHom.ker (aeval x : MRingOver F ι →ₐ[F] Ω)) := by
  have e : ∀ g : MRing ι, aeval x (MvPolynomial.map (Int.castRingHom F) g) = aeval x g := fun g => by
    rw [← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
  suffices h : RingHom.ker (aeval x : MRingOver F ι →ₐ[F] Ω) =
      (RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω)).map (MvPolynomial.map (Int.castRingHom F)) by
    rw [h]
    exact SemilocResidueAdjoin.isMultiHomogIdeal_map _ hmh
  refine le_antisymm (fun f hf => ?_) (Ideal.map_le_iff_le_comap.2 fun g hg => ?_)
  · obtain ⟨g, d, hd, hg⟩ := SemilocResidueAdjoin.exists_int_mul hF f
    have hg0 : g ∈ RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) := by
      rw [RingHom.mem_ker, ← e, ← hg, map_mul, (RingHom.mem_ker).1 hf, mul_zero]
    have hf' : f = C (d : F)⁻¹ * MvPolynomial.map (Int.castRingHom F) g := by
      rw [← hg, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hd, C_1, one_mul]
    rw [hf']
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hg0)
  · rw [Ideal.mem_comap, RingHom.mem_ker, e]
    exact hg

theorem SemilocResidueAdjoin.proof (hR : SemilocResidueFrac.Statement) (hT : ChartScalingIndep.Statement) :
    SemilocResidueAdjoin.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hZ hs hsP hW W' hW' _ G' i' hi'
  let F := (⊥ : Subfield G'.Φ)
  have hF : ∀ c : F, ∃ a b : ℤ, (b : F) ≠ 0 ∧ c = a / b := primeSubfield_exists_div
  have hx : ∀ k', G'.x' ⟨k', i' k'⟩ ≠ 0 := fun k' h => hi' k' (by
    rw [← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_X, h])
  have hmh := SemilocResidueAdjoin.isMultiHomogIdeal_ker hF G'.x' (by rw [G'.genericFibre_ker_target]; exact hW'.1.2.1)
  rw [hR K ι K' ι' κ v P' n s α W hv hP' hZ hs hsP hW W' hW' G' i' hi' F hF,
    SemilocRankAdjoin.chain hT G' i' F hv hx hmh]

end GroundTheory.Heights₂.Heights.Inter
end
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueDeg

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem SemilocResidueDeg.proof (hDim : SemilocResidueFibreDim.Statement) (hAdj : SemilocResidueAdjoin.Statement) :
    SemilocResidueDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hZ hs hsP hW W' hW' _ G' J' hJ
  have hrel : ∀ k', ∃ i, (X ⟨k', i⟩ : MRing ι') ∉ W' := hW'.1.2.2
  choose i' hi' using hrel
  have hfib : IsProjVarF (fibreIdeal κ G') 0 := hDim K ι K' ι' κ v P' n s α W hv hP' hZ hs hsP hW W' hW' G'
  have hz : ∀ k : FibreBlock κ, G'.x' ⟨k.1, i' k.1⟩ ≠ 0 := by
    intro k h0
    apply hi' k.1
    rw [← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
    exact h0
  have hj : IsChart (fibreIdeal κ G') (fun k => i' k.1) := by
    intro k hk
    apply hz k
    rw [fibreIdeal, RingHom.mem_ker, aeval_X] at hk
    exact hk
  refine ⟨_, hAdj K ι K' ι' κ v P' n s α W hv hP' hZ hs hsP hW W' hW' G' i' hi', ?_⟩
  rw [hJ.1 _ Fin.elim0 _ hfib hj]
  exact congrArg _ (ChartRankAdjoin.proof (FibreBlock κ) (fibreIdx ι' κ) G'.Φ G'.Φ' (fun q => G'.x' ⟨q.1.1, q.2⟩)
    (fun k => i' k.1) hz hfib.1.2.1).symm

end GroundTheory.Heights₂.Heights.Inter
end
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueFibreDim

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 PointVertical

theorem SemilocResidueFibreDim.proof (hFD : FibreDivSupp.Statement) (hDim : FibreDimStatement)
    (hAI : FibreDimensionZero.Statement) : SemilocResidueFibreDim.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hZ hs hsP hW W' hW' G'
  classical
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  have hsW' : rename v s ∈ W' := by
    have h : s ∈ imageZ v W' := hW'.2.2 ▸ hsW
    exact h
  have hD' : W' ∈ divSupp P' (rename v s) := ((hFD K ι K' ι' κ v P' n s α W hv hP' hZ hs hsP hW W').1 ⟨hW', hsW'⟩).1
  have hsec' : IsSectionOn P' (HermLine.sqMetric (ι := ι') (Function.extend κ α 0)) (rename v s) :=
    ⟨Function.extend κ α 0, fun _ => rfl, isMultiHomog_rename hv hs, hsP⟩
  have hsec : IsSectionOn (imageZ v P') (HermLine.sqMetric (ι := ι) α) s := ⟨α, fun _ => rfl, hs, hsP⟩
  have divSuppArith : DivSuppArithStatement := by
    intro K _ ι _ P n A s W hP hs hW
    obtain ⟨hK, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP
    obtain ⟨a, -, hsa, hsP⟩ := hs
    obtain ⟨hWmin, hWrel⟩ := hW
    have hWp : W.IsPrime := hWmin.1.1
    have hWmh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes hPh hsa hWmin
    have := hPp
    have h1 := dim_quot_minimal_add_one P W s hsP hWmin
    rw [hPdim] at h1
    have hdim : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      withBot_eq_of_add_one (by rw [h1, show n + 1 + Fintype.card K = n + Fintype.card K + 1 by omega])
    exact ⟨fun hh => ⟨hK, ⟨hWp, hWmh, hWrel⟩, hh, hdim⟩,
      fun hv => ⟨⟨hWp, hWmh, hWrel⟩, charOf_prime hWp hv, hdim⟩⟩
  have hA' := divSuppArith K' ι' P' n _ _ W' hP' hsec' hD'
  have hA := divSuppArith K ι (imageZ v P') n _ _ W hZ hsec hW
  have hdW : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    by_cases hh : IsHorizontal W
    · exact (hA.1 hh).2.2.2
    · exact (hA.2 hh).2.2
  by_cases hh' : IsHorizontal W'
  · have hh : IsHorizontal W := by
      unfold IsHorizontal at hh' ⊢
      rw [← hh', ← hW'.2.2]
      ext z
      simp [imageZ, Ideal.mem_comap]
    have hW'a : IsArithVar W' (n + 0) := hA'.1 hh'
    have hWa : IsArithVar (imageZ v W') n := hW'.2.2 ▸ hA.1 hh
    exact hDim K ι K' ι' κ v W' n 0 G' hv hW'a hWa
  · obtain ⟨hW'm, hpr, hdW'⟩ := hA'.2 hh'
    set p := charOf W' with hpdef
    have : Fact p.Prime := ⟨hpr⟩
    have hpW' : ((p : ℕ) : MRing ι') ∈ W' := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W'
    have hpW : ((p : ℕ) : MRing ι) ∈ W := by
      rw [← hW'.2.2]
      show rename v ((p : ℕ) : MRing ι) ∈ W'
      simpa using hpW'
    have hWm : IsMultiProjPrime W := hW'.2.2 ▸ isMultiProjPrime_imageZ hv hW'm
    have hWp : IsProjVarF (W'.map (red p)) n :=
      ⟨isMultiProjPrime_red p hW'm hpW', by rw [ringKrullDim_red p hpW', hdW']⟩
    have hVi : IsProjVarF (imageVar (ZMod p) v (W'.map (red p))) n := by
      rw [imageVar_red p v hpW', hW'.2.2]
      exact ⟨isMultiProjPrime_red p hWm hpW, by rw [ringKrullDim_red p hpW, hdW]⟩
    exact hAI K ι K' ι' κ v p W' n hv hpW' hWp hVi G'

end GroundTheory.Heights₂.Heights.Inter
end
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.SemilocResidueDegOfFibreIncomp

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter

theorem projDeg_all :
    ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)],
      ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι' := by
  intro F _ K _ ι _ K' _ ι' _
  exact GroundTheory.Heights₂.Heights.Targets.ProjDeg.of_found
    (GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.of_divPushForward
      (GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForward.proof
        GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe.proof
        GroundTheory.Heights₂.Heights.NumbersDVR.DivPushForwardLocalZero))
    GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg.proof F ι ι'

theorem semilocMaxIdeals_of_fibreIncomp (hFI : FibreIncomp.Statement) : SemilocMaxIdeals.Statement :=
  SemilocMaxIdeals.proof (FibreOverFinite.proof hFI) hFI SemilocIntegral.full LocRingDimOne.full

theorem semilocResidueDeg_of_fibreIncomp (hFI : FibreIncomp.Statement) (hFD : FibreDimStatement) :
    SemilocResidueDeg.Statement :=
  SemilocResidueDeg.proof (SemilocResidueFibreDim.proof (FibreDivSupp.proof hFI) hFD FibreDimensionZero.full)
    (SemilocResidueAdjoin.proof
      (SemilocResidueFrac.proof SemilocFinite.full (semilocMaxIdeals_of_fibreIncomp hFI))
      ChartScalingIndep.full)

end GroundTheory.Heights₂.Heights.ForSecondHalf
end
end
