module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.MeromorphicAtProd
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.NatCastPowCpow
public import GroundTheory.GlobalFields.TateThesis.DedekindZetaContinuation
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.FactorDifferentiable
public import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.SummablePrimesRpow
import Mathlib.Topology.UniformSpace.Uniformizable
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.ZetaOrd
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.FinMod

section

@[expose] public section

namespace PositivityTheory.Lord

theorem hasProd_compl_finset {ι : Type*} [DecidableEq ι] (f g : ι → ℂ) (a : ℂ) (T S : Finset ι) (hST : S ⊆ T)
    (hg : HasProd g a) (hg0 : ∀ v ∈ T, g v ≠ 0) (hfg : ∀ v, v ∉ T → f v = g v) :
    HasProd (fun v : {v // v ∉ S} => f v) (a * (∏ v ∈ T, (g v)⁻¹) * ∏ v ∈ T \ S, f v) := by
  let F : ι → ℂ := Set.mulIndicator {v | v ∉ S} f
  let k : ι → ℂ := fun v => if v ∈ T then (g v)⁻¹ * F v else 1
  have hkT : HasProd k (∏ v ∈ T, k v) :=
    hasProd_prod_of_ne_finset_one (fun v hv => if_neg hv)
  have hgk : ∀ v, g v * k v = F v := by
    intro v
    by_cases hv : v ∈ T
    · show g v * (if v ∈ T then (g v)⁻¹ * F v else 1) = F v
      rw [if_pos hv, ← mul_assoc, mul_inv_cancel₀ (hg0 v hv), one_mul]
    · have hvS : v ∉ S := fun h => hv (hST h)
      show g v * (if v ∈ T then (g v)⁻¹ * F v else 1) = Set.mulIndicator {v | v ∉ S} f v
      rw [if_neg hv, mul_one, Set.mulIndicator_of_mem (show v ∈ {v | v ∉ S} from hvS), hfg v hv]
  have hFT : ∏ v ∈ T, F v = ∏ v ∈ T \ S, f v := by
    rw [Finset.sdiff_eq_filter, Finset.prod_filter]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    by_cases hvS : v ∈ S
    · rw [if_neg (not_not.2 hvS)]
      exact Set.mulIndicator_of_notMem (show v ∉ {v | v ∉ S} from not_not.2 hvS) f
    · rw [if_pos hvS]
      exact Set.mulIndicator_of_mem (show v ∈ {v | v ∉ S} from hvS) f
  have hkprod : ∏ v ∈ T, k v = (∏ v ∈ T, (g v)⁻¹) * ∏ v ∈ T \ S, f v := by
    rw [← hFT, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun v hv => if_pos hv)
  have hF : HasProd F (a * (∏ v ∈ T, (g v)⁻¹) * ∏ v ∈ T \ S, f v) := by
    have h := hg.mul hkT
    rw [hkprod, ← mul_assoc] at h
    convert h using 1
    funext v
    exact (hgk v).symm
  exact (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ S})).2 hF

end PositivityTheory.Lord
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.NormESpZpow

section

@[expose] public section

open NumberField InfinitePlace IsDedekindDomain HeckeCharacterZeroLocus.SiegelWeilU

namespace PositivityTheory.Lord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cm_places {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    nrRealPlaces F = Module.finrank ℚ F ∧ nrComplexPlaces F = 0 ∧ nrRealPlaces E = 0 ∧
      nrComplexPlaces E = Module.finrank ℚ F := by
  obtain ⟨hF, hE, h2, -⟩ := h
  have hcF : nrComplexPlaces F = 0 := IsTotallyReal.nrComplexPlaces_eq_zero F
  have hrE : nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  have kF := card_add_two_mul_card_eq_rank F
  have kE := card_add_two_mul_card_eq_rank E
  have ht := Module.finrank_mul_finrank ℚ F E
  rw [h2] at ht
  refine ⟨by omega, hcF, hrE, by omega⟩

theorem eSp_zpow (v : HeightOneSpectrum (𝓞 F)) (j : ℤ) :
    PositivityTheory.SiegelWeilFormula.Gen.eSp E v ^ j = if Even j then 1 else PositivityTheory.SiegelWeilFormula.Gen.eSp E v := by
  unfold PositivityTheory.SiegelWeilFormula.Gen.eSp
  split_ifs with h1 h2 h2
  · exact h2.neg_one_zpow
  · exact (Int.not_even_iff_odd.1 h2).neg_one_zpow
  · exact one_zpow j
  · exact one_zpow j

end PositivityTheory.Lord
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.ZetaEGrouped

section

@[expose] public section

open NumberField IsDedekindDomain

namespace PositivityTheory.Lord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem zetaE_grouped {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => ∏ P ∈ fib F E v, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)))
      (GroundTheory.Global.continuedDedekindZeta E s)⁻¹ := by
  classical
  have hex : ∀ P : HeightOneSpectrum (𝓞 E), ∃ v : HeightOneSpectrum (𝓞 F), P ∈ fib F E v := by
    intro P
    refine ⟨⟨P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)), inferInstance, ?_⟩, ?_⟩
    · intro h
      exact P.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)
    · rw [mem_fib]
      exact ⟨rfl⟩
  have huniq : ∀ (P : HeightOneSpectrum (𝓞 E)) (v w : HeightOneSpectrum (𝓞 F)),
      P ∈ fib F E v → P ∈ fib F E w → v = w := by
    intro P v w hv hw
    rw [mem_fib] at hv hw
    apply HeightOneSpectrum.ext
    rw [hv.over, hw.over]
  choose π hπ using hex
  let e : (Σ v : HeightOneSpectrum (𝓞 F), {P // P ∈ fib F E v}) ≃ HeightOneSpectrum (𝓞 E) :=
    { toFun := fun x => x.2.1
      invFun := fun P => ⟨π P, ⟨P, hπ P⟩⟩
      left_inv := by
        rintro ⟨v, P, hP⟩
        exact Sigma.subtype_ext (huniq P _ _ (hπ P) hP) rfl
      right_inv := fun P => rfl }
  obtain ⟨h, -⟩ := zeta_euler E hs
  have h' := (e.hasProd_iff).2 h
  exact h'.sigma (fun v => Finset.hasProd (fib F E v) _)

end PositivityTheory.Lord
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.ZetaInvPoOfOneLt

section

@[expose] public section

open NumberField InfinitePlace IsDedekindDomain Filter Topology HeckeCharacterZeroLocus.SiegelWeilU
open GroundTheory.Global (continuedDedekindZeta meromorphicOn_continuedDedekindZeta)
open PositivityTheory.SiegelWeilFormula.Gen (eSp LOrd)

namespace PositivityTheory.Lord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem zeta_inv_po_of_one_lt (K : Type) [Field K] [NumberField K] {x : ℂ} (hx : 1 < x.re) :
    PO (fun s => (continuedDedekindZeta K s)⁻¹) x 0 := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  exact PO.of_analytic ((zeta_analyticAt K hx1).inv (zeta_euler K hx).2)

theorem factorF_zo (v : HeightOneSpectrum (𝓞 F)) (j : ℤ) :
    ZO (fun s : ℂ => 1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) (j : ℂ) (if j = 0 then 1 else 0) := by
  have hN := two_le_absNorm F v
  by_cases hj : j = 0
  · subst hj
    simpa using factor_zo_zero _ hN
  · rw [if_neg hj]
    simpa using factor_zo _ hN 1 (by simp) j hj

theorem lOrd_even (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (S : Finset (HeightOneSpectrum (𝓞 F))) (j : ℤ)
    (hj : Even j) :
    ∃ Z : ℂ → ℂ, MeromorphicOn Z Set.univ ∧
      (∀ s : ℂ, 1 < s.re → HasProd (fun v : {v // v ∉ S} =>
        1 - eSp E v.1 ^ j * (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)) (Z s)) ∧
      PO Z (j : ℂ) (if 1 ≤ j then 0 else if j = 0 then S.card + Module.finrank ℚ F - 1
        else Module.finrank ℚ F) := by
  classical
  obtain ⟨hFr, hFc, -, -⟩ := cm_places h
  have hfac : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : ℂ),
      AnalyticAt ℂ (fun s : ℂ => 1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) x := fun v x => by
    simpa using factor_analytic _ (by have := two_le_absNorm F v; omega) 1 x
  refine ⟨fun s => (continuedDedekindZeta F s)⁻¹ *
    ∏ v ∈ S, (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹, ?_, ?_, ?_⟩
  · intro x _
    exact ((meromorphicOn_continuedDedekindZeta F x trivial).inv).mul
      (meromorphicAt_prod S _ fun v _ => (hfac v x).meromorphicAt.inv)
  · intro s hs
    have hs0 : 0 < s.re := by linarith
    have key := hasProd_compl_finset (fun v => 1 - eSp E v ^ j * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))
      (fun v => 1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) _ S S (Finset.Subset.refl S) (zeta_euler F hs).1
      (fun v _ => by simpa using factor_ne_zero _ (two_le_absNorm F v) 1 s (by simp) hs0)
      (fun v _ => by simp [eSp_zpow, hj])
    rw [Finset.sdiff_self, Finset.prod_empty, mul_one] at key
    exact key
  · by_cases hj1 : 1 ≤ j
    · have hj0 : j ≠ 0 := by omega
      have hre : 1 < (j : ℂ).re := by
        obtain ⟨k, hk⟩ := hj
        simp only [Complex.intCast_re]
        exact_mod_cast (by omega : (1 : ℤ) < j)
      have hP := (zeta_inv_po_of_one_lt F hre).mul
        (PO.prod S (fun v s => (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) (fun _ => if j = 0 then 1 else 0)
          fun v _ => (factorF_zo v j).inv)
      rw [if_pos hj1]
      exact hP.mono (by simp [hj0])
    · rw [if_neg hj1]
      have hle : j ≤ 0 := by omega
      have hP := (zeta_zo_nonpos F j hle).inv.mul
        (PO.prod S (fun v s => (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) (fun _ => if j = 0 then 1 else 0)
          fun v _ => (factorF_zo v j).inv)
      have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
      refine hP.mono ?_
      by_cases hj0 : j = 0
      · simp [hj0, hFr, hFc] <;> omega
      · simp [hj0, hFr, hFc, hj]

private theorem hasProd_inv' {ι : Type} {f : ι → ℂ} {a : ℂ} (h : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => (f i)⁻¹) a⁻¹ := by
  unfold HasProd at h ⊢
  convert h.inv₀ ha using 1
  funext t
  exact Finset.prod_inv_distrib _

theorem lOrd_odd (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (S : Finset (HeightOneSpectrum (𝓞 F))) (j : ℤ)
    (hj : ¬ Even j) :
    ∃ Z : ℂ → ℂ, MeromorphicOn Z Set.univ ∧
      (∀ s : ℂ, 1 < s.re → HasProd (fun v : {v // v ∉ S} =>
        1 - eSp E v.1 ^ j * (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)) (Z s)) ∧
      PO Z (j : ℂ) (if 1 ≤ j then 0 else if j = 0 then S.card + Module.finrank ℚ F - 1
        else Module.finrank ℚ F) := by
  classical
  obtain ⟨-, -, hEr, hEc⟩ := cm_places h
  have h2 : Module.finrank F E = 2 := h.2.2.1
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hj ⟨0, rfl⟩
  have hfacF : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : ℂ),
      AnalyticAt ℂ (fun s : ℂ => 1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) x := fun v x => by
    simpa using factor_analytic _ (by have := two_le_absNorm F v; omega) 1 x
  have hfacE : ∀ (P : HeightOneSpectrum (𝓞 E)) (x : ℂ),
      AnalyticAt ℂ (fun s : ℂ => 1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) x := fun P x => by
    simpa using factor_analytic _ (by have := two_le_absNorm E P; omega) 1 x
  have hfac : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : ℂ),
      AnalyticAt ℂ (fun s : ℂ => 1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) x := fun v x =>
    factor_analytic _ (by have := two_le_absNorm F v; omega) _ x
  have hneF : ∀ (v : HeightOneSpectrum (𝓞 F)) (s : ℂ), 0 < s.re →
      (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ≠ 0 := fun v s hs => by
    simpa using factor_ne_zero _ (two_le_absNorm F v) 1 s (by simp) hs
  have hneE : ∀ (P : HeightOneSpectrum (𝓞 E)) (s : ℂ), 0 < s.re →
      (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ≠ 0 := fun P s hs => by
    simpa using factor_ne_zero _ (two_le_absNorm E P) 1 s (by simp) hs
  have hneFj : ∀ v : HeightOneSpectrum (𝓞 F), (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-(j : ℂ))) ≠ 0 :=
    fun v => by simpa using factor_ne_zero_int _ (two_le_absNorm F v) 1 (by simp) j hj0
  have hesp : ∀ v : HeightOneSpectrum (𝓞 F), eSp E v ^ j = eSp E v := fun v => by
    rw [eSp_zpow, if_neg hj]
  set T : Finset (HeightOneSpectrum (𝓞 F)) := S ∪ (badSet_finite F E).toFinset with hT
  refine ⟨fun s => ((continuedDedekindZeta E s)⁻¹ * continuedDedekindZeta F s *
      ∏ v ∈ T, ((∏ P ∈ fib F E v, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))) *
        (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)⁻¹) *
      ∏ v ∈ T \ S, (1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)), ?_, ?_, ?_⟩
  · intro x _
    refine ((((meromorphicOn_continuedDedekindZeta E x trivial).inv).mul
      (meromorphicOn_continuedDedekindZeta F x trivial)).mul ?_).mul ?_
    · exact meromorphicAt_prod T _ fun v _ =>
        ((meromorphicAt_prod (fib F E v) _ fun P _ => (hfacE P x).meromorphicAt).mul
          (hfacF v x).meromorphicAt.inv).inv
    · exact meromorphicAt_prod (T \ S) _ fun v _ => (hfac v x).meromorphicAt
  · intro s hs
    have hs0 : 0 < s.re := by linarith
    have hFinv : HasProd (fun v : HeightOneSpectrum (𝓞 F) => (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)
        (continuedDedekindZeta F s) := by
      have := hasProd_inv' (zeta_euler F hs).1 (inv_ne_zero (zeta_euler F hs).2)
      rwa [inv_inv] at this
    have hg := (zetaE_grouped (F := F) (E := E) hs).mul hFinv
    have key := hasProd_compl_finset (fun v => 1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))
      (fun v => (∏ P ∈ fib F E v, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))) *
        (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) _ T S Finset.subset_union_left hg
      (fun v _ => mul_ne_zero (Finset.prod_ne_zero_iff.2 fun P _ => hneE P s hs0) (inv_ne_zero (hneF v s hs0)))
      (fun v hv => by
        have hvb : v ∉ badSet F E := fun hb =>
          hv (Finset.mem_union_right _ ((badSet_finite F E).mem_toFinset.2 hb))
        rw [local_factor F E h2 v hvb s, mul_comm (1 - _) (1 - _), mul_assoc, mul_inv_cancel₀ (hneF v s hs0),
          mul_one])
    simp only [hesp]
    exact key
  · have hZg : ∀ v : HeightOneSpectrum (𝓞 F), ZO (fun s => (∏ P ∈ fib F E v,
        (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))) * (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) (j : ℂ) 0 := by
      intro v
      have h1 := ZO.prod (fib F E v) (fun P s => 1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) (fun _ => 0)
        (fun P _ => by
          have := factorF_zo P j
          rwa [if_neg hj0] at this)
      have h3 : ZO (fun s => (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) (j : ℂ) 0 :=
        ZO.of_analytic ((hfacF v j).inv (hneFj v)) (inv_ne_zero (hneFj v))
      have := h1.mul h3
      simp only [Finset.sum_const_zero, add_zero] at this
      exact this
    have hPg : PO (fun s => ∏ v ∈ T, ((∏ P ∈ fib F E v, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))) *
        (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)⁻¹) (j : ℂ) 0 := by
      have := PO.prod T (fun v s => ((∏ P ∈ fib F E v, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))) *
        (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)⁻¹) (fun _ => 0) (fun v _ => (hZg v).inv)
      simp only [Finset.sum_const_zero] at this
      exact this
    have hPf : PO (fun s => ∏ v ∈ T \ S, (1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) (j : ℂ) 0 := by
      have := PO.prod (T \ S) (fun v s => 1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) (fun _ => 0)
        (fun v _ => PO.of_analytic (hfac v j))
      simp only [Finset.sum_const_zero] at this
      exact this
    by_cases hj1 : 1 ≤ j
    · rw [if_pos hj1]
      by_cases hj1' : j = 1
      · subst hj1'
        obtain ⟨AE, hAE, hAE1, hevE⟩ := zeta_pole E
        obtain ⟨AF, hAF, -, hevF⟩ := zeta_pole F
        have hc : ((1 : ℤ) : ℂ) = 1 := by simp
        have hZ : PO (fun s => (continuedDedekindZeta E s)⁻¹ * continuedDedekindZeta F s) ((1 : ℤ) : ℂ) 0 := by
          rw [hc]
          refine ⟨fun s => AF s / AE s, hAF.div hAE hAE1, ?_⟩
          filter_upwards [hevE, hevF, self_mem_nhdsWithin] with s hE hF hs
          have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
          rw [← hE, ← hF, pow_zero, one_mul, mul_div_mul_left _ _ hs1, div_eq_inv_mul]
        exact ((hZ.mul hPg).mul hPf).mono (by norm_num)
      · have hre : 1 < (j : ℂ).re := by
          simp only [Complex.intCast_re]
          exact_mod_cast (by omega : (1 : ℤ) < j)
        have hj1c : (j : ℂ) ≠ 1 := by exact_mod_cast hj1'
        have hZ := (zeta_inv_po_of_one_lt E hre).mul (PO.of_analytic (zeta_analyticAt F hj1c))
        exact ((hZ.mul hPg).mul hPf).mono (by norm_num)
    · rw [if_neg hj1, if_neg hj0]
      have hle : j ≤ 0 := by omega
      have hj1c : (j : ℂ) ≠ 1 := by exact_mod_cast (by omega : j ≠ 1)
      have hZ := ((zeta_zo_nonpos E j hle).inv).mul (PO.of_analytic (zeta_analyticAt F hj1c))
      refine ((hZ.mul hPg).mul hPf).mono ?_
      simp [hEr, hEc, hj, hj0]

theorem _root_.PositivityTheory.SiegelWeilFormula.Gen.lOrd : LOrd := by
  intro F E _ _ _ _ _ σ h S j
  by_cases hj : Even j
  · exact lOrd_even σ h S j hj
  · exact lOrd_odd σ h S j hj

end PositivityTheory.Lord
end
end
