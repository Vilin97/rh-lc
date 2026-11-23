module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundOfCoreLawsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.TBDisc

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLam

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.TB

theorem latOfLam : LatOfLamSt := by
  intro D B P j X S ka wL wF large₂ C A hg hs hlam hspan hH2
  let Nf : NormFam B.KO (B.Cusp j ka) :=
    { N := B.supN j ka
      nonneg := B.supN_nonneg j ka
      eq_zero := fun σ v h => (B.supN_eq_zero j ka σ v).mp h
      smul := B.supN_smul j ka
      add := B.supN_add j ka }
  have hPL : ProdLower Nf (B.Mlat j ka)
      ((Fintype.card (B.KO →+* ℂ) : ℝ) * (WeightFamilies.PP0v D large₂ C A * (1 + Real.log ka.size) * ka.size)) := by
    intro f hf hne
    have h1 := hlam f hf hne
    unfold WeightFamilies.meanLogSup at h1
    by_cases hc : (Fintype.card (B.KO →+* ℂ) : ℝ) = 0
    · have hc' : Fintype.card (B.KO →+* ℂ) = 0 := by exact_mod_cast hc
      have hempty : IsEmpty (B.KO →+* ℂ) := Fintype.card_eq_zero_iff.mp hc'
      rw [hc, zero_mul, neg_zero]
      simp
    · have hpos : (0 : ℝ) < Fintype.card (B.KO →+* ℂ) :=
        lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hc)
      have h2 := (le_div_iff₀ hpos).mp h1
      show -((Fintype.card (B.KO →+* ℂ) : ℝ) * _) ≤ ∑ σ : B.KO →+* ℂ, Real.log (B.supN j ka σ f)
      linarith
  have hUD := discriminant_of_product_lower B.KO (B.Cusp j ka) Nf (B.Mlat j ka) _ hPL
  have hFG := formalGroup_of_discriminant B.KO (B.Cusp j ka) Nf (B.Mlat j ka) hUD
  exact Submodule.IsLattice.of_fg B.KO hFG

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeightModuleIsLatticeOfShortSeriesSpan

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

namespace GlobalTheory

private theorem full_of_short_span {D : D7} {B : WeightFamilies.Prov D}
    {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (S : WeightAlgebra.Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (hs : S.sK ≠ 0) (hsp : PullbackSections.SpanAt X ka)
    (hH : WeightAlgebra.H2 X S ka wL wF)
    (hlat : Submodule.IsLattice B.KO (B.Mlat j ka)) :
    Submodule.IsFullLattice B.KO (B.Mlat j ka) := by
  letI := hlat
  refine ⟨?_⟩
  apply top_unique
  rw [← hsp]
  apply Submodule.span_le.mpr
  intro f hf
  let n : ℕ := D.host.g 0 * D.host.g 1
  let k : ℕ := D.R.f * D.R.r * ka.n
  let t : 𝓞 B.KO := S.sK * (n : 𝓞 B.KO) ^ k
  have hn : n ≠ 0 := Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have ht : (t : B.KO) ≠ 0 := by
    have hsK : (S.sK : B.KO) ≠ 0 := by exact_mod_cast hs
    have hnK : (n : B.KO) ≠ 0 := by exact_mod_cast hn
    simp only [t, map_mul, map_pow, map_natCast]
    exact mul_ne_zero hsK (pow_ne_zero _ hnK)
  have hmem : t • f ∈ B.Mlat j ka := hH.2.2.2 (by
    simp only [WeightAlgebra.PJ.Thc, WeightAlgebra.PJ.scaled]
    refine Submodule.mem_map.mpr ⟨(n : 𝓞 B.KO) ^ k • f,
      Submodule.mem_map.mpr ⟨f, hf, by simp [n, k]⟩, ?_⟩
    simp only [t, LinearMap.smul_apply, LinearMap.id_apply, mul_smul])
  have hm : t • f ∈ Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) := Submodule.subset_span hmem
  have hsm : t • f = (t : B.KO) • f := (algebraMap_smul B.KO t f).symm
  rw [hsm] at hm
  have hm' := (Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka))).smul_mem (t : B.KO)⁻¹ hm
  have heq : (t : B.KO)⁻¹ • ((t : B.KO) • f) = f := by
    rw [← mul_smul, inv_mul_cancel₀ ht, one_smul]
  rwa [heq] at hm'


theorem latAt_record : ∀ (D : D7) (T : Core D) (h : LawsCore T), GamAt T → ∀ (large₂ : SizeData₂ D) (CA : ℝ), WeightAlgebra.ParA large₂ CA → ∀ (j : ℕ) (ka : WeightFamilies.Wt D j) (P : ModuliIntegralCharts.Prov D) (X : WeightAlgebra.PJ D (recB h) P j) (S : WeightAlgebra.Scal (recB h)) (wL wF : WeightFamilies.Wt D j), S.sK ≠ 0 → PullbackSections.SpanAt X ka → WeightAlgebra.H2 X S ka wL wF → Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB h) j ka := by
  intro D T h hG large₂ CA hA j ka P X S wL wF hs hsp hH
  obtain ⟨C0, -, hC⟩ := GlobalTheory.T.meanLogSupNorm_lower_bound_of_coreLaws
  apply full_of_short_span X S ka wL wF hs hsp hH
  exact PullbackSections.latOfLam D (recB h) P j X S ka wL wF large₂ C0 2 (fun i => (D.host.g_prime i).pos) hs
    (hC D T h hG large₂ hA.2.2.2.2.1 j ka C0 2 le_rfl le_rfl) hsp hH

end GlobalTheory
end
end
