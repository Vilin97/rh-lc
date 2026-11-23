module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsIsoGrCechMapPolyToGamma
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLimsupOfEventuallyPolynomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLineBundleSectionsLeImageFormsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimConeImageOfBirationalLinearSystem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
import Mathlib.Tactic.Basify
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPieceFinrankLeH0

section

@[expose] public section

open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.Adelic.LinSys

theorem finrank_quotient_piece_le_sections (k : Type) [Field k] (S : LinSys k) (hS : S.IsVariety)
    (m : ℕ) : Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) ≤ lbH0 k (lbPow S.L m) := by
  classical
  let : Module k (lbPow S.L m).Sec := Module.compHom (lbPow S.L m).Sec (algebraMap k Γ(S.Y, ⊤))
  have : IsScalarTower k Γ(S.Y, ⊤) (lbPow S.L m).Sec :=
    ⟨fun a b s => by
      show (a • b) • s = algebraMap k Γ(S.Y, ⊤) a • (b • s)
      rw [Algebra.smul_def, mul_smul]⟩
  have hfin : Module.Finite k (coh (twist (structureModule S.Y) (lbPow S.L m)) 0) :=
    finite_coh_zero_twist_of_isProjOver (f := S.str) (fun _ => rfl) hS.proj (isLB_lbPow S.isLB m)
  have : Module.Finite k (lbPow S.L m).Sec :=
    Module.Finite.equiv ((cohZeroTwistEquiv (lbPow S.L m)).restrictScalars k)
  rw [lineBundleGlobalSectionsDim_eq_finrank]
  let V := homogeneousSubmodule (Fin S.N) k m

  let φ : V →ₗ[k] (lbPow S.L m).Sec :=
    { toFun := fun g => S.form g.2
      map_add' := fun g h => (ProjCoh.formSecAdd k S.b (m : ℤ)).map_add
        ⟨g.1, mem_polyGrading_natCast.2 g.2⟩ ⟨h.1, mem_polyGrading_natCast.2 h.2⟩
      map_smul' := fun c g => ProjCoh.formSec_smul k S.b c (mem_polyGrading_natCast.2 g.2) _ }

  let f : V →ₗ[k] MvPolynomial (Fin S.N) k ⧸ S.imageIdeal :=
    (Ideal.Quotient.mkₐ k S.imageIdeal).toLinearMap ∘ₗ V.subtype
  have hker : LinearMap.ker f = LinearMap.ker φ := by
    ext g
    simp only [LinearMap.mem_ker]
    change Ideal.Quotient.mk S.imageIdeal g.1 = 0 ↔ S.form g.2 = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact S.mem_imageIdeal_iff g.2
  have hrange : quotPiece S.imageIdeal (m : ℤ) = LinearMap.range f := by
    rw [quotPiece_natCast, LinearMap.range_comp, Submodule.range_subtype]
  rw [hrange, ← f.quotKerEquivRange.finrank_eq, (Submodule.quotEquivOfEq _ _ hker).finrank_eq,
    φ.quotKerEquivRange.finrank_eq]
  exact Submodule.finrank_le _

end GlobalTheory.Adelic.LinSys
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPieceFinrankLeH0Statement

section

@[expose] public section

open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem _root_.GlobalTheory.T.quotient_piece_finrank_le_h0 : ∀ (k : Type) [Field k] (S : LinSys k), S.IsVariety → ∀ m : ℕ, Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) ≤ lbH0 k (lbPow S.L m) := by
  first | exact @GlobalTheory.Adelic.LinSys.finrank_quotient_piece_le_sections | exact GlobalTheory.Adelic.LinSys.finrank_quotient_piece_le_sections | (intros; apply GlobalTheory.Adelic.LinSys.finrank_quotient_piece_le_sections <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimConeImageOfBirationalLinearSystemStatement

section

@[expose] public section

open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem _root_.GlobalTheory.T.ringKrullDim_cone_image_of_birational_linearSystem : ∀ (k : Type) [Field k] (S : LinSys k), S.IsVariety → S.BasePointFree → S.Birational → ringKrullDim (MvPolynomial (Fin S.N) k ⧸ S.imageIdeal) = ((S.D + 1 : ℕ) : WithBot ℕ∞) := by
  first | exact @GlobalTheory.Adelic.ConeDim.ringKrullDim_imageIdeal_of_birational | exact GlobalTheory.Adelic.ConeDim.ringKrullDim_imageIdeal_of_birational | (intros; apply GlobalTheory.Adelic.ConeDim.ringKrullDim_imageIdeal_of_birational <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeImageBirationalLinearSystemEqSelfInt

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

open AlgebraicGeometry Filter GlobalTheory.CompHt
open scoped ENNReal

set_option autoImplicit false

namespace GlobalTheory.ImageDegree

theorem growth_eq_of_tendsto (D : ℕ) (r : ℕ → ℕ) {c : ℝ} (hc : 0 ≤ c)
    (h : Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (nhds (c / D.factorial))) :
    growth D (fun m => (r m : ℕ∞)) = ENNReal.ofReal c := by
  have hf : (0 : ℝ) < D.factorial := by positivity
  have h2 : Tendsto (fun m : ℕ => ENNReal.ofReal ((D.factorial : ℝ) * ((r m : ℝ) / (m : ℝ) ^ D))) atTop
      (nhds (ENNReal.ofReal c)) := by
    refine ENNReal.tendsto_ofReal ?_
    have := h.const_mul (D.factorial : ℝ)
    rwa [mul_div_cancel₀ _ hf.ne'] at this
  refine (Tendsto.limsup_eq ?_)
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (m : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm.ne')
  have hm'' : (m : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top m)
  rw [ENat.toENNReal_coe, mul_div_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_natCast]

theorem ringKrullDim_of_birational {k : Type} [Field k] (S : LinSys k) (h : S.IsVariety) (hb : S.BasePointFree)
    (hB : S.Birational) : ringKrullDim (MvPolynomial (Fin S.N) k ⧸ S.imageIdeal) = (S.D + 1 : ℕ) :=
  GlobalTheory.T.ringKrullDim_cone_image_of_birational_linearSystem k S h hb hB

theorem finrank_quotientPiece_le_lineBundleSections {k : Type} [Field k] (S : LinSys k) (h : S.IsVariety) (m : ℕ) :
    Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) ≤ lbH0 k (lbPow S.L m) :=
  GlobalTheory.T.quotient_piece_finrank_le_h0 k S h m

theorem rankGrowth_lineBundleSections_le_image_forms {k : Type} [Field k] [CharZero k] (S : LinSys k) (h : S.IsVariety) (hb : S.BasePointFree)
    (hB : S.Birational) :
    growth S.D (fun m => (lbH0 k (lbPow S.L m) : ℕ∞)) ≤
      growth S.D (fun m => (Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) :=
  GlobalTheory.T.rankGrowth_lineBundle_sections_le_image_forms k S h hb hB

theorem topologicalKrullDim_eq {k : Type} [Field k] (S : LinSys k) (h : S.IsVariety) :
    topologicalKrullDim S.Y = S.D := by
  have := HeightExists.isIntegral h
  have hc (U : S.Y.Opens) (hU : IsAffineOpen U) (hne : (U : Set S.Y).Nonempty) :
      topologicalKrullDim (U : Set S.Y) = S.D := by
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(S.Y, U))).trans
      (SmoothDim.ringKrullDim_affineOpen k _ S.str _ h.smooth U hU hne)
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
  · obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.Y.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top x)
    exact ⟨U, U.isOpen, hx, (hc U hU ⟨x, hx⟩).le⟩
  · obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.Y.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top (genericPoint S.Y))
    exact (hc U hU ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)

theorem degree_image_eq_topSelf : Quoted → ∀ (F : Type) [Field F] [NumberField F] (S : LinSys F), S.IsVariety → S.BasePointFree →
    S.Birational → 0 < S.del ∧ (hilbertDegree S.imageIdeal : ℤ) = S.del ∧
      ringKrullDim (MvPolynomial (Fin S.N) F ⧸ S.imageIdeal) = (S.D + 1 : ℕ) := by
  intro Q F _ _ S hV hb hB
  have hdim := ringKrullDim_of_birational S hV hb hB
  have hp := HeightExists.isPrime_imageIdeal hV
  have hI := S.isHomogeneous_imageIdeal
  have hdeg := degree_idealHilbertPoly_eq_of_isPrime hI hdim
  have hHG := (growth_of_eventually_eq_eval S.D 1 (fun m => Module.finrank F (quotPiece S.imageIdeal (m : ℤ)))
    (idealHilbertPoly S.imageIdeal) le_rfl (eventually_finrank_quotPiece hI)).1 hdeg.le (hilbertDegree S.imageIdeal)
    (cast_hilbertDegree_of_degree_eq hI hdeg)
  simp only [one_mul, Nat.cast_one, one_pow] at hHG
  have hHG' : growth S.D (fun m => (Module.finrank F (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) = hilbertDegree S.imageIdeal := by
    refine Eq.trans ?_ hHG
    congr 1
    funext m
    rw [one_mul]
  have hstr : strHom F S.Y = S.str := strHom_eq fun _ => rfl
  have hproj : IsProjOver (strHom F (X := S.Y)) := hstr ▸ hV.proj
  have hnef : IsNef F S.L := IsGenerated.isNef_of_isProjOver ⟨S.N, S.b, hb⟩ hV.proj
  have hYd := topologicalKrullDim_eq S hV
  have h0 := Q.nef.2.2.topSelf_nonneg hproj hYd hnef
  have hG := growth_eq_of_tendsto S.D (fun m => lbH0 F (lbPow S.L m)) (Int.cast_nonneg h0)
    (Q.nef.2.2.tendsto hproj hYd hnef)
  have hle1 : growth S.D (fun m => (Module.finrank F (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) ≤
      growth S.D (fun m => (lbH0 F (lbPow S.L m) : ℕ∞)) :=
    limsup_le_limsup (Eventually.of_forall fun m => ENNReal.div_le_div_right (mul_le_mul_right
      (ENat.toENNReal_le.2 (Nat.cast_le.2 (finrank_quotientPiece_le_lineBundleSections S hV m))) _) _)
  have hle2 := rankGrowth_lineBundleSections_le_image_forms S hV hb hB
  rw [hHG', hG] at hle1 hle2
  have e : (hilbertDegree S.imageIdeal : ℝ≥0∞) = ENNReal.ofReal (topSelfIntersection F S.L S.D : ℝ) := le_antisymm hle1 hle2
  have e' : ((hilbertDegree S.imageIdeal : ℝ) : ℝ) = (topSelfIntersection F S.L S.D : ℝ) := by
    rw [← ENNReal.ofReal_natCast] at e
    exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) (Int.cast_nonneg h0)).1 e
  have hdel : (hilbertDegree S.imageIdeal : ℤ) = S.del := by
    rw [LinSys.del]; exact_mod_cast e'
  obtain ⟨Ω, _, _, x, hx, -⟩ := HeightExists.exists_generic hV
  obtain ⟨j, hj⟩ := Function.ne_iff.1 (hb.coords_ne_zero x.1)
  have hX : (X j : MvPolynomial (Fin S.N) F) ∉ S.imageIdeal := fun hX => hj (by simpa using S.eval₂_coords_eq_zero x.1 hX)
  have hpos := hilbertDegree_pos hI hX
  exact ⟨hdel ▸ (by exact_mod_cast hpos), hdel, hdim⟩

end GlobalTheory.ImageDegree
end
end
