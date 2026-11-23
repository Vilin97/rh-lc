module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightCm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearL2Independent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemOfMemSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.DivisorMultipleNonnegEventually
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodCmPointAtCmBasisFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodCmPtFrPolyNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldFrameValueNeZeroOfComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFrameReadingNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCoverComponentExtendsToRankOneCuspData
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsPowMulMemCuspFormsOfWeightMatch

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightCmStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)


theorem _root_.GlobalTheory.T.exists_frame_denominator_dominant_weight_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ y : FrPt Xo c z.K, y.x = z.x → 1 ≤ (Dw).p → 1 ≤ (Dw).q → ∀ la : GlobalTheory.AllWt.Weight (Dw), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((Dw).p - 1)) → ∃ N : z.K, N ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw la 0), (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) → IsIntegral ℤ (N * evR Xo c F y) := by
  first | exact @GlobalTheory.LatFull.CMInt.exists_frame_denom_dominant | exact GlobalTheory.LatFull.CMInt.exists_frame_denom_dominant | (intros; apply GlobalTheory.LatFull.CMInt.exists_frame_denom_dominant <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsCmPointFrameNeZeroOfDominant

section

@[expose] public section

section
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.AllWt (bergOn framesOn)
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.CovDetectDom
theorem exists_cmPoint_frame_ne_zero_of_dominant : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → ∀ [StarRing (𝓞 D.host.E)], (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀ F ∈ Y.V (wtOf _ la 0), F ≠ 0 → ∃ (z : CMPt Y.d.Xo₂ Y.d.c₂) (La : ℝ) (y : FrPt Y.d.Xo₂ Y.d.c₂ z.K), z.Good (Module.finrank ℚ D.host.E / 2) La ∧ y.x = z.x ∧ evR Y.d.Xo₂ Y.d.c₂ F y ≠ 0 := by
  classical
  intro hP D T j Y e o hG hdeg _ _ la _ _ _ hstar F hF hF0
  have hσ : GoodEmb Y.d.c₂ Y.d.c₂.F.val.toRingHom := rfl
  have hU := hG.unf _ hσ
  have hFm := GlobalTheory.AllWt.mem_cuspW.1 hF
  obtain ⟨k, x₁, hx₁, hne₁⟩ := GlobalTheory.exists_rdU_ne_zero_of_mem_secZ _ _ _ _ _ _ _ _ _ hU _ F hFm.1 hF0
  obtain ⟨Xx, 𝔄, hX, h𝔄, hΛ⟩ := GlobalTheory.CovData.exists_dataX_good D T j Y e o hG _ hσ k
  have hbdd := (Formalism.L2.Pj.abelian₂.holSub_SS ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds _ _ (hFm.2 _ hσ) k).1
  have hr : 0 < D.R.r := by
    have hn : 0 < D.R.ord := D.R.ord_pos
    have hk := D.R.f_le_k
    have ht := D.R.rank_add_five_le
    unfold Ranks.r; omega
  obtain ⟨La, x, lam, hx, hB, hne⟩ := GlobalTheory.CMDetect.exists_cm_frame Xx _ hX hr _ _ hbdd hx₁ hne₁
  obtain ⟨z, σ₁, hz, hzx⟩ := GlobalTheory.LamT.exists_good_cmPt_at_frame _ _ _ _ _ _ hstar _ _ hU hr k ⟨x, hx⟩ Xx hX 𝔄 h𝔄 hΛ
    La lam hB
  have hev : evR Y.d.Xo₂ Y.d.c₂ F ((Y.U _).un k ⟨x, hx⟩) ≠ 0 := by
    intro h0
    apply hne
    change (if h : x ∈ ((Y.U _).X k).dom then toC (evR Y.d.Xo₂ Y.d.c₂ F ((Y.U _).un k ⟨x, h⟩)) else 0) = 0
    rw [dite_eq_left hx]
    exact h0
  obtain ⟨y, hy, hyne⟩ := GlobalTheory.FrameDenseZ.exists_frame_evR_ne_zero_of_complex _ _ _ _ _ _ z.K z.y _ F hFm.1 _ σ₁ _ hzx hev
  exact ⟨z, La, y, hz, hy.trans hz.2.2.2.1, hyne⟩
end GlobalTheory.CovDetectDom
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)


theorem _root_.GlobalTheory.T.cmPoint_detects_dominant_covering : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → ∀ [StarRing (𝓞 D.host.E)], (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀ F ∈ Y.V (wtOf _ la 0), F ≠ 0 → ∃ (z : CMPt Y.d.Xo₂ Y.d.c₂) (La : ℝ) (y : FrPt Y.d.Xo₂ Y.d.c₂ z.K), z.Good (Module.finrank ℚ D.host.E / 2) La ∧ y.x = z.x ∧ evR Y.d.Xo₂ Y.d.c₂ F y ≠ 0 := by
  first | exact @_root_.GlobalTheory.CovDetectDom.exists_cmPoint_frame_ne_zero_of_dominant | exact _root_.GlobalTheory.CovDetectDom.exists_cmPoint_frame_ne_zero_of_dominant | (intros; apply _root_.GlobalTheory.CovDetectDom.exists_cmPoint_frame_ne_zero_of_dominant <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity

section

@[expose] public section

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
noncomputable section
namespace GlobalTheory.CovTop.GoodDom
set_option maxHeartbeats 1000000 in
theorem weight_lattice_fg_on_domain : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) →
    FiniteDimensional Y.d.c₂.F (Y.V (wtOf _ la 0)) → (GlobalTheory.AllWt.latW Y.U (wtOf _ la 0)).FG := by
  intro hP D T j Y e o hG hE hp hq la hA hb hfd
  letI := T.Q.H.starRing
  refine GlobalTheory.fg_of_integral_functionals Y.d.c₂.F (Y.V (wtOf _ la 0)) _ fun x hx => ?_
  obtain ⟨z, La, y, hz, hyx, hne⟩ := _root_.GlobalTheory.T.cmPoint_detects_dominant_covering hP D T j Y e o hG hE hp hq la hA hb (fun _ => rfl) x.1 x.2
    (fun h => hx (Subtype.ext h))
  obtain ⟨N, hN, hint⟩ := GlobalTheory.T.exists_frame_denominator_dominant_weight_cm _ _ _ _ _ _ z _ La hz y hyx hp hq la hA hb
  refine ⟨z.K, inferInstance, inferInstance, inferInstance,
    { toFun := fun F => N * evR Y.d.Xo₂ Y.d.c₂ F.1 y
      map_add' := fun F G => ?_
      map_smul' := fun s F => ?_ }, mul_ne_zero hN hne, fun F hF => hint F.1 (GlobalTheory.AllWt.cuspW_le_secZ _ F.2) hF⟩
  · rw [← mul_add]
    exact congrArg _ (evalAt_add _ _ F.1 G.1 y)
  · have e1 : evR Y.d.Xo₂ Y.d.c₂ (s • F).1 y = algebraMap Y.d.c₂.F z.K s * evR Y.d.Xo₂ Y.d.c₂ F.1 y :=
      evalAt_smul _ _ s F.1 y
    rw [e1, RingHom.id_apply, Algebra.smul_def, mul_left_comm]
set_option maxHeartbeats 800000 in
theorem weight_lattice_span_on_domain : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ),
    Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) →
    Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.latW Y.U (wtOf _ la 0) : Set (Y.V (wtOf _ la 0))) = ⊤ := by
  intro hP D T j Y e o hY hE hp hq la hA hb
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨k, a, n, g, h, t, hdom, hn, hmem, ht, hgh, hh⟩ := _root_.GlobalTheory.T.weight_match_pow_mul_cuspidal hP D T j Y e o hY hE hp hq la hA hb f.1 f.2
  obtain ⟨s, hs, hsv⟩ := _root_.GlobalTheory.T.divisor_multiple_nonneg_eventually hP D T j Y e o hY hE a n hdom hn _ hmem
  have key : ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la',
      0 ≤ v ((s * t) • ((f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1))) := by
    intro la' v hv
    have hV := isVal_valSet la' v hv
    have e1 : (s • ((f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1) * g)) * h = (s * t) • ((f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1)) := by
      rw [smul_mul_assoc, mul_assoc, hgh, mul_smul_comm, mul_one, smul_smul]
    rw [← e1, hV.mul]
    exact add_nonneg (hsv la' v hv) (hh la' v hv)
  obtain ⟨s', hs', h'⟩ := GlobalTheory.SupFull.exists_smul_nonneg_of_pow (valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂))
    (fun la => isVal_valSet la) {(f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1)}
    (by rintro g' rfl; exact ⟨s * t, mul_ne_zero hs ht, key⟩) (f : Rul Y.d.Xo₂ Y.d.c₂) k
    (Submodule.subset_span rfl)
  have hmem' : s' • f ∈ GlobalTheory.AllWt.latW Y.U (wtOf _ la 0) :=
    GlobalTheory.AllWt.mem_supLat.2 fun la v hv => h' la v hv
  rw [← inv_smul_smul₀ hs' f]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem')
set_option maxHeartbeats 1000000 in
theorem covering_regular_at_domain : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Y.GoodAt (wtOf _ la 0) ∧ ∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ la 0) := by
  intro hP D T hL j hp hq hE _ Y e o hY la hA hb
  have hfd := GlobalTheory.Deep.finiteDimensional_V_of_good D T.toCore j Y e o hY (wtOf _ la 0)
  have hG : Y.GoodAt (wtOf _ la 0) :=
    ⟨hasGram_nrm_of_good D T.toCore j Y e o hY _, _root_.GlobalTheory.CovTop.GoodDom.weight_lattice_fg_on_domain hP D T.toCore j Y e o hY hE hp hq la hA hb hfd,
      _root_.GlobalTheory.CovTop.GoodDom.weight_lattice_span_on_domain hP D T.toCore j Y e o hY hE hp hq la hA hb⟩
  exact ⟨hG, fun Z => goodOn_of_goodAt D T.toCore j Y e o hY hE Z _ hG⟩
end GlobalTheory.CovTop.GoodDom
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.covering_domain_lattice_regularity : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Y.GoodAt (wtOf _ la 0) ∧ ∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ la 0) := by
  first | exact @_root_.GlobalTheory.CovTop.GoodDom.covering_regular_at_domain | exact _root_.GlobalTheory.CovTop.GoodDom.covering_regular_at_domain | (intros; apply _root_.GlobalTheory.CovTop.GoodDom.covering_regular_at_domain <;> assumption)
end
end
end
